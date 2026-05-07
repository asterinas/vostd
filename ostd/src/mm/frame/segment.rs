// SPDX-License-Identifier: MPL-2.0
//! A contiguous range of frames.
use vstd::prelude::*;
use vstd_extra::seq_extra::seq_tracked_split_at;

use core::{fmt::Debug, ops::Range};

use crate::mm::frame::{has_safe_slot, untyped::AnyUFrameMeta, Frame};
use crate::mm::page_table::RCClone;

use vstd_extra::cast_ptr::*;
use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use super::meta::mapping::{frame_to_index, frame_to_index_spec, frame_to_meta, meta_addr};
use super::{AnyFrameMeta, GetFrameError, MetaSlot};
use crate::mm::{paddr_to_vaddr, Paddr, PagingLevel, Vaddr};
use vstd::simple_pptr;
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::virt_mem_newer::MemView;
use vstd_extra::drop_tracking::*;

verus! {

/// A contiguous range of homogeneous physical memory frames.
///
/// This is a handle to multiple contiguous frames. It will be more lightweight
/// than owning an array of frame handles.
///
/// The ownership is achieved by the reference counting mechanism of frames.
/// When constructing a [`Segment`], the frame handles are created then
/// forgotten, leaving the reference count. When dropping a it, the frame
/// handles are restored and dropped, decrementing the reference count.
///
/// All the metadata of the frames are homogeneous, i.e., they are of the same
/// type.
#[repr(transparent)]
pub struct Segment<M: AnyFrameMeta + ?Sized> {
    /// The physical address range of the segment.
    pub range: Range<Paddr>,
    /// Marker for the metadata type.
    pub _marker: core::marker::PhantomData<M>,
}

impl<M: AnyFrameMeta + ?Sized> TrackDrop for Segment<M> {
    type State = (MetaRegionOwners, SegmentOwner<M>);

    open spec fn constructor_requires(self, s: Self::State) -> bool {
        true
    }

    open spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        s0 =~= s1
    }

    proof fn constructor_spec(self, tracked s: &mut Self::State) {
    }

    open spec fn drop_requires(self, s: Self::State) -> bool {
        let (regions, owner) = s;
        &&& self.inv()
        &&& self.wf(&owner)
        &&& owner.inv()
        &&& regions.inv()
        // The structural correspondence (slot present, raw_count == 1, perm
        // matches slot, distinct indices, etc.) is captured by `relate_regions`.
        &&& owner.relate_regions(regions)
        // Drop-specific last-ref condition: when ref_count == 1, the slot
        // has its inner storage initialized and is not on a list.
        &&& forall|i: int|
            #![trigger owner.perms[i]]
            0 <= i < owner.perms.len() as int ==> {
                let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                regions.slot_owners[idx].inner_perms.ref_count.value() == 1 ==> {
                    &&& regions.slot_owners[idx].inner_perms.storage.is_init()
                    &&& regions.slot_owners[idx].inner_perms.in_list.value() == 0
                }
            }
    }

    open spec fn drop_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        true
    }

    proof fn drop_tracked(self, tracked s: &mut Self::State) {
    }
}

/// A [`SegmentOwner<M>`] holds the permission tokens for all frames in the
/// [`Segment<M>`] for verification purposes.
///
/// The `range` field tracks which physical-address range this owner corresponds
/// to. It is a ghost-only field used by [`Self::inv`] to express the structural
/// connection between `perms` and the segment's frames.
pub tracked struct SegmentOwner<M: AnyFrameMeta + ?Sized> {
    /// The physical-address range of the segment that this owner corresponds to.
    pub ghost range: Range<Paddr>,
    /// The slot-pointer permissions for all frames in the segment.
    /// Inner permissions for each slot live exclusively in
    /// `regions.slot_owners[idx].inner_perms`; this `Seq` carries only the
    /// `simple_pptr::PointsTo<MetaSlot>` per frame.
    pub perms: Seq<simple_pptr::PointsTo<MetaSlot>>,
    pub _marker: core::marker::PhantomData<M>,
}

impl<M: AnyFrameMeta + ?Sized> Inv for Segment<M> {
    /// The invariant of a [`Segment`]:
    ///
    /// - the physical addresses of the frames are aligned and within bounds.
    /// - the range is well-formed, i.e., the start is less than or equal to the end.
    open spec fn inv(self) -> bool {
        &&& self.range.start % PAGE_SIZE == 0
        &&& self.range.end % PAGE_SIZE == 0
        &&& self.range.start <= self.range.end < MAX_PADDR
    }
}

impl<M: AnyFrameMeta + ?Sized> Inv for SegmentOwner<M> {
    /// The invariant of a [`SegmentOwner`]:
    ///
    /// - the tracked `range` is page-aligned and within bounds;
    /// - the number of permissions matches the number of frames in the range;
    /// - each permission's address corresponds to the meta slot of its frame
    ///   (so consecutive permissions are spaced by `META_SLOT_SIZE`);
    /// - each permission is initialized and individually well-formed.
    open spec fn inv(self) -> bool {
        &&& self.range.start % PAGE_SIZE == 0
        &&& self.range.end % PAGE_SIZE == 0
        &&& self.range.start <= self.range.end < MAX_PADDR
        &&& self.perms.len() * PAGE_SIZE == self.range.end - self.range.start
        &&& forall|i: int|
            #![trigger self.perms[i]]
            0 <= i < self.perms.len() as int ==> {
                &&& self.perms[i].addr() == meta_addr(
                    frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
                )
                // Meta slots are 64-byte aligned, not page-aligned.
                // (Pre-WIP this was `% PAGE_SIZE == 0`, which is unsatisfiable for
                // any segment whose start_paddr isn't 256KB-aligned and silently
                // made bodies with `owner.inv()` in their precondition verify
                // vacuously — independently of the inner_perms duplication issue.)
                &&& self.perms[i].addr() % super::meta::mapping::META_SLOT_SIZE == 0
                &&& self.perms[i].addr() < MAX_PADDR
                &&& self.perms[i].is_init()
            }
    }
}

impl<M: AnyFrameMeta + ?Sized> SegmentOwner<M> {
    /// The cross-object relation between a [`SegmentOwner`] and the global
    /// [`MetaRegionOwners`].
    ///
    /// For every frame `i` in the segment, this asserts:
    /// - the slot owner is present in `regions` and the perm matches it,
    /// - the slot's `self_addr` is consistent with its index,
    /// - the slot has a live, non-`UNUSED` reference count,
    /// - `raw_count == 1` (the segment holds one forgotten reference per frame),
    /// - the slot's perm is *not* in `regions.slots` (it lives in `self.perms`),
    /// - distinct frames in the segment map to distinct slot indices.
    ///
    /// This is an invariant preserved by every operation that transforms a
    /// `SegmentOwner` together with `MetaRegionOwners` — analogous to
    /// [`UniqueFrameOwner::global_inv`] but spanning all frames in a segment.
    pub open spec fn relate_regions(self, regions: MetaRegionOwners) -> bool {
        &&& forall|i: int|
            #![trigger self.perms[i]]
            0 <= i < self.perms.len() as int ==> {
                let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                &&& regions.slot_owners.contains_key(idx)
                &&& !regions.slots.contains_key(idx)
                &&& regions.slot_owners[idx].raw_count == 1
                &&& regions.slot_owners[idx].self_addr == meta_addr(idx)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    != super::meta::REF_COUNT_UNUSED
                &&& self.perms[i].value().wf(regions.slot_owners[idx])
            }
        &&& forall|i: int, j: int|
            #![trigger self.perms[i], self.perms[j]]
            0 <= i < j < self.perms.len() as int ==>
                frame_to_index((self.range.start + i * PAGE_SIZE) as usize)
                    != frame_to_index((self.range.start + j * PAGE_SIZE) as usize)
    }
}

impl<M: AnyFrameMeta + ?Sized> Segment<M> {
    /// The well-formedness relation between a [`Segment`] and its owner:
    ///
    /// - the segment's range matches the range tracked by the owner;
    /// - the number of permissions in the owner matches the number of frames in the segment;
    /// - the physical address of each permission matches the corresponding frame in the segment.
    ///
    /// This is *only* the cross-object relation; callers are expected to also
    /// state `self.inv()` (and where relevant `owner.inv()`) alongside. With
    /// `owner.inv()` the perm-address and length conjuncts are consequences of
    /// `self.range == owner.range`, but they are kept here for trigger
    /// availability at sites that don't invoke `owner.inv()`.
    ///
    /// Interested readers are encouraged to see [`frame_to_index`] and [`meta_addr`] for how
    /// we convert between physical addresses and meta region indices.
    pub open spec fn wf(&self, owner: &SegmentOwner<M>) -> bool {
        &&& self.range == owner.range
        &&& owner.perms.len() * PAGE_SIZE == self.range.end - self.range.start
        &&& forall|i: int|
            #![trigger owner.perms[i]]
            0 <= i < owner.perms.len() as int ==> owner.perms[i].addr() == meta_addr(
                frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
            )
    }

    /// Whether a [`MemView`] covers the segment through the kernel direct mapping.
    ///
    /// This predicate only describes the virtual-to-physical relation and the
    /// presence of initialized backing frame contents.
    pub open spec fn kernel_mem_view_covers(&self, view: &MemView) -> bool {
        &&& self.inv()
        &&& view.mappings.finite()
        &&& view.mappings_are_disjoint()
        &&& forall|vaddr: Vaddr|
            #![trigger view.addr_transl(vaddr)]
            paddr_to_vaddr(self.range.start) <= vaddr < paddr_to_vaddr(self.range.start)
                + self.range.end - self.range.start ==> {
                &&& view.addr_transl(vaddr) is Some
                &&& view.memory.contains_key(view.addr_transl(vaddr).unwrap().0)
                &&& view.memory[view.addr_transl(vaddr).unwrap().0].inv()
                &&& view.memory[view.addr_transl(vaddr).unwrap().0].contents[view.addr_transl(
                    vaddr,
                ).unwrap().1 as int] is Init
            }
        &&& forall|paddr: Paddr|
            #![trigger paddr_to_vaddr(paddr)]
            self.range.start <= paddr < self.range.end ==> {
                let vaddr = paddr_to_vaddr(paddr);
                &&& view.addr_transl(vaddr) is Some
                &&& view.addr_transl(vaddr).unwrap().0 <= paddr
                &&& paddr < view.addr_transl(vaddr).unwrap().0 + view.memory[view.addr_transl(
                    vaddr,
                ).unwrap().0].size@
                &&& view.addr_transl(vaddr).unwrap().1 == paddr - view.addr_transl(vaddr).unwrap().0
                &&& view.memory.contains_key(view.addr_transl(vaddr).unwrap().0)
                &&& view.memory[view.addr_transl(vaddr).unwrap().0].inv()
                &&& view.memory[view.addr_transl(vaddr).unwrap().0].contents[view.addr_transl(
                    vaddr,
                ).unwrap().1 as int] is Init
            }
    }
}

/// A contiguous range of homogeneous untyped physical memory frames that have any metadata.
///
/// In other words, the metadata of the frames are of the same type, and they
/// are untyped, but the type of metadata is not known at compile time. An
/// [`USegment`] as a parameter accepts any untyped segments.
///
/// The usage of this frame will not be changed while this object is alive.
pub type USegment = Segment<dyn AnyUFrameMeta>;

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Segment<M> {
    /// Returns the starting physical address of the contiguous frames.
    #[verifier::inline]
    pub open spec fn start_paddr_spec(&self) -> Paddr
        recommends
            self.inv(),
    {
        self.range.start
    }

    /// Returns the ending physical address of the contiguous frames.
    #[verifier::inline]
    pub open spec fn end_paddr_spec(&self) -> Paddr
        recommends
            self.inv(),
    {
        self.range.end
    }

    /// Returns the length in bytes of the contiguous frames.
    #[verifier::inline]
    pub open spec fn size_spec(&self) -> usize
        recommends
            self.inv(),
    {
        (self.range.end - self.range.start) as usize
    }

    /// Returns the number of pages of the contiguous frames.
    #[verifier::inline]
    pub open spec fn nrpage_spec(&self) -> usize
        recommends
            self.inv(),
    {
        self.size_spec() / PAGE_SIZE
    }

    /// Splits the contiguous frames into two at the given byte offset from the start in spec mode.
    pub open spec fn split_spec(self, offset: usize) -> (Self, Self)
        recommends
            self.inv(),
            offset % PAGE_SIZE == 0,
            0 < offset < self.size_spec(),
    {
        let at = (self.range.start + offset) as usize;
        let idx = at / PAGE_SIZE;
        (
            Self { range: self.range.start..at, _marker: core::marker::PhantomData },
            Self { range: at..self.range.end, _marker: core::marker::PhantomData },
        )
    }

    /// Gets the start physical address of the contiguous frames.
    #[inline(always)]
    #[verifier::when_used_as_spec(start_paddr_spec)]
    pub fn start_paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        returns
            self.start_paddr_spec(),
    {
        self.range.start
    }

    /// Gets the end physical address of the contiguous frames.
    #[inline(always)]
    #[verifier::when_used_as_spec(end_paddr_spec)]
    pub fn end_paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        returns
            self.end_paddr_spec(),
    {
        self.range.end
    }

    /// Gets the length in bytes of the contiguous frames.
    #[inline(always)]
    #[verifier::when_used_as_spec(size_spec)]
    pub fn size(&self) -> (res: usize)
        requires
            self.inv(),
        returns
            self.size_spec(),
    {
        self.range.end - self.range.start
    }

    /// The wrapper for the precondition for [`Self::from_unused`]:
    ///
    /// - the metadata function must be well-formed and valid for all frames in the range;
    /// - the metadata function must ensure that the frames can be created and owned by the segment.
    /// - for any frame created via the closure `metadata_fn`, the corresponding slot in `regions`
    ///   must be unused and not dropped in the owner ([`MetaRegionOwners`]).
    pub open spec fn from_unused_requires(
        regions: MetaRegionOwners,
        range: Range<Paddr>,
        metadata_fn: impl Fn(Paddr) -> (Paddr, M),
    ) -> bool {
        &&& regions.inv()
        &&& range.start % PAGE_SIZE == 0
        &&& range.end % PAGE_SIZE == 0
        &&& range.start <= range.end < MAX_PADDR
        &&& forall|paddr_in: Paddr|
            (range.start <= paddr_in < range.end && paddr_in % PAGE_SIZE == 0) ==> {
                &&& metadata_fn.requires((paddr_in,))
            }
        &&& forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
            metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> {
                &&& paddr_out < MAX_PADDR
                &&& paddr_out % PAGE_SIZE == 0
                &&& paddr_in == paddr_out
                &&& regions.slots.contains_key(frame_to_index(paddr_out))
                &&& regions.slot_owners[frame_to_index(paddr_out)].usage is Unused
                &&& regions.slot_owners[frame_to_index(paddr_out)].inner_perms.in_list.points_to(0)
            }
    }

    /// The wrapper for the postcondition for [`Self::from_unused`]:
    ///
    /// - if the result is `Ok`, then the returned segment must satisfy the invariant with the owner;
    /// - the returned segment must have the same physical address range as the input;
    /// - the returned owner must be `Some` if the result is `Ok`, and the owner must satisfy the invariant;
    pub open spec fn from_unused_ensures(
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        owner: Option<SegmentOwner<M>>,
        range: Range<Paddr>,
        metadata_fn: impl Fn(Paddr) -> (Paddr, M),
        r: Result<Self, GetFrameError>,
    ) -> bool {
        &&& r matches Ok(r) ==> {
            &&& new_regions.inv()
            &&& r.range.start == range.start
            &&& r.range.end == range.end
            &&& owner matches Some(owner) && {
                &&& r.inv()
                &&& r.wf(&owner)
                &&& forall|i: int|
                    #![trigger owner.perms[i]]
                    0 <= i < owner.perms.len() as int ==> {
                        &&& owner.perms[i].addr() == meta_addr(
                            frame_to_index_spec((range.start + i * PAGE_SIZE) as usize),
                        )
                    }
                &&& forall|paddr: Paddr|
                    #![trigger frame_to_index_spec(paddr)]
                    (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                        ==> !new_regions.slots.contains_key(frame_to_index_spec(paddr))
            }
        }
    }

    /// The wrapper for the precondition for [`Self::split`]:
    ///
    /// - the segment must satisfy its invariant ([`Self::inv`]) and the well-formedness
    ///   relation with the owner ([`Self::wf`]);
    /// - the offset must be aligned and within bounds;
    /// - the meta region must be valid and the owner must relate to it.
    pub open spec fn split_requires(
        self,
        owner: SegmentOwner<M>,
        offset: usize,
        regions: MetaRegionOwners,
    ) -> bool {
        &&& self.inv()
        &&& self.wf(&owner)
        &&& offset % PAGE_SIZE == 0
        &&& 0 < offset < self.size()
        &&& regions.inv()
        &&& owner.relate_regions(regions)
    }

    /// The wrapper for the postcondition for [`Self::split`]:
    ///
    /// - the resulting segments must satisfy the invariant with the corresponding owners;
    /// - the resulting segments must be the same as the result of [`Self::split_spec`];
    /// - the permissions in the original owner must be split into the resulting owners;
    /// - both halves continue to relate correctly to `regions` (which is unchanged).
    pub open spec fn split_ensures(
        self,
        offset: usize,
        lhs: Self,
        rhs: Self,
        ori_owner: SegmentOwner<M>,
        lhs_owner: SegmentOwner<M>,
        rhs_owner: SegmentOwner<M>,
        regions: MetaRegionOwners,
    ) -> bool {
        &&& lhs.inv()
        &&& lhs.wf(&lhs_owner)
        &&& rhs.inv()
        &&& rhs.wf(&rhs_owner)
        &&& (lhs, rhs) == self.split_spec(offset)
        &&& ori_owner.perms =~= (lhs_owner.perms + rhs_owner.perms)
        &&& lhs_owner.relate_regions(regions)
        &&& rhs_owner.relate_regions(regions)
    }

    /// The wrapper for the precondition for [`Self::into_raw`]:
    ///
    /// - the segment must satisfy the invariant with the owner;
    /// - the meta region in `regions` must satisfy the invariant;
    /// - the owner must relate correctly to `regions`.
    pub open spec fn into_raw_requires(
        self,
        regions: MetaRegionOwners,
        owner: SegmentOwner<M>,
    ) -> bool {
        &&& self.inv()
        &&& self.wf(&owner)
        &&& regions.inv()
        &&& owner.inv()
        &&& owner.relate_regions(regions)
    }

    /// The wrapper for the postcondition for [`Self::into_raw`]:
    ///
    /// - the returned physical address range must be the same as the segment's range;
    /// - the meta region is unchanged (so the relation with the returned owner is preserved).
    pub open spec fn into_raw_ensures(
        self,
        old_regions: MetaRegionOwners,
        regions: MetaRegionOwners,
        r: Range<Paddr>,
    ) -> bool {
        &&& r == self.range
        &&& regions.inv()
        &&& regions =~= old_regions
    }

    /// The wrapper for the precondition for [`Self::from_raw`]:
    ///
    /// - the meta region must satisfy its invariant;
    /// - the segment-to-be (with the supplied `range`) must satisfy its invariant
    ///   ([`Self::inv`]) and the well-formedness relation with `owner` ([`Self::wf`]);
    /// - `owner` must relate correctly to `regions`.
    ///
    /// Following the [`UniqueFrame::from_raw`] pattern, the contract here ties
    /// `range` and `owner` together up front so that the postcondition can
    /// directly advertise `r.inv()` and `r.wf(&owner)` for the caller.
    pub open spec fn from_raw_requires(
        regions: MetaRegionOwners,
        range: Range<Paddr>,
        owner: SegmentOwner<M>,
    ) -> bool {
        let as_segment = Segment::<M> { range, _marker: core::marker::PhantomData };
        &&& regions.inv()
        &&& owner.inv()
        &&& as_segment.wf(&owner)
        &&& owner.relate_regions(regions)
    }

    /// The wrapper for the postcondition for [`Self::from_raw`]:
    ///
    /// - the returned segment satisfies its invariant and is well-formed with `owner`;
    /// - the returned segment has the same physical address range as the input;
    /// - the meta region is unchanged (so the relation with `owner` is preserved).
    pub open spec fn from_raw_ensures(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        owner: SegmentOwner<M>,
        range: Range<Paddr>,
    ) -> bool {
        &&& self.range == range
        &&& self.inv()
        &&& self.wf(&owner)
        &&& new_regions.inv()
        &&& new_regions =~= old_regions
    }

    /// The wrapper for the precondition for slicing a segment with a given range:
    ///
    /// - the segment must satisfy its invariant ([`Self::inv`]) and the well-formedness
    ///   relation with the owner ([`Self::wf`]);
    /// - the slicing range must be aligned and within bounds of the segment;
    /// - the meta region must be valid and the owner must relate to it.
    pub open spec fn slice_requires(
        self,
        owner: SegmentOwner<M>,
        range: Range<Paddr>,
        regions: MetaRegionOwners,
    ) -> bool {
        &&& self.inv()
        &&& self.wf(&owner)
        &&& range.start % PAGE_SIZE == 0
        &&& range.end % PAGE_SIZE == 0
        &&& self.range.start + range.start <= self.range.start + range.end <= self.range.end
        &&& regions.inv()
        &&& owner.relate_regions(regions)
    }

    /// The wrapper for the postcondition for slicing a segment with a given range:
    ///
    /// - the resulting slice must satisfy the invariant with the constructed sub-owner;
    /// - the resulting slice must have the same physical address range as the slicing range;
    /// - the constructed sub-owner relates correctly to `regions`.
    ///
    /// See also [`vstd::seq::Seq::subrange`].
    pub open spec fn slice_ensures(
        self,
        owner: SegmentOwner<M>,
        range: Range<Paddr>,
        res: Self,
        regions: MetaRegionOwners,
    ) -> bool {
        let sub_owner = SegmentOwner {
            range: (self.range.start + range.start) as usize..(self.range.start
                + range.end) as usize,
            perms: owner.perms.subrange(
                (range.start / PAGE_SIZE) as int,
                (range.end / PAGE_SIZE) as int,
            ),
            _marker: core::marker::PhantomData,
        };
        &&& res.inv()
        &&& res.wf(&sub_owner)
        &&& sub_owner.relate_regions(regions)
    }

    /// Checks if the current segment can be iterated to get the next frame:
    ///
    /// - segment, owner, and meta regions must satisfy their respective invariants;
    /// - the segment is well-formed with the owner;
    /// - the owner relates correctly to `regions` (forgotten reference, slot
    ///   present and consistent, etc. — see [`SegmentOwner::relate_regions`]).
    ///
    /// All the per-frame coherence conditions previously listed inline are now
    /// consequences of `owner.relate_regions(regions)` instantiated at `i = 0`.
    pub open spec fn next_requires(
        self,
        regions: MetaRegionOwners,
        owner: SegmentOwner<M>,
    ) -> bool {
        &&& self.inv()
        &&& self.wf(&owner)
        &&& owner.inv()
        &&& regions.inv()
        &&& owner.relate_regions(regions)
    }

    /// The wrapper for the postcondition for iterating to the next frame:
    ///
    /// - if the result is [`None`], then the segment has been exhausted;
    /// - if the result is [`Some`], then the segment is advanced by one frame and
    ///   the returned frame is the next frame, with its slot restored to `regions`;
    /// - the new owner continues to relate correctly to the new regions.
    pub open spec fn next_ensures(
        old_self: Self,
        new_self: Self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        new_owner: SegmentOwner<M>,
        res: Option<Frame<M>>,
    ) -> bool {
        &&& new_regions.inv()
        &&& new_self.inv()
        &&& new_owner.relate_regions(new_regions)
        &&& match res {
            None => { &&& new_self.range.start == old_self.range.end },
            Some(f) => {
                &&& new_self.range.start == old_self.range.start + PAGE_SIZE
                &&& f.paddr() == old_self.range.start
                &&& new_regions.slots.contains_key(frame_to_index(f.paddr()))
                &&& new_regions.slot_owners[frame_to_index(f.paddr())].raw_count == 0
            },
        }
    }

    /// Creates a new [`Segment`] from unused frames.
    ///
    /// The caller must provide a closure to initialize metadata for all the frames.
    /// The closure receives the physical address of the frame and returns the
    /// metadata, which is similar to [`core::array::from_fn`].
    ///
    /// It returns an error if:
    ///  - any of the frames cannot be created with a specific reason.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// See [`Self::from_unused_requires`].
    /// ## Postconditions
    /// See [`Self::from_unused_ensures`].
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
                -> owner: Tracked<Option<SegmentOwner<M>>>,
        requires
            Self::from_unused_requires(*old(regions), range, metadata_fn),
        ensures
            Self::from_unused_ensures(*old(regions), *final(regions), owner@, range, metadata_fn, r),
    )]
    pub fn from_unused(range: Range<Paddr>, metadata_fn: impl Fn(Paddr) -> (Paddr, M)) -> (res:
        Result<Self, GetFrameError>) {
        proof_decl! {
            let tracked mut owner: Option<SegmentOwner<M>> = None;
            let tracked mut addrs = Seq::<usize>::tracked_empty();
            let tracked mut perms = Seq::<simple_pptr::PointsTo<MetaSlot>>::tracked_empty();
        }
        // Construct a segment early to recycle previously forgotten frames if
        // the subsequent operations fails in the middle.
        let mut segment = Self {
            range: range.start..range.start,
            _marker: core::marker::PhantomData,
        };

        let mut i = 0;
        let addr_len = (range.end - range.start) / PAGE_SIZE;

        #[verus_spec(
            invariant
                i <= addr_len,
                i as int == addrs.len(),
                i as int == perms.len(),
                range.start % PAGE_SIZE == 0,
                range.end % PAGE_SIZE == 0,
                range.start <= range.start + i * PAGE_SIZE <= range.end,
                range.end == range.start + addr_len * PAGE_SIZE,
                addr_len == (range.end - range.start) / PAGE_SIZE as int,
                i <= addr_len,
                forall|paddr_in: Paddr|
                    (range.start + i * PAGE_SIZE <= paddr_in < range.end && paddr_in % PAGE_SIZE == 0) ==> {
                        &&& metadata_fn.requires((paddr_in,))
                    },
                forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
                    range.start + i * PAGE_SIZE <= paddr_in < range.end
                        && paddr_in % PAGE_SIZE == 0
                        && metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> {
                        &&& paddr_out < MAX_PADDR
                        &&& paddr_out % PAGE_SIZE == 0
                        &&& paddr_in == paddr_out
                        &&& regions.slots.contains_key(frame_to_index(paddr_out))
                        &&& regions.slot_owners[frame_to_index(paddr_out)].usage is Unused
                        &&& regions.slot_owners[frame_to_index(paddr_out)].inner_perms.in_list.points_to(0)
                    },
                forall|j: int|
                    0 <= j < addrs.len() as int ==> {
                        &&& !regions.slots.contains_key(frame_to_index_spec(addrs[j]))
                        &&& addrs[j] % PAGE_SIZE == 0
                        &&& addrs[j] < MAX_PADDR
                        &&& addrs[j] == range.start + (j as u64) * PAGE_SIZE
                    },
                forall|j: int|
                    #![trigger perms[j]]
                    0 <= j < perms.len() as int ==> {
                        &&& perms[j].addr() == frame_to_meta(addrs[j])
                        &&& perms[j].is_init()
                    },
                regions.inv(),
                segment.range.start == range.start,
                segment.range.end == range.start + i * PAGE_SIZE,
            decreases addr_len - i,
        )]
        while i < addr_len {
            let paddr_in = range.start + i * PAGE_SIZE;
            let (paddr, meta) = metadata_fn(paddr_in);

            let (frame, Tracked(frame_perm)) = match #[verus_spec(with Tracked(regions))]
            MetaSlot::get_from_unused(paddr, meta, false) {
                Ok(res) => {
                    let (ptr, Tracked(frame_perm)) = res;
                    (Frame { ptr, _marker: core::marker::PhantomData::<M> }, Tracked(frame_perm))
                },
                Err(e) => {
                    return {
                        proof_with!(|= Tracked(owner));
                        Err(e)
                    };
                },
            };

            proof {
                perms.tracked_push(frame_perm);
            }

            let _ = ManuallyDrop::new(frame, Tracked(regions));
            segment.range.end = paddr + PAGE_SIZE;
            proof {
                addrs.tracked_push(paddr);
            }

            i += 1;
        }

        proof {
            broadcast use vstd_extra::seq_extra::lemma_seq_to_set_map_contains;

            owner = Some(SegmentOwner { range, perms, _marker: core::marker::PhantomData });

            assert forall|addr: usize|
                #![trigger frame_to_index_spec(addr)]
                range.start <= addr < range.end && addr % PAGE_SIZE == 0 implies {
                &&& !regions.slots.contains_key(frame_to_index_spec(addr))
            } by {
                if !addrs.contains(addr) {
                    let j = (addr - range.start) / PAGE_SIZE as int;
                    assert(addrs[j as int] == addr);
                }
            }
        }

        proof_with!(|= Tracked(owner));
        Ok(segment)
    }

    /// Splits the frames into two at the given byte offset from the start.
    ///
    /// The resulting frames cannot be empty. So the offset cannot be neither
    /// zero nor the length of the frames.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// See [`Self::split_requires`].
    ///
    /// ## Postconditions
    /// See [`Self::split_ensures`].
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<SegmentOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
                -> frame_perms: (Tracked<SegmentOwner<M>>, Tracked<SegmentOwner<M>>),
        requires
            Self::split_requires(self, owner, offset, *old(regions)),
        ensures
            *final(regions) =~= *old(regions),
            Self::split_ensures(
                self,
                offset,
                r.0,
                r.1,
                owner,
                frame_perms.0@,
                frame_perms.1@,
                *final(regions),
            ),
    )]
    pub fn split(self, offset: usize) -> (Self, Self) {
        let at = self.range.start + offset;
        let idx = offset / PAGE_SIZE;
        let res = (
            Self { range: self.range.start..at, _marker: core::marker::PhantomData },
            Self { range: at..self.range.end, _marker: core::marker::PhantomData },
        );

        let _ = core::mem::ManuallyDrop::new(self);

        let tracked mut perms = owner.perms;
        let tracked rest = seq_tracked_split_at(&mut perms, idx as int);
        let tracked frame_perms1 = SegmentOwner { range: res.0.range, perms, _marker: core::marker::PhantomData };
        let tracked frame_perms2 = SegmentOwner { range: res.1.range, perms: rest, _marker: core::marker::PhantomData };

        proof_with!(|= (Tracked(frame_perms1), Tracked(frame_perms2)));
        res
    }

    /// Forgets the [`Segment`] and gets a raw range of physical addresses.
    ///
    /// The segment's permissions are returned to the caller via `frame_perms`.
    /// The caller is responsible for holding onto the permissions and providing
    /// them back when restoring the segment with [`Self::from_raw`].
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<SegmentOwner<M>>,
                -> frame_perms: Tracked<SegmentOwner<M>>,
        requires
            Self::into_raw_requires(self, *old(regions), owner),
        ensures
            Self::into_raw_ensures(self, *old(regions), *final(regions), r),
            frame_perms@ == owner,
    )]
    pub(crate) fn into_raw(self) -> Range<Paddr> {
        let range = self.range.clone();
        let _ = core::mem::ManuallyDrop::new(self);

        proof_with!(|= Tracked(owner));
        range
    }

    /// Restores the [`Segment`] from the raw physical address range.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// See [`Self::from_raw_requires`].
    ///
    /// ## Postconditions
    /// See [`Self::from_raw_ensures`].
    ///
    /// # Safety
    ///
    /// The range must be a forgotten [`Segment`] that matches the type `M`.
    /// The caller must provide the permissions that were returned by [`Self::into_raw`].
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<SegmentOwner<M>>,
        requires
            Self::from_raw_requires(*old(regions), range, owner),
        ensures
            Self::from_raw_ensures(r, *old(regions), *final(regions), owner, range),
    )]
    pub(crate) unsafe fn from_raw(range: Range<Paddr>) -> Self {
        Self { range, _marker: core::marker::PhantomData }
    }

    /// Gets an extra handle to the frames in the byte offset range.
    ///
    /// The sliced byte offset range in indexed by the offset from the start of
    /// the contiguous frames. The resulting frames holds extra reference counts.
    ///
    /// # Verified Properties
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// See [`Self::slice_requires`].
    ///
    /// ## Postconditions
    /// See [`Self::slice_ensures`].
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&SegmentOwner<M>>,
            Tracked(regions): Tracked<&MetaRegionOwners>,
        requires
            Self::slice_requires(*self, *owner, *range, *regions),
        ensures
            Self::slice_ensures(*self, *owner, *range, r, *regions),
    )]
    pub fn slice(&self, range: &Range<Paddr>) -> Self {
        let start = self.range.start + range.start;
        let end = self.range.start + range.end;

        let mut i = 0;
        let addr_len = (end - start) / PAGE_SIZE;
        while i < addr_len
            invariant
                start % PAGE_SIZE == 0,
                end % PAGE_SIZE == 0,
                start + i * PAGE_SIZE <= end,
                i <= addr_len,
                addr_len == (end - start) / PAGE_SIZE as int,
            decreases addr_len - i,
        {
            let paddr = start + i * PAGE_SIZE;
            // SAFETY: We already have reference counts for the frames since
            // for each frame there would be a forgotten handle when creating
            // the `Segment` object.
            // unsafe { inc_frame_ref_count(paddr); }
            i += 1;
        }

        Self { range: start..end, _marker: core::marker::PhantomData }
    }

    /// Gets the next frame in the segment (raw), if any.
    ///
    /// Since the segments here must be "non-active" where
    /// there is no extra Verus-tracked permission [`SegmentOwner`]
    /// associated with it; [`Segment`] becomes a kind of "zombie"
    /// container through which we can only iterate the frames and
    /// get the frame out of the `regions` instead.
    ///
    /// # Note
    ///
    /// We chose to make `next` the member function of [`Segment`] rather than a trait method
    /// because the current Verus standard library has limited support for [`core::iter::Iterator`]
    /// and associated types, and we want to avoid the complexity of defining a custom iterator trait
    /// and implementing it for `Segment`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// See [`Self::next_requires`].
    ///
    /// ## Postconditions
    /// See [`Self::next_ensures`].
    #[verus_spec(res =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut SegmentOwner<M>>
        requires
            Self::next_requires(*old(self), *old(regions), *old(owner)),
        ensures
            Self::next_ensures(
                *old(self),
                *final(self),
                *old(regions),
                *final(regions),
                *final(owner),
                res,
            ),
    )]
    pub fn next(&mut self) -> Option<Frame<M>> {
        if self.range.start < self.range.end {
            let tracked perm = owner.perms.tracked_remove(0);

            proof_decl! {
                let tracked from_raw_debt: crate::specs::mm::frame::frame_specs::BorrowDebt;
            }

            let frame = unsafe {
                #[verus_spec(with Tracked(regions), Tracked(&perm) => Tracked(from_raw_debt))]
                Frame::<M>::from_raw(self.range.start)
            };

            proof {
                // raw_count was 1 (segment was forgotten via into_raw), so discharge trivially.
                from_raw_debt.discharge_bookkeeping();
            }

            self.range.start = self.range.start + PAGE_SIZE;
            Some(frame)
        } else {
            None
        }
    }
}

impl<M: AnyFrameMeta + ?Sized> Drop for Segment<M> {
    /// Verified drop: iterates over each frame in the segment, decrements its
    /// reference count, and if it was the last reference, tears down the metadata.
    fn drop(self, Tracked(s): Tracked<(MetaRegionOwners, SegmentOwner<M>)>) -> (res: Tracked<(MetaRegionOwners, SegmentOwner<M>)>)
    {
        let tracked (mut regions, mut owner) = s;
        let ghost n = owner.perms.len();
        let mut paddr = self.range.start;

        let ghost mut k: int = 0;

        let ghost old_regions = regions;
        let ghost old_owner = owner;

        // Helper spec: the frame index for the j-th frame in the segment
        let ghost frame_idx = |j: int| -> usize { frame_to_index((self.range.start + j * PAGE_SIZE) as usize) };

        loop
            invariant
                regions.inv(),
                self.inv(),
                self.range.start <= paddr <= self.range.end,
                paddr == (self.range.start + k * PAGE_SIZE) as usize,
                paddr % PAGE_SIZE == 0,
                paddr < MAX_PADDR,
                0 <= k <= n,
                n == (self.range.end - self.range.start) as int / PAGE_SIZE as int,
                owner.perms.len() == n - k,
                paddr < self.range.end <==> k < n,
                // Remaining owner.perms are the suffix of the original
                forall|j: int|
                    #![trigger owner.perms[j]]
                    0 <= j < (n - k) ==>
                        owner.perms[j] == old_owner.perms[j + k],
                // Unprocessed frames' slot_owners are present and unchanged
                forall|j: int| #![trigger old_owner.perms[j]]
                    k <= j < n ==> {
                        &&& regions.slot_owners.contains_key(frame_idx(j))
                        &&& regions.slot_owners[frame_idx(j)] == old_regions.slot_owners[frame_idx(j)]
                    },
                // Slots not belonging to any frame in the segment are unchanged
                forall|si: usize| #![trigger regions.slot_owners[si]]
                    (forall|j: int| #![trigger old_owner.perms[j]]
                        0 <= j < n ==> si != frame_idx(j))
                    ==> regions.slot_owners[si] == old_regions.slot_owners[si],
                // slots map: processed frames' PointsTo re-inserted, rest unchanged
                forall|si: usize| #![trigger regions.slots[si]]
                    (forall|j: int| #![trigger old_owner.perms[j]]
                        0 <= j < k ==> si != frame_idx(j))
                    ==> regions.slots.contains_key(si) == old_regions.slots.contains_key(si),
                // Distinct indices (from drop_requires, propagated)
                forall|i: int, j: int|
                    #![trigger old_owner.perms[i], old_owner.perms[j]]
                    0 <= i < j < n ==> frame_idx(i) != frame_idx(j),
                // Original drop_requires still holds (old_regions/old_owner are immutable ghosts)
                self.drop_requires((old_regions, old_owner)),
            decreases n - k,
        {
            if paddr >= self.range.end {
                break;
            }

            let ghost cur_idx = frame_idx(k);
            let tracked slot_perm = owner.perms.tracked_remove(0);

            // slot_perm == old_owner.perms[k] (from shift invariant)

            proof {
                assert(self.drop_requires((old_regions, old_owner)));
                let ghost idx_k = frame_to_index((self.range.start + k * PAGE_SIZE) as usize);
                assert(idx_k == cur_idx);
            }

            let ghost pre_slot_own = regions.slot_owners[cur_idx];
            let tracked mut slot_own = regions.slot_owners.tracked_remove(cur_idx);

            let meta_vaddr = frame_to_meta(paddr);
            let ptr = vstd::simple_pptr::PPtr::<super::MetaSlot>::from_addr(meta_vaddr);

            proof {
                assert(slot_perm.is_init());
                assert(slot_perm.value().wf(slot_own));
                assert(slot_perm.value().ref_count.id() == slot_own.inner_perms.ref_count.id());
                assert(slot_own.inner_perms.ref_count.value() > 0);
                assert(meta_addr(frame_to_index(paddr)) == frame_to_meta(paddr)) by {
                    assert(frame_to_index(paddr) == paddr / PAGE_SIZE);
                    assert(meta_addr(frame_to_index(paddr)) == (crate::specs::arch::kspace::FRAME_METADATA_RANGE.start + frame_to_index(paddr) * super::meta::mapping::META_SLOT_SIZE) as usize);
                }
                assert(slot_perm.pptr() == ptr);
            }

            let slot = ptr.borrow(Tracked(&slot_perm));
            let last_ref_cnt = slot.ref_count.fetch_sub(Tracked(&mut slot_own.inner_perms.ref_count), 1);

            // The segment held one forgotten reference per frame
            // (`relate_regions` => `raw_count == 1`). With this iteration
            // consuming that forgotten reference, the bookkeeping decrement
            // must happen before any potential `drop_last_in_place`.
            proof {
                slot_own.raw_count = (slot_own.raw_count - 1) as usize;
            }

            if last_ref_cnt == 1 {
                super::acquire_fence();

                proof {
                    assert(slot_own.inner_perms.ref_count.value() == 0u64);
                    assert(slot_own.raw_count == 0);
                    assert(slot_own.inner_perms.storage.is_init());
                    assert(slot_own.inner_perms.in_list.value() == 0u64);
                    assert(slot_own.inv());
                    assert(MetaSlot::drop_last_in_place_safety_cond(slot_own));
                }

                #[verus_spec(with Tracked(&mut slot_own))]
                slot.drop_last_in_place();
            }

            proof {
                let ghost mid_regions = regions;

                regions.slot_owners.tracked_insert(cur_idx, slot_own);

                assert(regions.slot_owners.dom() =~= mid_regions.slot_owners.dom().insert(cur_idx));
                assert(slot_own.inv());

                regions.slots.tracked_insert(cur_idx, slot_perm);
                assert(regions.slots.dom().finite());

                assert forall|i: usize| i < super::meta::mapping::max_meta_slots() <==>
                    #[trigger] regions.slot_owners.contains_key(i) by { }

                assert forall|i: usize| #[trigger] regions.slots.contains_key(i) implies i < super::meta::mapping::max_meta_slots() by {
                    if i == cur_idx {
                        assert(regions.slot_owners.contains_key(cur_idx));
                    }
                }

                assert forall|i: usize| #[trigger] regions.slots.contains_key(i) implies ({
                    &&& regions.slot_owners.contains_key(i)
                    &&& regions.slot_owners[i].inv()
                    &&& regions.slots[i].is_init()
                    &&& regions.slots[i].addr() == meta_addr(i)
                    &&& regions.slots[i].value().wf(regions.slot_owners[i])
                    &&& regions.slot_owners[i].self_addr == regions.slots[i].addr()
                }) by {
                    if i == cur_idx {
                        assert(regions.slots[i].is_init());
                        assert(regions.slots[i].addr() == meta_addr(i));
                        assert(regions.slots[i].value().wf(regions.slot_owners[i]));
                        assert(regions.slot_owners[i].self_addr == regions.slots[i].addr());
                    }
                }

                assert forall|i: usize| #[trigger] regions.slot_owners.contains_key(i) implies regions.slot_owners[i].inv() by {
                    if i == cur_idx {
                        assert(slot_own.inv());
                    }
                }
            }

            paddr = paddr + PAGE_SIZE;

            proof {
                k = k + 1;

                assert forall|j: int| #![trigger old_owner.perms[j]]
                    k <= j < n implies
                        regions.slot_owners[frame_idx(j)] == old_regions.slot_owners[frame_idx(j)]
                by {
                    let ghost _a = old_owner.perms[j];
                    let ghost _b = old_owner.perms[(k - 1) as int];
                    assert(frame_idx(j) != frame_idx(k - 1));
                };

                assert forall|si: usize| #![trigger regions.slot_owners[si]]
                    (forall|j: int| #![trigger old_owner.perms[j]]
                        0 <= j < n ==> si != frame_idx(j))
                    implies regions.slot_owners[si] == old_regions.slot_owners[si]
                by {
                    let ghost _trigger = old_owner.perms[(k - 1) as int];
                    assert(si != frame_idx(k - 1));
                };
            }
        }

        Tracked((regions, owner))
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> RCClone for Segment<M> {
    open spec fn clone_requires(self, perm: MetaRegionOwners) -> bool {
        &&& self.inv()
        &&& perm.inv()
        &&& forall|pa: Paddr|
            #![trigger frame_to_index(pa)]
            (self.range.start <= pa < self.range.end && pa % PAGE_SIZE == 0) ==> {
                let idx = frame_to_index(pa);
                &&& perm.slots.contains_key(idx)
                &&& has_safe_slot(pa)
                &&& perm.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& perm.slot_owners[idx].inner_perms.ref_count.value() + 1
                    < super::meta::REF_COUNT_MAX
                &&& !MetaSlot::inc_ref_count_panic_cond(
                    perm.slot_owners[idx].inner_perms.ref_count)
            }
    }

    open spec fn clone_ensures(self, old_perm: MetaRegionOwners, new_perm: MetaRegionOwners, res: Self) -> bool {
        &&& res.range == self.range
        &&& res.inv()
        &&& new_perm.inv()
    }

    fn clone(&self, Tracked(perm): Tracked<&mut MetaRegionOwners>) -> (res: Self)
    {
        let mut paddr = self.range.start;

        let ghost old_perm = *perm;
        loop
            invariant
                perm.inv(),
                self.inv(),
                perm.slots =~= old_perm.slots,
                perm.slot_owners.dom() =~= old_perm.slot_owners.dom(),
                self.range.start <= paddr <= self.range.end,
                paddr % PAGE_SIZE == 0,
                paddr < MAX_PADDR,
                forall|pa: Paddr|
                    #![trigger frame_to_index(pa)]
                    (paddr <= pa < self.range.end && pa % PAGE_SIZE == 0) ==> {
                        let idx = frame_to_index(pa);
                        &&& perm.slots.contains_key(idx)
                        &&& has_safe_slot(pa)
                        &&& perm.slot_owners[idx].inner_perms.ref_count.value() > 0
                        &&& perm.slot_owners[idx].inner_perms.ref_count.value() + 1
                            < super::meta::REF_COUNT_MAX
                        &&& !MetaSlot::inc_ref_count_panic_cond(
                            perm.slot_owners[idx].inner_perms.ref_count)
                    },
            decreases self.range.end - paddr,
        {
            if paddr >= self.range.end {
                break;
            }

            proof {
                assert(paddr + PAGE_SIZE <= self.range.end);
                assert(paddr + PAGE_SIZE <= MAX_PADDR);
            }

            #[verus_spec(with Tracked(perm))]
            crate::mm::frame::inc_frame_ref_count(paddr);

            paddr = paddr + PAGE_SIZE;
        }

        Self {
            range: self.range.start..self.range.end,
            _marker: core::marker::PhantomData,
        }
    }
}

} // verus!
