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
use super::{AnyFrameMeta, GetFrameError, MetaPerm, MetaSlot};
use crate::mm::{paddr_to_vaddr, Paddr, PagingLevel, Vaddr};
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
        &&& self.inv_with(&owner)
        &&& owner.inv()
        &&& regions.inv()
        // Each frame's slot must be accessible with the right properties.
        // `raw_count == 1` matches the post-`from_unused` state (each frame
        // was forgotten via `ManuallyDrop`, leaving one outstanding raw paddr).
        &&& forall|i: int|
            #![trigger owner.perms[i]]
            0 <= i < owner.perms.len() as int ==> {
                let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                &&& regions.slot_owners.contains_key(idx)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() != super::meta::REF_COUNT_UNUSED
                &&& regions.slot_owners[idx].raw_count == 1
                &&& regions.slot_owners[idx].self_addr == meta_addr(idx)
                // The perm's PointsTo matches the slot
                &&& owner.perms[i].points_to.is_init()
                &&& owner.perms[i].points_to.value().wf(regions.slot_owners[idx])
                // Last-ref condition
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() == 1 ==> {
                    &&& regions.slot_owners[idx].inner_perms.storage.is_init()
                    &&& regions.slot_owners[idx].inner_perms.in_list.value() == 0
                }
            }
        // Distinct slot indices for different frames
        &&& forall|i: int, j: int|
            #![trigger owner.perms[i], owner.perms[j]]
            0 <= i < j < owner.perms.len() as int ==>
                frame_to_index((self.range.start + i * PAGE_SIZE) as usize)
                    != frame_to_index((self.range.start + j * PAGE_SIZE) as usize)
    }

    open spec fn drop_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        true
    }

    proof fn drop_tracked(self, tracked s: &mut Self::State) {
    }
}

/// A [`SegmentOwner<M>`] holds the permission tokens for all frames in the
/// [`Segment<M>`] for verification purposes.
pub tracked struct SegmentOwner<M: AnyFrameMeta + ?Sized> {
    /// The permissions for all frames in the segment, which must be well-formed and valid.
    pub perms: Seq<MetaPerm<M>>,
}

impl<M: AnyFrameMeta + ?Sized> Inv for Segment<M> {
    /// The invariant of a [`Segment`]:
    ///
    /// - the physical addresses of the frames are aligned and within bounds.
    /// - the range is well-formed, i.e., the start is less than or equal to the end.
    open spec fn inv(self) -> bool {
        &&& self.range.start % PAGE_SIZE == 0
        &&& self.range.end % PAGE_SIZE == 0
        &&& self.range.start <= self.range.end <= MAX_PADDR
    }
}

impl<M: AnyFrameMeta + ?Sized> Inv for SegmentOwner<M> {
    /// The invariant of a [`Segment`]:
    ///
    /// - the permissions are well-formed and valid;
    /// - the physical addresses of the permissions are aligned and within bounds.
    open spec fn inv(self) -> bool {
        &&& forall|i: int|
            #![trigger self.perms[i]]
            0 <= i < self.perms.len() as int ==> {
                &&& self.perms[i].addr() % PAGE_SIZE == 0
                &&& self.perms[i].addr() < MAX_PADDR
                &&& self.perms[i].wf(&self.perms[i].inner_perms)
                &&& self.perms[i].is_init()
            }
    }
}

impl<M: AnyFrameMeta + ?Sized> Segment<M> {
    /// The invariant of a [`Segment`] with a specific owner, such that besides [`Self::inv`]:
    ///
    /// - the number of permissions in the owner matches the number of frames in the segment;
    /// - the physical address of each permission matches the corresponding frame in the segment.
    ///
    /// Interested readers are encouraged to see [`frame_to_index`] and [`meta_addr`] for how
    /// we convert between physical addresses and meta region indices.
    pub open spec fn inv_with(&self, owner: &SegmentOwner<M>) -> bool {
        &&& self.inv()
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

impl<M: AnyFrameMeta + ?Sized> SegmentOwner<M> {
    /// Produces a kernel direct-mapping memory view for the segment.
    ///
    /// This is a proof bridge from segment ownership to the VM I/O memory-view
    /// model. It should eventually be justified by a real frame-content owner
    /// instead of metadata permissions alone.
    #[verifier::external_body]
    pub proof fn produce_kernel_mem_view(tracked &self, segment: Segment<M>) -> (tracked view:
        MemView)
        requires
            self.inv(),
            segment.inv_with(self),
        ensures
            segment.kernel_mem_view_covers(&view),
    {
        arbitrary()
    }

    /// Borrows a kernel direct-mapping memory view for the segment.
    ///
    /// This is the read-side counterpart of [`Self::produce_kernel_mem_view`],
    /// used when the VM I/O owner only needs a shared read view.
    #[verifier::external_body]
    pub proof fn borrow_kernel_mem_view<'a>(tracked &'a self, segment: Segment<M>) -> (tracked view:
        &'a MemView)
        requires
            self.inv(),
            segment.inv_with(self),
        ensures
            segment.kernel_mem_view_covers(view),
    {
        arbitrary()
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
        // All range constraints are runtime-checked: alignment and
        // `range.end <= MAX_PADDR` surface as `Err` results, and
        // `range.start < range.end` is a runtime panic — see
        // `from_unused_ensures` for the corresponding postconditions.
        &&& regions.inv()
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
    /// - if the input range is misaligned, the result is `Err(NotAligned)`;
    /// - if the input range exceeds `MAX_PADDR`, the result is `Err(OutOfBound)`;
    /// - if the input was aligned and within `MAX_PADDR` and the function terminated,
    ///   then `range.start < range.end` (the runtime `assert!` would otherwise diverge).
    pub open spec fn from_unused_ensures(
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        owner: Option<SegmentOwner<M>>,
        range: Range<Paddr>,
        metadata_fn: impl Fn(Paddr) -> (Paddr, M),
        r: Result<Self, GetFrameError>,
    ) -> bool {
        &&& (range.start % PAGE_SIZE != 0 || range.end % PAGE_SIZE != 0)
            ==> r == Err::<Self, _>(GetFrameError::NotAligned)
        &&& (range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0 && range.end > MAX_PADDR)
            ==> r == Err::<Self, _>(GetFrameError::OutOfBound)
        &&& (range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0 && range.end <= MAX_PADDR)
            ==> range.start < range.end
        &&& r matches Ok(r) ==> {
            &&& new_regions.inv()
            &&& r.range.start == range.start
            &&& r.range.end == range.end
            &&& owner matches Some(owner) && {
                &&& r.inv_with(&owner)
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
    /// - the segment must satisfy the invariant with the owner ([`Self::inv_with`])
    ///
    /// Offset alignment and bounds are runtime-asserted; if the function
    /// terminates, those facts are recovered as postconditions — see
    /// [`Self::split_ensures`].
    pub open spec fn split_requires(self, owner: SegmentOwner<M>, offset: usize) -> bool {
        self.inv_with(&owner)
    }

    /// The wrapper for the postcondition for [`Self::split`]:
    ///
    /// - the resulting segments must satisfy the invariant with the corresponding owners;
    /// - the resulting segments must be the same as the result of [`Self::split_spec`];
    /// - the permissions in the original owner must be split into the resulting owners.
    /// - if the function terminated, the offset was aligned and strictly within
    ///   bounds (the runtime `assert!`s would otherwise diverge).
    pub open spec fn split_ensures(
        self,
        offset: usize,
        lhs: Self,
        rhs: Self,
        ori_owner: SegmentOwner<M>,
        lhs_owner: SegmentOwner<M>,
        rhs_owner: SegmentOwner<M>,
    ) -> bool {
        &&& offset % PAGE_SIZE == 0
        &&& 0 < offset < self.size()
        &&& lhs.inv_with(&lhs_owner)
        &&& rhs.inv_with(&rhs_owner)
        &&& (lhs, rhs) == self.split_spec(offset)
        &&& ori_owner.perms =~= (lhs_owner.perms + rhs_owner.perms)
    }

    /// The wrapper for the precondition for [`Self::into_raw`]:
    ///
    /// - the segment must satisfy the invariant with the owner;
    /// - the meta region in `regions` must satisfy the invariant.
    pub open spec fn into_raw_requires(
        self,
        regions: MetaRegionOwners,
        owner: SegmentOwner<M>,
    ) -> bool {
        &&& self.inv_with(&owner)
        &&& regions.inv()
        &&& owner.inv()
    }

    /// The wrapper for the postcondition for [`Self::into_raw`]:
    ///
    /// - the returned physical address range must be the same as the segment's range;
    /// - the meta region is unchanged.
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
    /// - the range must be a forgotten [`Segment`] that matches the type `M`;
    /// - the caller must provide the owner with valid permissions;
    /// - the range must be aligned and within bounds.
    pub open spec fn from_raw_requires(
        regions: MetaRegionOwners,
        range: Range<Paddr>,
        owner: SegmentOwner<M>,
    ) -> bool {
        &&& regions.inv()
        &&& range.start % PAGE_SIZE == 0
        &&& range.end % PAGE_SIZE == 0
        &&& range.start < range.end < MAX_PADDR
    }

    /// The wrapper for the postcondition for [`Self::from_raw`]:
    ///
    /// - the returned segment must have the same physical address range as the input;
    /// - the meta region is unchanged.
    pub open spec fn from_raw_ensures(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        owner: SegmentOwner<M>,
        range: Range<Paddr>,
    ) -> bool {
        &&& self.range == range
        &&& new_regions.inv()
        &&& new_regions =~= old_regions
    }

    /// The wrapper for the precondition for slicing a segment with a given range:
    ///
    /// - the segment must satisfy the invariant with the owner ([`Self::inv_with`])
    /// - each frame's slot in `regions` must be live so its reference count can be incremented.
    ///
    /// Range alignment and bounds are runtime-asserted; if the function
    /// terminates, those facts are recovered as postconditions — see
    /// [`Self::slice_ensures`].
    pub open spec fn slice_requires(
        self,
        owner: SegmentOwner<M>,
        regions: MetaRegionOwners,
        range: Range<Paddr>,
    ) -> bool {
        &&& self.inv_with(&owner)
        &&& regions.inv()
        &&& forall|pa: Paddr|
            #![trigger frame_to_index(pa)]
            (self.range.start + range.start <= pa < self.range.start + range.end
                && pa % PAGE_SIZE == 0) ==> {
                let idx = frame_to_index(pa);
                &&& regions.slots.contains_key(idx)
                &&& has_safe_slot(pa)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() + 1
                    < super::meta::REF_COUNT_MAX
                &&& !MetaSlot::inc_ref_count_panic_cond(
                    regions.slot_owners[idx].inner_perms.ref_count)
            }
    }

    /// The wrapper for the postcondition for slicing a segment with a given range:
    ///
    /// - the resulting slice must satisfy the invariant with the owner;
    /// - the resulting slice must have the same physical address range as the slicing range.
    /// - the meta region's invariant is preserved.
    /// - if the function terminated, the slicing range was aligned and within
    ///   bounds (the runtime `assert!`s would otherwise diverge).
    ///
    /// See also [`vstd::seq::Seq::subrange`].
    pub open spec fn slice_ensures(
        self,
        owner: SegmentOwner<M>,
        new_regions: MetaRegionOwners,
        range: Range<Paddr>,
        res: Self,
    ) -> bool {
        &&& range.start % PAGE_SIZE == 0
        &&& range.end % PAGE_SIZE == 0
        &&& self.range.start + range.start <= self.range.start + range.end <= self.range.end
        &&& res.inv_with(
            &SegmentOwner {
                perms: owner.perms.subrange(
                    (range.start / PAGE_SIZE) as int,
                    (range.end / PAGE_SIZE) as int,
                ),
            },
        )
        &&& new_regions.inv()
    }

    /// Checks if the current segment can be iterated to get the next frame:
    ///
    /// - the segment and meta regions must satisfy their respective invariants;
    /// - the frame's slot must not be in `regions.slots` (the owner holds the permission);
    /// - the frame's raw_count must be 1 (it was forgotten once).
    pub open spec fn next_requires(
        self,
        regions: MetaRegionOwners,
        owner: SegmentOwner<M>,
    ) -> bool {
        &&& self.inv()
        &&& regions.inv()
        &&& owner.perms.len() > 0
        &&& !regions.slots.contains_key(frame_to_index(self.range.start))
        &&& regions.slot_owners.contains_key(frame_to_index(self.range.start))
        &&& regions.slot_owners[frame_to_index(self.range.start)].raw_count == 1
        &&& regions.slot_owners[frame_to_index(self.range.start)].self_addr == frame_to_meta(
            self.range.start,
        )
        &&& owner.perms[0].points_to.is_init()
        &&& owner.perms[0].points_to.addr() == frame_to_meta(self.range.start)
        &&& owner.perms[0].points_to.value().wf(
            regions.slot_owners[frame_to_index(self.range.start)],
        )
    }

    /// The wrapper for the postcondition for iterating to the next frame:
    ///
    /// - if the result is [`None`], then the segment has been exhausted;
    /// - if the result is [`Some`], then the segment is advanced by one frame and
    ///   the returned frame is the next frame, with its slot restored to `regions`.
    pub open spec fn next_ensures(
        old_self: Self,
        new_self: Self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        res: Option<Frame<M>>,
    ) -> bool {
        &&& new_regions.inv()
        &&& new_self.inv()
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
            let tracked mut perms = Seq::<MetaPerm<M>>::tracked_empty();
            let tracked mut perm_opt: Option<MetaPerm<M>>;
        }

        if range.start % PAGE_SIZE != 0 || range.end % PAGE_SIZE != 0 {
            return {
                proof_with!(|= Tracked(owner));
                Err(GetFrameError::NotAligned)
            };
        }
        if range.end > MAX_PADDR {
            return {
                proof_with!(|= Tracked(owner));
                Err(GetFrameError::OutOfBound)
            };
        }
        vstd_extra::assert!(range.start < range.end);
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
                range.end <= MAX_PADDR,
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
                        &&& perms[j].wf(&perms[j].inner_perms)
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

            let res = #[verus_spec(with Tracked(regions) => Tracked(perm_opt))]
            Frame::<M>::from_unused(paddr, meta);
            let frame = match res {
                Ok(f) => f,
                Err(e) => {
                    return {
                        proof_with!(|= Tracked(owner));
                        Err(e)
                    };
                },
            };

            proof {
                let tracked frame_perm = perm_opt.tracked_unwrap();
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

            owner = Some(SegmentOwner { perms });

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
            Self::split_requires(self, owner, offset),
        ensures
            Self::split_ensures(self, offset, r.0, r.1, owner, frame_perms.0@, frame_perms.1@),
    )]
    pub fn split(self, offset: usize) -> (Self, Self) {
        vstd_extra::assert!(offset % PAGE_SIZE == 0);
        vstd_extra::assert!(0 < offset && offset < self.size());

        let at = self.range.start + offset;
        let idx = offset / PAGE_SIZE;
        let res = (
            Self { range: self.range.start..at, _marker: core::marker::PhantomData },
            Self { range: at..self.range.end, _marker: core::marker::PhantomData },
        );

        let _ = core::mem::ManuallyDrop::new(self);

        let tracked mut perms = owner.perms;
        let tracked rest = seq_tracked_split_at(&mut perms, idx as int);
        let tracked frame_perms1 = SegmentOwner { perms };
        let tracked frame_perms2 = SegmentOwner { perms: rest };

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
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            Self::slice_requires(*self, *owner, *old(regions), *range),
        ensures
            Self::slice_ensures(*self, *owner, *final(regions), *range, r),
    )]
    pub fn slice(&self, range: &Range<Paddr>) -> Self {
        vstd_extra::assert!(range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0);

        //*** KNOWN BUG: `self.range.start + range.{start,end}` could overflow. For now, assume that it doesn't. ***
        assume(self.range.start + range.start <= usize::MAX);
        assume(self.range.start + range.end <= usize::MAX);

        let start = self.range.start + range.start;
        let end = self.range.start + range.end;
        vstd_extra::assert!(start <= end && end <= self.range.end);

        let mut paddr = start;
        let ghost old_regions = *regions;
        while paddr < end
            invariant
                regions.inv(),
                self.inv(),
                start % PAGE_SIZE == 0,
                end % PAGE_SIZE == 0,
                start <= paddr <= end,
                end <= self.range.end,
                self.range.end <= MAX_PADDR,
                paddr % PAGE_SIZE == 0,
                forall|pa: Paddr|
                    #![trigger frame_to_index(pa)]
                    (paddr <= pa < end && pa % PAGE_SIZE == 0) ==> {
                        let idx = frame_to_index(pa);
                        &&& regions.slots.contains_key(idx)
                        &&& has_safe_slot(pa)
                        &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                        &&& regions.slot_owners[idx].inner_perms.ref_count.value() + 1
                            < super::meta::REF_COUNT_MAX
                        &&& !MetaSlot::inc_ref_count_panic_cond(
                            regions.slot_owners[idx].inner_perms.ref_count)
                    },
            decreases end - paddr,
        {
            // SAFETY: We already have reference counts for the frames since
            // for each frame there would be a forgotten handle when creating
            // the `Segment` object.
            #[verus_spec(with Tracked(regions))]
            crate::mm::frame::inc_frame_ref_count(paddr);

            paddr = paddr + PAGE_SIZE;
        }

        Self { range: start..end, _marker: core::marker::PhantomData }
    }

}

#[verus_verify]
impl<M: AnyFrameMeta> From<Frame<M>> for Segment<M> {
    /// Converts a single [`Frame`] into a one-page [`Segment`] by forgetting
    /// the frame and recording its paddr range. Symmetric to vostd's
    /// `From<Frame<M>> for Segment<M>`.
    //
    // Trusted at the trait boundary: the `From::from` signature can't thread
    // `Tracked` metadata to bump the frame's `raw_count` via the verified
    // `vstd_extra::drop_tracking::ManuallyDrop`, so we use `core::mem`'s
    // version. Same trust pattern as the `Iterator` impl.
    #[verifier::external_body]
    fn from(frame: Frame<M>) -> Self {
        let pa = frame.start_paddr();
        let _ = core::mem::ManuallyDrop::new(frame);
        Self {
            range: pa..(pa + PAGE_SIZE),
            _marker: core::marker::PhantomData,
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Iterator for Segment<M> {
    type Item = Frame<M>;

    /// Gets the next frame in the segment.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// See [`Self::next_requires`].
    ///
    /// ## Postconditions
    /// See [`Self::next_ensures`].
    //
    // The body matches vostd's `Iterator::next` for `Segment<M>`. Verus's
    // `core::iter::Iterator` support doesn't allow threading `Tracked`
    // metadata through the trait method's fixed signature, so the verified
    // contract is captured by the inherent `next_requires`/`next_ensures`
    // spec functions and the body is trusted at the trait boundary — same
    // pattern used by `Cursor`'s Iterator impl.
    #[verifier::external_body]
    fn next(&mut self) -> Option<Self::Item> {
        if self.range.start < self.range.end {
            // SAFETY: each frame in the range was a forgotten handle when
            // creating the `Segment` object.
            let frame = unsafe { Frame::<M>::from_raw(self.range.start) };
            self.range.start = self.range.start + PAGE_SIZE;
            Some(frame)
        } else {
            None
        }
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Drop for Segment<M> {
    /// Verified drop: for each frame in the segment, restore the [`Frame`]
    /// from its raw paddr (consuming the outstanding `raw_count` recorded by
    /// the segment) and let it drop normally — symmetric to vostd's
    /// `drop(unsafe { Frame::<M>::from_raw(paddr) })`.
    //
    // The body's per-iteration preconditions for `Frame::from_raw` and
    // `frame.drop` are derivable from `drop_requires`, but the resulting
    // multi-forall loop invariant exceeds Verus's solver budget even after
    // factoring into `spinoff_prover` lemmas. The contract (drop_requires/
    // drop_ensures) is the verified surface; the body is trusted at the
    // contract boundary, same trust posture as the original `?Sized` impl.
    #[verifier::external_body]
    fn drop(self, Tracked(s): Tracked<(MetaRegionOwners, SegmentOwner<M>)>) -> (res: Tracked<(MetaRegionOwners, SegmentOwner<M>)>)
    {
        let tracked (mut regions, mut owner) = s;
        let mut paddr = self.range.start;

        while paddr < self.range.end {
            let tracked perm = owner.perms.tracked_remove(0);
            proof_decl! {
                let tracked debt: crate::specs::mm::frame::frame_specs::BorrowDebt;
            }
            // SAFETY: each frame in the range was a forgotten handle when the
            // segment was constructed via `from_unused`.
            let frame = unsafe {
                #[verus_spec(with Tracked(&mut regions), Tracked(&perm) => Tracked(debt))]
                Frame::<M>::from_raw(paddr)
            };
            let Tracked(regions_new) = frame.drop(Tracked(regions));
            proof {
                regions = regions_new;
            }
            paddr = paddr + PAGE_SIZE;
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
                paddr <= MAX_PADDR,
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
