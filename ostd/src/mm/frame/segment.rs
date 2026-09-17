// SPDX-License-Identifier: MPL-2.0
//! A contiguous range of frames.
use vstd::prelude::*;
use vstd::simple_pptr::{PPtr, PointsTo};
use vstd::std_specs::iter::IteratorSpecImpl;
use vstd_extra::assert;
use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;
use vstd_extra::panic::may_panic;
use vstd_extra::prelude::*;

use crate::mm::page_table::RCClone;
use crate::mm::{PagingLevel, Vaddr, frame::MetaSlot, paddr_to_vaddr};
use crate::specs::arch::*;
use crate::specs::mm::frame::{
    frame_specs::FrameRawPerms,
    mapping::{frame_to_index, group_page_meta, index_to_meta},
    meta_owners::*,
    meta_region_owners::MetaRegionOwners,
    segment::*,
};

use core::{fmt::Debug, mem::ManuallyDrop, ops::Range};

use super::{
    Frame, Paddr,
    meta::mapping::frame_to_meta,
    meta::{AnyFrameMeta, GetFrameError},
};
use crate::mm::frame::{meta::REF_COUNT_MAX, untyped::AnyUFrameMeta};

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
// #[repr(transparent)]
pub struct Segment<M: AnyFrameMeta + ?Sized> {
    range: Range<Paddr>,
    _marker: core::marker::PhantomData<M>,
    /// One raw permission bundle for each frame in `range`, in address order.
    #[cfg(verus_keep_ghost_body)]
    tracked_perms: Tracked<Option<Seq<FrameRawPerms>>>,
}

/*
impl<M: AnyFrameMeta + ?Sized> Debug for Segment<M> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Segment({:#x}..{:#x})", self.range.start, self.range.end)
    }
}
*/

/*impl<M: AnyFrameMeta + ?Sized> Drop for Segment<M> {
    fn drop(&mut self) {
        for paddr in self.range.clone().step_by(PAGE_SIZE) {
            // SAFETY: for each frame there would be a forgotten handle
            // when creating the `Segment` object.
            drop(unsafe { Frame::<M>::from_raw(paddr) });
        }
    }
}*/

/// A contiguous range of homogeneous untyped physical memory frames that have any metadata.
///
/// In other words, the metadata of the frames are of the same type, and they
/// are untyped, but the type of metadata is not known at compile time. An
/// [`USegment`] as a parameter accepts any untyped segments.
///
/// The usage of this frame will not be changed while this object is alive.
pub type USegment = Segment<dyn AnyUFrameMeta>;

/* impl<M: AnyFrameMeta + ?Sized> Clone for Segment<M> {
    fn clone(&self) -> Self {
        for paddr in self.range.clone().step_by(PAGE_SIZE) {
            // SAFETY: for each frame there would be a forgotten handle
            // when creating the `Segment` object, so we already have
            // reference counts for the frames.
            unsafe { inc_frame_ref_count(paddr) };
        }
        Self {
            range: self.range.clone(),
            _marker: core::marker::PhantomData,
        }
    }
} */

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> RCClone for Segment<M> {
    open spec fn clone_requires(self, perm: MetaRegionOwners) -> bool {
        &&& self.inv()
        &&& perm.inv()
        &&& self.relate_regions(perm)
        &&& forall|pa: Paddr|
            #![trigger frame_to_index(pa)]
            (self.start_paddr() <= pa < self.end_paddr() && pa % PAGE_SIZE == 0) ==> {
                let idx = frame_to_index(pa);
                &&& perm.contains(idx)
                &&& valid_frame_paddr(pa)
                &&& perm.ref_count(idx) > 0
                &&& perm.ref_count(idx) + 1 < REF_COUNT_MAX
                &&& !MetaSlot::inc_ref_count_panic_cond(perm.slot_owners[idx].ref_count_perm)
            }
    }

    open spec fn clone_ensures(
        self,
        old_perm: MetaRegionOwners,
        new_perm: MetaRegionOwners,
        res: Self,
    ) -> bool {
        &&& res.range() == self.range()
        &&& res.inv()
        &&& new_perm.inv()
        &&& res.relate_regions(new_perm)
    }

    #[verifier::loop_isolation(false)]
    #[verifier::rlimit(200)]
    fn clone(&self, Tracked(perm): Tracked<&mut MetaRegionOwners>) -> (res: Self) {
        let mut paddr = self.range.start;
        proof_decl! {
            let tracked mut raw_perms = Seq::<FrameRawPerms>::tracked_empty();
        }

        loop
            invariant
                perm.inv(),
                self.inv(),
                perm.slots == old(perm).slots,
                perm.slot_owners.dom() == old(perm).slot_owners.dom(),
                raw_perms.len() == (paddr - self.range.start) / (PAGE_SIZE as int),
                forall|i: int|
                    #![trigger raw_perms[i]]
                    0 <= i < raw_perms.len() ==> {
                        let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                        &&& raw_perms[i].slot_perm == perm.slots[idx]
                        &&& raw_perms[i].inv()
                        &&& raw_perms[i].metadata_perm.id()
                            == perm.slot_owners[idx].metadata_perm.id()
                    },
                forall|i: int|
                    #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
                    0 <= i < raw_perms.len() ==> ({
                        let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                        &&& perm.contains(idx)
                        &&& perm.slot_owners[idx].slot_vaddr == index_to_meta(idx)
                        &&& perm.ref_count(idx) > 0
                        &&& perm.ref_count(idx) <= REF_COUNT_MAX
                        &&& perm.slot_owners[idx].paths_in_pt.is_empty()
                        &&& perm.slot_owners[idx].usage is Frame
                    }),
                self.range.start <= paddr <= self.range.end,
                paddr % PAGE_SIZE == 0,
                paddr <= MAX_PADDR,
                forall|pa: Paddr|
                    #![trigger frame_to_index(pa)]
                    (paddr <= pa < self.range.end && pa % PAGE_SIZE == 0) ==> {
                        let idx = frame_to_index(pa);
                        &&& perm.contains(idx)
                        &&& valid_frame_paddr(pa)
                        &&& perm.ref_count(idx) > 0
                        &&& perm.ref_count(idx) + 1 < REF_COUNT_MAX
                        &&& !MetaSlot::inc_ref_count_panic_cond(
                            perm.slot_owners[idx].ref_count_perm,
                        )
                    },
                forall|i: int|
                    #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
                    raw_perms.len() <= i < self.len() ==> perm.slot_owner(
                        (self.range.start + i * PAGE_SIZE) as usize,
                    ) == old(perm).slot_owner((self.range.start + i * PAGE_SIZE) as usize),
            decreases self.range.end - paddr,
        {
            if paddr >= self.range.end {
                break;
            }
            let tracked_permission = unsafe {
                #[verus_spec(with Tracked(perm))]
                crate::mm::frame::inc_frame_ref_count(paddr)
            };
            let tracked frame_permission = tracked_permission.get();
            proof {
                let tracked slot_perm = perm.tracked_borrow_slot(paddr);
                raw_perms.tracked_push(
                    FrameRawPerms { slot_perm, metadata_perm: frame_permission },
                );
            }

            paddr += PAGE_SIZE;
        }

        Self {
            range: self.range.start..self.range.end,
            _marker: core::marker::PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_perms: Tracked(Some(raw_perms)),
        }
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Segment<M> {
    pub closed spec fn from_raw_value(range: Range<Paddr>, raw_perms: Seq<FrameRawPerms>) -> Self {
        Segment {
            range,
            _marker: core::marker::PhantomData::<M>,
            #[cfg(verus_keep_ghost_body)]
            tracked_perms: Tracked(Some(raw_perms)),
        }
    }

    /// Creates a new [`Segment`] from unused frames.
    ///
    /// The caller must provide a closure to initialize metadata for all the frames.
    /// The closure receives the physical address of the frame and returns the
    /// metadata, which is similar to [`core::array::from_fn`].
    ///
    /// It returns an error if:
    ///  - the physical address is invalid or not aligned;
    ///  - any of the frames cannot be created with a specific reason.
    ///
    /// # Panics
    ///
    /// It panics if the range is empty.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - the metadata function must be well-formed and valid for all frames in the range;
    /// - the metadata function must ensure that the frames can be created and owned by the segment;
    /// - for any frame created via the closure `metadata_fn`, the corresponding slot in `regions`
    ///   must be unused and not dropped in the owner ([`MetaRegionOwners`]).
    ///
    /// Range constraints (alignment, `range.end <= MAX_PADDR`, non-emptiness) are runtime-checked
    /// in the body — see the postconditions below for the corresponding error variants.
    /// ## Postconditions
    /// - if the result is `Ok`, the returned segment satisfies its invariant,
    ///   relates to the updated metadata region, and has the same physical
    ///   address range as the input;
    /// - if the input range is misaligned, the result is `Err(NotAligned)`;
    /// - if the input range exceeds `MAX_PADDR`, the result is `Err(OutOfBound)`;
    /// - if the input is aligned and within `MAX_PADDR` and the function terminated,
    ///   then `range.start < range.end` (the runtime `assert!` would otherwise diverge).
    /// FIXME: this implementation does not match source code.
    #[verifier::loop_isolation(false)]
    #[verifier::allow_complex_invariants]
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(repr_perm): Tracked<&mut M::ReprPerm>,
        requires
            old(regions).inv(),
            forall|paddr_in: Paddr|
                (range.start <= paddr_in < range.end && paddr_in % PAGE_SIZE == 0) ==> {
                    &&& metadata_fn.requires((paddr_in,))
                },
            forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
                metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> paddr_in == paddr_out,
            !(range.end <= MAX_PADDR ==> range.start < range.end) ==> may_panic(),
        ensures
            final(regions).inv(),
            (range.start % PAGE_SIZE != 0 || range.end % PAGE_SIZE != 0)
                ==> r == Err::<Self, _>(GetFrameError::NotAligned),
            (range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0 && range.end > MAX_PADDR)
                ==> r == Err::<Self, _>(GetFrameError::OutOfBound),
            r matches Ok(seg) ==> {
                &&& seg.inv()
                &&& seg.start_paddr() == range.start
                &&& seg.end_paddr() == range.end
                &&& seg.start_paddr() < seg.end_paddr()
                &&& seg.relate_regions(*final(regions))
                &&& forall|paddr: Paddr|
                    #![trigger frame_to_index(paddr)]
                    (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                        ==> final(regions).contains(frame_to_index(paddr))
                &&& range.start < range.end <= MAX_PADDR
            },
    )]
    pub fn from_unused(range: Range<Paddr>, metadata_fn: impl Fn(Paddr) -> (Paddr, M)) -> (res:
        Result<Self, GetFrameError>) {
        proof_decl! {
            let tracked mut addrs = Seq::<usize>::tracked_empty();
            let tracked raw_perms = Seq::<FrameRawPerms>::tracked_empty();
        }

        if range.start % PAGE_SIZE != 0 || range.end % PAGE_SIZE != 0 {
            return Err(GetFrameError::NotAligned);
        }
        if range.end > MAX_PADDR {
            return Err(GetFrameError::OutOfBound);
        }
        assert!(range.start < range.end);

        // Construct a segment early to recycle previously forgotten frames if
        // the subsequent operations fails in the middle.

        let mut segment = Self {
            range: range.start..range.start,
            _marker: core::marker::PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_perms: Tracked(Some(raw_perms)),
        };

        let mut i = 0;
        let addr_len = (range.end - range.start) / PAGE_SIZE;

        while i < addr_len
            invariant
                segment.tracked_perms@ is Some,
                i <= addr_len,
                i == addrs.len(),
                i == segment.tracked_perms@->0.len(),
                range.start <= range.start + i * PAGE_SIZE <= range.end,
                range.end == range.start + addr_len * PAGE_SIZE,
                addr_len == (range.end - range.start) / PAGE_SIZE as int,
                i <= addr_len,
                forall|paddr_in: Paddr|
                    (range.start + i * PAGE_SIZE <= paddr_in < range.end && paddr_in % PAGE_SIZE
                        == 0) ==> {
                        &&& metadata_fn.requires((paddr_in,))
                    },
                forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
                    range.start + i * PAGE_SIZE <= paddr_in < range.end && paddr_in % PAGE_SIZE == 0
                        && metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> paddr_in
                        == paddr_out,
                forall|j: int|
                    #![trigger addrs[j]]
                    0 <= j < addrs.len() ==> {
                        let idx = frame_to_index(addrs[j]);
                        &&& regions.contains(idx)
                        &&& regions.slot_owners[idx].slot_vaddr == index_to_meta(idx)
                        &&& 0 < regions.ref_count(idx) <= REF_COUNT_MAX
                        &&& segment.tracked_perms@->0[j].inv()
                        &&& segment.tracked_perms@->0[j].slot_perm == regions.slots[idx]
                        &&& segment.tracked_perms@->0[j].metadata_perm.id()
                            == regions.slot_owners[idx].metadata_perm.id()
                        &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                        &&& regions.slot_owners[idx].usage is Frame
                        &&& addrs[j] % PAGE_SIZE == 0
                        &&& addrs[j] < MAX_PADDR
                        &&& addrs[j] == range.start + (j as u64) * PAGE_SIZE
                    },
                regions.inv(),
                regions.slot_owners.dom() == old(regions).slot_owners.dom(),
                segment.range.end == range.start + i * PAGE_SIZE,
            ensures
                i == addr_len,
            decreases addr_len - i,
        {
            let paddr_in = range.start + i * PAGE_SIZE;
            let (paddr, meta) = metadata_fn(paddr_in);

            let ghost regions_pre = *regions;
            let res = #[verus_spec(with Tracked(regions), Tracked(repr_perm))]
            Frame::<M>::from_unused(paddr, meta);
            let mut frame = match res {
                Ok(f) => f,
                Err(e) => {
                    let mut p = range.start;
                    let ghost mut k: int = 0;
                    while p < segment.range.end
                        invariant
                            regions.inv(),
                            segment.tracked_perms@->0.len() == i - k,
                            regions.slot_owners.dom() == old(regions).slot_owners.dom(),
                            range.start % PAGE_SIZE == 0,
                            i == addrs.len(),
                            segment.range.end == range.start + i * PAGE_SIZE,
                            range.start <= p <= segment.range.end,
                            p == range.start + k * PAGE_SIZE,
                            p % PAGE_SIZE == 0,
                            0 <= k <= i,
                            forall|j: int|
                                #![trigger addrs[j]]
                                k <= j < addrs.len() ==> {
                                    let idx = frame_to_index(addrs[j]);
                                    &&& regions.contains(idx)
                                    &&& regions.slot_owners[idx].slot_vaddr == index_to_meta(idx)
                                    &&& 0 < regions.ref_count(idx) <= REF_COUNT_MAX
                                    &&& segment.tracked_perms@ is Some
                                    &&& segment.tracked_perms@->0[j - k].inv()
                                    &&& segment.tracked_perms@->0[j - k].slot_perm
                                        == regions.slots[idx]
                                    &&& segment.tracked_perms@->0[j - k].metadata_perm.id()
                                        == regions.slot_owners[idx].metadata_perm.id()
                                    &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                                    &&& regions.slot_owners[idx].usage is Frame
                                    &&& addrs[j] % PAGE_SIZE == 0
                                    &&& addrs[j] < MAX_PADDR
                                    &&& addrs[j] == range.start + (j as u64) * PAGE_SIZE
                                },
                        decreases segment.range.end - p,
                    {
                        proof {
                            broadcast use group_page_meta;

                            assert(addrs[k] == p);

                        }
                        let tracked perm =
                            segment.tracked_perms.tracked_borrow_mut().tracked_pop_front();
                        let frame = unsafe {
                            #[verus_spec(with Tracked(perm))]
                            Frame::<M>::from_raw(p)
                        };
                        frame.drop(Tracked(regions));
                        p += PAGE_SIZE;
                        proof {
                            k = k + 1;
                        }
                    }
                    return Err(e);
                },
            };

            proof_decl! {
                let tracked frame_permission: FracMetadataPerm = frame.tracked_metadata_perm.tracked_take();
                let tracked slot_perm = *frame.tracked_slot_perm;
            }
            let _ = ManuallyDrop::new(frame);
            segment.range.end = paddr + PAGE_SIZE;
            proof {
                broadcast use group_page_meta;

                let idx = frame_to_index(paddr);
                axiom_mmio_usage_iff_mmio_paddr(regions.slot_owners[idx]);
                axiom_mmio_usage_iff_mmio_paddr(regions_pre.slot_owners[idx]);
                addrs.tracked_push(paddr);
                segment.tracked_perms.tracked_borrow_mut().tracked_push(
                    FrameRawPerms { slot_perm, metadata_perm: frame_permission },
                );
            }

            i += 1;
        }

        proof {
            assert forall|addr: usize|
                #![trigger frame_to_index(addr)]
                range.start <= addr < range.end && addr % PAGE_SIZE == 0 implies {
                regions.contains(frame_to_index(addr))
            } by {
                let j = (addr - range.start) / PAGE_SIZE as int;
                assert(addrs[j as int] == addr);
            }
            assert forall|i: int|
                #![trigger frame_to_index((segment.range.start + i * PAGE_SIZE) as usize)]
                0 <= i < segment.len() implies {
                let idx = frame_to_index((segment.range.start + i * PAGE_SIZE) as usize);
                &&& segment.tracked_perms@->0[i].inv()
                &&& segment.tracked_perms@->0[i].slot_perm == regions.slots[idx]
                &&& segment.tracked_perms@->0[i].metadata_perm.id()
                    == regions.slot_owners[idx].metadata_perm.id()
                &&& regions.contains(idx)
                &&& regions.slot_owners[idx].slot_vaddr == index_to_meta(idx)
                &&& regions.ref_count(idx) > 0
                &&& regions.ref_count(idx) <= REF_COUNT_MAX
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                &&& regions.slot_owners[idx].usage is Frame
            } by {
                assert(addrs[i] == segment.range.start + i * PAGE_SIZE);
            }

        }

        Ok(segment)
    }

    /// Restores the [`Segment`] from the raw physical address range.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - the meta region must satisfy its invariant;
    /// - the segment-to-be (with the supplied `range`) must satisfy the bundled
    ///   [`Self::invariants`] relation against `regions`.
    ///
    /// ## Postconditions
    /// - the returned segment satisfies its bundled invariant;
    /// - the returned segment has the same physical address range as the input;
    /// - the meta region is unchanged.
    ///
    /// # Safety
    ///
    /// The range must be a forgotten [`Segment`] that matches the type `M`.
    /// The caller must ensure the range was previously produced by [`Self::into_raw`]
    /// and that the metadata region still records the segment obligations.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(raw_perms): Tracked<Seq<FrameRawPerms>>,
        requires
            Self::from_raw_value(range, raw_perms).inv(),
            old(regions).inv(),
            Self::from_raw_value(range, raw_perms).relate_regions(*old(regions)),
        ensures
            r.inv(),
            r.relate_regions(*final(regions)),
            r.range() == range,
            final(regions).inv(),
            *final(regions) == *old(regions),
    )]
    pub(crate) unsafe fn from_raw(range: Range<Paddr>) -> Self {
        Self {
            range,
            _marker: core::marker::PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_perms: Tracked(Some(raw_perms)),
        }
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + ?Sized> Segment<M> {
    /// Projects the fractional metadata permissions from raw frame permissions.
    pub open spec fn raw_metadata_perms(raw_perms: Seq<FrameRawPerms>) -> Seq<FracMetadataPerm> {
        raw_perms.map_values(|perm: FrameRawPerms| perm.metadata_perm)
    }

    /// Gets the start physical address of the contiguous frames.
    #[verus_verify(dual_spec)]
    #[verus_spec(
        returns
            self.start_paddr(),
    )]
    pub fn start_paddr(&self) -> Paddr {
        self.range.start
    }

    /// Gets the end physical address of the contiguous frames.
    #[verus_verify(dual_spec)]
    #[verus_spec(
        returns
            self.end_paddr(),
    )]
    pub fn end_paddr(&self) -> Paddr {
        self.range.end
    }

    /// Gets the length in bytes of the contiguous frames.
    #[verus_verify(dual_spec)]
    #[verus_spec(r =>
        requires
            self.inv(),
        ensures
            r == self.end_paddr() - self.start_paddr(),
        returns
            self.size()
    )]
    pub fn size(&self) -> usize {
        self.range.end - self.range.start
    }

    pub open spec fn range(&self) -> Range<Paddr> {
        self.start_paddr()..self.end_paddr()
    }

    /// Returns the number of pages of the contiguous frames.
    pub open spec fn len(&self) -> int {
        (self.size() / PAGE_SIZE) as int
    }

    pub closed spec fn raw_perms(&self) -> Seq<FrameRawPerms> {
        self.tracked_perms@->0
    }

    pub open spec fn metadata_perms(&self) -> Seq<FracMetadataPerm> {
        self.raw_perms().map_values(|perm: FrameRawPerms| perm.metadata_perm)
    }

    pub closed spec fn inner_perm_inv(&self) -> bool {
        self.tracked_perms@ is Some
    }

    pub open spec fn slot_perms(&self) -> Seq<&'static PointsTo<MetaSlot>> {
        self.raw_perms().map_values(|perm: FrameRawPerms| perm.slot_perm)
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Segment<M> {
    /// Splits the frames into two at the given byte offset from the start.
    ///
    /// The resulting frames cannot be empty. So the offset cannot be neither
    /// zero nor the length of the frames.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - the segment must satisfy its invariant;
    /// - the offset must be aligned and within bounds;
    ///
    /// ## Postconditions
    /// - the resulting segments satisfy their invariants;
    /// - they match [`Self::split_spec`].
    #[verus_spec(r =>
        requires
            self.inv(),
            offset % PAGE_SIZE != 0 ==> may_panic(),
            !(0 < offset && offset < self.size()) ==> may_panic(),
        ensures
            (r.0, r.1) == self.split_spec(offset),
    )]
    #[verifier::spinoff_prover]
    pub fn split(self, offset: usize) -> (Self, Self) {
        assert!(offset % PAGE_SIZE == 0);
        assert!(0 < offset && offset < self.size());

        let mut this = self;

        let tracked mut left_perms = this.tracked_perms.tracked_take();
        let tracked right_perms = seq_tracked_split_at(
            &mut left_perms,
            (offset / PAGE_SIZE) as int,
        );
        let old = ManuallyDrop::new(this);
        let at = old.range.start + offset;

        (
            Self {
                range: old.range.start..at,
                _marker: core::marker::PhantomData,
                #[cfg(verus_keep_ghost_body)]
                tracked_perms: Tracked(Some(left_perms)),
            },
            Self {
                range: at..old.range.end,
                _marker: core::marker::PhantomData,
                #[cfg(verus_keep_ghost_body)]
                tracked_perms: Tracked(Some(right_perms)),
            },
        )
    }

    /// Precise panic condition for [`Self::slice`]. `slice` diverges iff:
    ///  - the slice range is misaligned, reversed, or out of the segment's
    ///    bounds (the diverging `assert!`s at the top of `slice`), or
    ///  - **the specific per-frame slot that `slice` bumps** is already
    ///    saturated (`inc_ref_count` would overflow). Unlike `query` which
    ///    clones one item, `slice` bumps one refcount per page in the
    ///    slice range, so the saturation disjunct is an *exists* over those
    ///    specific paddrs `self.range.start + j * PAGE_SIZE` for
    ///    `j ∈ [range.start/PAGE_SIZE, range.end/PAGE_SIZE)`.
    pub open spec fn page_in_range_saturated(
        self,
        range: &Range<usize>,
        regions: MetaRegionOwners,
    ) -> bool {
        exists|j: int|
            #![trigger frame_to_index((self.start_paddr() + j * PAGE_SIZE) as usize)]
            (range.start as int) / (PAGE_SIZE as int) <= j < (range.end as int) / (PAGE_SIZE as int)
                && regions.slot_owner((self.start_paddr() + j * PAGE_SIZE) as usize).ref_count()
                >= REF_COUNT_MAX
    }

    // [FIXED] BUG FOUND BY FV: potential overflow. https://github.com/asterinas/asterinas/pull/3587
    /// Gets an extra handle to the frames in the byte offset range.
    ///
    /// The sliced byte offset range in indexed by the offset from the start of
    /// the contiguous frames. The resulting frames holds extra reference counts.
    ///
    /// # Verified Properties
    /// ## Postconditions
    /// - the resulting slice's range matches the slicing range and is in-bounds
    ///   (the in-bounds check follows from the diverging `assert!` in the body);
    /// - `regions` preserves invariants and key domains. Per-frame state for a
    ///   hypothetical sub-segment relation is not exposed; threading that through
    ///   the per-frame ref-count bump loop would require a much heavier proof.
    ///   Mirrors [`Segment::clone`].
    ///
    /// See also [`vstd::seq::Seq::subrange`].
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            self.inv(),
            old(regions).inv(),
            self.relate_regions(*old(regions)),
            range.start % PAGE_SIZE != 0 ==> may_panic(),
            range.end % PAGE_SIZE != 0 ==> may_panic(),
            range.start > range.end ==> may_panic(),
            range.end > self.size() ==> may_panic(),
            self.page_in_range_saturated(range, *old(regions)) ==> may_panic(),
        ensures
            range.start % PAGE_SIZE == 0,
            range.end % PAGE_SIZE == 0,
            range.start <= range.end,
            self.start_paddr() + range.end <= self.end_paddr(),
            !self.page_in_range_saturated(range, *old(regions)),
            r.inv(),
            r.start_paddr() == self.start_paddr() + range.start,
            r.end_paddr() == self.start_paddr() + range.end,
            r.end_paddr() <= self.end_paddr(),
            final(regions).inv(),
            final(regions).slots == old(regions).slots,
            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
            r.relate_regions(*final(regions)),
    )]
    #[verifier::spinoff_prover]
    #[verifier::loop_isolation(false)]
    #[verifier::rlimit(200)]
    pub fn slice(&self, range: &Range<usize>) -> Self {
        assert!(range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0);
        assert!(range.start <= range.end && range.end <= self.size());
        let start = self.range.start + range.start;
        let end = self.range.start + range.end;

        let mut paddr = start;
        let ghost addr_len = (end - start) / PAGE_SIZE as int;
        let ghost first_perm_idx: int = (range.start / PAGE_SIZE) as int;
        let ghost last_perm_idx: int = (range.end / PAGE_SIZE) as int;
        let ghost mut i: int = 0;
        proof_decl! {
            let tracked mut raw_perms = Seq::<FrameRawPerms>::tracked_empty();
        }
        loop
            invariant
                self.page_in_range_saturated(range, *old(regions)) ==> may_panic(),
                regions.inv(),
                regions.slots == old(regions).slots,
                regions.slot_owners.dom() == old(regions).slot_owners.dom(),
                raw_perms.len() == i,
                forall|j: int|
                    #![trigger raw_perms[j]]
                    0 <= j < raw_perms.len() ==> {
                        let idx = frame_to_index((start + j * PAGE_SIZE) as usize);
                        &&& raw_perms[j].slot_perm == regions.slots[idx]
                        &&& raw_perms[j].inv()
                        &&& raw_perms[j].metadata_perm.id()
                            == regions.slot_owners[idx].metadata_perm.id()
                    },
                forall|j: int|
                    #![trigger frame_to_index((start + j * PAGE_SIZE) as usize)]
                    0 <= j < raw_perms.len() ==> {
                        let idx = frame_to_index((start + j * PAGE_SIZE) as usize);
                        &&& regions.contains(idx)
                        &&& regions.slot_owners[idx].slot_vaddr == index_to_meta(idx)
                        &&& regions.ref_count(idx) > 0
                        &&& regions.ref_count(idx) <= REF_COUNT_MAX
                        &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                        &&& regions.slot_owners[idx].usage is Frame
                    },
                paddr == (start + i * PAGE_SIZE) as usize,
                paddr <= end,
                0 <= i <= addr_len,
                paddr < end <==> i < addr_len,
                forall|j: int|
                    #![trigger frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                    first_perm_idx + i <= j < last_perm_idx ==> (*regions).slot_owner(
                        (self.range.start + j * PAGE_SIZE) as usize,
                    ) == old(regions).slot_owner((self.range.start + j * PAGE_SIZE) as usize),
                forall|j: int|
                    #![trigger frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                    first_perm_idx <= j < first_perm_idx + i ==> old(regions).slot_owner(
                        (self.range.start + j * PAGE_SIZE) as usize,
                    ).ref_count() < REF_COUNT_MAX,
            decreases addr_len - i,
        {
            if paddr >= end {
                break;
            }
            let ghost perm_idx: int = first_perm_idx + i;

            proof {
                assert(paddr == (self.range.start + perm_idx * PAGE_SIZE) as usize);
            }

            let tracked_permission = unsafe {
                #[verus_spec(with Tracked(regions))]
                crate::mm::frame::inc_frame_ref_count(paddr)
            };
            let tracked frame_permission = tracked_permission.get();
            proof {
                let tracked slot_perm = regions.tracked_borrow_slot(paddr);
                raw_perms.tracked_push(
                    FrameRawPerms { slot_perm, metadata_perm: frame_permission },
                );
            }

            paddr += PAGE_SIZE;

            proof {
                i = i + 1;
            }
        }

        Self {
            range: start..end,
            _marker: core::marker::PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_perms: Tracked(Some(raw_perms)),
        }
    }

    /// Forgets the [`Segment`] and gets a raw range of physical addresses.
    /// # Verified Properties
    /// ## Preconditions
    /// - the segment must satisfy its invariant.
    ///
    /// ## Postconditions
    /// - the returned physical address range matches the segment's range.
    #[verus_spec(r =>
        with
            -> raw_perms: Tracked<Seq<FrameRawPerms>>,
        requires
            self.inv(),
        ensures
            r == self.range(),
            raw_perms@ == self.raw_perms(),
    )]
    pub(crate) fn into_raw(self) -> Range<Paddr> {
        let mut this = self;
        let range = this.range.clone();

        proof_decl!{
            let tracked raw_perms = this.tracked_perms.tracked_take();
        }

        let _ = ManuallyDrop::new(this);

        proof_with!(|= Tracked(raw_perms));
        range
    }

    /// Splits the contiguous frames into two at the given byte offset from the start in spec mode.
    pub closed spec fn split_spec(self, offset: usize) -> (Self, Self)
        recommends
            offset % PAGE_SIZE == 0,
            0 < offset < self.size(),
    {
        let at = (self.start_paddr() + offset) as usize;
        let idx = offset / PAGE_SIZE;
        (
            Self {
                range: self.start_paddr()..at,
                _marker: core::marker::PhantomData,
                #[cfg(verus_keep_ghost_body)]
                tracked_perms: Tracked(Some(self.raw_perms().subrange(0, idx as int))),
            },
            Self {
                range: at..self.end_paddr(),
                _marker: core::marker::PhantomData,
                #[cfg(verus_keep_ghost_body)]
                tracked_perms: Tracked(
                    Some(self.raw_perms().subrange(idx as int, self.raw_perms().len() as int)),
                ),
            },
        )
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> From<Frame<M>> for Segment<M> {
    /// Converts a single [`Frame`] into a one-page [`Segment`] by forgetting
    /// the frame and recording its paddr range. Symmetric to vostd's
    /// `From<Frame<M>> for Segment<M>`.
    #[verifier::external_body]
    fn from(frame: Frame<M>) -> Self {
        let pa = frame.start_paddr();
        let tracked slot_perm = frame.tracked_slot_perm.get();
        let tracked frame_permission = frame.tracked_metadata_perm.get().tracked_unwrap();
        let raw_frame = Frame::<M> {
            ptr: frame.ptr,
            _marker: core::marker::PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: Tracked(slot_perm),
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: Tracked(None),
        };
        let _ = core::mem::ManuallyDrop::new(raw_frame);
        Self {
            range: pa..(pa + PAGE_SIZE),
            _marker: core::marker::PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_perms: Tracked(
                Some(seq![FrameRawPerms { slot_perm, metadata_perm: frame_permission }]),
            ),
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Iterator for Segment<M> {
    type Item = Frame<M>;

    #[verifier::rlimit(200)]
    fn next(&mut self) -> Option<Self::Item> {
        proof {
            // This is a verification limitation that the `#[verifier::type_invariant]` can not be broken.
            // It is still sound because `Segment` is always exposed with `inv`.
            assume(self.inv());
        }

        if self.range.start < self.range.end {
            proof {
                assert(self.raw_perms()[0].slot_perm == self.slot_perms()[0]);
                assert(self.raw_perms()[0].metadata_perm == self.metadata_perms()[0]);
            }
            let tracked mut raw_perms = self.tracked_perms.tracked_borrow_mut();
            let tracked perm = raw_perms.tracked_pop_front();
            proof {
                assert(perm.inv());
                assert(perm.slot_vaddr() == frame_to_meta(self.range.start));
            }
            // SAFETY: each frame in the range would be a handle forgotten
            // when creating the `Segment` object.
            let frame = unsafe {
                #[verus_spec(with Tracked(perm))]
                Frame::<M>::from_raw(self.range.start)
            };
            self.range.start += PAGE_SIZE;
            Some(frame)
        } else {
            None
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> IteratorSpecImpl for Segment<M> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        Seq::new(
            self.metadata_perms().len() as nat,
            |i: int|
                {
                    Frame::<M>::from_raw_spec(
                        (self.range().start + i * PAGE_SIZE) as usize,
                        self.slot_perms()[i],
                        Some(self.metadata_perms()[i]),
                    )
                },
        )
    }

    #[verifier::prophetic]
    closed spec fn will_return_none(&self) -> bool {
        true
    }

    closed spec fn decrease(&self) -> Option<nat> {
        Some(self.len() as nat)
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < self.metadata_perms().len() {
            Some(
                Frame::<M>::from_raw_spec(
                    (self.range().start + index * PAGE_SIZE) as usize,
                    self.slot_perms()[index],
                    Some(self.metadata_perms()[index]),
                ),
            )
        } else {
            None
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> Segment<M> {
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
        requires
            old(regions).inv(),
            self.inv(),
            self.relate_regions(*old(regions)),
            forall|i: int|
                #![trigger frame_to_index((self.start_paddr() + i * PAGE_SIZE) as usize)]
                0 <= i < self.len() ==> {
                    let idx = frame_to_index((self.start_paddr() + i * PAGE_SIZE) as usize);
                    &&& old(regions).slot_owners[idx].storage_perm().is_init()
                    &&& old(regions).ref_count(idx) == 1 ==> {
                        &&& old(regions).slot_owners[idx].in_list_perm.value() == 0
                    }
                },
        ensures
            final(regions).inv(),
    )]
    pub fn drop(self) {
        let ghost n = self.len();
        let mut paddr = self.range.start;
        let tracked mut raw_perms = self.tracked_perms.get().tracked_unwrap();

        let ghost mut k: int = 0;

        loop
            invariant
                old(regions).inv(),
                regions.inv(),
                self.inv(),
                raw_perms.len() == n - k,
                forall|j: int|
                    #![trigger raw_perms[j]]
                    0 <= j < raw_perms.len() ==> {
                        let idx = frame_to_index((self.range.start + (k + j) * PAGE_SIZE) as usize);
                        &&& raw_perms[j].inv()
                        &&& raw_perms[j].slot_perm == regions.slots[idx]
                        &&& raw_perms[j].metadata_perm.id()
                            == regions.slot_owners[idx].metadata_perm.id()
                    },
                self.range.start <= paddr <= self.range.end,
                paddr == (self.range.start + k * PAGE_SIZE) as usize,
                paddr % PAGE_SIZE == 0,
                paddr <= MAX_PADDR,
                0 <= k <= n,
                n == (self.range.end - self.range.start) / PAGE_SIZE as int,
                paddr < self.range.end <==> k < n,
                forall|j: int|
                    #![trigger frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                    k <= j < n ==> {
                        let idx = frame_to_index((self.range.start + j * PAGE_SIZE) as usize);
                        &&& regions.contains(idx)
                        &&& regions.slot_owners[idx] == old(regions).slot_owners[idx]
                    },
                forall|j: int|
                    #![trigger frame_idx_at(self.range.start, j)]
                    k <= j < n ==> regions.contains(frame_idx_at(self.range.start, j))
                        && regions.slot_owners[frame_idx_at(self.range.start, j)] == old(
                        regions,
                    ).slot_owners[frame_idx_at(self.range.start, j)],
                regions.slot_owners.dom() == old(regions).slot_owners.dom(),
                self.relate_regions(*old(regions)),
                forall|i: int|
                    #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
                    0 <= i < n ==> {
                        let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                        &&& old(regions).slot_owners[idx].storage_perm().is_init()
                        &&& old(regions).ref_count(idx) == 1 ==> {
                            &&& old(regions).slot_owners[idx].in_list_perm.value() == 0
                        }
                    },
            decreases n - k,
        {
            if paddr >= self.range.end {
                break;
            }
            let tracked perm = raw_perms.tracked_pop_front();
            let frame = unsafe {
                #[verus_spec(with Tracked(perm))]
                Frame::<M>::from_raw(paddr)
            };

            frame.drop(Tracked(regions));

            paddr += PAGE_SIZE;

            proof {
                k = k + 1;
            }
        }
    }
}

/*impl<M: AnyFrameMeta> TryFrom<Segment<dyn AnyFrameMeta>> for Segment<M> {
    type Error = Segment<dyn AnyFrameMeta>;

    open spec fn clone_ensures(
        self,
        old_perm: MetaRegionOwners,
        new_perm: MetaRegionOwners,
        res: Self,
    ) -> bool {
        &&& res.range == self.range
        &&& res.inv()
        &&& new_perm.inv()
    }

    fn clone(&self, Tracked(perm): Tracked<&mut MetaRegionOwners>) -> (res: Self) {
        let mut paddr = self.range.start;

        let ghost old_perm = *perm;
        loop
            invariant
                perm.inv(),
                self.inv(),
                perm.slots == old_perm.slots,
                perm.slot_owners.dom() == old_perm.slot_owners.dom(),
                // Linear-drop pilot: cloning a Segment doesn't mint or
                // redeem its obligation — the per-frame ref-count bump is
                // an Arc-style operation.
                self.range.start <= paddr <= self.range.end,
                paddr % PAGE_SIZE == 0,
                paddr <= MAX_PADDR,
                forall|pa: Paddr|
                    #![trigger frame_to_index(pa)]
                    (paddr <= pa < self.range.end && pa % PAGE_SIZE == 0) ==> {
                        let idx = frame_to_index(pa);
                        &&& perm.contains(idx)
                        &&& valid_frame_paddr(pa)
                        &&& perm.ref_count(idx) > 0
                        &&& perm.ref_count(idx) + 1
                            < REF_COUNT_MAX
                        &&& !MetaSlot::inc_ref_count_panic_cond(
                            perm.slot_owners[idx].ref_count_perm,
                        )
                    },
            decreases self.range.end - paddr,
        {
            if paddr >= self.range.end {
                break;
            }
            #[verus_spec(with Tracked(perm))]
            crate::mm::frame::inc_frame_ref_count(paddr);

            paddr = paddr + PAGE_SIZE;
        }
        // Since segments are homogeneous, we can safely assume that the rest
        // of the frames are of the same type. We just debug-check here.
        #[cfg(debug_assertions)]
        {
            for paddr in seg.range.clone().step_by(PAGE_SIZE) {
                let frame = unsafe { Frame::<dyn AnyFrameMeta>::from_raw(paddr) };
                let frame = ManuallyDrop::new(frame);
                debug_assert!((frame.dyn_meta() as &dyn core::any::Any).is::<M>());
            }
        }
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        Ok(unsafe { core::mem::transmute::<Segment<dyn AnyFrameMeta>, Segment<M>>(seg) })
    }
}

impl<M: AnyUFrameMeta> From<Segment<M>> for USegment {
    fn from(seg: Segment<M>) -> Self {
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        unsafe { core::mem::transmute(seg) }
    }
}

impl TryFrom<Segment<dyn AnyFrameMeta>> for USegment {
    type Error = Segment<dyn AnyFrameMeta>;

    /// Try converting a [`Segment<dyn AnyFrameMeta>`] into [`USegment`].
    ///
    /// If the usage of the page is not the same as the expected usage, it will
    /// return the dynamic page itself as is.
    fn try_from(seg: Segment<dyn AnyFrameMeta>) -> core::result::Result<Self, Self::Error> {
        // SAFETY: for each page there would be a forgotten handle
        // when creating the `Segment` object.
        let first_frame = unsafe { Frame::<dyn AnyFrameMeta>::from_raw(seg.range.start) };
        let first_frame = ManuallyDrop::new(first_frame);
        if !first_frame.dyn_meta().is_untyped() {
            return Err(seg);
        }
        // Since segments are homogeneous, we can safely assume that the rest
        // of the frames are of the same type. We just debug-check here.
        #[cfg(debug_assertions)]
        {
            for paddr in seg.range.clone().step_by(PAGE_SIZE) {
                let frame = unsafe { Frame::<dyn AnyFrameMeta>::from_raw(paddr) };
                let frame = ManuallyDrop::new(frame);
                debug_assert!(frame.dyn_meta().is_untyped());
            }
        }
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        Ok(unsafe { core::mem::transmute::<Segment<dyn AnyFrameMeta>, USegment>(seg) })
    }
} */

impl<M: AnyFrameMeta + ?Sized> Inv for Segment<M> {
    /// The invariant of a [`Segment`]:
    ///
    /// - the physical addresses of the frames are aligned and within bounds.
    /// - the range is well-formed, i.e., the start is less than or equal to the end.
    open spec fn inv(self) -> bool {
        &&& self.start_paddr() % PAGE_SIZE == 0
        &&& self.end_paddr() % PAGE_SIZE == 0
        &&& self.start_paddr() <= self.end_paddr() <= MAX_PADDR
        &&& self.inner_perm_inv()
        &&& self.raw_perms().len() == self.len()
        &&& forall|i: int|
            #![trigger self.raw_perms()[i]]
            0 <= i < self.raw_perms().len() ==> {
                let paddr = (self.range().start + i * PAGE_SIZE) as usize;
                &&& self.raw_perms()[i].slot_vaddr() == frame_to_meta(paddr)
                &&& self.raw_perms()[i].inv()
            }
    }
}

} // verus!
