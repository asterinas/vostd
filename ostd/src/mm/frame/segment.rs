// SPDX-License-Identifier: MPL-2.0
//! A contiguous range of frames.
use vstd::modes::tracked_swap;
use vstd::prelude::*;
use vstd::proph::ProphecyGhost;
use vstd::simple_pptr;
use vstd::std_specs::iter::{IteratorSpec, IteratorSpecImpl};
use vstd_extra::assert;
use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;
use vstd_extra::panic::may_panic;
use vstd_extra::prelude::*;

use crate::mm::page_table::RCClone;
use crate::mm::{Paddr, PagingLevel, Vaddr, paddr_to_vaddr};
use crate::specs::arch::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::frame::segment::*;
use crate::specs::mm::frame::{
    mapping::{frame_to_index, group_page_meta, meta_addr},
    meta_owners::*,
};
use crate::specs::mm::virt_mem::MemView;

use core::{fmt::Debug, /*mem::ManuallyDrop,*/ ops::Range};

use super::meta::mapping::frame_to_meta;
use super::{AnyFrameMeta, GetFrameError, MetaSlot};
use crate::mm::frame::{Frame, meta::REF_COUNT_MAX, untyped::AnyUFrameMeta};

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
        &&& forall|pa: Paddr|
            #![trigger frame_to_index(pa)]
            (self.start_paddr() <= pa < self.end_paddr() && pa % PAGE_SIZE == 0) ==> {
                let idx = frame_to_index(pa);
                &&& perm.slots.contains_key(idx)
                &&& has_safe_slot(pa)
                &&& perm.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& perm.slot_owners[idx].inner_perms.ref_count.value() + 1
                    < super::meta::REF_COUNT_MAX
                &&& !MetaSlot::inc_ref_count_panic_cond(perm.slot_owners[idx].inner_perms.ref_count)
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
        // `Segment::clone` bumps each page's refcount via
        // `inc_frame_ref_count` (which preserves the ledger), not through
        // `Frame::clone`, so it is net-zero on `frame_obligations`. (The
        // trait no longer hardcodes this; each impl states its own effect.)
        &&& new_perm.frame_obligations =~= old_perm.frame_obligations
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
                perm.frame_obligations == old_perm.frame_obligations,
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
                            perm.slot_owners[idx].inner_perms.ref_count,
                        )
                    },
            decreases self.range.end - paddr,
        {
            if paddr >= self.range.end {
                break;
            }
            unsafe {
                #[verus_spec(with Tracked(perm))]
                crate::mm::frame::inc_frame_ref_count(paddr)
            };

            paddr = paddr + PAGE_SIZE;
        }

        Self { range: self.range.start..self.range.end, _marker: core::marker::PhantomData }
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Segment<M> {
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
    /// - the metadata function must be well-formed and valid for all frames in the range;
    /// - the metadata function must ensure that the frames can be created and owned by the segment;
    /// - for any frame created via the closure `metadata_fn`, the corresponding slot in `regions`
    ///   must be unused and not dropped in the owner ([`MetaRegionOwners`]).
    ///
    /// Range constraints (alignment, `range.end <= MAX_PADDR`, non-emptiness) are runtime-checked
    /// in the body — see the postconditions below for the corresponding error variants.
    /// ## Postconditions
    /// - if the result is `Ok`, the returned segment satisfies its invariant with the owner,
    ///   has the same physical address range as the input, and the owner is `Some`;
    /// - if the input range is misaligned, the result is `Err(NotAligned)`;
    /// - if the input range exceeds `MAX_PADDR`, the result is `Err(OutOfBound)`;
    /// - if the input is aligned and within `MAX_PADDR` and the function terminated,
    ///   then `range.start < range.end` (the runtime `assert!` would otherwise diverge).
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
                -> owner: Tracked<Option<SegmentOwner<M>>>,
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
            r is Err ==> final(regions).frame_obligations == old(regions).frame_obligations,
            (range.start % PAGE_SIZE != 0 || range.end % PAGE_SIZE != 0)
                ==> r == Err::<Self, _>(GetFrameError::NotAligned),
            (range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0 && range.end > MAX_PADDR)
                ==> r == Err::<Self, _>(GetFrameError::OutOfBound),
            r is Ok ==> range.end <= MAX_PADDR ==> range.start < range.end,
            r matches Ok(seg) ==> {
                &&& seg.start_paddr() == range.start
                &&& seg.end_paddr() == range.end
                &&& seg.start_paddr() < seg.end_paddr()
                &&& crate::specs::mm::frame::segment::seg_obligations_minted(
                    *old(regions),
                    *final(regions),
                    range.start,
                    crate::specs::mm::frame::segment::seg_nframes(range),
                )
                &&& owner@ matches Some(owner) && {
                    &&& seg.inv()
                    &&& seg.wf(&owner)
                }
                &&& forall|paddr: Paddr|
                    #![trigger frame_to_index(paddr)]
                    (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                        ==> final(regions).slots.contains_key(frame_to_index(paddr))
            },
    )]
    pub fn from_unused(range: Range<Paddr>, metadata_fn: impl Fn(Paddr) -> (Paddr, M)) -> (res:
        Result<Self, GetFrameError>) {
        proof_decl! {
            let tracked mut owner: Option<SegmentOwner<M>> = None;
            let tracked mut addrs = Seq::<usize>::tracked_empty();
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
        assert!(range.start < range.end);

        let mut segment = Self {
            range: range.start..range.start,
            _marker: core::marker::PhantomData,
        };

        let mut i = 0;
        let addr_len = (range.end - range.start) / PAGE_SIZE;

        while i < addr_len
            invariant
                i <= addr_len,
                i as int == addrs.len(),
                range.start % PAGE_SIZE == 0,
                range.end % PAGE_SIZE == 0,
                range.end <= MAX_PADDR,
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
                    0 <= j < addrs.len() as int ==> {
                        let idx = frame_to_index(addrs[j]);
                        &&& regions.slots.contains_key(idx)
                        &&& regions.slot_owners.contains_key(idx)
                        &&& regions.slot_owners[idx].slot_vaddr == meta_addr(idx)
                        &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                        &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                            <= crate::mm::frame::meta::REF_COUNT_MAX
                        &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                        &&& addrs[j] % PAGE_SIZE == 0
                        &&& addrs[j] < MAX_PADDR
                        &&& addrs[j] == range.start + (j as u64) * PAGE_SIZE
                    },
                regions.inv(),
                regions.frame_obligations == old(regions).frame_obligations,
                regions.slot_owners.dom() == old(regions).slot_owners.dom(),
                segment.range.start == range.start,
                segment.range.end == range.start + i * PAGE_SIZE,
            ensures
                i == addr_len,
            decreases addr_len - i,
        {
            let paddr_in = range.start + i * PAGE_SIZE;
            let (paddr, meta) = metadata_fn(paddr_in);

            let ghost regions_pre = *regions;
            let res = #[verus_spec(with Tracked(regions))]
            Frame::<M>::from_unused(paddr, meta);
            let frame = match res {
                Ok(f) => f,
                Err(e) => {
                    let mut p = range.start;
                    let ghost mut k: int = 0;
                    while p < segment.range.end
                        invariant
                            regions.inv(),
                            regions.frame_obligations == old(regions).frame_obligations,
                            regions.slot_owners.dom() == old(regions).slot_owners.dom(),
                            range.start % PAGE_SIZE == 0,
                            i as int == addrs.len(),
                            segment.range.end == range.start + i * PAGE_SIZE,
                            segment.range.end <= MAX_PADDR,
                            range.start <= p <= segment.range.end,
                            p == range.start + k * PAGE_SIZE,
                            p % PAGE_SIZE == 0,
                            0 <= k <= i,
                            forall|j: int|
                                #![trigger addrs[j]]
                                k <= j < addrs.len() as int ==> {
                                    let idx = frame_to_index(addrs[j]);
                                    &&& regions.slots.contains_key(idx)
                                    &&& regions.slot_owners.contains_key(idx)
                                    &&& regions.slot_owners[idx].slot_vaddr == meta_addr(idx)
                                    &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                                    &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                                        <= crate::mm::frame::meta::REF_COUNT_MAX
                                    &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                                    &&& addrs[j] % PAGE_SIZE == 0
                                    &&& addrs[j] < MAX_PADDR
                                    &&& addrs[j] == range.start + (j as u64) * PAGE_SIZE
                                },
                        decreases segment.range.end - p,
                    {
                        let ghost reclaim_pre = *regions;
                        let ghost idx_k = frame_to_index(p);
                        proof {
                            broadcast use group_page_meta;

                            assert(addrs[k] == p);
                            assert(meta_addr(idx_k) == frame_to_meta(p));
                            assert(regions.slots.contains_key(idx_k));
                        }
                        proof_decl! {
                            let tracked from_raw_obl: vstd_extra::drop_tracking::DropObligation<
                                usize,
                            >;
                        }
                        let frame = unsafe {
                            #[verus_spec(with Tracked(regions) => Tracked(from_raw_obl))]
                            Frame::<M>::from_raw(p)
                        };
                        proof {
                            broadcast use group_page_meta;

                            assert(regions.slots[idx_k].pptr() == frame.ptr);
                        }
                        frame.drop(Tracked(regions), Tracked(from_raw_obl));
                        proof {
                            assert forall|j: int|
                                #![trigger addrs[j]]
                                (k + 1) <= j < addrs.len() as int implies ({
                                let idx = frame_to_index(addrs[j]);
                                &&& regions.slots.contains_key(idx)
                                &&& regions.slot_owners.contains_key(idx)
                                &&& regions.slot_owners[idx] == reclaim_pre.slot_owners[idx]
                            }) by {
                                assert(addrs[j] != p);
                                crate::specs::mm::frame::mapping::lemma_frame_to_index_injective(
                                    addrs[j],
                                    p,
                                );
                            };
                        }
                        p = p + PAGE_SIZE;
                        proof {
                            k = k + 1;
                        }
                    }
                    return {
                        proof_with!(|= Tracked(owner));
                        Err(e)
                    };
                },
            };

            let _ = ManuallyDrop::new(frame, Tracked(regions));
            segment.range.end = paddr + PAGE_SIZE;
            proof {
                broadcast use group_page_meta;

                regions.inv_implies_correct_addr(paddr);
                let idx = frame_to_index(paddr);
                axiom_mmio_usage_iff_mmio_paddr(regions.slot_owners[idx]);
                axiom_mmio_usage_iff_mmio_paddr(regions_pre.slot_owners[idx]);
                assert(regions_pre.slot_owners[idx].paths_in_pt.is_empty());
                assert(regions.slot_owners[idx].paths_in_pt
                    == regions_pre.slot_owners[idx].paths_in_pt);
                assert(regions.frame_obligations == regions_pre.frame_obligations);
                addrs.tracked_push(paddr);
            }

            i += 1;
        }

        proof {
            // Per-frame migration: record one forgotten reference per frame in
            // `frame_obligations`. The construction loop above is net-zero on
            // the ledger (each `Frame::from_unused` mint is cancelled by its
            // `ManuallyDrop`); this post-loop pass records the segment's
            // retained per-frame references, replacing the old single
            // range-keyed `obligations` entry.
            // The construction loop preserved `frame_obligations`, so the mint
            // helper's exact delta (stated against the pre-mint state) telescopes
            // to the function's entry state for the postcondition.
            assert(regions.frame_obligations == old(regions).frame_obligations);
            crate::specs::mm::frame::segment::tracked_mint_seg_obligations(
                regions,
                range.start,
                addr_len as int,
            );
            assert(addr_len as int == crate::specs::mm::frame::segment::seg_nframes(range));
            owner = Some(SegmentOwner { range, _marker: core::marker::PhantomData });

            assert forall|addr: usize|
                #![trigger frame_to_index(addr)]
                range.start <= addr < range.end && addr % PAGE_SIZE == 0 implies {
                regions.slots.contains_key(frame_to_index(addr))
            } by {
                let j = (addr - range.start) / PAGE_SIZE as int;
                assert(addrs[j as int] == addr);
            }
        }

        proof_with!(|= Tracked(owner));
        Ok(segment)
    }

    /// Restores the [`Segment`] from the raw physical address range.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - the meta region must satisfy its invariant;
    /// - the segment-to-be (with the supplied `range`) must satisfy its invariant
    ///   ([`Self::inv`]) and the well-formedness relation with `owner` ([`Self::wf`]);
    /// - `owner` must relate correctly to `regions`.
    ///
    /// Following the [`UniqueFrame::from_raw`] pattern, the contract here ties
    /// `range` and `owner` together up front so that the postcondition can
    /// directly advertise `r.inv()` and `r.wf(&owner)` for the caller.
    ///
    /// ## Postconditions
    /// - the returned segment satisfies its invariant and is well-formed with `owner`;
    /// - the returned segment has the same physical address range as the input;
    /// - the meta region is unchanged (preserving the relation with `owner`).
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
            old(regions).inv(),
            owner.inv(),
            range == owner.range,
            owner.relate_regions(*old(regions)),
        ensures
            r.range() == range,
            r.inv(),
            r.wf(&owner),
            final(regions).inv(),
            *final(regions) == *old(regions),
    )]
    pub(crate) unsafe fn from_raw(range: Range<Paddr>) -> Self {
        Self { range, _marker: core::marker::PhantomData }
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + ?Sized> Segment<M> {
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
    /// - the segment must satisfy its invariant ([`Self::inv`]) and the well-formedness
    ///   relation with the owner ([`Self::wf`]);
    /// - the offset must be aligned and within bounds;
    /// - the meta region must be valid and the owner must relate to it.
    ///
    /// ## Postconditions
    /// - the resulting segments satisfy their invariants with the corresponding owners;
    /// - they match [`Self::split_spec`];
    /// - the original owner's permissions are split between the two new owners;
    /// - both halves continue to relate correctly to `regions` (which is unchanged).
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<SegmentOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
                -> result_owners: (Tracked<SegmentOwner<M>>, Tracked<SegmentOwner<M>>),
        requires
            self.invariants(&owner, *old(regions)),
            offset % PAGE_SIZE != 0 ==> may_panic(),
            !(0 < offset && offset < self.size()) ==> may_panic(),
        ensures
            final(regions).slots == old(regions).slots,
            final(regions).slot_owners == old(regions).slot_owners,
            final(regions).frame_obligations == old(regions).frame_obligations,
            (r.0, r.1) == self.split_spec(offset),
            r.0.invariants(&result_owners.0@, *final(regions)),
            r.1.invariants(&result_owners.1@, *final(regions)),
    )]
    pub fn split(self, offset: usize) -> (Self, Self) {
        assert!(offset % PAGE_SIZE == 0);
        assert!(0 < offset && offset < self.size());

        let ghost old_regions = *regions;

        let old = ManuallyDrop::new(self, Tracked(regions));
        let at = old.range.start + offset;

        let ghost old_start = old@.start_paddr();
        let ghost old_end = old@.end_paddr();

        let tracked frame_own1 = SegmentOwner {
            range: old_start..at,
            _marker: core::marker::PhantomData,
        };
        let tracked frame_own2 = SegmentOwner {
            range: at..old_end,
            _marker: core::marker::PhantomData,
        };
        proof {
            assert(*regions == old_regions);
            assert(regions.slot_owners == old_regions.slot_owners);
            assert(regions.frame_obligations == old_regions.frame_obligations);
            assert forall|i: int|
                #![trigger frame_to_index((frame_own1.range.start + i * PAGE_SIZE) as usize)]
                0 <= i < crate::specs::mm::frame::segment::seg_nframes(frame_own1.range) implies {
                let idx = frame_to_index((frame_own1.range.start + i * PAGE_SIZE) as usize);
                &&& regions.frame_obligations.count(idx) >= 1
                &&& regions.slot_owners.contains_key(idx)
                &&& regions.slots.contains_key(idx)
                &&& regions.slot_owners[idx].slot_vaddr == meta_addr(idx)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    <= crate::mm::frame::meta::REF_COUNT_MAX
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                &&& regions.slot_owners[idx].usage is Frame
            } by {
                owner.relate_regions_at(old_regions, i);
            }
            assert forall|i: int|
                #![trigger frame_to_index((frame_own2.range.start + i * PAGE_SIZE) as usize)]
                0 <= i < crate::specs::mm::frame::segment::seg_nframes(frame_own2.range) implies {
                let idx = frame_to_index((frame_own2.range.start + i * PAGE_SIZE) as usize);
                &&& regions.frame_obligations.count(idx) >= 1
                &&& regions.slot_owners.contains_key(idx)
                &&& regions.slots.contains_key(idx)
                &&& regions.slot_owners[idx].slot_vaddr == meta_addr(idx)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    <= crate::mm::frame::meta::REF_COUNT_MAX
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                &&& regions.slot_owners[idx].usage is Frame
            } by {
                owner.relate_regions_at(old_regions, i + (offset / PAGE_SIZE) as int);
            }

            assert forall|i: int, j: int|
                #![trigger frame_to_index((frame_own1.range.start + i * PAGE_SIZE) as usize),
                    frame_to_index((frame_own1.range.start + j * PAGE_SIZE) as usize)]
                0 <= i < j < crate::specs::mm::frame::segment::seg_nframes(
                    frame_own1.range,
                ) implies frame_to_index((frame_own1.range.start + i * PAGE_SIZE) as usize)
                != frame_to_index((frame_own1.range.start + j * PAGE_SIZE) as usize) by {
                owner.relate_regions_distinct(old_regions, i, j);
            }
            assert forall|i: int, j: int|
                #![trigger frame_to_index((frame_own2.range.start + i * PAGE_SIZE) as usize),
                    frame_to_index((frame_own2.range.start + j * PAGE_SIZE) as usize)]
                0 <= i < j < crate::specs::mm::frame::segment::seg_nframes(
                    frame_own2.range,
                ) implies frame_to_index((frame_own2.range.start + i * PAGE_SIZE) as usize)
                != frame_to_index((frame_own2.range.start + j * PAGE_SIZE) as usize) by {
                owner.relate_regions_distinct(
                    old_regions,
                    i + (offset / PAGE_SIZE) as int,
                    j + (offset / PAGE_SIZE) as int,
                );
            }
        }
        proof_with!(|= (Tracked(frame_own1), Tracked(frame_own2)));
        (
            Self { range: old.range.start..at, _marker: core::marker::PhantomData },
            Self { range: at..old.range.end, _marker: core::marker::PhantomData },
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
            #![trigger frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
            (range.start as int) / (PAGE_SIZE as int) <= j < (range.end as int) / (PAGE_SIZE as int)
                && regions.slot_owners[frame_to_index(
                (self.start_paddr() + j * PAGE_SIZE) as usize,
            )].inner_perms.ref_count.value() >= REF_COUNT_MAX
    }

    /// Gets an extra handle to the frames in the byte offset range.
    ///
    /// The sliced byte offset range in indexed by the offset from the start of
    /// the contiguous frames. The resulting frames holds extra reference counts.
    ///
    /// # Verified Properties
    /// ## Postconditions
    /// - the resulting slice's range matches the slicing range and is in-bounds
    ///   (the in-bounds check follows from the diverging `assert!` in the body);
    /// - `regions` preserves invariants and key domains. Per-frame state — e.g.
    ///   that a hypothetical `sub_owner.relate_regions(regions)` would hold —
    ///   is *not* exposed; threading that through the per-frame ref-count bump
    ///   loop would require a much heavier proof. Mirrors [`Segment::clone`].
    ///
    /// See also [`vstd::seq::Seq::subrange`].
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&SegmentOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            self.invariants(owner, *old(regions)),
            range.start % PAGE_SIZE != 0 ==> may_panic(),
            range.end % PAGE_SIZE != 0 ==> may_panic(),
            range.start > range.end ==> may_panic(),
            self.range.start as int + range.end as int > self.range.end as int ==> may_panic(),
            self.page_in_range_saturated(range, *old(regions)) ==> may_panic(),
        ensures
            range.start % PAGE_SIZE == 0,
            range.end % PAGE_SIZE == 0,
            range.start <= range.end,
            self.range.start as int + range.end as int <= self.range.end as int,
            !self.page_in_range_saturated(range, *old(regions)),
            r.inv(),
            r.start_paddr() == self.start_paddr() + range.start,
            r.end_paddr() == self.start_paddr() + range.end,
            r.end_paddr() <= self.end_paddr(),
            final(regions).inv(),
            final(regions).slots == old(regions).slots,
            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
            final(regions).frame_obligations == old(regions).frame_obligations,
    )]
    #[verifier::rlimit(8000)]
    pub fn slice(&self, range: &Range<usize>) -> Self {
        // KNOWN BUG: potential overflows https://github.com/asterinas/asterinas/issues/3165
        assume(self.range.start + range.start <= usize::MAX);
        assume(self.range.start + range.end <= usize::MAX);

        assert!(range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0);
        let start = self.range.start + range.start;
        let end = self.range.start + range.end;
        assert!(start <= end && end <= self.range.end);

        let mut paddr = start;
        let ghost addr_len = (end - start) / PAGE_SIZE as int;
        let ghost first_perm_idx: int = (range.start / PAGE_SIZE) as int;
        let ghost last_perm_idx: int = (range.end / PAGE_SIZE) as int;
        let ghost old_regions = *regions;
        let ghost mut i: int = 0;
        loop
            invariant
                self.page_in_range_saturated(range, *old(regions)) ==> may_panic(),
                old_regions == *old(regions),
                regions.inv(),
                regions.slots == old_regions.slots,
                regions.slot_owners.dom() == old_regions.slot_owners.dom(),
                regions.frame_obligations == old_regions.frame_obligations,
                start == self.range.start + range.start,
                end == self.range.start + range.end,
                start <= end <= self.range.end,
                start % PAGE_SIZE == 0,
                end % PAGE_SIZE == 0,
                paddr == (start + i * PAGE_SIZE) as usize,
                paddr <= end,
                0 <= i <= addr_len,
                addr_len == (end - start) / PAGE_SIZE as int,
                paddr < end <==> i < addr_len,
                self.inv(),
                self.wf(&owner),
                owner.inv(),
                owner.relate_regions(old_regions),
                first_perm_idx == range.start / PAGE_SIZE,
                last_perm_idx == range.end / PAGE_SIZE,
                first_perm_idx + addr_len as int == last_perm_idx,
                first_perm_idx + i <= last_perm_idx,
                forall|j: int|
                    #![trigger frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                    first_perm_idx + i <= j < last_perm_idx ==> (
                    *regions).slot_owners[frame_to_index(
                        (self.range.start + j * PAGE_SIZE) as usize,
                    )] == old_regions.slot_owners[frame_to_index(
                        (self.range.start + j * PAGE_SIZE) as usize,
                    )],
                forall|j: int|
                    #![trigger frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                    first_perm_idx <= j < first_perm_idx + i
                        ==> old_regions.slot_owners[frame_to_index(
                        (self.range.start + j * PAGE_SIZE) as usize,
                    )].inner_perms.ref_count.value() < REF_COUNT_MAX,
            ensures
                i == addr_len,
            decreases addr_len - i,
        {
            if paddr >= end {
                break;
            }
            let ghost slot_idx: usize = frame_to_index(paddr);
            let ghost perm_idx: int = first_perm_idx + i;

            proof {
                owner.relate_regions_at(old_regions, perm_idx);
                assert(regions.slot_owners[slot_idx] == old_regions.slot_owners[slot_idx]);
            }

            unsafe {
                #[verus_spec(with Tracked(regions))]
                crate::mm::frame::inc_frame_ref_count(paddr)
            };

            paddr = paddr + PAGE_SIZE;

            proof {
                i = i + 1;
                assert forall|j: int|
                    #![trigger frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                    first_perm_idx + i <= j < last_perm_idx implies (
                *regions).slot_owners[frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                    == old_regions.slot_owners[frame_to_index(
                    (self.range.start + j * PAGE_SIZE) as usize,
                )] by {};
            }
        }

        Self { range: start..end, _marker: core::marker::PhantomData }
    }

    /// Forgets the [`Segment`] and gets a raw range of physical addresses.
    ///
    /// The segment's permissions are returned to the caller via `frame_perms`.
    /// The caller is responsible for holding onto the permissions and providing
    /// them back when restoring the segment with [`Self::from_raw`].
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - the segment must satisfy the invariant with the owner;
    /// - the meta region in `regions` must satisfy the invariant;
    /// - the owner must relate correctly to `regions`.
    ///
    /// ## Postconditions
    /// - the returned physical address range matches the segment's range;
    /// - the meta region is unchanged (preserving the relation with the returned owner).
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<SegmentOwner<M>>,
                -> frame_perms: Tracked<SegmentOwner<M>>,
        requires
            self.invariants(&owner, *old(regions)),
        ensures
            r == self.range(),
            final(regions).inv(),
            *final(regions) == *old(regions),
            frame_perms@ == owner,
    )]
    pub(crate) fn into_raw(self) -> Range<Paddr> {
        let range = self.range.clone();
        let _ = ManuallyDrop::new(self, Tracked(regions));

        proof_with!(|= Tracked(owner));
        range
    }

    /// Returns the number of pages of the contiguous frames.
    #[verifier::inline]
    pub open spec fn nrpage_spec(&self) -> usize
        recommends
            self.inv(),
    {
        self.size() / PAGE_SIZE
    }

    /// Splits the contiguous frames into two at the given byte offset from the start in spec mode.
    pub closed spec fn split_spec(self, offset: usize) -> (Self, Self)
        recommends
            self.inv(),
            offset % PAGE_SIZE == 0,
            0 < offset < self.size(),
    {
        let at = (self.start_paddr() + offset) as usize;
        let idx = at / PAGE_SIZE;
        (
            Self { range: self.start_paddr()..at, _marker: core::marker::PhantomData },
            Self { range: at..self.end_paddr(), _marker: core::marker::PhantomData },
        )
    }
}

/// A frame yielded from a [`SegmentIterator`] together with its drop obligation.
pub type SegmentIteratorItem<M> = (Frame<M>, Tracked<DropObligation<usize>>);

/// Prophetic sequence state used to specify the frames that a segment iterator will yield.
#[verifier::reject_recursive_types(T)]
pub tracked struct SegmentIteratorProphecySeq<T> {
    tracked var: ProphecyGhost<Seq<T>>,
    ghost done: bool,
}

impl<T> SegmentIteratorProphecySeq<T> {
    #[verifier::prophetic]
    closed spec fn seq(&self) -> Seq<T> {
        if self.done {
            Seq::empty()
        } else {
            self.var.value()
        }
    }

    proof fn new() -> (tracked res: Self)
        ensures
            !res.done,
    {
        SegmentIteratorProphecySeq { var: ProphecyGhost::new(), done: false }
    }

    proof fn resolve_cons(tracked &mut self, value: T)
        requires
            !old(self).done,
        ensures
            !final(self).done,
            old(self).seq() == seq![value] + final(self).seq(),
    {
        let tracked mut var = ProphecyGhost::new();
        tracked_swap(&mut var, &mut self.var);
        var.resolve_dependent(&self.var, |tail| seq![value] + tail);
    }

    proof fn resolve_nil(tracked &mut self)
        ensures
            old(self).seq() == Seq::<T>::empty(),
            final(self).seq() == Seq::<T>::empty(),
            final(self).done,
    {
        if !self.done {
            let tracked mut var = ProphecyGhost::new();
            tracked_swap(&mut var, &mut self.var);
            var.resolve(seq![]);
            self.done = true;
        }
    }
}

/// Verified iterator over the frames owned by a [`Segment`].
///
/// The iterator advances an owned suffix of the segment while threading the
/// metadata region owner and segment owner permissions.
#[verifier::reject_recursive_types(M)]
pub struct SegmentIterator<'a, M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> {
    segment: &'a Segment<M>,
    range: Range<Paddr>,
    tracked_regions: Tracked<&'a mut MetaRegionOwners>,
    tracked_owner: Tracked<&'a mut SegmentOwner<M>>,
    tracked_remaining: Tracked<SegmentIteratorProphecySeq<SegmentIteratorItem<M>>>,
}

#[verus_verify]
impl<'a, M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> SegmentIterator<'a, M> {
    pub closed spec fn segment_ref(&self) -> &'a Segment<M> {
        self.segment
    }

    pub closed spec fn range_spec(&self) -> Range<Paddr> {
        self.range
    }

    pub closed spec fn current_segment(&self) -> Segment<M> {
        Segment { range: self.range.start..self.range.end, _marker: core::marker::PhantomData }
    }

    #[verifier::prophetic]
    pub closed spec fn remaining_spec(&self) -> Seq<SegmentIteratorItem<M>> {
        self.tracked_remaining@.seq()
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& self.segment.inv()
        &&& self.segment.range.start <= self.range.start
        &&& self.range.end == self.segment.range.end
        &&& self.current_segment().invariants(self.tracked_owner@, *self.tracked_regions@)
        &&& self.range.start < self.range.end ==> !self.tracked_remaining@.done
    }

    #[verus_spec(res =>
        with
            Tracked(regions): Tracked<&'a mut MetaRegionOwners>,
            Tracked(owner): Tracked<&'a mut SegmentOwner<M>>,
        requires
            segment.invariants(owner, *regions),
        ensures
            res.segment_ref() == segment,
            res.range_spec() == segment.range,
            IteratorSpec::decrease(&res) is Some,
            IteratorSpec::initial_value_relation(&res, &res),
    )]
    pub fn new(segment: &'a Segment<M>) -> Self {
        Self {
            segment,
            range: segment.range.start..segment.range.end,
            tracked_regions: Tracked(regions),
            tracked_owner: Tracked(owner),
            tracked_remaining: Tracked(SegmentIteratorProphecySeq::new()),
        }
    }

    /// Advances the verified segment iterator by one frame.
    ///
    /// This helper is the proof-carrying body behind [`Iterator::next`]. The
    /// tracked metadata region, segment owner, and prophecy state are supplied
    /// through `#[verus_spec]`, keeping the executable signature free of tracked
    /// arguments.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - the segment must satisfy its invariant;
    /// - `range` must be a suffix of `segment.range`;
    /// - the segment represented by `range` must satisfy its invariant with the
    ///   tracked owner and meta regions, which includes the owner/region relation;
    /// - if `range` is non-empty, the remaining prophecy sequence must not have
    ///   been resolved to `done`.
    ///
    /// ## Postconditions
    /// - the segment must satisfy its invariant;
    /// - `range` remains a suffix of `segment.range`;
    /// - the segment represented by the final `range` satisfies its invariant
    ///   with the final tracked owner and meta regions;
    /// - if the result is `None`, `range` is unchanged and both the old and final
    ///   remaining prophecy sequences are empty;
    /// - if the result is `Some(item)`, `range.start` advances by one page, the
    ///   yielded frame starts at the old `range.start`, and the old remaining
    ///   prophecy sequence is exactly `item` followed by the final one;
    /// - if the final `range` is still non-empty, the remaining prophecy sequence
    ///   is still unresolved.
    #[verus_spec(res =>
        with
            Tracked(regions_ref): Tracked<&mut &'a mut MetaRegionOwners>,
            Tracked(owner_ref): Tracked<&mut &'a mut SegmentOwner<M>>,
            Tracked(remaining): Tracked<&mut SegmentIteratorProphecySeq<SegmentIteratorItem<M>>>,
        requires
            segment.inv(),
            segment.range.start <= old(range).start,
            old(range).end == segment.range.end,
            (Segment {
                range: old(range).start..old(range).end,
                _marker: core::marker::PhantomData,
            }).invariants(*old(owner_ref), **old(regions_ref)),
            old(range).start < old(range).end ==> !old(remaining).done,
        ensures
            segment.inv(),
            segment.range.start <= final(range).start,
            final(range).end == segment.range.end,
            (Segment {
                range: final(range).start..final(range).end,
                _marker: core::marker::PhantomData,
            }).invariants(*final(owner_ref), **final(regions_ref)),
            final(range).start < final(range).end ==> !final(remaining).done,
            match res {
                None => {
                    &&& final(range).start == old(range).start
                    &&& final(range).end == old(range).end
                    &&& old(remaining).seq() == Seq::<SegmentIteratorItem<M>>::empty()
                    &&& final(remaining).seq() == Seq::<SegmentIteratorItem<M>>::empty()
                },
                Some(item) => {
                    &&& final(range).start == old(range).start + PAGE_SIZE
                    &&& final(range).end == old(range).end
                    &&& item.0.paddr() == old(range).start
                    &&& old(remaining).seq() == seq![item] + final(remaining).seq()
                },
            },
        no_unwind
    )]
    fn next_inner(segment: &'a Segment<M>, range: &mut Range<Paddr>) -> (res: Option<
        SegmentIteratorItem<M>,
    >) {
        if range.start < range.end {
            let ghost old_remaining = remaining.seq();
            let ghost old_range = range.start..range.end;
            let ghost old_owner = **owner_ref;
            let ghost old_regions = **regions_ref;
            let paddr = range.start;

            proof {
                old_owner.relate_regions_at(old_regions, 0);
                assert(paddr == old_range.start);
            }

            proof_decl! {
                let tracked from_raw_obl: DropObligation<usize>;
            }
            let frame = unsafe {
                #[verus_spec(with Tracked(*regions_ref) => Tracked(from_raw_obl))]
                Frame::<M>::from_raw(paddr)
            };

            proof {
                let new_range = ((old_range.start + PAGE_SIZE) as usize)..old_range.end;
                let tracked redeem_tok = DropObligation::tracked_mint(frame.index());
                (*regions_ref).tracked_redeem_frame_obligation(redeem_tok);
                assert((**regions_ref).frame_obligations == old_regions.frame_obligations);
                (**owner_ref).range = new_range;

                assert forall|i: int|
                    #![trigger frame_to_index(((**owner_ref).range.start + i * PAGE_SIZE) as usize)]
                    0 <= i < crate::specs::mm::frame::segment::seg_nframes(
                        (**owner_ref).range,
                    ) implies {
                    let idx = frame_to_index(((**owner_ref).range.start + i * PAGE_SIZE) as usize);
                    &&& (**regions_ref).frame_obligations.count(idx) >= 1
                    &&& (**regions_ref).slot_owners.contains_key(idx)
                    &&& (**regions_ref).slots.contains_key(idx)
                    &&& (**regions_ref).slot_owners[idx].slot_vaddr == meta_addr(idx)
                    &&& (**regions_ref).slot_owners[idx].inner_perms.ref_count.value() > 0
                    &&& (**regions_ref).slot_owners[idx].inner_perms.ref_count.value()
                        <= crate::mm::frame::meta::REF_COUNT_MAX
                    &&& (**regions_ref).slot_owners[idx].paths_in_pt.is_empty()
                    &&& (**regions_ref).slot_owners[idx].usage is Frame
                } by {
                    old_owner.relate_regions_at(old_regions, i + 1);
                    old_owner.relate_regions_distinct(old_regions, 0, i + 1);
                }
                assert forall|i: int, j: int|
                    #![trigger frame_to_index(((**owner_ref).range.start + i * PAGE_SIZE) as usize),
                        frame_to_index(((**owner_ref).range.start + j * PAGE_SIZE) as usize)]
                    0 <= i < j < crate::specs::mm::frame::segment::seg_nframes(
                        (**owner_ref).range,
                    ) implies frame_to_index(((**owner_ref).range.start + i * PAGE_SIZE) as usize)
                    != frame_to_index(((**owner_ref).range.start + j * PAGE_SIZE) as usize) by {
                    old_owner.relate_regions_distinct(old_regions, i + 1, j + 1);
                }
                broadcast use group_page_meta;

                assert((**regions_ref).slots[frame.index()].pptr() == frame.ptr);
                assert(frame.wf_with_region(**regions_ref));
            }

            range.start = range.start + PAGE_SIZE;
            let item = (frame, Tracked(from_raw_obl));
            proof {
                remaining.resolve_cons(item);
                broadcast use vstd::seq::group_seq_axioms;

                assert(remaining.seq() == old_remaining.drop_first());
                assert(item == old_remaining[0]);
            }
            Some(item)
        } else {
            let ghost old_remaining = remaining.seq();
            proof {
                remaining.resolve_nil();
                assert(remaining.seq() == old_remaining);
            }
            None
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> IteratorSpecImpl for SegmentIterator<
    '_,
    M,
> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        self.remaining_spec()
    }

    #[verifier::prophetic]
    closed spec fn will_return_none(&self) -> bool {
        true
    }

    closed spec fn decrease(&self) -> Option<nat> {
        Some((self.range.end - self.range.start) as nat)
    }

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& init.remaining_spec() == self.remaining_spec()
        &&& init.segment_ref() == self.segment_ref()
        &&& init.range_spec() == self.range_spec()
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        None
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Iterator for SegmentIterator<'_, M> {
    type Item = SegmentIteratorItem<M>;

    /// Gets the next frame in the segment.
    fn next(&mut self) -> Option<Self::Item> {
        proof {
            use_type_invariant(&*self);
        }

        #[verus_spec(with
            Tracked(self.tracked_regions.borrow_mut()),
            Tracked(self.tracked_owner.borrow_mut()),
            Tracked(self.tracked_remaining.borrow_mut()),
        )]
        SegmentIterator::next_inner(self.segment, &mut self.range)
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> From<Frame<M>> for Segment<M> {
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
        Self { range: pa..(pa + PAGE_SIZE), _marker: core::marker::PhantomData }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Iterator for Segment<M> {
    type Item = Frame<M>;

    /// Gets the next frame in the segment.
    //
    // Verus's `core::iter::Iterator` support doesn't allow threading `Tracked`
    // metadata through the trait method's fixed signature, so the verified
    // `next` lives as an inherent method on `Segment<M>` and the trait body
    // is trusted at the trait boundary.
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

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> Segment<M> {
    /// Verified drop: iterates over each frame in the segment, decrements its
    /// reference count, and (when last ref) tears down the metadata.
    ///
    /// Per-frame linear-drop: before the teardown loop, this redeems the one
    /// `frame_obligations` entry the segment retained per frame (minted by
    /// `Segment::from_unused`). Failing to drop the segment leaves those
    /// per-frame counts outstanding and breaks
    /// [`MetaRegionOwners::clean_inv`] at the enclosing function's exit.
    #[verus_spec(
        with Tracked(owner): Tracked<SegmentOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
        requires
            self.invariants(&owner, *old(regions)),
            forall|i: int|
                #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
                0 <= i < crate::specs::mm::frame::segment::seg_nframes(self.range) ==> {
                    let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                    old(regions).slot_owners[idx].inner_perms.ref_count.value() == 1 ==> {
                        &&& old(regions).slot_owners[idx].inner_perms.storage.is_init()
                        &&& old(regions).slot_owners[idx].inner_perms.in_list.value() == 0
                    }
                },
        ensures
            final(regions).inv(),
    )]
    pub fn drop(self) {
        let tracked owner = owner;
        let ghost old_owner = owner;
        let ghost n = crate::specs::mm::frame::segment::seg_nframes(self.range);
        let mut paddr = self.range.start;

        let ghost mut k: int = 0;

        let ghost old_owner = owner;

        assert forall|i: int| #![trigger frame_idx_at(self.range.start, i)] 0 <= i < n implies {
            let idx = frame_idx_at(self.range.start, i);
            old(regions).slot_owners[idx].inner_perms.ref_count.value() == 1 ==> {
                &&& old(regions).slot_owners[idx].inner_perms.storage.is_init()
                &&& old(regions).slot_owners[idx].inner_perms.in_list.value() == 0
            }
        } by {};

        proof {
            assert(old_owner.range == self.range);
            assert forall|i: int|
                #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
                0 <= i < n implies old(regions).frame_obligations.count(
                frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
            ) >= 1 by {
                old_owner.relate_regions_at(*old(regions), i);
            };
            assert forall|i: int, j: int|
                #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
                    frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                0 <= i < j < n implies frame_to_index((self.range.start + i * PAGE_SIZE) as usize)
                != frame_to_index((self.range.start + j * PAGE_SIZE) as usize) by {
                old_owner.relate_regions_distinct(*old(regions), i, j);
            };
            crate::specs::mm::frame::segment::tracked_redeem_seg_obligations(
                regions,
                self.range.start,
                n,
            );
        }

        loop
            invariant
                regions.inv(),
                self.inv(),
                self.range.start <= paddr <= self.range.end,
                paddr == (self.range.start + k * PAGE_SIZE) as usize,
                paddr % PAGE_SIZE == 0,
                paddr <= MAX_PADDR,
                0 <= k <= n,
                n == (self.range.end - self.range.start) as int / PAGE_SIZE as int,
                paddr < self.range.end <==> k < n,
                forall|j: int|
                    #![trigger frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                    k <= j < n ==> {
                        let idx = frame_to_index((self.range.start + j * PAGE_SIZE) as usize);
                        &&& regions.slot_owners.contains_key(idx)
                        &&& regions.slots.contains_key(idx)
                        &&& regions.slot_owners[idx] == old(regions).slot_owners[idx]
                    },
                forall|j: int|
                    #![trigger frame_idx_at(self.range.start, j)]
                    k <= j < n ==> regions.slot_owners.contains_key(
                        frame_idx_at(self.range.start, j),
                    ) && regions.slot_owners[frame_idx_at(self.range.start, j)] == old(
                        regions,
                    ).slot_owners[frame_idx_at(self.range.start, j)],
                regions.slot_owners.dom() == old(regions).slot_owners.dom(),
                self.wf(&old_owner),
                old_owner.inv(),
                old(regions).inv(),
                old_owner.relate_regions(*old(regions)),
                old_owner.range == self.range,
                forall|i: int|
                    #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
                    0 <= i < n ==> {
                        let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                        old(regions).slot_owners[idx].inner_perms.ref_count.value() == 1 ==> {
                            &&& old(regions).slot_owners[idx].inner_perms.storage.is_init()
                            &&& old(regions).slot_owners[idx].inner_perms.in_list.value() == 0
                        }
                    },
            decreases n - k,
        {
            if paddr >= self.range.end {
                break;
            }
            proof {
                old_owner.relate_regions_at(*old(regions), k);
            }

            proof_decl! {
                let tracked from_raw_obl: vstd_extra::drop_tracking::DropObligation<usize>;
            }

            // SAFETY: each segment frame holds a forgotten reference;
            // `from_raw` mints the obligation and `frame.drop` consumes
            // it directly. The old "redeem-then-mint-then-drop" dance
            // is gone — `from_raw`'s freshly minted obligation feeds
            // straight into `frame.drop`.
            let frame = unsafe {
                #[verus_spec(with Tracked(regions) => Tracked(from_raw_obl))]
                Frame::<M>::from_raw(paddr)
            };

            frame.drop(Tracked(regions), Tracked(from_raw_obl));

            proof {
                assert forall|j: int|
                    #![trigger frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                    (k + 1) <= j < n implies {
                    let idx = frame_to_index((self.range.start + j * PAGE_SIZE) as usize);
                    &&& regions.slot_owners.contains_key(idx)
                    &&& regions.slots.contains_key(idx)
                    &&& regions.slot_owners[idx] == old(regions).slot_owners[idx]
                } by {
                    old_owner.relate_regions_distinct(*old(regions), k, j);
                };
            }

            paddr = paddr + PAGE_SIZE;

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
                perm.frame_obligations == old_perm.frame_obligations,
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
                            perm.slot_owners[idx].inner_perms.ref_count,
                        )
                    },
            decreases self.range.end - paddr,
        {
            if paddr >= self.range.end {
                break;
            }
            proof {
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
    }
}

} // verus!
