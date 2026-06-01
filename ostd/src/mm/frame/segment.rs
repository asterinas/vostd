// SPDX-License-Identifier: MPL-2.0
//! A contiguous range of frames.
use vstd::prelude::*;
use vstd::simple_pptr;
use vstd_extra::assert;
use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;
use vstd_extra::panic::may_panic;
use vstd_extra::prelude::*;

use crate::mm::page_table::RCClone;
use crate::mm::{paddr_to_vaddr, Paddr, PagingLevel, Vaddr};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::frame::segment::*;
use crate::specs::mm::virt_mem::MemView;

use core::{fmt::Debug, /*mem::ManuallyDrop,*/ ops::Range};

use super::meta::mapping::{frame_to_index, frame_to_index_spec, frame_to_meta, meta_addr};
use super::{AnyFrameMeta, GetFrameError, MetaSlot};
use crate::mm::frame::{has_safe_slot, untyped::AnyUFrameMeta, Frame};

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
    }

    fn clone(&self, Tracked(perm): Tracked<&mut MetaRegionOwners>) -> (res: Self) {
        let mut paddr = self.range.start;

        let ghost old_perm = *perm;
        loop
            invariant
                perm.inv(),
                self.inv(),
                perm.slots =~= old_perm.slots,
                perm.slot_owners.dom() =~= old_perm.slot_owners.dom(),
                // Linear-drop pilot: cloning a Segment doesn't mint or
                // redeem its obligation — the per-frame ref-count bump is
                // an Arc-style operation.
                perm.obligations =~= old_perm.obligations,
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
                assert(paddr + PAGE_SIZE <= self.range.end);
                assert(paddr + PAGE_SIZE <= MAX_PADDR);
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
                -> owner_and_obl: Tracked<Option<(SegmentOwner<M>, DropObligation<Range<Paddr>>)>>,
        requires
            old(regions).inv(),
            // Linear-drop pilot: the freshly-constructed segment's range
            // must not collide with an outstanding obligation, otherwise
            // we'd have two live `SegmentOwner`s claiming the same range.
            !old(regions).obligations.contains(range),
            forall|paddr_in: Paddr|
                (range.start <= paddr_in < range.end && paddr_in % PAGE_SIZE == 0) ==> {
                    &&& metadata_fn.requires((paddr_in,))
                },
            forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
                metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> {
                    &&& paddr_out < MAX_PADDR
                    &&& paddr_out % PAGE_SIZE == 0
                    &&& paddr_in == paddr_out
                    &&& old(regions).slots.contains_key(frame_to_index(paddr_out))
                    &&& old(regions).slot_owners[frame_to_index(paddr_out)].usage is Unused
                    &&& old(regions).slot_owners[frame_to_index(paddr_out)].inner_perms.in_list.points_to(0)
                },
            !(range.end <= MAX_PADDR ==> range.start < range.end) ==> may_panic(),
        ensures
            final(regions).inv(),
            // Linear-drop pilot: on any error path, the ledger is unchanged
            // (no obligation was minted). On Ok, the ledger gains `range`.
            r is Err ==> final(regions).obligations =~= old(regions).obligations,
            (range.start % PAGE_SIZE != 0 || range.end % PAGE_SIZE != 0)
                ==> r == Err::<Self, _>(GetFrameError::NotAligned),
            (range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0 && range.end > MAX_PADDR)
                ==> r == Err::<Self, _>(GetFrameError::OutOfBound),
            r is Ok ==> range.end <= MAX_PADDR ==> range.start < range.end,
            r matches Ok(r) ==> {
                &&& final(regions).inv()
                &&& r.start_paddr() == range.start
                &&& r.end_paddr() == range.end
                &&& r.start_paddr() < r.end_paddr()
                &&& final(regions).obligations =~= old(regions).obligations.insert(range)
                &&& owner_and_obl@ matches Some((owner, obl)) && {
                    &&& r.inv()
                    &&& r.wf(&owner)
                    &&& obl.value() == range
                    // Design B: the slot perms stay canonical in
                    // `regions.slots` (borrowable), so they are *present*.
                    &&& forall|paddr: Paddr|
                        #![trigger frame_to_index_spec(paddr)]
                        (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                            ==> final(regions).slots.contains_key(frame_to_index_spec(paddr))
                }
            },
    )]
    pub fn from_unused(range: Range<Paddr>, metadata_fn: impl Fn(Paddr) -> (Paddr, M)) -> (res:
        Result<Self, GetFrameError>) {
        proof_decl! {
            let tracked mut owner_and_obl:
                Option<(SegmentOwner<M>, DropObligation<Range<Paddr>>)> = None;
            let tracked mut addrs = Seq::<usize>::tracked_empty();
        }

        if range.start % PAGE_SIZE != 0 || range.end % PAGE_SIZE != 0 {
            return {
                proof_with!(|= Tracked(owner_and_obl));
                Err(GetFrameError::NotAligned)
            };
        }
        if range.end > MAX_PADDR {
            return {
                proof_with!(|= Tracked(owner_and_obl));
                Err(GetFrameError::OutOfBound)
            };
        }
        assert!(range.start < range.end);
        // Construct a segment early to recycle previously forgotten frames if
        // the subsequent operations fails in the middle.
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
                        && metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> {
                        &&& paddr_out < MAX_PADDR
                        &&& paddr_out % PAGE_SIZE == 0
                        &&& paddr_in == paddr_out
                        &&& regions.slots.contains_key(frame_to_index(paddr_out))
                        &&& regions.slot_owners[frame_to_index(paddr_out)].usage is Unused
                        &&& regions.slot_owners[frame_to_index(
                            paddr_out,
                        )].inner_perms.in_list.points_to(0)
                    },
                // Design B: each processed frame's slot perm is re-parked in
                // `regions.slots` (canonical, borrowable), the frame is
                // forgotten (`raw_count == 1`) and live (`ref_count >= 1`).
                forall|j: int|
                    #![trigger addrs[j]]
                    0 <= j < addrs.len() as int ==> {
                        let idx = frame_to_index_spec(addrs[j]);
                        &&& regions.slots.contains_key(idx)
                        &&& regions.slot_owners.contains_key(idx)
                        &&& regions.slot_owners[idx].raw_count == 1
                        &&& regions.slot_owners[idx].self_addr == meta_addr(idx)
                        &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                        &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                            <= crate::mm::frame::meta::REF_COUNT_MAX
                        &&& addrs[j] % PAGE_SIZE == 0
                        &&& addrs[j] < MAX_PADDR
                        &&& addrs[j] == range.start + (j as u64) * PAGE_SIZE
                    },
                regions.inv(),
                // Linear-drop pilot: the per-frame setup neither mints
                // nor redeems the segment-level obligation; the mint
                // happens once after the loop.
                regions.obligations =~= old(regions).obligations,
                segment.range.start == range.start,
                segment.range.end == range.start + i * PAGE_SIZE,
            ensures
                i == addr_len,
            decreases addr_len - i,
        {
            let paddr_in = range.start + i * PAGE_SIZE;
            let (paddr, meta) = metadata_fn(paddr_in);

            let res = #[verus_spec(with Tracked(regions))]
            Frame::<M>::from_unused(paddr, meta);
            let frame = match res {
                Ok(f) => f,
                Err(e) => {
                    return {
                        proof_with!(|= Tracked(owner_and_obl));
                        Err(e)
                    };
                },
            };

            let _ = ManuallyDrop::new(frame, Tracked(regions));
            segment.range.end = paddr + PAGE_SIZE;
            proof {
                addrs.tracked_push(paddr);
            }

            i += 1;
        }

        proof {
            // Linear-drop pilot: mint the obligation token now that the
            // segment is fully constructed. The token + ledger insert are
            // produced atomically by the axiom.
            let tracked obl = regions.tracked_mint_obligation(range);
            let tracked seg_owner =
                SegmentOwner { range, _marker: core::marker::PhantomData };
            owner_and_obl = Some((seg_owner, obl));

            // Every frame in `range` had its perm re-parked into
            // `regions.slots` (Design B), so the slot key is present. Each
            // `addr` in range is `addrs[j]` for `j = (addr-range.start)/PS`,
            // and the loop invariant pins `slots.contains_key` for that `j`.
            assert forall|addr: usize|
                #![trigger frame_to_index_spec(addr)]
                range.start <= addr < range.end && addr % PAGE_SIZE == 0 implies {
                regions.slots.contains_key(frame_to_index_spec(addr))
            } by {
                let j = (addr - range.start) / PAGE_SIZE as int;
                assert(0 <= j < addrs.len() as int);
                assert(addrs[j as int] == addr);
            }
        }

        proof_with!(|= Tracked(owner_and_obl));
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
            *final(regions) =~= *old(regions),
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
                -> frame_perms: (Tracked<SegmentOwner<M>>, Tracked<SegmentOwner<M>>),
        requires
            self.inv(),
            self.wf(&owner),
            offset % PAGE_SIZE == 0,
            0 < offset < self.size(),
            old(regions).inv(),
            owner.relate_regions(*old(regions)),
        ensures
            *final(regions) =~= *old(regions),
            r.0.inv(),
            r.0.wf(&frame_perms.0@),
            r.1.inv(),
            r.1.wf(&frame_perms.1@),
            (r.0, r.1) == self.split_spec(offset),
            frame_perms.0@.relate_regions(*final(regions)),
            frame_perms.1@.relate_regions(*final(regions)),
    )]
    pub fn split(self, offset: usize) -> (Self, Self) {
        assert!(offset % PAGE_SIZE == 0);
        assert!(0 < offset && offset < self.size());

        // Snapshot before the `ManuallyDrop` local named `old` shadows the
        // verus `old(regions)` builtin. `split` leaves `regions` unchanged
        // (`Segment::constructor_ensures` is `s0 =~= s1`), so this equals
        // both `*old(regions)` and `*final(regions)`.
        let ghost old_regions = *regions;

        let old = ManuallyDrop::new(self, Tracked(regions));
        let at = old.range.start + offset;

        let ghost old_start = old@.start_paddr();
        let ghost old_end = old@.end_paddr();

        // Design B: no owned perms to split — the two halves are just
        // sub-ranges; their `relate_regions` follows from the original
        // owner's over the (unchanged) `regions`.
        let tracked frame_own1 = SegmentOwner {
            range: old_start..at,
            _marker: core::marker::PhantomData,
        };
        let tracked frame_own2 = SegmentOwner {
            range: at..old_end,
            _marker: core::marker::PhantomData,
        };
        proof {
            assert forall|i: int|
                #![trigger frame_to_index((frame_own1.range.start + i * PAGE_SIZE) as usize)]
                0 <= i < crate::specs::mm::frame::segment::seg_nframes(frame_own1.range) implies {
                let idx = frame_to_index((frame_own1.range.start + i * PAGE_SIZE) as usize);
                &&& regions.slot_owners.contains_key(idx)
                &&& regions.slots.contains_key(idx)
                &&& regions.slot_owners[idx].raw_count == 1
                &&& regions.slot_owners[idx].self_addr == meta_addr(idx)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    <= crate::mm::frame::meta::REF_COUNT_MAX
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                &&& regions.slot_owners[idx].usage
                    == crate::specs::mm::frame::meta_owners::PageUsage::Frame
            } by {
                owner.relate_regions_at(old_regions, i);
            }
            assert forall|i: int|
                #![trigger frame_to_index((frame_own2.range.start + i * PAGE_SIZE) as usize)]
                0 <= i < crate::specs::mm::frame::segment::seg_nframes(frame_own2.range) implies {
                let idx = frame_to_index((frame_own2.range.start + i * PAGE_SIZE) as usize);
                &&& regions.slot_owners.contains_key(idx)
                &&& regions.slots.contains_key(idx)
                &&& regions.slot_owners[idx].raw_count == 1
                &&& regions.slot_owners[idx].self_addr == meta_addr(idx)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    <= crate::mm::frame::meta::REF_COUNT_MAX
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                &&& regions.slot_owners[idx].usage
                    == crate::specs::mm::frame::meta_owners::PageUsage::Frame
            } by {
                owner.relate_regions_at(old_regions, i + (offset / PAGE_SIZE) as int);
            }
            // Distinctness forall of `relate_regions` for each half, derived
            // from the original owner's distinctness over the (unchanged)
            // regions. `frame_own1` shares `owner.range.start`; `frame_own2`
            // is shifted by `offset / PAGE_SIZE` frames.
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
            self.inv(),
            self.wf(&owner),
            owner.inv(),
            old(regions).inv(),
            owner.relate_regions(*old(regions)),
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
            final(regions).slots =~= old(regions).slots,
            final(regions).slot_owners.dom() =~= old(regions).slot_owners.dom(),
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
                regions.slots =~= old_regions.slots,
                regions.slot_owners.dom() =~= old_regions.slot_owners.dom(),
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
                // For frames not yet processed, the entry is unchanged from
                // `old_regions`. This lets the next iteration recover the
                // ref-count/wf facts via `relate_regions`.
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
                )] by {
                    let _ = frame_to_index((self.range.start + perm_idx * PAGE_SIZE) as usize);
                    let _ = frame_to_index((self.range.start + j * PAGE_SIZE) as usize);
                };
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
            self.inv(),
            self.wf(&owner),
            old(regions).inv(),
            owner.inv(),
            owner.relate_regions(*old(regions)),
        ensures
            r == self.range(),
            final(regions).inv(),
            *final(regions) =~= *old(regions),
            frame_perms@ == owner,
    )]
    pub(crate) fn into_raw(self) -> Range<Paddr> {
        let range = self.range.clone();
        let _ = ManuallyDrop::new(self, Tracked(regions));

        proof_with!(|= Tracked(owner));
        range
    }

    /// Gets the next frame in the segment.
    ///
    /// This is the verified counterpart of [`Iterator::next`] for `Segment<M>`.
    /// The trait method is `external_body` because Verus's `core::iter::Iterator`
    /// support can't thread `Tracked` metadata through the trait method's
    /// fixed signature.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - segment, owner, and meta regions must satisfy their respective invariants;
    /// - the segment is well-formed with the owner;
    /// - the owner relates correctly to `regions` (forgotten reference, slot
    ///   present and consistent, etc. — see [`SegmentOwner::relate_regions`]).
    ///
    /// All the per-frame coherence conditions previously listed inline are now
    /// consequences of `owner.relate_regions(regions)` instantiated at `i = 0`.
    ///
    /// ## Postconditions
    /// - if the result is [`None`], then the segment has been exhausted;
    /// - if the result is [`Some`], then the segment is advanced by one frame and
    ///   the returned frame is the next frame, with its slot restored to `regions`;
    /// - the new owner continues to relate correctly to the new regions.
    #[verus_spec(res =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut SegmentOwner<M>>
        requires
            old(self).inv(),
            old(self).wf(old(owner)),
            old(owner).inv(),
            old(regions).inv(),
            old(owner).relate_regions(*old(regions)),
        ensures
            final(regions).inv(),
            final(self).inv(),
            final(owner).relate_regions(*final(regions)),
            match res {
                None => final(self).start_paddr() == old(self).end_paddr(),
                Some(f) => {
                    &&& final(self).start_paddr() == old(self).start_paddr() + PAGE_SIZE
                    &&& f.paddr() == old(self).start_paddr()
                    &&& final(regions).slots.contains_key(frame_to_index(f.paddr()))
                    &&& final(regions).slot_owners[frame_to_index(f.paddr())].raw_count == 0
                },
            },
    )]
    pub fn next(&mut self) -> Option<Frame<M>> {
        if self.range.start < self.range.end {
            proof {
                // Frame 0's per-slot facts (slot present in `regions.slots`,
                // forgotten with `raw_count == 1`, live refcount).
                owner.relate_regions_at(*old(regions), 0);
            }
            proof_decl! {
                let tracked from_raw_debt: crate::specs::mm::frame::frame_specs::BorrowDebt;
            }

            let frame = unsafe {
                #[verus_spec(with Tracked(regions) => Tracked(from_raw_debt))]
                Frame::<M>::from_raw(self.range.start)
            };

            proof {
                from_raw_debt.discharge_bookkeeping();
                owner.range = ((self.range.start + PAGE_SIZE) as usize)..self.range.end;

                // Re-establish `owner.relate_regions(*regions)` for the
                // shrunk range. New frame `i` == old frame `i + 1`
                // (`owner.range.start == old(owner).range.start + PAGE_SIZE`);
                // `from_raw` only touched frame 0's slot, and distinctness
                // (`relate_regions_distinct(0, i+1)`) shows every remaining
                // frame's slot/owner is unchanged from `*old(regions)`.
                assert forall|i: int|
                    #![trigger frame_to_index((owner.range.start + i * PAGE_SIZE) as usize)]
                    0 <= i < crate::specs::mm::frame::segment::seg_nframes(owner.range) implies {
                    let idx = frame_to_index((owner.range.start + i * PAGE_SIZE) as usize);
                    &&& regions.slot_owners.contains_key(idx)
                    &&& regions.slots.contains_key(idx)
                    &&& regions.slot_owners[idx].raw_count == 1
                    &&& regions.slot_owners[idx].self_addr == meta_addr(idx)
                    &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                    &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                        <= crate::mm::frame::meta::REF_COUNT_MAX
                    &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                    &&& regions.slot_owners[idx].usage
                        == crate::specs::mm::frame::meta_owners::PageUsage::Frame
                } by {
                    old(owner).relate_regions_at(*old(regions), i + 1);
                    old(owner).relate_regions_distinct(*old(regions), 0, i + 1);
                }
                assert forall|i: int, j: int|
                    #![trigger frame_to_index((owner.range.start + i * PAGE_SIZE) as usize),
                        frame_to_index((owner.range.start + j * PAGE_SIZE) as usize)]
                    0 <= i < j < crate::specs::mm::frame::segment::seg_nframes(
                        owner.range,
                    ) implies frame_to_index((owner.range.start + i * PAGE_SIZE) as usize)
                    != frame_to_index((owner.range.start + j * PAGE_SIZE) as usize) by {
                    old(owner).relate_regions_distinct(*old(regions), i + 1, j + 1);
                }
            }

            self.range.start = self.range.start + PAGE_SIZE;
            Some(frame)
        } else {
            None
        }
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
    /// Linear-drop pilot: the drop additionally consumes a
    /// [`DropObligation<Range<Paddr>>`] token bound to `self.range`. The
    /// matching ledger entry was added by `Segment::from_unused` and is
    /// redeemed at the end of this body. Skipping this call leaves
    /// `regions.obligations` non-empty and breaks
    /// [`MetaRegionOwners::clean_inv`] at the enclosing function's exit.
    #[verus_spec(
        with Tracked(owner): Tracked<SegmentOwner<M>>,
            Tracked(obligation): Tracked<DropObligation<Range<Paddr>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
        requires
            self.inv(),
            self.wf(&owner),
            owner.inv(),
            old(regions).inv(),
            owner.relate_regions(*old(regions)),
            // Linear-drop pilot preconditions.
            obligation.value() == self.range,
            old(regions).obligations.contains(self.range),
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
            final(regions).obligations =~= old(regions).obligations.remove(self.range),
    )]
    pub fn drop(self) {
        let tracked owner = owner;
        let ghost old_owner = owner;
        let ghost n = crate::specs::mm::frame::segment::seg_nframes(self.range);
        let mut paddr = self.range.start;

        let ghost mut k: int = 0;

        let ghost old_owner = owner;

        // Re-trigger the precondition's `forall|i| owner.perms[i] => ...`
        // under `frame_idx_at(self.range.start, i)`, which is the trigger the
        // loop invariant uses.
        assert forall|i: int| #![trigger frame_idx_at(self.range.start, i)] 0 <= i < n implies {
            let idx = frame_idx_at(self.range.start, i);
            old(regions).slot_owners[idx].inner_perms.ref_count.value() == 1 ==> {
                &&& old(regions).slot_owners[idx].inner_perms.storage.is_init()
                &&& old(regions).slot_owners[idx].inner_perms.in_list.value() == 0
            }
        } by {};

        loop
            invariant
                regions.inv(),
                // Linear-drop pilot: the per-frame loop body neither mints
                // nor redeems segment obligations (the `slots`/`slot_owners`
                // axioms preserve `obligations` verbatim, as do
                // `Frame::from_raw` and `Frame::drop`).
                regions.obligations =~= old(regions).obligations,
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
                // Unprocessed frames' slot_owners are present and unchanged
                forall|j: int|
                    #![trigger frame_idx_at(self.range.start, j)]
                    k <= j < n ==> regions.slot_owners.contains_key(
                        frame_idx_at(self.range.start, j),
                    ) && regions.slot_owners[frame_idx_at(self.range.start, j)] == old(
                        regions,
                    ).slot_owners[frame_idx_at(self.range.start, j)],
                regions.slot_owners.dom() =~= old(regions).slot_owners.dom(),
                // Function-entry snapshots, restated for each iteration's
                // `from_raw`/`drop` preconditions.
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
                // Frame `k`'s per-slot facts: forgotten (`raw_count == 1`),
                // slot perm canonical in `regions.slots`, live refcount.
                old_owner.relate_regions_at(*old(regions), k);
            }

            proof_decl! {
                let tracked from_raw_debt: crate::specs::mm::frame::frame_specs::BorrowDebt;
            }

            // SAFETY: each segment frame holds a forgotten reference
            // (`relate_regions` ⇒ `raw_count == 1`), which `from_raw`
            // reclaims; the subsequent `frame.drop` decrements `ref_count`
            // and (when last ref) tears down the metadata.
            let frame = unsafe {
                #[verus_spec(with Tracked(regions) => Tracked(from_raw_debt))]
                Frame::<M>::from_raw(paddr)
            };

            proof {
                from_raw_debt.discharge_bookkeeping();
            }

            frame.drop(Tracked(regions));

            proof {
                // Only slot `k` was touched (`from_raw` removed+reinserted
                // its slot key, `drop` adjusted its owner). Every remaining
                // `j > k` has a distinct index (`relate_regions` distinctness)
                // so its slot/owner are untouched.
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

        // Linear-drop pilot: redeem the obligation, removing `self.range`
        // from `regions.obligations`. Skipping this would leave the ledger
        // non-empty and any caller requiring `clean_inv()` would fail.
        proof {
            regions.tracked_redeem_obligation(obligation);
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
                perm.slots =~= old_perm.slots,
                perm.slot_owners.dom() =~= old_perm.slot_owners.dom(),
                // Linear-drop pilot: cloning a Segment doesn't mint or
                // redeem its obligation — the per-frame ref-count bump is
                // an Arc-style operation.
                perm.obligations =~= old_perm.obligations,
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
                assert(paddr + PAGE_SIZE <= self.range.end);
                assert(paddr + PAGE_SIZE <= MAX_PADDR);
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
