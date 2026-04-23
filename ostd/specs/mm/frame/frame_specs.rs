use vstd::prelude::*;

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::{get_slot_spec, mapping::frame_to_index, REF_COUNT_UNUSED};
use crate::mm::frame::*;
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::{MetaPerm, MetaSlotStorage};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use core::marker::PhantomData;

verus! {

/// A tracked obligation token issued when `from_raw` is called without the
/// bookkeeping precondition (`raw_count == 1`).  The holder must ensure that
/// the resulting `Frame` is wrapped in `ManuallyDrop::new` (which increments
/// `raw_count` to 1) before the `Frame` could be dropped.
///
/// The token is linear: Verus requires every tracked value to be consumed,
/// so the caller is forced to account for it.
pub tracked struct BorrowDebt {
    /// Index of the frame slot this debt applies to.
    pub ghost frame_index: usize,
    /// The `raw_count` that was observed when `from_raw` was called.
    pub ghost raw_count_at_issue: usize,
}

impl BorrowDebt {
    /// Discharge the debt when the bookkeeping precondition was already met
    /// (`raw_count` was 1 at the time of `from_raw`).  This is the zero-cost
    /// path for normal `from_raw` callers.
    pub proof fn discharge_bookkeeping(tracked self)
        requires self.raw_count_at_issue == 1,
    {}

    /// Discharge the debt after the `Frame` has been wrapped in
    /// `ManuallyDrop::new`, which increments `raw_count` to 1.
    /// This is the path used by `borrow_paddr`.
    pub proof fn discharge_with_manual_drop(tracked self, regions: &MetaRegionOwners)
        requires
            regions.slot_owners.contains_key(self.frame_index),
            regions.slot_owners[self.frame_index].raw_count == 1,
    {}

    /// Discharge the debt in the proof of
    /// `lemma_from_raw_manuallydrop_general`, where the state observed is
    /// the immediate post-`from_raw` state (`raw_count == 0`). The lemma
    /// itself proves that the subsequent `ManuallyDrop::new` restores the
    /// bookkeeping, so consuming the debt here is sound.
    pub proof fn discharge_in_lemma(tracked self, regions: &MetaRegionOwners)
        requires
            regions.slot_owners.contains_key(self.frame_index),
            regions.slot_owners[self.frame_index].raw_count == 0,
    {}
}

impl<'a, M: AnyFrameMeta> Frame<M> {
    // ── from_raw precondition predicates ──

    /// **Safety**: The frame exists and is addressable.  This is sufficient to
    /// call `from_raw` provided the caller will immediately wrap the result in
    /// `ManuallyDrop::new` (i.e., the borrow pattern).
    pub open spec fn from_raw_requires_safety(regions: MetaRegionOwners, paddr: Paddr) -> bool {
        &&& regions.slot_owners.contains_key(frame_to_index(paddr))
        &&& regions.slot_owners[frame_to_index(paddr)].self_addr == frame_to_meta(paddr)
        &&& has_safe_slot(paddr) // TODO: this should actually imply the first condition
        &&& regions.inv()
    }

    /// **Bookkeeping**: Exactly one forgotten copy exists (`raw_count == 1`).
    /// When this holds, the `Frame` returned by `from_raw` may be dropped
    /// normally (its `drop_requires` is satisfied after `ManuallyDrop::new`
    /// increments `raw_count`).  When this does *not* hold, the caller must
    /// wrap the result in `ManuallyDrop::new` to prevent the `Frame` from
    /// being dropped (`drop_requires` needs `raw_count > 0`).
    pub open spec fn from_raw_requires_bookkeeping(regions: MetaRegionOwners, paddr: Paddr) -> bool {
        regions.slot_owners[frame_to_index(paddr)].raw_count == 1
    }

    /// Full precondition (safety + bookkeeping).  Retained for backward
    /// compatibility with callers that restore a previously-forgotten frame.
    pub open spec fn from_raw_requires(regions: MetaRegionOwners, paddr: Paddr) -> bool {
        &&& Self::from_raw_requires_safety(regions, paddr)
        &&& Self::from_raw_requires_bookkeeping(regions, paddr)
    }

    pub open spec fn from_raw_ensures(
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        paddr: Paddr,
        r: Self,
    ) -> bool {
        &&& new_regions.inv()
        &&& new_regions.slots.contains_key(frame_to_index(paddr))
        &&& new_regions.slot_owners[frame_to_index(paddr)].raw_count == 0
        &&& new_regions.slot_owners[frame_to_index(paddr)].inner_perms ==
            old_regions.slot_owners[frame_to_index(paddr)].inner_perms
        &&& new_regions.slot_owners[frame_to_index(paddr)].usage ==
            old_regions.slot_owners[frame_to_index(paddr)].usage
        &&& new_regions.slot_owners[frame_to_index(paddr)].paths_in_pt ==
            old_regions.slot_owners[frame_to_index(paddr)].paths_in_pt
        &&& new_regions.slot_owners[frame_to_index(paddr)].self_addr == r.ptr.addr()
        &&& forall|i: usize|
            #![trigger new_regions.slot_owners[i], old_regions.slot_owners[i]]
            i != frame_to_index(paddr) ==> new_regions.slot_owners[i] == old_regions.slot_owners[i]
        &&& forall|i: usize|
            i != frame_to_index(paddr) ==>
            new_regions.slots.contains_key(i) == old_regions.slots.contains_key(i)
        &&& r.ptr.addr() == frame_to_meta(paddr)
        &&& r.paddr() == paddr
    }


    // ── into_raw precondition predicates ──

    /// **Safety Invariant**: The frame's structural invariant must hold.
    pub open spec fn into_raw_pre_frame_inv(self) -> bool {
        self.inv()
    }

    /// **Bookkeeping**: The frame must be in use (not unused).
    pub open spec fn into_raw_pre_not_unused(self, regions: MetaRegionOwners) -> bool {
        regions.slot_owners[self.index()].inner_perms.ref_count.value() != REF_COUNT_UNUSED
    }

    // ── into_raw postcondition predicates ──

    /// **Correctness**: The frame's raw count is incremented.
    pub open spec fn into_raw_post_raw_count_incremented(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
    ) -> bool {
        &&& new_regions.slot_owners.contains_key(self.index())
        &&& new_regions.slot_owners[self.index()].raw_count
            == (old_regions.slot_owners[self.index()].raw_count + 1) as usize
    }

    /// **Safety**: Frames other than this one are not affected by the call.
    pub open spec fn into_raw_post_noninterference(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
    ) -> bool {
        &&& forall|i: usize|
            #![trigger new_regions.slots[i], old_regions.slots[i]]
            i != self.index() && old_regions.slots.contains_key(i)
                ==> new_regions.slots.contains_key(i)
                    && new_regions.slots[i] == old_regions.slots[i]
        &&& forall|i: usize|
            #![trigger new_regions.slot_owners[i], old_regions.slot_owners[i]]
            i != self.index() ==> new_regions.slot_owners[i] == old_regions.slot_owners[i]
        &&& new_regions.slot_owners.dom() =~= old_regions.slot_owners.dom()
    }
}

} // verus!
