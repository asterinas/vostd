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

// Unbounded so `from_raw` (which lives in an unbounded `impl Frame<M>` block
// to break the AnyFrameMeta trait-resolution cycle in PT-node on_drop) can
// reference these helpers via `Self::from_raw_*`.
impl<'a, M: ?Sized> Frame<M> {
    // ── from_raw precondition predicates ──
    /// **Safety**: The frame exists, is addressable, and its slot is alive
    /// (not torn down: `ref_count != REF_COUNT_UNUSED`). Under the
    /// borrow-protocol redesign this liveness gate replaces the prior
    /// `raw_count <= 1` check — a slot that has not been torn down is safe
    /// to re-materialize as a `Frame` value. (`>= 1` is *not* the right
    /// gate, since the `UNUSED` sentinel `u64::MAX` also satisfies it; and
    /// the PT-node ownership model only exposes `!= UNUSED`.)
    pub open spec fn from_raw_requires_safety(regions: MetaRegionOwners, paddr: Paddr) -> bool {
        &&& regions.slot_owners.contains_key(frame_to_index(paddr))
        &&& regions.slot_owners[frame_to_index(paddr)].self_addr == frame_to_meta(paddr)
        &&& has_safe_slot(paddr)
        &&& regions.inv()
        &&& regions.slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value()
            != REF_COUNT_UNUSED
    }

    pub open spec fn from_raw_ensures(
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        paddr: Paddr,
        r: Self,
    ) -> bool {
        &&& new_regions.inv()
        &&& new_regions.slots.contains_key(frame_to_index(paddr))
        &&& new_regions.slot_owners[frame_to_index(paddr)]
            =~= old_regions.slot_owners[frame_to_index(paddr)]
        &&& new_regions.slot_owners[frame_to_index(paddr)].self_addr == r.ptr.addr()
        &&& forall|i: usize|
            #![trigger new_regions.slot_owners[i], old_regions.slot_owners[i]]
            i != frame_to_index(paddr) ==> new_regions.slot_owners[i] == old_regions.slot_owners[i]
        &&& forall|i: usize|
            i != frame_to_index(paddr) ==> new_regions.slots.contains_key(i)
                == old_regions.slots.contains_key(i)
        &&& r.ptr.addr() == frame_to_meta(paddr)
        &&& r.paddr() == paddr
        &&& r.inv()
        // Borrow-protocol: `from_raw` mints exactly one entry in
        // `frame_obligations` at the recovered slot's index. The returned
        // `DropObligation` token is the receipt; the entry will be
        // consumed by either `ManuallyDrop::new` (FrameRef-style borrow)
        // or `Frame::drop` (reclaim-and-drop). Segment-level ledger is
        // untouched.
        &&& new_regions.obligations =~= old_regions.obligations
        &&& new_regions.frame_obligations =~= old_regions.frame_obligations.insert(
            frame_to_index(paddr),
        )
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

    /// **Safety**: Frames other than this one are not affected by the call.
    pub open spec fn into_raw_post_noninterference(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
    ) -> bool {
        &&& forall|i: usize|
            #![trigger new_regions.slots[i], old_regions.slots[i]]
            i != self.index() && old_regions.slots.contains_key(i)
                ==> new_regions.slots.contains_key(i) && new_regions.slots[i]
                == old_regions.slots[i]
        &&& forall|i: usize|
            #![trigger new_regions.slot_owners[i], old_regions.slot_owners[i]]
            i != self.index() ==> new_regions.slot_owners[i] == old_regions.slot_owners[i]
        &&& new_regions.slot_owners.dom() =~= old_regions.slot_owners.dom()
    }
}

} // verus!
