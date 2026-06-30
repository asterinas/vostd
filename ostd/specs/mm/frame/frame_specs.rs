use vstd::prelude::*;

use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::{
    META_SLOT_SIZE, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
    mapping::{frame_to_meta, meta_to_frame},
};
use crate::mm::frame::*;
use crate::mm::kspace::FRAME_METADATA_RANGE;
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::*;
use crate::specs::mm::frame::meta_owners::{MetaPerm, MetaSlotStorage};
use crate::specs::mm::frame::{mapping::frame_to_index, meta_region_owners::MetaRegionOwners};

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
        &&& regions.slot_owners[frame_to_index(paddr)].slot_vaddr == frame_to_meta(paddr)
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
        &&& new_regions.slot_owners[frame_to_index(paddr)].slot_vaddr == r.ptr.addr()
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

impl<M: ?Sized> Inv for Frame<M> {
    open spec fn inv(self) -> bool {
        &&& self.ptr.addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= self.ptr.addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
    }
}

impl<M: ?Sized> Frame<M> {
    pub open spec fn paddr(self) -> usize {
        meta_to_frame(self.ptr.addr())
    }

    pub open spec fn index(self) -> usize {
        frame_to_index(self.paddr())
    }
}

impl<M: ?Sized> Frame<M> {
    /// Cross-object well-formedness predicate: this `Frame` handle and
    /// the supplied [`MetaRegionOwners`] state are mutually consistent.
    /// Packages the static "Frame ⟷ state" conjuncts (slot/pointer
    /// identity, slot in-use range) so that consumer specs
    /// ([`drop_requires`], [`clone_requires`]) read uniformly.
    ///
    /// **Name**: `wf_with_region` (not just `wf`) to avoid clashing with the
    /// `OwnerOf::wf(self, Self::Owner)` impl that
    /// [`PageTableNode<C> = Frame<PageTablePageMeta<C>>`] inherits — the
    /// two predicates take different argument types and serve different
    /// purposes (per-handle vs. per-owner well-formedness).
    ///
    /// The rc range (`> 0 ∧ ≠ UNUSED ∧ ≠ UNIQUE ∧ ≤ MAX`) captures the
    /// fact that holding a `Frame<M>` is itself evidence that the slot
    /// is in the SHARED state — no UNUSED, no UNIQUE (which is reserved
    /// for [`UniqueFrame`]). Combined with
    /// [`MetaSlotOwner::inv`]'s SHARED branch (post Item 1), `wf_with_region`
    /// implies `storage.is_init`, `in_list == 0`, and `vtable_ptr.is_init`
    /// at the slot, so consumers don't have to repeat those.
    ///
    /// **Not preserved by `drop` for `self`**: dropping `self` releases
    /// the reference; for *other* handles to the same slot, `wf_with_region`
    /// is preserved by `drop`'s `>1` branch (post rc ∈ [1, MAX-1]) and
    /// vacuous in the `==1` branch (no other handles to break).
    pub open spec fn wf_with_region(self, s: MetaRegionOwners) -> bool {
        let idx = self.index();
        let slot_own = s.slot_owners[idx];
        &&& self.inv()
        &&& s.inv()
        &&& s.slots.contains_key(idx)
        &&& s.slots[idx].pptr() == self.ptr
        &&& s.slot_owners.contains_key(idx)
        &&& slot_own.inner_perms.ref_count.value() != REF_COUNT_UNUSED
        &&& slot_own.inner_perms.ref_count.value() != REF_COUNT_UNIQUE
        &&& slot_own.inner_perms.ref_count.value() > 0
        &&& slot_own.inner_perms.ref_count.value() <= REF_COUNT_MAX
    }
}

/// We need to keep track of when frames are forgotten with `ManuallyDrop`.
/// We maintain a counter for each frame of how many times it has been forgotten (`raw_count`).
/// Calling `ManuallyDrop::new` increments the counter. It is technically safe to forget a frame multiple times,
/// and this will happen with read-only `FrameRef`s. All such references need to be dropped by the time
/// `from_raw` is called. So, `ManuallyDrop::drop` decrements the counter when the reference is dropped,
/// and `from_raw` may only be called when the counter is 1.
impl<M: ?Sized> TrackDrop for Frame<M> {
    type State = MetaRegionOwners;

    /// Slot index. Lets the obligation token identify *which* slot it
    /// belongs to — `Drop::drop`'s precondition then refuses a token
    /// from one slot being used to drop a Frame at another slot.
    /// (Full per-instance ledger enforcement is a follow-up; for now
    /// `consume_obligation` is a no-op so the token's identity is
    /// documentary rather than gated against a multiset.)
    type Key = usize;

    open spec fn key(self) -> Self::Key {
        self.index()
    }

    open spec fn constructor_requires(self, s: Self::State) -> bool {
        &&& s.slot_owners.contains_key(self.index())
        &&& s.inv()
    }

    open spec fn constructor_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl_key: Self::Key,
    ) -> bool {
        let slot_own = s0.slot_owners[self.index()];
        &&& s1.slot_owners[self.index()] == slot_own
        &&& forall|i: usize|
            #![trigger s1.slot_owners[i]]
            i != self.index() ==> s1.slot_owners[i] == s0.slot_owners[i]
        &&& s1.slots =~= s0.slots
        &&& s1.slot_owners.dom()
            =~= s0.slot_owners.dom()
        // Linear-drop pilot: minting a `Frame` (bumping `raw_count`) does
        // not affect the segment obligation ledger.
        // Frame-side ledger: `constructor_spec` adds one entry at the
        // slot index via the paired mint axiom (multiset semantics).
        &&& s1.frame_obligations =~= s0.frame_obligations.insert(obl_key)
    }

    proof fn constructor_spec(self, tracked s: &mut Self::State) -> (tracked obl: DropObligation<
        Self::Key,
    >) {
        let meta_addr = self.ptr.addr();
        let index = frame_to_index(meta_to_frame(meta_addr));
        let tracked mut slot_own = s.slot_owners.tracked_remove(index);
        s.slot_owners.tracked_insert(index, slot_own);
        // Paired mint axiom: produces the token AND adds its Loc to
        // `frame_obligations`. Replaces the prior ledger-less
        // `DropObligation::tracked_mint(index)`.
        s.tracked_mint_frame_obligation(index)
    }

    // It is unsound to drop a `Frame` while raw paddrs to it remain
    // outstanding (`raw_count > 0`), since those raw paddrs could be revived
    // via `from_raw` after the slot has been torn down. Hence the drop is
    // only permitted when `raw_count == 0`.
    open spec fn drop_requires(self, s: Self::State) -> bool {
        let idx = frame_to_index(meta_to_frame(self.ptr.addr()));
        let slot_own = s.slot_owners[idx];
        // Cross-object validity: this Frame is consistent with `s` and
        // the slot is in the SHARED rc range. `wf_with_region` carries the
        // slot identity + pointer agreement + `rc ∈ (0, MAX] ∧ ≠ UNIQUE`
        // bounds.
        &&& self.wf_with_region(
            s,
        )
        // Borrow-protocol transition: `raw_count` is dormant. The
        // "outstanding raw paddrs must be drained before drop" guarantee
        // is now carried by the `frame_obligations` ledger together with
        // `from_raw`'s `ref_count >= 1` safety check (a torn-down slot is
        // `UNUSED` and cannot be `from_raw`'d).
        // At `ref_count == 1` the teardown branch of `drop_last_in_place`
        // runs, requiring an empty `paths_in_pt` (the strengthened
        // `MetaSlotOwner::inv` UNUSED branch demands it post-teardown,
        // and `drop_last_in_place` doesn't touch paths). Sound: at
        // `ref_count == 1` the `Frame` being dropped is the sole
        // reference, so there is no live PTE mapping (a mapping would
        // be a further reference, forcing `ref_count >= 2`).
        //
        // The other `drop_last_in_place_safety_cond` conjuncts
        // (`storage.is_init`, `in_list == 0`) are subsumed by the
        // strengthened `MetaSlotOwner::inv` SHARED branch
        // (`0 < rc <= REF_COUNT_MAX`) — they hold universally for any
        // in-use slot, not just at `rc == 1`.
        &&& slot_own.inner_perms.ref_count.value() == 1 ==> {
            &&& slot_own.paths_in_pt.is_empty()
        }
    }

    open spec fn drop_ensures(self, s0: Self::State, s1: Self::State, obl_key: Self::Key) -> bool {
        let idx = frame_to_index(meta_to_frame(self.ptr.addr()));
        let so0 = s0.slot_owners[idx];
        let so1 = s1.slot_owners[idx];
        &&& s1.inv()
        &&& forall|i: usize|
            #![trigger s1.slot_owners[i]]
            i != idx ==> s1.slot_owners[i] == s0.slot_owners[i]
        &&& s1.slots =~= s0.slots
        &&& s1.slot_owners.dom()
            =~= s0.slot_owners.dom()
        // The slot's identity / page-table linkage is preserved by a
        // drop (it only adjusts refcount and, on teardown, storage).
        &&& so1.slot_vaddr == so0.slot_vaddr
        &&& so1.usage == so0.usage
        &&& so1.paths_in_pt
            == so0.paths_in_pt
        // Refcount transition. `drop_requires` guarantees the old value
        // is in `[1, REF_COUNT_MAX]`, so these cases are exhaustive:
        //  - last reference (== 1): the slot is torn down to UNUSED.
        //  - otherwise (> 1): the refcount is decremented by one.
        &&& so0.inner_perms.ref_count.value() == 1 ==> so1.inner_perms.ref_count.value()
            == REF_COUNT_UNUSED
        &&& so0.inner_perms.ref_count.value() > 1 ==> so1.inner_perms.ref_count.value() == (
        so0.inner_perms.ref_count.value()
            - 1) as u64
        // Linear-drop pilot: `Frame::drop` doesn't redeem segment-level
        // obligations, so the segment ledger is preserved.
        // Frame-side ledger: routed through `consume_obligation` (called
        // by Drop::drop's body first), the count at `obl_key` shrinks
        // by 1.
        &&& s1.frame_obligations =~= s0.frame_obligations.remove(obl_key)
    }

    /// `ManuallyDrop::new` / `Drop::drop` require the ledger to contain
    /// at least one entry at this slot — preventing a forged token
    /// from being used to "consume" a non-existent obligation.
    open spec fn consume_requires(self, s: Self::State, obl_key: Self::Key) -> bool {
        s.frame_obligations.count(obl_key) > 0
    }

    open spec fn consume_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl_key: Self::Key,
    ) -> bool {
        // Multiset count at the slot shrinks by 1; everything else
        // (slots, slot_owners, segment ledger) is preserved.
        &&& s1.frame_obligations =~= s0.frame_obligations.remove(obl_key)
        &&& s1.slots =~= s0.slots
        &&& s1.slot_owners =~= s0.slot_owners
    }

    proof fn consume_obligation(
        self,
        tracked s: &mut Self::State,
        tracked obl: DropObligation<Self::Key>,
    ) {
        // Paired redeem axiom: removes one entry at `obl.value()` from
        // `frame_obligations`. Leaves `slot_owners` (including
        // `raw_count`) untouched — the deliberate-leak semantic.
        s.tracked_redeem_frame_obligation(obl);
    }
}

} // verus!
