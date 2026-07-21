use core::marker::PhantomData;

use vstd::prelude::*;
use vstd_extra::{cast_ptr::*, ownership::*};

use crate::specs::{
    arch::*,
    mm::frame::{
        FramePermission, mapping::frame_to_index, meta_owners::PageUsage,
        meta_region_owners::MetaRegionOwners,
    },
};

use crate::mm::{
    Paddr, PagingLevel, Vaddr,
    frame::{
        meta::{
            META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
            mapping::{frame_to_meta, meta_to_frame},
        },
        *,
    },
    kspace::FRAME_METADATA_RANGE,
};

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
    pub open spec fn from_raw_requires_safety(
        regions: MetaRegionOwners,
        paddr: Paddr,
        permission: FramePermission,
    ) -> bool {
        let idx = frame_to_index(paddr);
        &&& regions.slot_owners.contains_key(frame_to_index(paddr))
        &&& regions.slot_owners[frame_to_index(paddr)].slot_vaddr == frame_to_meta(paddr)
        &&& has_safe_slot(paddr)
        &&& regions.inv()
        &&& regions.slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value()
            != REF_COUNT_UNUSED
        &&& permission.frac() == 1
        &&& permission.id() == regions.slots[idx].id()
        &&& permission.resource().pptr()
            == vstd::simple_pptr::PPtr::<MetaSlot>::from_addr(frame_to_meta(paddr))
    }

    pub open spec fn from_raw_ensures(
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        paddr: Paddr,
        permission: FramePermission,
        r: Self,
    ) -> bool {
        &&& new_regions == old_regions
        &&& r.ptr.addr() == frame_to_meta(paddr)
        &&& r.paddr() == paddr
        &&& r.inv()
        &&& r.tracked_perm@ == permission
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
        &&& self.tracked_perm@.frac() == 1
        &&& self.tracked_perm@.resource().pptr() == self.ptr
    }
}

impl<M: ?Sized> Frame<M> {
    pub open spec fn paddr(self) -> usize {
        meta_to_frame(self.ptr.addr())
    }

    pub open spec fn index(self) -> usize {
        frame_to_index(self.paddr())
    }

    pub open spec fn from_unused_spec(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
            pre.inv(),
    {
        let idx = frame_to_index(paddr);
        let pre_owner = pre.slot_owners[idx];
        let post_owner = post.slot_owners[idx];
        {
            &&& pre_owner.inner_perms.ref_count.value() == REF_COUNT_UNUSED
            &&& MetaSlot::get_from_unused_inner_perms_spec(false, post_owner.inner_perms)
            &&& post_owner.usage == PageUsage::Frame
            &&& post_owner.slot_vaddr == pre_owner.slot_vaddr
            &&& post_owner.paths_in_pt == pre_owner.paths_in_pt
            &&& post.slot_owners =~= pre.slot_owners.insert(idx, post_owner)
            &&& post.slots.dom() =~= pre.slots.dom()
            &&& post.slots[idx].id() == pre.slots[idx].id()
            &&& post.slots[idx].resource() == pre.slots[idx].resource()
            &&& post.slots[idx].frac() + 1 == pre.slots[idx].frac()
            &&& forall|i: usize| i != idx ==> #[trigger] post.slots[i] == pre.slots[i]
        }
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
        &&& s.slots[idx].resource().pptr() == self.ptr
        &&& self.tracked_perm@.id() == s.slots[idx].id()
        &&& s.slot_owners.contains_key(idx)
        &&& slot_own.inner_perms.ref_count.value() != REF_COUNT_UNUSED
        &&& slot_own.inner_perms.ref_count.value() != REF_COUNT_UNIQUE
        &&& slot_own.inner_perms.ref_count.value() > 0
        &&& slot_own.inner_perms.ref_count.value() <= REF_COUNT_MAX
    }
}

impl<M: ?Sized> Frame<M> {
    pub open spec fn drop_requires(self, s: MetaRegionOwners) -> bool {
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

    pub open spec fn drop_ensures(
        self,
        s0: MetaRegionOwners,
        s1: MetaRegionOwners,
    ) -> bool {
        let idx = frame_to_index(meta_to_frame(self.ptr.addr()));
        let so0 = s0.slot_owners[idx];
        let so1 = s1.slot_owners[idx];
        &&& s1.inv()
        &&& forall|i: usize|
            #![trigger s1.slot_owners[i]]
            i != idx ==> s1.slot_owners[i] == s0.slot_owners[i]
        &&& s1.slots.dom() =~= s0.slots.dom()
        &&& s1.slots[idx].id() == s0.slots[idx].id()
        &&& s1.slots[idx].resource() == s0.slots[idx].resource()
        &&& s1.slots[idx].frac() == s0.slots[idx].frac() + 1
        &&& forall|i: usize| i != idx ==> #[trigger] s1.slots[i] == s0.slots[i]
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
    }
}

} // verus!
