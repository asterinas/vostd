use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::{self, *};

use core::ops::Range;

use vstd_extra::cast_ptr::{self, Repr};
use vstd_extra::drop_tracking::DropObligation;
use vstd_extra::ghost_tree::TreePath;
use vstd_extra::ownership::*;

use super::meta_owners::{MetaPerm, MetaSlotModel, MetaSlotOwner, MetaSlotStorage};
use super::*;
use crate::mm::Paddr;
use crate::mm::frame::Link;
use crate::mm::frame::meta::{
    AnyFrameMeta, META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, mapping::frame_to_meta,
};
use crate::mm::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::{MAX_PADDR, NR_ENTRIES, PAGE_SIZE};
use crate::specs::mm::frame::linked_list::linked_list_owners::MetaSlotSmall;
use crate::specs::mm::frame::{
    mapping::{frame_to_index, max_meta_slots, meta_addr},
    meta_owners::Metadata,
};

verus! {

/// Represents the ownership of the meta-frame memory region.
/// # Verification Design
/// ## Slot owners
/// Every metadata slot has its owner ([`MetaSlotOwner`]) tracked by the `slot_owners` map at all times.
/// This makes the `MetaRegionOwners` the one place that tracks every frame, whether or not it is
/// in use.
/// ## Slot permissions
/// We treat the slot permissions differently depending on how they are used. The permissions of unused slots
/// are tracked in `slots`, as are those of frames that do not otherwise belong to any other data structure.
/// This is necessary because those frames can have a new reference taken at any time via `Frame::from_in_use`.
/// Unique frames and frames that are forgotten with `into_raw` have their permissions tracked by the owner of
/// whatever object they belong to. Their permissions will be returned to `slots` when the object is dropped.
/// Whether or not the frame has a permission in `slots`, it will always have an owner in `slot_owners`,
/// which tracks information that needs to be globally visible.
/// ## Safety
/// Forgetting a slot with `into_raw` or `ManuallyDrop::new` will leak the frame.
/// Forgetting it multiple times without restoring it will likely result in a memory leak, but not double-free.
/// Double-free happens when `from_raw` is called on a frame that is not forgotten, or that has been
/// dropped with `ManuallyDrop::drop` instead of `into_raw`. All functions in
/// the verified code that call `from_raw` have a precondition that the frame's index is not a key in `slots`.
#[verifier::ext_equal]
pub tracked struct MetaRegionOwners {
    pub slots: Map<usize, simple_pptr::PointsTo<MetaSlot>>,
    pub slot_owners: Map<usize, MetaSlotOwner>,
    /// Outstanding per-instance obligations for both `Frame<M>` and
    /// `Segment<M>`, as a multiset of slot indices. `ManuallyDrop::new(frame,
    /// ..)` adds one entry at `frame.key()` (mint paired with the `raw_count++`
    /// bump); `Frame::drop` (via `consume_obligation`) and `ManuallyDrop::new`
    /// redeem one. A `Segment<M>` records one entry per frame it holds (see
    /// [`crate::specs::mm::frame::segment::tracked_mint_seg_obligations`]).
    /// Multiset semantics — multiple outstanding obligations at the same slot
    /// are counted individually.
    pub frame_obligations: vstd::multiset::Multiset<usize>,
}

pub ghost struct MetaRegionModel {
    pub slots: Map<usize, MetaSlotModel>,
}

impl Inv for MetaRegionOwners {
    open spec fn inv(self) -> bool {
        &&& {
            // All accessible slots are within the valid address range.
            forall|i: usize| i < max_meta_slots() <==> #[trigger] self.slot_owners.contains_key(i)
        }
        &&& {
            forall|i: usize| #[trigger]
                self.slot_owners.contains_key(i) ==> self.slots.contains_key(i)
        }
        &&& { forall|i: usize| #[trigger] self.slots.contains_key(i) ==> i < max_meta_slots() }
        &&& {
            forall|i: usize| #[trigger]
                self.slots.contains_key(i) ==> {
                    &&& self.slot_owners[i].inv()
                    &&& self.slots[i].is_init()
                    &&& self.slots[i].addr() == meta_addr(i)
                    &&& self.slots[i].value().wf(self.slot_owners[i])
                    &&& self.slot_owners[i].slot_vaddr == self.slots[i].addr()
                }
        }
    }
}

impl Inv for MetaRegionModel {
    open spec fn inv(self) -> bool {
        &&& forall|i: usize| i < max_meta_slots() <==> #[trigger] self.slots.contains_key(i)
        &&& forall|i: usize| #[trigger] self.slots.contains_key(i) ==> self.slots[i].inv()
    }
}

impl View for MetaRegionOwners {
    type V = MetaRegionModel;

    open spec fn view(&self) -> <Self as View>::V {
        let slots = self.slot_owners.map_values(|s: MetaSlotOwner| s@);
        MetaRegionModel { slots }
    }
}

impl InvView for MetaRegionOwners {
    proof fn view_preserves_inv(self) {
    }
}

impl MetaRegionOwners {
    pub open spec fn ref_count(self, i: usize) -> (res: u64)
        recommends
            self.inv(),
            i < max_meta_slots() as usize,
    {
        self.slot_owners[i].inner_perms.ref_count.value()
    }

    /// `other` agrees with `self` on every slot owner except the one at index
    /// `idx`: a single-slot operation leaves all other slots' owners untouched.
    pub open spec fn slot_owners_agree_except(self, other: MetaRegionOwners, idx: usize) -> bool {
        forall|i: usize|
            #![trigger other.slot_owners[i]]
            i != idx ==> other.slot_owners[i] == self.slot_owners[i]
    }

    pub axiom fn borrow_typed_perm<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        &self,
        i: usize,
    ) -> (tracked res: &vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<M>>)
        requires
            self.slots.contains_key(i),
            self.slot_owners.contains_key(i),
            vstd_extra::cast_ptr::PointsTo::<MetaSlot, Metadata<M>>::new_spec(
                self.slots[i],
                self.slot_owners[i].inner_perms,
            ).wf(&self.slot_owners[i].inner_perms),
        ensures
            res.points_to == self.slots[i],
            res.inner_perms == self.slot_owners[i].inner_perms,
            res.wf(&res.inner_perms),
    ;

    /// Mutable analog of [`borrow_typed_perm`]. Lends out a `&'a mut cast_ptr`
    /// reconstructed from `slots[i]` (outer simple-pptr) and
    /// `slot_owners[i].inner_perms` (inner perms). While the returned reference
    /// is live, `self` is mutably borrowed; on borrow-end, `self.slots[i]` and
    /// `self.slot_owners[i].inner_perms` are restored from the final cast_ptr.
    /// Every other slot/slot_owner is fully preserved, and the other fields of
    /// `slot_owners[i]` (raw_count/usage/slot_vaddr/paths_in_pt) are unchanged.
    pub axiom fn borrow_mut_typed_perm<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        &mut self,
        i: usize,
    ) -> (tracked res: &mut vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<M>>)
        requires
            old(self).slots.contains_key(i),
            old(self).slot_owners.contains_key(i),
            vstd_extra::cast_ptr::PointsTo::<MetaSlot, Metadata<M>>::new_spec(
                old(self).slots[i],
                old(self).slot_owners[i].inner_perms,
            ).wf(&old(self).slot_owners[i].inner_perms),
        ensures
            res.points_to == old(self).slots[i],
            res.inner_perms == old(self).slot_owners[i].inner_perms,
            res.wf(&res.inner_perms),
            final(self).slots.dom() == old(self).slots.dom(),
            final(self).slot_owners.dom() == old(self).slot_owners.dom(),
            final(self).slots[i] == final(res).points_to,
            final(self).slot_owners[i].inner_perms == final(res).inner_perms,
            forall|k: usize| k != i ==> #[trigger] final(self).slots[k] == old(self).slots[k],
            forall|k: usize|
                k != i ==> #[trigger] final(self).slot_owners[k] == old(self).slot_owners[k],
            final(self).slot_owners[i].usage == old(self).slot_owners[i].usage,
            final(self).slot_owners[i].slot_vaddr == old(self).slot_owners[i].slot_vaddr,
            final(self).slot_owners[i].paths_in_pt == old(self).slot_owners[i].paths_in_pt,
            final(self).frame_obligations == old(self).frame_obligations,
    ;

    pub open spec fn paddr_range_in_region(self, range: Range<Paddr>) -> bool
        recommends
            self.inv(),
            range.start < range.end < MAX_PADDR,
    {
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> self.slots.contains_key(frame_to_index(paddr))
    }

    pub open spec fn paddr_range_not_mapped(self, range: Range<Paddr>) -> bool
        recommends
            self.inv(),
            range.start < range.end < MAX_PADDR,
    {
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> self.slot_owners[frame_to_index(paddr)].paths_in_pt.is_empty()
    }

    pub open spec fn paddr_range_not_in_region(self, range: Range<Paddr>) -> bool
        recommends
            self.inv(),
            range.start < range.end < MAX_PADDR,
    {
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> !self.slots.contains_key(frame_to_index(paddr))
    }

    /// Instantiates `paddr_range_not_mapped` at a specific paddr in the range.
    pub proof fn paddr_not_mapped_at(self, range: Range<Paddr>, paddr: Paddr)
        requires
            self.paddr_range_not_mapped(range),
            range.start <= paddr,
            paddr < range.end,
            paddr % PAGE_SIZE == 0,
        ensures
            self.slot_owners[frame_to_index(paddr)].paths_in_pt.is_empty(),
    {
        // The trigger frame_to_index(paddr) fires from the ensures clause,
        // instantiating the forall in paddr_range_not_mapped at this paddr.
    }

    pub proof fn inv_implies_correct_addr(self, paddr: usize)
        requires
            paddr < MAX_PADDR,
            paddr % PAGE_SIZE == 0,
            self.inv(),
        ensures
            self.slot_owners.contains_key(frame_to_index(paddr) as usize),
    {
    }

    /// Move a slot pointer permission *into* `slots[index]` from caller-supplied storage.
    /// Used by `Frame::from_raw` after the migration to typed slot perms — the perm being
    /// returned to `regions.slots` has no `inner_perms` baggage; the inner-perms live in
    /// `slot_owners[index].inner_perms`.
    pub axiom fn sync_slot_perm(
        tracked &mut self,
        index: usize,
        perm: &simple_pptr::PointsTo<MetaSlot>,
    )
        ensures
            final(self).slots == old(self).slots.insert(index, *perm),
            final(self).slot_owners == old(self).slot_owners,
            final(self).frame_obligations == old(self).frame_obligations,
    ;

    // ----------------------------------------------------------------------
    // Per-frame linear-drop ledger machinery.
    // ----------------------------------------------------------------------
    /// "Clean" boundary invariant: standard invariant plus an empty per-frame
    /// obligation multiset (every minted token has been redeemed via
    /// `Drop::drop` or `ManuallyDrop::new`; and every `Segment` has been
    /// dropped, draining its per-frame entries).
    ///
    /// Functions that should leave no outstanding `Frame`/`Segment` obligations
    /// (e.g., top-of-call-stack entry points, or any helper that opens fresh
    /// resources locally) should require this in their postcondition instead of
    /// the plain `inv()`.
    pub open spec fn clean_inv(self) -> bool {
        &&& self.inv()
        // Per-frame linear-drop discipline via the multiset ledger: every
        // `ManuallyDrop::new` / segment-frame mint adds one entry, every
        // `Drop::drop` / `ManuallyDrop::new` / segment-frame redeem removes one.
        &&& self.frame_obligations.len() == 0
    }

    // ----------------------------------------------------------------------
    // Frame-side per-instance ledger.
    // ----------------------------------------------------------------------
    pub open spec fn mint_frame_obligation(self, slot_idx: usize) -> Self {
        Self { frame_obligations: self.frame_obligations.insert(slot_idx), ..self }
    }

    pub open spec fn redeem_frame_obligation(self, slot_idx: usize) -> Self
        recommends
            self.frame_obligations.count(slot_idx) > 0,
    {
        Self { frame_obligations: self.frame_obligations.remove(slot_idx), ..self }
    }

    /// Pairs the production of a per-Frame [`DropObligation`] with a
    /// `+1` on the `frame_obligations[slot_idx]` count. Called by Frame's
    /// `constructor_spec` (i.e. `ManuallyDrop::new(frame, ..)`).
    pub axiom fn tracked_mint_frame_obligation(tracked &mut self, slot_idx: usize) -> (tracked obl:
        DropObligation<usize>)
        ensures
            obl.value() == slot_idx,
            *final(self) == old(self).mint_frame_obligation(slot_idx),
    ;

    /// Redeems a per-Frame obligation, decrementing `frame_obligations`
    /// at `obl.value()`. Called by Frame's `consume_obligation` (i.e.
    /// by `Drop::drop` or `ManuallyDrop::new`).
    pub axiom fn tracked_redeem_frame_obligation(
        tracked &mut self,
        tracked obl: DropObligation<usize>,
    )
        requires
            old(self).frame_obligations.count(obl.value()) > 0,
        ensures
            *final(self) == old(self).redeem_frame_obligation(obl.value()),
    ;
}

} // verus!
