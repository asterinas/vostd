use vstd::prelude::*;

use vstd_extra::{cast_ptr::*, drop_tracking::*, ownership::*};

use crate::specs::{
    arch::MAX_NR_PAGES,
    mm::{
        Paddr,
        frame::{
            mapping::{frame_to_index, index_to_meta, max_meta_slots},
            meta_region_owners::MetaRegionOwners,
        },
    },
};

use crate::mm::{
    frame::{
        meta::{
            REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
            mapping::{frame_to_meta, meta_to_frame},
        },
        *,
    },
    kspace::FRAME_METADATA_RANGE,
};

use super::meta_owners::*;

verus! {

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> UniqueFrame<M> {
    pub open spec fn paddr(self) -> Paddr {
        meta_to_frame(self.ptr.addr())
    }

    pub open spec fn index(self) -> int {
        frame_to_index(self.paddr())
    }
}

//FIXME: why do we need a index here?
pub tracked struct UniqueFrameOwner<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta_own: M::Owner,
    pub repr_perm: Option<M::Perm>,
    pub ghost slot_index: int,
}

pub ghost struct UniqueFrameModel<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta: <M::Owner as View>::V,
}

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrameOwner<M> {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.slot_index < MAX_NR_PAGES
        &&& self.slot_index < max_meta_slots()
        &&& self.repr_perm is Some
    }
}

impl<M: AnyFrameMeta + Sized + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrameModel<M> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> View for UniqueFrameOwner<M> {
    type V = UniqueFrameModel<M>;

    open spec fn view(&self) -> Self::V {
        UniqueFrameModel { meta: self.meta_own@ }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> InvView for UniqueFrameOwner<M> {
    proof fn view_preserves_inv(self) {
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> OwnerOf for UniqueFrame<M> {
    type Owner = UniqueFrameOwner<M>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.ptr.addr() == index_to_meta(owner.slot_index)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrame<M> {
    /// Cross-object validity of a live UNIQUE handle against the region map —
    /// the [`UniqueFrame`] analog of [`Frame::wf_with_region`] (which covers
    /// the SHARED state). Bundles the structural `wf` / `owner.inv` /
    /// `regions.inv` facts with the UNIQUE-state slot facts so a consumer (e.g.
    /// [`UniqueFrame::drop`]) can state a single invariant instead of re-listing
    /// each conjunct.
    ///
    /// The slot's `slot_owners.contains_key(idx)`, `slot_vaddr == index_to_meta(idx)`,
    /// `storage.is_init()`, and `vtable_ptr.is_init()` are **derived**, not
    /// required: `regions.inv()` (with `owner.inv()`'s `idx < max_meta_slots`)
    /// delivers the first two and `slot_owners[idx].inv()`; the latter's UNIQUE
    /// branch (under `rc == REF_COUNT_UNIQUE`) gives the storage/vtable init.
    /// The genuinely-extra conjuncts are the UNIQUE state itself plus
    /// `in_list == 0` and `paths_in_pt.is_empty()` (a sole owner is neither on
    /// the free list nor mapped into any page table).
    pub open spec fn wf_with_region(self, owner: UniqueFrameOwner<M>, s: MetaRegionOwners) -> bool {
        let idx = owner.slot_index;
        let so = s.slot_owners[idx];
        &&& self.wf(owner)
        &&& owner.inv()
        &&& s.inv()
        &&& so.inner_perms.ref_count.value() == REF_COUNT_UNIQUE
        &&& so.inner_perms.in_list.value() == 0
        &&& so.paths_in_pt.is_empty()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrameOwner<M> {
    pub open spec fn meta_wf(self, regions: MetaRegionOwners) -> bool {
        typed_meta_wf::<M>(
            regions.slots[self.slot_index],
            regions.slot_owners[self.slot_index].inner_perms.storage,
            self.repr_perm->0,
        )
    }

    pub open spec fn meta_value(self, regions: MetaRegionOwners) -> M
        recommends
            self.meta_wf(regions),
    {
        typed_meta_value::<M>(
            regions.slot_owners[self.slot_index].inner_perms.storage,
            self.repr_perm->0,
        )
    }

    pub open spec fn perm_inv(self, perm: vstd::simple_pptr::PointsTo<MetaSlot>) -> bool {
        &&& perm.is_init()
        &&& perm.addr() == index_to_meta(self.slot_index)
    }

    /// Borrow-model global invariant: the frame's permission is parked in
    /// `regions.slots[slot_index]` (NOT owned by the frame), and the
    /// concrete storage and representation permissions decode to metadata
    /// matching `meta_own`. A `UniqueFrame` is the sole live reference to its
    /// slot, so the slot sits at `REF_COUNT_UNIQUE` — the unique-frame analog
    /// of the segment's `0 < ref_count <= REF_COUNT_MAX` regime in
    /// [`Segment::relate_regions`]. Being live, it also owes a pending-Drop
    /// obligation in `frame_obligations` (minted at `from_unused`/`from_raw`,
    /// consumed by `drop`/`into_raw`).
    pub open spec fn global_inv(self, regions: MetaRegionOwners) -> bool {
        &&& regions.slots.contains_key(self.slot_index)
        &&& regions.slot_owners.contains_key(self.slot_index)
        &&& self.meta_wf(regions)
        &&& regions.slots[self.slot_index].addr() == index_to_meta(self.slot_index)
        &&& self.meta_value(regions).wf(self.meta_own)
        &&& regions.slot_owners[self.slot_index].slot_vaddr == index_to_meta(self.slot_index)
        &&& regions.slot_owners[self.slot_index].inner_perms.ref_count.value()
            == REF_COUNT_UNIQUE
        // Data-frame node-repark discriminator (our change): a unique frame's
        // slot is tracked with `Frame` usage, distinguishing it from page-table
        // node slots (`PageTable`) and letting linked-list/list-store consumers
        // derive `usage == Frame` (e.g. for the empty-`paths_in_pt` argument).
        &&& regions.slot_owners[self.slot_index].usage is Frame
        &&& regions.frame_obligations.count(self.slot_index) > 0
    }

    pub proof fn global_inv_preserved_by_slot_equality(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
    )
        requires
            self.global_inv(old_regions),
            new_regions.inv(),
            new_regions.slots.contains_key(self.slot_index),
            new_regions.slot_owners.contains_key(self.slot_index),
            new_regions.slots[self.slot_index] == old_regions.slots[self.slot_index],
            new_regions.slot_owners[self.slot_index] == old_regions.slot_owners[self.slot_index],
            new_regions.frame_obligations == old_regions.frame_obligations,
        ensures
            self.global_inv(new_regions),
    {
    }

    pub proof fn from_raw_owner(owner: M::Owner, repr_perm: M::Perm, index: Ghost<int>) -> Self {
        UniqueFrameOwner::<M> { meta_own: owner, repr_perm: Some(repr_perm), slot_index: index@ }
    }

    pub open spec fn from_unused_owner(
        old_regions: MetaRegionOwners,
        paddr: Paddr,
        metadata: M,
        res: Self,
        regions: MetaRegionOwners,
    ) -> bool {
        &&& <M as OwnerOf>::wf(metadata, res.meta_own)
        &&& res.slot_index == frame_to_index(paddr)
        &&& regions.slots[res.slot_index].addr() == frame_to_meta(paddr)
        &&& res.meta_wf(regions)
        &&& res.meta_value(regions) == metadata
        &&& regions.slots == old_regions.slots
        &&& regions.slot_owners[frame_to_index(paddr)].inner_perms
            == old_regions.slot_owners[frame_to_index(paddr)].inner_perms
        &&& regions.slot_owners[frame_to_index(paddr)].usage
            == old_regions.slot_owners[frame_to_index(paddr)].usage
        &&& regions.slot_owners[frame_to_index(paddr)].paths_in_pt
            == old_regions.slot_owners[frame_to_index(paddr)].paths_in_pt
        &&& forall|i: int|
            i != frame_to_index(paddr) ==> regions.slot_owners[i]
                == old_regions.slot_owners[i]
        // Setting up the owner does not touch the per-frame ledger; the
        // pending-Drop obligation is minted by `from_unused` itself.
        &&& regions.frame_obligations == old_regions.frame_obligations
        &&& regions.inv()
    }

    pub axiom fn tracked_from_unused_owner(
        tracked regions: &mut MetaRegionOwners,
        tracked repr_perm: M::Perm,
        paddr: Paddr,
    ) -> (tracked res: Self)
        ensures
            Self::from_unused_owner(
                *old(regions),
                paddr,
                res.meta_value(*final(regions)),
                res,
                *final(regions),
            ),
            res.repr_perm == Some(repr_perm),
    ;

    pub proof fn tracked_borrow_repr_perm(tracked &self) -> (tracked res: &M::Perm)
        requires
            self.repr_perm is Some,
        ensures
            *res == self.repr_perm->0,
    {
        self.repr_perm.tracked_borrow()
    }

    pub proof fn tracked_borrow_mut_repr_perm(tracked &mut self) -> (tracked res: &mut M::Perm)
        requires
            old(self).inv(),
        ensures
            *res == old(self).repr_perm->0,
            final(self).meta_own == old(self).meta_own,
            final(self).slot_index == old(self).slot_index,
            final(self).repr_perm is Some,
            final(self).repr_perm->0 == *final(res),
            final(self).inv(),
    {
        match &mut self.repr_perm {
            Some(perm) => perm,
            None => proof_from_false(),
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> TrackDrop for UniqueFrame<M> {
    type State = MetaRegionOwners;

    /// Slot index — identifies *which* slot the obligation belongs to.
    /// `UniqueFrame` shares the `frame_obligations` multiset with `Frame`:
    /// at any moment a slot is in either Frame-SHARED mode (ref_count in
    /// [1, MAX]) or UniqueFrame-UNIQUE mode (ref_count == UNIQUE), never
    /// both, so the multiset semantics are unambiguous.
    type Obligation = DropObligation<int>;

    open spec fn tracked_redeem_requires(self, s: Self::State) -> bool {
        &&& s.slot_owners.contains_key(self.index())
        &&& s.slot_owners[frame_to_index(
            meta_to_frame(self.ptr.addr()),
        )].inner_perms.ref_count.value() != REF_COUNT_UNUSED
        &&& s.inv()
    }

    open spec fn tracked_redeem_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        &&& s1.slot_owners[self.index()].inner_perms == s0.slot_owners[self.index()].inner_perms
        &&& s1.slot_owners[self.index()].slot_vaddr == s0.slot_owners[self.index()].slot_vaddr
        &&& s1.slot_owners[self.index()].usage == s0.slot_owners[self.index()].usage
        &&& s1.slot_owners[self.index()].paths_in_pt == s0.slot_owners[self.index()].paths_in_pt
        &&& forall|i: int|
            #![trigger s1.slot_owners[i]]
            i != self.index() ==> s1.slot_owners[i] == s0.slot_owners[i]
        &&& s1.slots
            =~= s0.slots
        // Linear-drop discipline: minting a UniqueFrame (`MD::new`) adds
        // one entry at the slot index via the paired mint axiom — same
        // ledger Frame uses.
        &&& s1.frame_obligations =~= s0.frame_obligations.insert(self.index())
        &&& obl.value() == self.index()
        &&& s1.inv()
    }

    proof fn tracked_redeem(self, tracked s: &mut Self::State) -> (tracked obl: Self::Obligation) {
        let index = self.index();
        let tracked mut slot_own = s.slot_owners.tracked_remove(index);
        s.slot_owners.tracked_insert(index, slot_own);
        // Paired mint axiom: produces the token AND adds its Loc to
        // `frame_obligations` — replaces the prior ledger-less
        // `DropObligation::tracked_mint(())`.
        s.tracked_mint_frame_obligation(index)
    }

    open spec fn drop_requires(self, s: Self::State, obl: Self::Obligation) -> bool {
        &&& s.slot_owners.contains_key(self.index())
        &&& s.inv()
        &&& s.frame_obligations.count(self.index()) > 0
        &&& obl.value() == self.index()
    }

    open spec fn drop_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        &&& forall|i: int|
            #![trigger s1.slot_owners[i]]
            i != self.index() ==> s1.slot_owners[i] == s0.slot_owners[i]
        &&& s1.slots
            =~= s0.slots
        // The trait-level `drop_ensures` records the per-instance
        // ledger contribution: one entry at `obl_key` is removed via
        // `consume_obligation`. (`UniqueFrame`'s inherent `drop` exec
        // function is responsible for arranging this in the body.)
        &&& s1.frame_obligations =~= s0.frame_obligations.remove(self.index())
        &&& s1.inv()
    }
}

} // verus!
