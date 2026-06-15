use vstd::prelude::*;
use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;

use super::meta_owners::*;
use crate::mm::frame::*;
use crate::mm::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::Paddr;
use crate::specs::mm::frame::mapping::{
    frame_to_index, frame_to_meta, max_meta_slots, meta_addr, meta_to_frame,
};
use crate::specs::mm::frame::meta_region_owners::{MetaRegionModel, MetaRegionOwners};

verus! {

pub tracked struct UniqueFrameOwner<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta_own: M::Owner,
    pub ghost slot_index: usize,
}

pub ghost struct UniqueFrameModel<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta: <M::Owner as View>::V,
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrameOwner<M> {
    open spec fn inv(self) -> bool {
        &&& self.slot_index < MAX_NR_PAGES
        &&& self.slot_index < max_meta_slots()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrameModel<M> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> View for UniqueFrameOwner<M> {
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
        &&& self.ptr.addr() == meta_addr(owner.slot_index)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> ModelOf for UniqueFrame<M> {

}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrameOwner<M> {
    /// The typed permission for this frame, reconstructed from the region: the
    /// outer pointer-perm `regions.slots[slot_index]` paired with the inner
    /// perms `regions.slot_owners[slot_index].inner_perms`. Borrow-model analog
    /// of the owned `meta_perm` field; meaningful where `slots.contains_key`.
    pub open spec fn meta_perm_of(self, regions: MetaRegionOwners) -> PointsTo<
        MetaSlot,
        Metadata<M>,
    > {
        PointsTo::new_spec(
            regions.slots[self.slot_index],
            regions.slot_owners[self.slot_index].inner_perms,
        )
    }

    pub open spec fn perm_inv(self, perm: vstd::simple_pptr::PointsTo<MetaSlot>) -> bool {
        &&& perm.is_init()
        &&& perm.addr() == meta_addr(self.slot_index)
    }

    /// Borrow-model global invariant: the frame's permission is parked in
    /// `regions.slots[slot_index]` (NOT owned by the frame), and the
    /// reconstructed `meta_perm_of` is well-formed and decodes to metadata
    /// matching `meta_own`. A `UniqueFrame` is the sole live reference to its
    /// slot, so the slot sits at `REF_COUNT_UNIQUE` — the unique-frame analog
    /// of the segment's `0 < ref_count <= REF_COUNT_MAX` regime in
    /// [`SegmentOwner::relate_regions`]. Being live, it also owes a pending-Drop
    /// obligation in `frame_obligations` (minted at `from_unused`/`from_raw`,
    /// consumed by `drop`/`into_raw`).
    pub open spec fn global_inv(self, regions: MetaRegionOwners) -> bool {
        let perm = self.meta_perm_of(regions);
        &&& regions.slots.contains_key(self.slot_index)
        &&& regions.slot_owners.contains_key(self.slot_index)
        &&& perm.is_init()
        &&& perm.wf(&perm.inner_perms)
        &&& perm.addr() == meta_addr(self.slot_index)
        &&& perm.addr() == perm.points_to.addr()
        &&& perm.value().metadata.wf(self.meta_own)
        &&& regions.slot_owners[self.slot_index].self_addr == meta_addr(self.slot_index)
        &&& regions.slot_owners[self.slot_index].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
        &&& regions.frame_obligations.count(self.slot_index) > 0
    }

    pub proof fn from_raw_owner(owner: M::Owner, index: Ghost<usize>) -> Self {
        UniqueFrameOwner::<M> { meta_own: owner, slot_index: index@ }
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
        &&& res.meta_perm_of(regions).addr() == frame_to_meta(paddr)
        &&& res.meta_perm_of(regions).value().metadata == metadata
        &&& regions.slots == old_regions.slots
        &&& regions.slot_owners[frame_to_index(paddr)].inner_perms
            == old_regions.slot_owners[frame_to_index(paddr)].inner_perms
        &&& regions.slot_owners[frame_to_index(paddr)].usage
            == old_regions.slot_owners[frame_to_index(paddr)].usage
        &&& regions.slot_owners[frame_to_index(paddr)].paths_in_pt
            == old_regions.slot_owners[frame_to_index(paddr)].paths_in_pt
        &&& forall|i: usize|
            i != frame_to_index(paddr) ==> regions.slot_owners[i]
                == old_regions.slot_owners[i]
        // Setting up the owner does not touch the per-frame ledger; the
        // pending-Drop obligation is minted by `from_unused` itself.
        &&& regions.frame_obligations == old_regions.frame_obligations
        &&& regions.inv()
    }

    pub axiom fn tracked_from_unused_owner(
        tracked regions: &mut MetaRegionOwners,
        paddr: Paddr,
    ) -> (tracked res: Self)
        ensures
            Self::from_unused_owner(
                *old(regions),
                paddr,
                res.meta_perm_of(*final(regions)).value().metadata,
                res,
                *final(regions),
            ),
    ;
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> TrackDrop for UniqueFrame<M> {
    type State = MetaRegionOwners;

    /// Slot index — identifies *which* slot the obligation belongs to.
    /// `UniqueFrame` shares the `frame_obligations` multiset with `Frame`:
    /// at any moment a slot is in either Frame-SHARED mode (ref_count in
    /// [1, MAX]) or UniqueFrame-UNIQUE mode (ref_count == UNIQUE), never
    /// both, so the multiset semantics are unambiguous.
    type Key = usize;

    open spec fn key(self) -> Self::Key {
        frame_to_index(meta_to_frame(self.ptr.addr()))
    }

    open spec fn constructor_requires(self, s: Self::State) -> bool {
        &&& s.slot_owners.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& s.slot_owners[frame_to_index(
            meta_to_frame(self.ptr.addr()),
        )].inner_perms.ref_count.value() != REF_COUNT_UNUSED
        &&& s.inv()
    }

    open spec fn constructor_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl_key: Self::Key,
    ) -> bool {
        &&& s1.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].inner_perms
            == s0.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].inner_perms
        &&& s1.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].self_addr
            == s0.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].self_addr
        &&& s1.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].usage
            == s0.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].usage
        &&& s1.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].paths_in_pt
            == s0.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].paths_in_pt
        &&& forall|i: usize|
            #![trigger s1.slot_owners[i]]
            i != frame_to_index(meta_to_frame(self.ptr.addr())) ==> s1.slot_owners[i]
                == s0.slot_owners[i]
        &&& s1.slots
            =~= s0.slots
        // Linear-drop discipline: minting a UniqueFrame (`MD::new`) adds
        // one entry at the slot index via the paired mint axiom — same
        // ledger Frame uses.
        &&& s1.frame_obligations =~= s0.frame_obligations.insert(obl_key)
        &&& s1.inv()
    }

    proof fn constructor_spec(self, tracked s: &mut Self::State) -> (tracked obl: DropObligation<
        Self::Key,
    >) {
        let index = frame_to_index(meta_to_frame(self.ptr.addr()));
        let tracked mut slot_own = s.slot_owners.tracked_remove(index);
        s.slot_owners.tracked_insert(index, slot_own);
        // Paired mint axiom: produces the token AND adds its Loc to
        // `frame_obligations` — replaces the prior ledger-less
        // `DropObligation::tracked_mint(())`.
        s.tracked_mint_frame_obligation(index)
    }

    open spec fn drop_requires(self, s: Self::State) -> bool {
        &&& s.slot_owners.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& s.inv()
    }

    open spec fn drop_ensures(self, s0: Self::State, s1: Self::State, obl_key: Self::Key) -> bool {
        &&& forall|i: usize|
            #![trigger s1.slot_owners[i]]
            i != frame_to_index(meta_to_frame(self.ptr.addr())) ==> s1.slot_owners[i]
                == s0.slot_owners[i]
        &&& s1.slots
            =~= s0.slots
        // The trait-level `drop_ensures` records the per-instance
        // ledger contribution: one entry at `obl_key` is removed via
        // `consume_obligation`. (`UniqueFrame`'s inherent `drop` exec
        // function is responsible for arranging this in the body.)
        &&& s1.frame_obligations =~= s0.frame_obligations.remove(obl_key)
        &&& s1.inv()
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
        // `frame_obligations`. Leaves `slot_owners` untouched.
        s.tracked_redeem_frame_obligation(obl);
    }
}

} // verus!
