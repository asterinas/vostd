use vstd::prelude::*;
use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;

use super::meta_owners::*;
use crate::mm::frame::*;
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::mapping::{
    frame_to_index, frame_to_meta, max_meta_slots, meta_addr, meta_to_frame,
};
use crate::specs::mm::frame::meta_region_owners::{MetaRegionModel, MetaRegionOwners};
use crate::specs::mm::Paddr;

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
    /// matching `meta_own`.
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
        &&& regions.slot_owners[frame_to_index(paddr)].raw_count
            == old_regions.slot_owners[frame_to_index(paddr)].raw_count
        &&& regions.slot_owners[frame_to_index(paddr)].usage
            == old_regions.slot_owners[frame_to_index(paddr)].usage
        &&& regions.slot_owners[frame_to_index(paddr)].paths_in_pt
            == old_regions.slot_owners[frame_to_index(paddr)].paths_in_pt
        &&& forall|i: usize|
            i != frame_to_index(paddr) ==> regions.slot_owners[i] == old_regions.slot_owners[i]
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

    open spec fn constructor_requires(self, s: Self::State) -> bool {
        &&& s.slot_owners.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& s.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].raw_count == 0
        &&& s.slot_owners[frame_to_index(
            meta_to_frame(self.ptr.addr()),
        )].inner_perms.ref_count.value() != REF_COUNT_UNUSED
        &&& s.inv()
    }

    open spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        &&& s1.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].raw_count == 1
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
        &&& s1.slots =~= s0.slots
        &&& s1.inv()
    }

    proof fn constructor_spec(self, tracked s: &mut Self::State) {
        let index = frame_to_index(meta_to_frame(self.ptr.addr()));
        let tracked mut slot_own = s.slot_owners.tracked_remove(index);
        slot_own.raw_count = 1;
        s.slot_owners.tracked_insert(index, slot_own);
    }

    open spec fn drop_requires(self, s: Self::State) -> bool {
        &&& s.slot_owners.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& s.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].raw_count > 0
        &&& s.inv()
    }

    open spec fn drop_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        &&& s1.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].raw_count == 0
        &&& forall|i: usize|
            #![trigger s1.slot_owners[i]]
            i != frame_to_index(meta_to_frame(self.ptr.addr())) ==> s1.slot_owners[i]
                == s0.slot_owners[i]
        &&& s1.slots =~= s0.slots
        &&& s1.inv()
    }
}

} // verus!
