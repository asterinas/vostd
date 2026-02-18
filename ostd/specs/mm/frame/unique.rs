use vstd::prelude::*;
use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;
use vstd_extra::undroppable::*;

use super::meta_owners::*;
use crate::mm::frame::*;
use crate::specs::mm::Paddr;
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::mapping::{frame_to_index, frame_to_meta, meta_addr, meta_to_frame, max_meta_slots};
use crate::specs::mm::frame::meta_region_owners::{MetaRegionModel, MetaRegionOwners};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;

verus! {

pub tracked struct UniqueFrameOwner<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta_own: M::Owner,
    pub meta_perm: PointsTo<MetaSlot, Metadata<M>>,
    pub ghost slot_index: usize,
}

pub ghost struct UniqueFrameModel<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta: <M::Owner as View>::V,
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrameOwner<M> {
    open spec fn inv(self) -> bool {
        &&& self.meta_perm.is_init()
        &&& self.meta_perm.wf()
        &&& self.slot_index == frame_to_index(meta_to_frame(self.meta_perm.addr()))
        &&& self.slot_index < max_meta_slots()
        &&& (self.slot_index - FRAME_METADATA_RANGE.start) as usize % META_SLOT_SIZE == 0
        &&& self.meta_perm.addr() < FRAME_METADATA_RANGE.start + MAX_NR_PAGES * META_SLOT_SIZE
        &&& self.meta_perm.addr() == meta_addr(self.slot_index)
        &&& self.meta_perm.addr() == self.meta_perm.points_to.addr()
        &&& self.meta_perm.value().metadata.wf(self.meta_own)
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
        &&& self.ptr.addr() == owner.meta_perm.addr()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> ModelOf for UniqueFrame<M> {

}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrameOwner<M> {
    
    pub open spec fn perm_inv(self, perm: vstd::simple_pptr::PointsTo<MetaSlot>) -> bool {
        &&& perm.is_init()
        &&& perm.addr() == self.meta_perm.addr()
    }

    pub open spec fn global_inv(self, regions: MetaRegionOwners) -> bool {
        &&& regions.slots.contains_key(self.slot_index) ==> self.perm_inv(
            regions.slots[self.slot_index],
        )
        &&& regions.dropped_slots.contains_key(self.slot_index) ==> self.perm_inv(
            regions.dropped_slots[self.slot_index],
        )
        &&& regions.slot_owners.contains_key(self.slot_index) ==> {
            &&& regions.slot_owners[self.slot_index].ref_count.value() != REF_COUNT_UNUSED
            &&& regions.slot_owners[self.slot_index].ref_count.value() != 0
        }
    }

    pub proof fn from_raw_owner(
        owner: M::Owner,
        index: Ghost<usize>,
        perm: PointsTo<MetaSlot, Metadata<M>>,
    ) -> Self {
        UniqueFrameOwner::<M> { meta_own: owner, meta_perm: perm, slot_index: index@ }
    }

    pub open spec fn from_unused_owner_spec(
        old_regions: MetaRegionOwners,
        paddr: Paddr,
        metadata: M,
        res: Self,
        regions: MetaRegionOwners,
    ) -> bool {
        &&& res.meta_perm == PointsTo::<MetaSlot, Metadata<M>>::new_spec(frame_to_meta(paddr), regions.slots[frame_to_index(paddr)])
        &&& <M as OwnerOf>::wf(metadata,res.meta_own)
        &&& regions.slots == old_regions.slots.remove(frame_to_index(paddr))
        &&& regions.dropped_slots == old_regions.dropped_slots
        &&& regions.slot_owners == old_regions.slot_owners
        &&& regions.inv()
    }

    pub axiom fn from_unused_owner(
        tracked regions: &mut MetaRegionOwners,
        paddr: Paddr,
        metadata: M,
    ) -> (tracked res: Self)
    ensures
        Self::from_unused_owner_spec(*old(regions), paddr, metadata, res, *regions);
    /* {
        let tracked perm = regions.slots.tracked_remove(frame_to_index(paddr));
        UniqueFrameOwner::<M> {
            meta_own: regions.slot_owners[frame_to_index(paddr)],
            meta_perm: perm,
            slot_index: frame_to_index(paddr)
        }
    }*/
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Undroppable for UniqueFrame<M> {
    type State = MetaRegionOwners;

    open spec fn constructor_requires(self, s: Self::State) -> bool {
        &&& s.slots.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& !s.dropped_slots.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& s.inv()
    }

    open spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        &&& !s1.slots.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& s1.dropped_slots.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& s1.inv()
        &&& s1.slots == s0.slots.remove(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& s1.dropped_slots == s0.dropped_slots.insert(
            frame_to_index(meta_to_frame(self.ptr.addr())),
            s0.slots[frame_to_index(meta_to_frame(self.ptr.addr()))],
        )
        &&& s1.slot_owners == s0.slot_owners
    }

    proof fn constructor_spec(self, tracked s: &mut Self::State) {
        let index = frame_to_index(meta_to_frame(self.ptr.addr()));
        let tracked perm = s.slots.tracked_remove(index);
        s.dropped_slots.tracked_insert(index, perm);
    }
}

}