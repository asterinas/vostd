use vstd::prelude::*;

use vstd::simple_pptr::*;
use vstd_extra::cast_ptr::{self, Repr};

use super::*;

verus! {

#[rustc_has_incoherent_inherent_impls]
pub struct UniqueFrame<M: AnyFrameMeta> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
}

pub tracked struct UniqueFrameOwner<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta_own: Tracked<M::Owner>,
    pub meta_perm: Tracked<vstd_extra::cast_ptr::PointsTo<MetaSlotStorage, M>>,
    pub slot_index: usize,
}

pub ghost struct UniqueFrameModel<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta: <M::Owner as View>::V,
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrameOwner<M> {
    open spec fn inv(self) -> bool {
        &&& self.meta_perm@.is_init()
        &&& self.meta_perm@.wf()
        &&& self.slot_index == frame_to_index(meta_to_frame(self.meta_perm@.addr()))
        &&& self.slot_index < max_meta_slots()
        &&& (self.slot_index - FRAME_METADATA_RANGE().start) as usize % META_SLOT_SIZE() == 0
        &&& self.meta_perm@.addr() < FRAME_METADATA_RANGE().start + MAX_NR_PAGES()
            * META_SLOT_SIZE()
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
        UniqueFrameModel { meta: self.meta_own@@ }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> InvView for UniqueFrameOwner<M> {
    proof fn view_preserves_inv(self) {
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrameOwner<M> {
    pub open spec fn perm_inv(self, perm: PointsTo<MetaSlot>) -> bool {
        &&& perm.is_init()
        &&& perm.value().storage.addr() == self.meta_perm@.addr()
        &&& perm.value().storage.addr() == self.meta_perm@.points_to@.addr()
    }

    pub open spec fn global_inv(self, regions: MetaRegionOwners) -> bool {
        &&& regions.slots.contains_key(self.slot_index) ==> self.perm_inv(
            regions.slots[self.slot_index]@,
        )
        &&& regions.dropped_slots.contains_key(self.slot_index) ==> self.perm_inv(
            regions.dropped_slots[self.slot_index]@,
        )
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> OwnerOf for UniqueFrame<M> {
    type Owner = UniqueFrameOwner<M>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.ptr.addr() == owner.meta_perm@.addr()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> ModelOf for UniqueFrame<M> {

}

/*impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrameModel<M> {
    pub open spec fn from_raw_spec(region: MetaRegionModel, paddr: Paddr) -> Self {
        Self {
            slot: region.slots[frame_to_index(paddr)],
        }
    }
}*/

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrameOwner<M> {
    pub fn from_raw_owner(
        owner: Tracked<M::Owner>,
        index: usize,
        perm: Tracked<vstd_extra::cast_ptr::PointsTo<MetaSlotStorage, M>>,
    ) -> Tracked<Self> {
        Tracked(UniqueFrameOwner::<M> { meta_own: owner, meta_perm: perm, slot_index: index })
    }
}

} // verus!
