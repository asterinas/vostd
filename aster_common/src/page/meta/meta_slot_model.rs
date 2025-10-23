//! The model of a metadata slot. It includes:
//! - The model of the metadata slot: `MetaSlotModel`.
//! - The invariants for both MetaSlot and MetaSlotModel.
//! - The primitives for MetaSlot.
use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::*;

use vstd_extra::cast_ptr::{self, Repr};
use vstd_extra::ownership::*;

use crate::prelude::*;

use std::marker::PhantomData;

verus! {

pub enum MetaSlotStatus {
    UNUSED,
    UNIQUE,
    SHARED,
    OVERFLOW,
    UNDER_CONSTRUCTION,
}

/* Phase I version; TODO: check conversions
#[derive(PartialEq)]
pub ghost enum MetaSlotState {
    Unused,
    Claimed,
    Used,
    Finalizing,
} */

pub const REF_COUNT_UNUSED: u64 = u64::MAX;

pub const REF_COUNT_UNIQUE: u64 = u64::MAX - 1;

pub const REF_COUNT_MAX: u64 = i64::MAX as u64;

pub tracked struct MetaSlotOwner {
    pub storage: Tracked<PointsTo<MetaSlotStorage>>,
    pub ref_count: Tracked<PermissionU64>,
    pub vtable_ptr: Tracked<PointsTo<usize>>,
    pub in_list: Tracked<PermissionU64>,
    pub self_addr: usize,
    pub usage: PageUsage,
}

impl Inv for MetaSlotOwner {
    open spec fn inv(self) -> bool {
        &&& self.ref_count@.value() == REF_COUNT_UNUSED ==> {
            &&& self.vtable_ptr@.is_uninit()
            &&& self.in_list@.value() == 0
        }
        &&& self.ref_count@.value() == REF_COUNT_UNIQUE ==> {
            &&& self.vtable_ptr@.is_init()
        }
        &&& 0 < self.ref_count@.value() < REF_COUNT_MAX ==> {
            &&& self.vtable_ptr@.is_init()
        }
        &&& REF_COUNT_MAX <= self.ref_count@.value() < REF_COUNT_UNUSED ==> { false }
        &&& self.ref_count@.value() == 0 ==> {
            &&& self.vtable_ptr@.is_uninit()
            &&& self.in_list@.value() == 0
        }
        &&& FRAME_METADATA_RANGE().start <= self.self_addr < FRAME_METADATA_RANGE().end
        &&& self.self_addr % META_SLOT_SIZE() == 0
    }
}

pub ghost struct MetaSlotModel {
    pub status: MetaSlotStatus,
    pub storage: MemContents<MetaSlotStorage>,
    pub ref_count: u64,
    pub vtable_ptr: MemContents<usize>,
    pub in_list: u64,
    pub self_addr: usize,
    pub usage: PageUsage,
}

impl Inv for MetaSlotModel {
    open spec fn inv(self) -> bool {
        match self.ref_count {
            REF_COUNT_UNUSED => {
                &&& self.vtable_ptr.is_uninit()
                &&& self.in_list == 0
            },
            REF_COUNT_UNIQUE => { &&& self.vtable_ptr.is_init() },
            0 => {
                &&& self.vtable_ptr.is_uninit()
                &&& self.in_list == 0
            },
            _ if self.ref_count < REF_COUNT_MAX => { &&& self.vtable_ptr.is_init() },
            _ => { false },
        }
    }
}

impl InvView for MetaSlotOwner {
    type V = MetaSlotModel;

    open spec fn view(self) -> Self::V {
        let storage = self.storage@.mem_contents();
        let ref_count = self.ref_count@.value();
        let vtable_ptr = self.vtable_ptr@.mem_contents();
        let in_list = self.in_list@.value();
        let self_addr = self.self_addr;
        let usage = self.usage;
        let status = match ref_count {
            REF_COUNT_UNUSED => MetaSlotStatus::UNUSED,
            REF_COUNT_UNIQUE => MetaSlotStatus::UNIQUE,
            0 => MetaSlotStatus::UNDER_CONSTRUCTION,
            _ if ref_count < REF_COUNT_MAX => MetaSlotStatus::SHARED,
            _ => MetaSlotStatus::OVERFLOW,
        };
        MetaSlotModel { status, storage, ref_count, vtable_ptr, in_list, self_addr, usage }
    }

    proof fn view_preserves_inv(&self) {
        admit()
    }
}

impl OwnerOf for MetaSlot {
    type Owner = MetaSlotOwner;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        &&& self.storage == owner.storage@.pptr()
        &&& self.ref_count.id() == owner.ref_count@.id()
        &&& self.vtable_ptr == owner.vtable_ptr@.pptr()
        &&& self.in_list.id() == owner.in_list@.id()
    }
}

impl ModelOf for MetaSlot {

}

impl MetaSlotOwner {
    pub fn cast_perm<T: Repr<MetaSlotStorage>>(self) -> Tracked<
        vstd_extra::cast_ptr::PointsTo<MetaSlotStorage, T>,
    > {
        vstd_extra::cast_ptr::PointsTo::new(self.self_addr, self.storage)
    }
}

/*pub tracked struct UniqueFrameLinkOwner<M: AnyFrameMeta + Repr<MetaSlotInner>> {
    pub link_own : LinkOwner,
    pub link_perm : Tracked<vstd_extra::cast_ptr::PointsTo<MetaSlotStorage, Link<M>>>,
    pub frame_own : UniqueFrameOwner<Link<M>>
}*/

pub tracked struct UniqueFrameOwner<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta_own: Tracked<M::Owner>,
    pub meta_perm: Tracked<vstd_extra::cast_ptr::PointsTo<MetaSlotStorage, M>>,
    pub slot_index: usize,
}

pub ghost struct UniqueFrameModel<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta: <M::Owner as InvView>::V,
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrameOwner<M> {
    open spec fn inv(self) -> bool {
        &&& self.meta_perm@.is_init()
        &&& self.meta_perm@.wf()
        &&& self.slot_index == frame_to_index(meta_to_frame(self.meta_perm@.addr()))
        &&& self.slot_index < max_meta_slots()
        &&& (self.slot_index - FRAME_METADATA_RANGE().start) as usize % META_SLOT_SIZE() == 0
        &&& self.meta_perm@.addr() % META_SLOT_SIZE() == 0
        &&& FRAME_METADATA_RANGE().start <= self.meta_perm@.addr() < FRAME_METADATA_RANGE().start
            + MAX_NR_PAGES() * META_SLOT_SIZE()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrameModel<M> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> InvView for UniqueFrameOwner<M> {
    type V = UniqueFrameModel<M>;

    open spec fn view(self) -> Self::V {
        UniqueFrameModel { meta: self.meta_own@@ }
    }

    proof fn view_preserves_inv(&self) {
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrameOwner<M> {
    pub open spec fn perm_inv(&self, perm: PointsTo<MetaSlot>) -> bool {
        &&& perm.is_init()
        &&& perm.addr() == self.meta_perm@.addr()
        &&& perm.value().storage.addr() == self.meta_perm@.addr()
        &&& perm.value().storage.addr() == self.meta_perm@.points_to@.addr()
    }

    pub open spec fn global_inv(&self, regions: MetaRegionOwners) -> bool {
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

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        &&& self.ptr.addr() == owner.meta_perm@.addr()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> ModelOf for UniqueFrame<M> {

}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrameOwner<M> {
    pub fn from_raw_owner(
        owner: Tracked<M::Owner>,
        index: usize,
        perm: Tracked<vstd_extra::cast_ptr::PointsTo<MetaSlotStorage, M>>,
    ) -> Tracked<Self> {
        Tracked(UniqueFrameOwner::<M> { meta_own: owner, meta_perm: perm, slot_index: index })
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> Link<M> {
    pub open spec fn into_spec(self) -> StoredLink {
        let next = match self.next {
            Some(link) => Some(link.addr),
            None => None,
        };
        let prev = match self.prev {
            Some(link) => Some(link.addr),
            None => None,
        };
        StoredLink { next: next, prev: prev, slot: self.meta.to_repr() }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into(self) -> (res: StoredLink)
        ensures
            res == self.into_spec(),
    {
        let next = match self.next {
            Some(link) => Some(link.addr),
            None => None,
        };
        let prev = match self.prev {
            Some(link) => Some(link.addr),
            None => None,
        };
        StoredLink { next: next, prev: prev, slot: self.meta.to_repr() }
    }
}

} // verus!
