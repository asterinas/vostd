use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use super::meta_owners::{
    MetaSlotModel, MetaSlotOwner, MetaSlotStatus, MetaSlotStorage, Metadata, PageUsage,
};
use crate::mm::frame::meta::{
    get_slot_spec,
    mapping::{frame_to_index, frame_to_meta},
    REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
};
use crate::mm::frame::*;
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::meta_region_owners::{MetaRegionModel, MetaRegionOwners};

use core::marker::PhantomData;

verus! {

impl MetaSlot {

    pub open spec fn get_from_unused_spec(
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
        {
            &&& post.slots =~= pre.slots.remove(idx)
            &&& post.slot_owners[idx].inner_perms is None
            &&& post.slot_owners[idx].usage == PageUsage::Frame
            &&& post.slot_owners[idx].raw_count == pre.slot_owners[idx].raw_count
            &&& post.slot_owners[idx].self_addr == pre.slot_owners[idx].self_addr
            &&& post.slot_owners[idx].path_if_in_pt == pre.slot_owners[idx].path_if_in_pt
            &&& forall|i: usize| i != idx ==> (#[trigger] post.slot_owners[i] == pre.slot_owners[i])
        }
    }

    pub open spec fn get_from_unused_perm_spec<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        paddr: Paddr,
        metadata: M,
        as_unique_ptr: bool,
        ptr: PPtr<MetaSlot>,
        perm: PointsTo<MetaSlot, Metadata<M>>,
    ) -> bool {
        &&& ptr.addr() == frame_to_meta(paddr)
        &&& perm.addr() == frame_to_meta(paddr)
        &&& perm.is_init()
        &&& perm.value().metadata == metadata
        &&& perm.value().ref_count == (if as_unique_ptr { REF_COUNT_UNIQUE as u64 } else { 1u64 })
    }

    pub open spec fn inc_ref_count_panic_cond(rc_perm: PermissionU64) -> bool {
        rc_perm.value() >= REF_COUNT_MAX
    }

    pub open spec fn frame_paddr_safety_cond(perm: vstd::simple_pptr::PointsTo<MetaSlot>) -> bool {
        &&& FRAME_METADATA_RANGE.start <= perm.addr() < FRAME_METADATA_RANGE.end
        &&& perm.addr() % META_SLOT_SIZE == 0
    }

    pub open spec fn get_from_in_use_panic_cond(paddr: Paddr, regions: MetaRegionOwners) -> bool {
        let idx = frame_to_index(paddr);
        let pre_perms = regions.slot_owners[idx].inner_perms.unwrap().ref_count.value();
        pre_perms + 1 >= REF_COUNT_MAX
    }

    pub open spec fn get_from_in_use_success(paddr: Paddr, pre: MetaRegionOwners, post: MetaRegionOwners) -> bool
        recommends
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
            pre.inv(),
    {
        let idx = frame_to_index(paddr);
        let pre_perms = pre.slot_owners[idx].inner_perms.unwrap().ref_count.value();
        {
            &&& post.slot_owners[idx].inner_perms.unwrap().ref_count.value() == pre_perms + 1
            &&& post.slot_owners[idx].inner_perms.unwrap().ref_count.id() == pre.slot_owners[idx].inner_perms.unwrap().ref_count.id()
            &&& post.slot_owners[idx].inner_perms.unwrap().storage == pre.slot_owners[idx].inner_perms.unwrap().storage
            &&& post.slot_owners[idx].inner_perms.unwrap().vtable_ptr == pre.slot_owners[idx].inner_perms.unwrap().vtable_ptr
            &&& post.slot_owners[idx].inner_perms.unwrap().in_list == pre.slot_owners[idx].inner_perms.unwrap().in_list
            &&& post.slot_owners[idx].self_addr == pre.slot_owners[idx].self_addr
            &&& post.slot_owners[idx].usage == pre.slot_owners[idx].usage
            &&& post.slot_owners[idx].raw_count == pre.slot_owners[idx].raw_count
            &&& post.slot_owners[idx].path_if_in_pt == pre.slot_owners[idx].path_if_in_pt
            &&& forall|i: usize| i != idx ==> (#[trigger] post.slot_owners[i] == pre.slot_owners[i])
        }
    }

    pub open spec fn drop_last_in_place_safety_cond(owner: MetaSlotOwner) -> bool {
        &&& owner.inner_perms is Some
        &&& owner.inner_perms.unwrap().ref_count.value() == 0
        &&& owner.inner_perms.unwrap().storage.is_init()
        &&& owner.inner_perms.unwrap().in_list.value() == 0
        &&& owner.raw_count == 0
    }

    pub open spec fn inc_ref_count_spec(&self, pre: MetaSlotModel) -> (MetaSlotModel)
        recommends
            pre.inv(),
            pre.status == MetaSlotStatus::SHARED,
    {
        MetaSlotModel { ref_count: (pre.ref_count + 1) as u64, ..pre }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Frame<M> {
    pub open spec fn from_raw_spec(paddr: Paddr) -> Self {
        Frame::<M> {
            ptr: PPtr::<MetaSlot>(frame_to_meta(paddr), PhantomData),
            _marker: PhantomData,
        }
    }
}

} // verus!
