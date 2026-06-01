use vstd::atomic::*;
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
use crate::specs::mm::frame::meta_owners::MetadataInnerPerms;
use crate::specs::mm::frame::meta_region_owners::{MetaRegionModel, MetaRegionOwners};

use core::marker::PhantomData;

verus! {

impl MetaSlot {
    pub open spec fn get_from_unused_inner_perms_spec(
        as_unique: bool,
        perms: MetadataInnerPerms,
    ) -> bool {
        &&& perms.ref_count.value() == (if as_unique {
            REF_COUNT_UNIQUE as u64
        } else {
            1u64
        })
        &&& perms.in_list.value() == 0
        &&& perms.storage.is_init()
        &&& perms.vtable_ptr.is_init()
    }

    pub open spec fn get_from_unused_spec(
        paddr: Paddr,
        as_unique: bool,
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
            &&& post.slot_owners.dom() =~= pre.slot_owners.dom()
            &&& MetaSlot::get_from_unused_inner_perms_spec(
                as_unique,
                post.slot_owners[idx].inner_perms,
            )
            &&& post.slot_owners[idx].usage == PageUsage::Frame
            &&& post.slot_owners[idx].raw_count == pre.slot_owners[idx].raw_count
            &&& post.slot_owners[idx].self_addr == pre.slot_owners[idx].self_addr
            &&& post.slot_owners[idx].paths_in_pt == pre.slot_owners[idx].paths_in_pt
            &&& forall|i: usize| i != idx ==> (#[trigger] post.slot_owners[i] == pre.slot_owners[i])
            &&& pre.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNUSED
        }
    }

    /// Design-B variant of [`get_from_unused_spec`]: models the
    /// post-state *after the caller re-parks* the returned slot perm
    /// into `regions.slots` (see [`crate::mm::frame::Frame::from_unused`]
    /// — it hands the perm back via the `perm` out-param and the caller
    /// re-inserts it). The only difference from [`get_from_unused_spec`]
    /// is the `slots` clause: the domain is *preserved* (`pre.slots.dom()`)
    /// rather than `pre.slots.remove(idx)`, since the perm is immediately
    /// re-inserted. All `slot_owners` transitions are identical.
    pub open spec fn get_from_unused_reparked_spec(
        paddr: Paddr,
        as_unique: bool,
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
            &&& post.slots.dom() =~= pre.slots.dom()
            &&& forall|k: usize| #![trigger post.slots[k]]
                k != idx && pre.slots.contains_key(k) ==> post.slots[k] == pre.slots[k]
            &&& post.slot_owners.dom() =~= pre.slot_owners.dom()
            &&& MetaSlot::get_from_unused_inner_perms_spec(
                as_unique,
                post.slot_owners[idx].inner_perms,
            )
            &&& post.slot_owners[idx].usage == PageUsage::Frame
            &&& post.slot_owners[idx].raw_count == pre.slot_owners[idx].raw_count
            &&& post.slot_owners[idx].self_addr == pre.slot_owners[idx].self_addr
            &&& post.slot_owners[idx].paths_in_pt == pre.slot_owners[idx].paths_in_pt
            &&& forall|i: usize| i != idx ==> (#[trigger] post.slot_owners[i] == pre.slot_owners[i])
            &&& pre.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNUSED
        }
    }

    pub open spec fn get_from_unused_perm_spec<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        paddr: Paddr,
        metadata: M,
        as_unique: bool,
        ptr: PPtr<MetaSlot>,
        perm: simple_pptr::PointsTo<MetaSlot>,
    ) -> bool {
        &&& ptr.addr() == frame_to_meta(paddr)
        &&& perm.addr() == frame_to_meta(paddr)
        &&& perm.is_init()
        &&& perm.pptr() == ptr
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
        let pre_perms = regions.slot_owners[idx].inner_perms.ref_count.value();
        pre_perms + 1 >= REF_COUNT_MAX
    }

    pub open spec fn get_from_in_use_success(
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
        let pre_perms = pre.slot_owners[idx].inner_perms.ref_count.value();
        {
            &&& post.slot_owners[idx].inner_perms.ref_count.value() == pre_perms + 1
            &&& post.slot_owners[idx].inner_perms.ref_count.id()
                == pre.slot_owners[idx].inner_perms.ref_count.id()
            &&& post.slot_owners[idx].inner_perms.storage
                == pre.slot_owners[idx].inner_perms.storage
            &&& post.slot_owners[idx].inner_perms.vtable_ptr
                == pre.slot_owners[idx].inner_perms.vtable_ptr
            &&& post.slot_owners[idx].inner_perms.in_list
                == pre.slot_owners[idx].inner_perms.in_list
            &&& post.slot_owners[idx].self_addr == pre.slot_owners[idx].self_addr
            &&& post.slot_owners[idx].usage == pre.slot_owners[idx].usage
            &&& post.slot_owners[idx].raw_count == pre.slot_owners[idx].raw_count
            &&& post.slot_owners[idx].paths_in_pt == pre.slot_owners[idx].paths_in_pt
            &&& forall|i: usize| i != idx ==> (#[trigger] post.slot_owners[i] == pre.slot_owners[i])
        }
    }

    pub open spec fn drop_last_in_place_safety_cond(owner: MetaSlotOwner) -> bool {
        &&& (owner.inner_perms.ref_count.value() == 0 || owner.inner_perms.ref_count.value()
            == REF_COUNT_UNIQUE)
        &&& owner.inner_perms.storage.is_init()
        &&& owner.inner_perms.in_list.value() == 0
        &&& owner.raw_count == 0
        // The slot is torn down to `REF_COUNT_UNUSED`; the strengthened
        // `MetaSlotOwner::inv` UNUSED branch requires an empty
        // `paths_in_pt`, and `drop_last_in_place` does not touch
        // `paths_in_pt`, so it must already be empty. Sound: a slot at
        // the teardown point has no live PTE mapping (a mapping is a
        // reference — it would keep the count above the teardown
        // threshold).
        &&& owner.paths_in_pt.is_empty()
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
