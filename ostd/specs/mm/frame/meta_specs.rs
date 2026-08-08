use core::marker::PhantomData;

use vstd::prelude::*;

use vstd::{
    atomic::*,
    simple_pptr::{self, PPtr},
};
use vstd_extra::{cast_ptr::*, ownership::*};

use crate::specs::{
    arch::*,
    mm::frame::{
        mapping::{frame_to_index, index_to_meta},
        meta_region_owners::MetaRegionOwners,
    },
};

use crate::mm::{
    Paddr, PagingLevel, Vaddr,
    frame::{
        meta::{
            META_SLOT_SIZE, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
            mapping::{frame_to_meta, meta_to_frame},
        },
        *,
    },
    kspace::FRAME_METADATA_RANGE,
};

use super::meta_owners::{
    FracMetadataPerm, MetaSlotModel, MetaSlotOwner, MetaSlotStatus, MetaSlotStorage, MetadataPerms,
    PageUsage,
};

verus! {

global layout MetaSlot is size == 64, align == 8;

impl MetaSlot {
    pub proof fn lemma_layout()
        ensures
            core::mem::size_of::<MetaSlot>() == META_SLOT_SIZE,
            vstd::layout::size_of::<MetaSlot>() == META_SLOT_SIZE,
    {
        broadcast use VERUS_layout_of_MetaSlot;

    }

    pub open spec fn get_from_unused_owner_spec(as_unique: bool, owner: MetaSlotOwner) -> bool {
        &&& owner.ref_count() == (if as_unique {
            REF_COUNT_UNIQUE as u64
        } else {
            1u64
        })
        &&& owner.in_list_perm.value() == 0
        &&& owner.metadata_perm.frac() == (if as_unique {
            0int
        } else {
            (REF_COUNT_MAX - 1) as int
        })
        &&& as_unique ==> owner.metadata_perm.is_resource_vacant()
        &&& !as_unique ==> {
            &&& owner.storage_perm().is_init()
            &&& owner.vtable_ptr_perm().is_init()
        }
    }

    /// The metadata-region transition of claiming an unused slot.
    pub open spec fn get_from_unused_region_spec(
        paddr: Paddr,
        as_unique: bool,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool {
        let idx = frame_to_index(paddr);
        let pre_owner = pre.slot_owners[idx];
        let post_owner = post.slot_owners[idx];
        {
            &&& pre_owner.ref_count() == REF_COUNT_UNUSED
            &&& MetaSlot::get_from_unused_owner_spec(as_unique, post_owner)
            &&& post_owner.usage is Frame
            &&& post_owner.slot_vaddr == pre_owner.slot_vaddr
            &&& post_owner.paths_in_pt == pre_owner.paths_in_pt
            &&& post =~= pre.insert_slot_owner(paddr, post_owner)
        }
    }

    /// The complete successful result of claiming an unused slot, including
    /// the fraction returned to the new frame handle.
    pub open spec fn get_from_unused_spec<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        paddr: Paddr,
        metadata: M,
        as_unique: bool,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
        repr_perm: M::ReprPerm,
        permissions: (Option<FracMetadataPerm>, Option<MetadataPerms>),
    ) -> bool {
        let idx = frame_to_index(paddr);
        let metadata_perms = if as_unique {
            permissions.1->0
        } else {
            permissions.0->0.resource()
        };
        &&& Self::get_from_unused_region_spec(paddr, as_unique, pre, post)
        &&& as_unique ==> {
            &&& permissions.0 is None
            &&& permissions.1 is Some
        }
        &&& !as_unique ==> {
            &&& permissions.0 is Some
            &&& permissions.1 is None
            &&& permissions.0->0.frac() == 1
            &&& permissions.0->0.id() == post.slot_owners[idx].metadata_perm.id()
        }
        &&& metadata_perms.storage_perm.id() == post.slots[idx].value().storage.id()
        &&& metadata_perms.storage_perm.is_init()
        &&& metadata_perms.vtable_ptr_perm.pptr() == post.slots[idx].value().vtable_ptr
        &&& metadata_perms.vtable_ptr_perm.is_init()
        &&& <M as Repr<MetaSlotStorage>>::wf(metadata_perms.storage_perm.value(), repr_perm)
        &&& M::from_repr_spec(metadata_perms.storage_perm.value(), repr_perm) == metadata
    }

    /// Variant of [`get_from_unused_region_spec`] for allocating a page-table *node*
    /// (always non-unique). Identical except the claimed slot becomes
    /// `PageUsage::PageTable` rather than `PageUsage::Frame`: a page-table
    /// node is tracked with `PageTable` usage, which gives a clean
    /// usage-based discriminator between node slots and data-frame slots
    /// (the latter are `Frame`/MMIO). Used by the node allocators
    /// (`PageTableNode::alloc`, `PageTable::empty_with_owner`).
    pub open spec fn get_node_from_unused_spec(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool {
        let idx = frame_to_index(paddr);
        {
            &&& post.slot_owners.dom() =~= pre.slot_owners.dom()
            &&& MetaSlot::get_from_unused_owner_spec(false, post.slot_owners[idx])
            &&& post.slot_owners[idx].usage is PageTable
            &&& post.slot_owners[idx].slot_vaddr == pre.slot_owners[idx].slot_vaddr
            &&& post.slot_owners[idx].paths_in_pt == pre.slot_owners[idx].paths_in_pt
            &&& forall|i: int| i != idx ==> (#[trigger] post.slot_owners[i] == pre.slot_owners[i])
            &&& pre.slot_owners[idx].ref_count() == REF_COUNT_UNUSED
        }
    }

    /// Permission-location clause for the static `MetaSlot` permissions.
    /// They remain parked in `regions.slots`; `get_from_unused` only returns a
    /// fractional metadata permission. Pair this with
    /// [`get_from_unused_region_spec`] to fully describe the region post-state.
    pub open spec fn slot_perm_reparked_spec(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool {
        let idx = frame_to_index(paddr);
        &&& post.slots.dom() =~= pre.slots.dom()
        &&& forall|k: int|
            #![trigger post.slots[k]]
            k != idx && pre.contains(k) ==> post.slots[k] == pre.slots[k]
    }

    pub open spec fn inc_ref_count_panic_cond(rc_perm: PermissionU64) -> bool {
        rc_perm.value() >= REF_COUNT_MAX
    }

    pub open spec fn frame_paddr_safety_cond(perm: vstd::simple_pptr::PointsTo<MetaSlot>) -> bool {
        &&& FRAME_METADATA_RANGE.start <= perm.addr() < FRAME_METADATA_RANGE.end
        &&& perm.addr() % META_SLOT_SIZE == 0
    }

    pub open spec fn get_from_in_use_success(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool {
        let idx = frame_to_index(paddr);
        let pre_perms = pre.slot_owners[idx].ref_count();
        {
            &&& post.slot_owners[idx].ref_count() == pre_perms + 1
            &&& post.slot_owners[idx].ref_count_perm.id()
                == pre.slot_owners[idx].ref_count_perm.id()
            &&& post.slot_owners[idx].metadata_perm.id() == pre.slot_owners[idx].metadata_perm.id()
            &&& post.slot_owners[idx].metadata_perm.frac() + 1
                == pre.slot_owners[idx].metadata_perm.frac()
            &&& post.slot_owners[idx].metadata_perm@ == pre.slot_owners[idx].metadata_perm@
            &&& post.slot_owners[idx].in_list_perm == pre.slot_owners[idx].in_list_perm
            &&& post.slot_owners[idx].slot_vaddr == pre.slot_owners[idx].slot_vaddr
            &&& post.slot_owners[idx].usage == pre.slot_owners[idx].usage
            &&& post.slot_owners[idx].paths_in_pt == pre.slot_owners[idx].paths_in_pt
            &&& forall|i: int| i != idx ==> (#[trigger] post.slot_owners[i] == pre.slot_owners[i])
        }
    }

    pub open spec fn drop_last_in_place_safety_cond(owner: MetaSlotOwner) -> bool {
        &&& owner.ref_count() == 0
        &&& owner.metadata_perm.is_full()
        &&& owner.storage_perm().is_init()
        &&& owner.vtable_ptr_perm().is_init()
        &&& owner.in_list_perm.value()
            == 0
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
            #[cfg(verus_keep_ghost_body)]
            tracked_perm: Tracked(None),
        }
    }
}

} // verus!
