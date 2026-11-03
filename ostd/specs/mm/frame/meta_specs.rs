use vstd::{atomic::*, prelude::*, simple_pptr::PointsTo};
use vstd_extra::{cast_ptr::*, ownership::*, sum::Sum};

use crate::specs::{
    arch::*,
    mm::frame::{
        frame_specs::*,
        mapping::{frame_to_index, index_to_meta},
        meta_region_owners::MetaRegionOwners,
    },
};

use super::meta_owners::{
    FracMetadataPerm, MetaSlotOwner, MetaSlotStorage, MetadataPerm, PageUsage,
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

verus! {

global layout MetaSlot is size == 64, align == 8;

impl MetaSlot {
    /// The relation between the [`MetaSlot`] permission and a metadata permission fraction.
    #[verifier::inline]
    pub open spec fn perms_related(
        slot_perm: PointsTo<MetaSlot>,
        metadata_perm: MetadataPerm,
    ) -> bool {
        &&& metadata_perm.storage_perm.is_init()
        &&& metadata_perm.vtable_ptr_perm.is_init()
        &&& slot_perm.value().storage.id() == metadata_perm.storage_perm.id()
        &&& slot_perm.value().vtable_ptr == metadata_perm.vtable_ptr_perm.pptr()
    }

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
            REF_COUNT_MAX - 1
        })
        &&& as_unique ==> owner.metadata_perm.is_resource_vacant()
        &&& !as_unique ==> {
            &&& owner.storage_perm().is_init()
            &&& owner.vtable_ptr_perm().is_init()
        }
    }

    /// The metadata region transition of claiming an unused slot.
    pub open spec fn claim_unused_slot_region_spec(
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
            &&& post_owner.slot_vaddr == pre_owner.slot_vaddr
            &&& post =~= pre.insert_slot_owner(paddr, post_owner)
        }
    }

    /// The metadata region transition of claiming an unused slot for a frame.
    pub open spec fn get_from_unused_region_spec(
        paddr: Paddr,
        as_unique: bool,
        usage: PageUsage,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool {
        let idx = frame_to_index(paddr);
        &&& Self::claim_unused_slot_region_spec(paddr, as_unique, pre, post)
        &&& post.slot_owners[idx].usage == usage
        &&& post.slot_owners[idx].paths_in_pt == pre.slot_owners[idx].paths_in_pt
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
        permission: Sum<FracMetadataPerm, MetadataPerm>,
    ) -> bool {
        let idx = frame_to_index(paddr);
        let metadata_perms = match permission {
            Sum::Left(permission) => permission.resource(),
            Sum::Right(permission) => permission,
        };
        &&& Self::get_from_unused_region_spec(paddr, as_unique, metadata_perms.usage(), pre, post)
        &&& as_unique ==> permission is Right
        &&& !as_unique ==> {
            &&& permission is Left
            &&& permission->Left_0.frac() == 1
            &&& permission->Left_0.id() == post.slot_owners[idx].metadata_perm.id()
        }
        &&& Self::perms_related(*post.slots[idx], metadata_perms)
        &&& <M as Repr<MetaSlotStorage>>::wf(metadata_perms.storage_perm.value(), repr_perm)
        &&& M::from_repr_spec(metadata_perms.storage_perm.value(), repr_perm) == metadata
    }

    pub open spec fn inc_ref_count_panic_cond(rc_perm: PermissionU64) -> bool {
        rc_perm.value() >= REF_COUNT_MAX
    }

    pub open spec fn frame_paddr_safety_cond(perm: PointsTo<MetaSlot>) -> bool {
        &&& FRAME_METADATA_RANGE.start <= perm.addr() < FRAME_METADATA_RANGE.end
        &&& perm.addr() % META_SLOT_SIZE == 0
    }

    pub open spec fn get_from_in_use_success_spec(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
        metadata_perm: FracMetadataPerm,
    ) -> bool {
        let idx = frame_to_index(paddr);
        {
            &&& pre.inc_frame_reference_region_spec(paddr, post)
            &&& metadata_perm.frac() == 1
            &&& metadata_perm.id() == post.slot_owners[idx].metadata_perm.id()
            &&& Self::perms_related(*post.slots[idx], metadata_perm.resource())
        }
    }

    pub open spec fn drop_last_in_place_safety_cond(owner: MetaSlotOwner) -> bool {
        &&& (owner.ref_count() == 0 || owner.ref_count() == REF_COUNT_UNIQUE)
        &&& owner.metadata_perm.is_full()
        &&& owner.storage_perm().is_init()
        &&& owner.vtable_ptr_perm().is_init()
        &&& owner.in_list_perm.value() == 0
        &&& owner.paths_in_pt.is_empty()
    }
}

} // verus!
