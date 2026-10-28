use crate::specs::mm::frame::meta_owners::META_STORAGE_SIZE;
use vstd::{
    atomic::*,
    cell::pcell_maybe_uninit,
    prelude::*,
    simple_pptr::{PPtr, PointsTo},
};
use vstd_extra::substructural::{CellUnwrap, FieldSplit, StructToField};
use vstd_extra::typing::tagged::MaxSize;
use vstd_extra::{ownership::*, sum::Sum};

use crate::specs::{
    arch::*,
    mm::frame::{
        frame_specs::*,
        mapping::{frame_to_index, index_to_meta},
        meta_region_owners::MetaRegionOwners,
    },
};

use super::meta_owners::{
    FracMetadataPerm, MetaSlotOwner, MetaSlotStatus, MetaSlotStorage, MetadataPerm, PageUsage,
    recorded_meta_id, typed_meta_value, typed_meta_wf,
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

/// Identifies `storage` as the first field of a [`MetaSlot`].
impl StructToField for MetaSlot {
    type FirstField = pcell_maybe_uninit::PCell<MetaSlotStorage>;

    /// The three fields the metadata chain never touches. They are named only
    /// so that [`Self::combine`] can put them back unchanged.
    type Remainder = (PAtomicU64, PPtr<usize>, PAtomicU64);

    open spec fn split(self) -> (Self::FirstField, Self::Remainder) {
        (self.storage, (self.ref_count, self.vtable_ptr, self.in_list))
    }

    open spec fn combine(f: Self::FirstField, r: Self::Remainder) -> Self {
        MetaSlot { storage: f, ref_count: r.0, vtable_ptr: r.1, in_list: r.2 }
    }

    proof fn roundtrip(self) {
    }

    axiom fn split_first(tracked perm: PointsTo<MetaSlot>) -> (tracked res: (
        FieldSplit<MetaSlot, Self::Remainder>,
        PointsTo<Self::FirstField>,
    ));

    axiom fn combine_first(
        tracked rest: FieldSplit<MetaSlot, Self::Remainder>,
        tracked perm: PointsTo<Self::FirstField>,
    ) -> (tracked res: PointsTo<MetaSlot>);

    axiom fn borrow_first<'a>(tracked perm: &'a PointsTo<MetaSlot>) -> (tracked res: &'a PointsTo<
        Self::FirstField,
    >);

    axiom fn borrow_first_mut<'a>(tracked perm: &'a mut PointsTo<MetaSlot>) -> (tracked res:
        &'a mut PointsTo<Self::FirstField>);
}

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

    /// The slot's metadata storage, as a pointer permission at type `M`.
    ///
    /// The whole chain from [`vstd_extra::substructural`] in one step: step 1
    /// [`StructToField::borrow_first`] down to the storage cell, step 2
    /// [`CellUnwrap::unwrap_ref`] to its contents, step 3
    /// [`MetaSlotStorage::as_meta_perm`] to the `M` those bytes hold.
    ///
    /// A proof function rather than part of [`MetaSlot::as_meta_ptr`] because
    /// the *pointer* does not depend on how the metadata permission is
    /// borrowed, only the permission does. Keeping them apart lets
    /// `as_meta_ptr` be the single exec function upstream has, and puts the
    /// shared/exclusive split entirely in proof code -- here and in
    /// [`Self::meta_perm_mut`].
    pub proof fn meta_perm<'a, M: AnyFrameMeta + MaxSize<META_STORAGE_SIZE>>(
        tracked slot_perm: &'a PointsTo<MetaSlot>,
        tracked metadata_perm: &'a MetadataPerm,
    ) -> (tracked res: &'a PointsTo<M>)
        requires
            typed_meta_wf::<M>(*slot_perm, *metadata_perm),
        ensures
            res.addr() == slot_perm.addr(),
            res.is_init(),
            res.value() == typed_meta_value::<M>(*metadata_perm),
    {
        let tracked cell_perm = MetaSlot::borrow_first(slot_perm);
        let tracked storage_perm = MetaSlotStorage::unwrap_ref(
            cell_perm,
            &metadata_perm.storage_perm,
        );
        MetaSlotStorage::as_meta_perm::<M>(storage_perm)
    }

    /// [`Self::meta_perm`] for exclusive access.
    ///
    /// Only reachable with the whole [`MetadataPerm`], which is why it serves
    /// `UniqueFrame` and not `Frame`: a `Frame`'s permission is a
    /// `Count` fraction, and a fraction can only ever be borrowed shared.
    ///
    /// The `final` clauses carry the write back the other way: whatever the
    /// borrow ends up holding is what the slot holds, and it still holds an
    /// `M`.
    pub proof fn meta_perm_mut<'a, M: AnyFrameMeta + MaxSize<META_STORAGE_SIZE>>(
        tracked slot_perm: &'a PointsTo<MetaSlot>,
        tracked metadata_perm: &'a mut MetadataPerm,
    ) -> (tracked res: &'a mut PointsTo<M>)
        requires
            typed_meta_wf::<M>(*slot_perm, *old(metadata_perm)),
        ensures
            res.addr() == slot_perm.addr(),
            res.is_init(),
            res.value() == typed_meta_value::<M>(*old(metadata_perm)),
            final(res).is_init(),
            typed_meta_wf::<M>(*slot_perm, *final(metadata_perm)),
            typed_meta_value::<M>(*final(metadata_perm)) == final(res).value(),
    {
        let tracked cell_perm = MetaSlot::borrow_first(slot_perm);
        let tracked storage_perm = MetaSlotStorage::unwrap_mut(
            cell_perm,
            &mut metadata_perm.storage_perm,
        );
        MetaSlotStorage::as_meta_perm_mut::<M>(storage_perm)
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
    pub open spec fn get_from_unused_spec<M: AnyFrameMeta + MaxSize<META_STORAGE_SIZE>>(
        paddr: Paddr,
        metadata: M,
        as_unique: bool,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
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
        &&& metadata_perms.storage_perm.value().holds::<M>()
        &&& metadata_perms.storage_perm.value().value::<M>()
            == metadata
        // The recorded identity, beside the value it identifies. `write_meta` stamps
        // this when it installs the metadata; stating it here is what carries it out
        // through `get_from_unused` to callers that aggregate frames.
        &&& metadata_perms.meta_type_id == recorded_meta_id::<M>()
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
