//! Embedding of `VmSpace`-level operations: creation and drop.
//!
//! Per-op steps operate on tracked owners directly — no store lookups,
//! no preconditions on store membership, no `if`-guards. The store-side
//! extract / insert and id-management lives in
//! [`super::VmStore`]'s methods and the [`super::step`] dispatcher.
use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::specs::mm::{
    frame::{
        mapping::frame_to_index, meta_owners::PageUsage, meta_region_owners::MetaRegionOwners,
    },
    page_table::cursor::owners::CursorOwner,
};

use crate::mm::{
    frame::meta::REF_COUNT_UNUSED,
    vm_space::{UserPtConfig, vm_space_specs::VmSpaceOwner},
};

verus! {

/// The metadata-slot index of a `VmSpace`'s page-table *root* node. This
/// is the slot whose perm `VmSpace::new` (`empty_with_owner`) permanently
/// extracts from `regions.slots` (the root is owned by the page table,
/// not parked in the free pool).
pub open spec fn vm_space_root_idx(owner: VmSpaceOwner) -> int {
    frame_to_index(owner.page_table_owner.value().meta_slot_paddr()->0)
}

// =============================================================================
// _embedded axiom
// =============================================================================
/// Mirror of [`crate::mm::vm_space::VmSpace::new`].
///
/// `metaregion_sound_preserves`: any `CursorOwner` sound w.r.t. the
/// old `regions` is still sound w.r.t. the new `regions`. Mirrors the
/// underlying `create_user_page_table` regions-preservation property.
pub axiom fn vm_space_new_embedded<'a>(tracked regions: &mut MetaRegionOwners) -> (tracked res:
    VmSpaceOwner)
    requires
        old(regions).inv(),
    ensures
        final(regions).inv(),
        res.inv(),
        // `VmSpace::new` (`create_user_page_table` → `empty_with_owner`)
        // allocates a fresh PT root and PERMANENTLY extracts its slot
        // perm from `regions.slots` (the root is owned by the page table,
        // not parked in the free pool). Every OTHER slot perm is
        // preserved. The extracted root slot is an active page-table node
        // (`usage == PageTable`, `rc != UNUSED`) — exactly the
        // `structural_inv` slot-perm coverage exception, so coverage
        // stays chainable. (Mirrors `empty_with_owner`'s ensures, which
        // removes `frame_to_index(root_paddr)` from `regions.slots`.)
        old(regions).slots.contains_key(vm_space_root_idx(res)),
        final(regions).slots == old(regions).slots.remove(vm_space_root_idx(res)),
        final(regions).slot_owners[vm_space_root_idx(res)].usage == PageUsage::PageTable,
        final(regions).slot_owners[vm_space_root_idx(res)].inner_perms.ref_count.value()
            != REF_COUNT_UNUSED,
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].inner_perms.in_list == old(
                regions,
            ).slot_owners[i].inner_perms.in_list,
        // Stage 5.3: `VmSpace::new` / `cursor` only allocate fresh PT
        // nodes — every *changed* slot was UNUSED before and becomes a
        // non-UNUSED PT node (`usage == PageTable`). `accounting_inv`
        // chains from this; the `usage == PageTable` strengthening also
        // feeds `structural_inv`'s slot-perm coverage exception.
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] != old(regions).slot_owners[i] ==> {
                &&& old(regions).slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].usage == PageUsage::PageTable
            },
        forall|c: CursorOwner<'a, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

// =============================================================================
// step proofs
// =============================================================================
/// Per-op step for `Op::NewVmSpace`. Produces a fresh tracked
/// `VmSpaceOwner` from the regions; the caller (the dispatcher in
/// [`super::step`]) is responsible for inserting it into the store
/// under a fresh id.
pub(super) proof fn new_vm_space_step<'a>(tracked regions: &mut MetaRegionOwners) -> (tracked res:
    VmSpaceOwner)
    requires
        old(regions).inv(),
    ensures
        final(regions).inv(),
        res.inv(),
        // `VmSpace::new` (`create_user_page_table` → `empty_with_owner`)
        // allocates a fresh PT root and PERMANENTLY extracts its slot
        // perm from `regions.slots` (the root is owned by the page table,
        // not parked in the free pool). Every OTHER slot perm is
        // preserved. The extracted root slot is an active page-table node
        // (`usage == PageTable`, `rc != UNUSED`) — exactly the
        // `structural_inv` slot-perm coverage exception, so coverage
        // stays chainable. (Mirrors `empty_with_owner`'s ensures, which
        // removes `frame_to_index(root_paddr)` from `regions.slots`.)
        old(regions).slots.contains_key(vm_space_root_idx(res)),
        final(regions).slots == old(regions).slots.remove(vm_space_root_idx(res)),
        final(regions).slot_owners[vm_space_root_idx(res)].usage == PageUsage::PageTable,
        final(regions).slot_owners[vm_space_root_idx(res)].inner_perms.ref_count.value()
            != REF_COUNT_UNUSED,
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].inner_perms.in_list == old(
                regions,
            ).slot_owners[i].inner_perms.in_list,
        // Stage 5.3: `VmSpace::new` / `cursor` only allocate fresh PT
        // nodes — every *changed* slot was UNUSED before and becomes a
        // non-UNUSED PT node (`usage == PageTable`). `accounting_inv`
        // chains from this; the `usage == PageTable` strengthening also
        // feeds `structural_inv`'s slot-perm coverage exception.
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] != old(regions).slot_owners[i] ==> {
                &&& old(regions).slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].usage == PageUsage::PageTable
            },
        forall|c: CursorOwner<'a, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    vm_space_new_embedded(regions)
}

/// Per-op step for `Op::DropVmSpace`. The caller has already extracted
/// the owner from the store; this function drops it (the value goes
/// out of scope at the end).
pub(super) proof fn drop_vm_space_step(tracked _owner: VmSpaceOwner) {
}

} // verus!
