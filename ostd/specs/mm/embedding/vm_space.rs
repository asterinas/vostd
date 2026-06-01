//! Embedding of `VmSpace`-level operations: creation and drop.
//!
//! Per-op steps operate on tracked owners directly — no store lookups,
//! no preconditions on store membership, no `if`-guards. The store-side
//! extract / insert and id-management lives in
//! [`super::VmStore`]'s methods and the [`super::step`] dispatcher.
use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::mm::vm_space::vm_space_specs::VmSpaceOwner;
use crate::mm::vm_space::UserPtConfig;
use crate::specs::mm::frame::meta_owners::{PageUsage, REF_COUNT_UNUSED};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::owners::CursorOwner;

verus! {

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
        // `VmSpace::new` (`create_user_page_table`) allocates a fresh
        // page table; it never touches the boot-fixed metadata slot-perm
        // map nor the `raw_count` / `in_list` fields. Preserving the
        // `slots` domain (#2 / #3b) and `raw_count` / `in_list` (#4
        // partial) keeps `VmStore::inv`'s coverage clauses chainable.
        final(regions).slots =~= old(regions).slots,
        forall|i: usize| #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].raw_count == old(regions).slot_owners[i].raw_count
            && final(regions).slot_owners[i].inner_perms.in_list
                == old(regions).slot_owners[i].inner_perms.in_list,
        // Stage 5.3: `VmSpace::new` / `cursor` only allocate fresh PT
        // nodes — every *changed* slot was UNUSED before and becomes a
        // non-UNUSED PT node (usage != Frame). `accounting_inv` chains
        // from this single clause.
        forall|i: usize| #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] != old(regions).slot_owners[i] ==> {
                &&& old(regions).slot_owners[i].inner_perms.ref_count.value()
                        == REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value()
                        != REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].usage != PageUsage::Frame
            },
        forall|c: CursorOwner<'a, UserPtConfig>| #![auto]
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
        // `VmSpace::new` (`create_user_page_table`) allocates a fresh
        // page table; it never touches the boot-fixed metadata slot-perm
        // map nor the `raw_count` / `in_list` fields. Preserving the
        // `slots` domain (#2 / #3b) and `raw_count` / `in_list` (#4
        // partial) keeps `VmStore::inv`'s coverage clauses chainable.
        final(regions).slots =~= old(regions).slots,
        forall|i: usize| #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].raw_count == old(regions).slot_owners[i].raw_count
            && final(regions).slot_owners[i].inner_perms.in_list
                == old(regions).slot_owners[i].inner_perms.in_list,
        // Stage 5.3: `VmSpace::new` / `cursor` only allocate fresh PT
        // nodes — every *changed* slot was UNUSED before and becomes a
        // non-UNUSED PT node (usage != Frame). `accounting_inv` chains
        // from this single clause.
        forall|i: usize| #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] != old(regions).slot_owners[i] ==> {
                &&& old(regions).slot_owners[i].inner_perms.ref_count.value()
                        == REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value()
                        != REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].usage != PageUsage::Frame
            },
        forall|c: CursorOwner<'a, UserPtConfig>| #![auto]
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
