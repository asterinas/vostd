//! Embedding of `Cursor` / `CursorMut` operations: open, drop,
//! navigation (query/find_next/jump), and mutation
//! (map/unmap/protect_next).
//!
//! Per-op steps operate on tracked owners directly — no store lookups,
//! no preconditions on store membership, no `if`-guards. The store-side
//! extract / insert and id-management lives in
//! [`super::VmStore`]'s methods and the [`super::step`] dispatcher.
//!
//! # Mirroring exec preconditions
//!
//! Each `_embedded` axiom carries the same `requires` as its exec
//! counterpart, expressed against our model. The expressible parts are:
//!
//! - `owner.inv()`, `owner.children_not_locked(guards)`,
//!   `owner.nodes_locked(guards)`, `!owner.popped_too_high` —
//!   bundled as `CursorEntry::inv` (entry-side); see [`super::CursorEntry`].
//! - `owner.in_locked_range()` — NOT a precondition of `query`, `jump`,
//!   or `map`: each handles an out-of-range cursor itself (graceful
//!   `Err` for `query`; a faithful `panic_diverge` otherwise) and
//!   re-derives `in_locked_range` internally. `protect_next` still
//!   requires it; see exec clauses.
//! - `regions.inv()`, `owner.metaregion_sound(regions)` — passed via
//!   `&mut regions`.
//! - `tlb_model.inv()` — passed via `&mut tlb_model` to `map` / `unmap`.
//!
//! # Model gaps
//!
//! - **Exec `Cursor` handle**: the exec `Cursor::invariants` requires
//!   `self.inv()` and `self.wf(owner)` over the runtime `Cursor`
//!   struct. Our embedding doesn't carry that handle (it's tied to the
//!   `&'rcu RCU guard` reference, not constructible in pure ghost
//!   mode), so these conjuncts are MODEL GAPS. Owner-side state
//!   already mirrors handle state (`owner.va`, `owner.level`,
//!   `owner.guard_level`), so `wf(owner)` is essentially tautological
//!   if we postulate the handle's existence; `inv()` follows from
//!   `owner.inv()` plus this projection.
//! - **`item_wf` on map**: the exec [`crate::mm::vm_space::CursorMut::map`]
//!   requires `old(self).item_wf(frame, prop, entry_owner, *old(regions))`,
//!   which constrains a separate `EntryOwner<UserPtConfig>` argument
//!   produced by cursor traversal. We don't model `EntryOwner` here.
//! - **`protect_next` closure preconditions**: the exec method takes a
//!   closure `op: impl FnOnce(PageProperty) -> PageProperty` with
//!   `forall |p| op.requires((p,))` plus a trackedness-preservation
//!   constraint. Our `Op::ProtectNext` doesn't carry the closure.
use core::ops::Range;

use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::mm::frame::{has_safe_slot, UFrame};
use crate::mm::page_prop::PageProperty;
use crate::mm::vm_space::vm_space_specs::VmSpaceOwner;
use crate::mm::vm_space::UserPtConfig;
use crate::mm::{Paddr, Vaddr};
use crate::specs::mm::frame::mapping::frame_to_index_spec;
use crate::specs::mm::frame::meta_owners::{
    PageUsage, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::owners::CursorOwner;
use crate::specs::mm::page_table::node::Guards;
use crate::specs::mm::tlb::TlbModel;

use super::{axiom_cursor_entry_new, CursorEntry, CursorKind, VmSpaceId};

verus! {

// =============================================================================
// _embedded axioms
// =============================================================================
/// Mirror of [`crate::mm::vm_space::VmSpace::cursor`].
///
/// The exec method mutates `&mut Guards` (adding locks for the new
/// cursor) and `&mut MetaRegionOwners`. Here, since each `CursorEntry`
/// carries its own self-contained `Guards` (a per-cursor model
/// restriction; see module-level docs), we *return* a fresh `Guards`
/// alongside the owner instead of mutating a shared one.
///
/// The `metaregion_sound_preserves` ensures clause says that any
/// `CursorOwner` that was sound w.r.t. the old `regions` is still
/// sound w.r.t. the new `regions`. This mirrors the exec
/// `PageTable::cursor` ensures that preserves `paths_in_pt` and
/// non-saturation across all slots ([page_table/mod.rs:1599-1661]).
pub axiom fn vm_space_cursor_embedded<'a, 'rcu>(
    tracked vm_space: &VmSpaceOwner,
    tracked regions: &mut MetaRegionOwners,
    va: Range<Vaddr>,
) -> (tracked res: Option<(CursorOwner<'rcu, UserPtConfig>, Guards<'rcu>)>)
    requires
        vm_space.inv(),
        old(regions).inv(),
    ensures
        final(regions).inv(),
        // Page-table cursor ops never touch the metadata slot-perm map
        // (`slots` is the boot-fixed metadata region) nor the
        // ManuallyDrop `raw_count` / free-list `in_list` fields; only
        // `slot_owners` refcount / `paths_in_pt` changes. Preserving the
        // `slots` domain (#2 / #3b) and `raw_count` / `in_list` (#4
        // partial) keeps `VmStore::inv`'s coverage clauses chainable
        // across cursor methods.
        final(regions).slots =~= old(regions).slots,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].raw_count == old(regions).slot_owners[i].raw_count
                && final(regions).slot_owners[i].inner_perms.in_list == old(
                regions,
            ).slot_owners[i].inner_perms.in_list,
        // Stage 5.3: opening a cursor only allocates fresh PT nodes —
        // every *changed* slot was UNUSED before and becomes a
        // non-UNUSED PT node (usage != Frame). `accounting_inv` chains
        // from this single clause.
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] != old(regions).slot_owners[i] ==> {
                &&& old(regions).slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].usage != PageUsage::Frame
            },
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
        res matches Some((c, g)) ==> {
            &&& c.inv()
            &&& c.children_not_locked(g)
            &&& c.nodes_locked(g)
            &&& !c.popped_too_high
            &&& c.metaregion_sound(*final(regions))
        },
;

/// Mirror of [`crate::mm::vm_space::VmSpace::cursor_mut`].
pub axiom fn vm_space_cursor_mut_embedded<'a, 'rcu>(
    tracked vm_space: &VmSpaceOwner,
    tracked regions: &mut MetaRegionOwners,
    va: Range<Vaddr>,
) -> (tracked res: Option<(CursorOwner<'rcu, UserPtConfig>, Guards<'rcu>)>)
    requires
        vm_space.inv(),
        old(regions).inv(),
    ensures
        final(regions).inv(),
        // Page-table cursor ops never touch the metadata slot-perm map
        // (`slots` is the boot-fixed metadata region) nor the
        // ManuallyDrop `raw_count` / free-list `in_list` fields; only
        // `slot_owners` refcount / `paths_in_pt` changes. Preserving the
        // `slots` domain (#2 / #3b) and `raw_count` / `in_list` (#4
        // partial) keeps `VmStore::inv`'s coverage clauses chainable
        // across cursor methods.
        final(regions).slots =~= old(regions).slots,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].raw_count == old(regions).slot_owners[i].raw_count
                && final(regions).slot_owners[i].inner_perms.in_list == old(
                regions,
            ).slot_owners[i].inner_perms.in_list,
        // Stage 5.3: opening a cursor only allocates fresh PT nodes —
        // every *changed* slot was UNUSED before and becomes a
        // non-UNUSED PT node (usage != Frame). `accounting_inv` chains
        // from this single clause.
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] != old(regions).slot_owners[i] ==> {
                &&& old(regions).slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].usage != PageUsage::Frame
            },
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
        res matches Some((c, g)) ==> {
            &&& c.inv()
            &&& c.children_not_locked(g)
            &&& c.nodes_locked(g)
            &&& !c.popped_too_high
            &&& c.metaregion_sound(*final(regions))
        },
;

/// Mirror of [`crate::mm::vm_space::Cursor::query`] /
/// [`crate::mm::vm_space::CursorMut::query`].
///
/// Exec requires `invariants(owner, regions, guards)`. It does **not**
/// require `owner.in_locked_range()`: an out-of-range cursor is handled
/// by `Cursor::query`'s graceful `Err` (the exec `requires` was relaxed
/// accordingly; `in_locked_range` now only governs success, not safety).
///
/// `metaregion_sound_preserves`: a `CursorOwner` that was sound w.r.t.
/// the old `regions` is still sound w.r.t. the new `regions`. This
/// keeps `VmStore::inv` chainable across method calls that touch
/// regions.
///
/// **Result `Some(paddr)` / `None`.** Exec `query` returns
/// `(Range<Vaddr>, Option<MappedItem>)`. When the inner `Option` is
/// `Some(item)` and the item is *tracked* (non-MMIO), exec
/// `clone_item` bumps `rc` at the leaf slot by one. The returned
/// `Paddr` here is the cloned leaf's physical address (i.e. the
/// new handle the caller now logically owns); the embedding's
/// [`step_query`] registers a fresh [`FrameEntry`] at that paddr
/// to keep `accounting_inv`'s `rc == H + P` chained. `None` covers
/// three cases: query returned `Err` (out of range), query returned
/// `Ok(_, None)` (cursor not at a leaf), or query returned a `Some`
/// non-tracked (MMIO) item (`clone_item` is a no-op for those).
/// In all three `None` subcases `slot_owners` is fully preserved.
pub axiom fn cursor_query_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    tracked regions: &mut MetaRegionOwners,
    tracked guards: &mut Guards<'rcu>,
) -> (res: Option<Paddr>)
    requires
        old(owner).inv(),
        old(regions).inv(),
        old(owner).children_not_locked(*old(guards)),
        old(owner).nodes_locked(*old(guards)),
        old(owner).metaregion_sound(*old(regions)),
        !old(owner).popped_too_high,
    ensures
        final(owner).inv(),
        final(regions).inv(),
        final(owner).children_not_locked(*final(guards)),
        final(owner).nodes_locked(*final(guards)),
        final(owner).metaregion_sound(*final(regions)),
        !final(owner).popped_too_high,
        // `slots` preserved (the boot-fixed metadata perm map).
        final(regions).slots =~= old(regions).slots,
        // `None` ⟹ slot_owners fully preserved (no clone happened).
        res is None ==> forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] == old(regions).slot_owners[i],
        // `Some(paddr)` ⟹ `rc++` at the cloned leaf's slot; all other
        // slots fully preserved. The cloned leaf must be a tracked
        // (non-MMIO) data Frame whose slot is in-bound and active.
        res matches Some(paddr) ==> {
            &&& has_safe_slot(paddr)
            &&& old(regions).slot_owners[frame_to_index_spec(paddr)].usage == PageUsage::Frame
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value()
                == (old(regions).slot_owners[frame_to_index_spec(
                paddr,
            )].inner_perms.ref_count.value() + 1) as nat
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value()
                <= REF_COUNT_MAX
            &&& forall|i: usize|
                #![trigger final(regions).slot_owners[i]]
                i != frame_to_index_spec(paddr) ==> final(regions).slot_owners[i] == old(
                    regions,
                ).slot_owners[i]
            // At the cloned slot, only `ref_count` changes — everything
            // else (`raw_count`, `in_list`, `usage`, `paths_in_pt`,
            // `storage`, `self_addr`, `vtable_ptr`) is preserved.
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].raw_count == old(
                regions,
            ).slot_owners[frame_to_index_spec(paddr)].raw_count
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].self_addr == old(
                regions,
            ).slot_owners[frame_to_index_spec(paddr)].self_addr
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].usage == old(
                regions,
            ).slot_owners[frame_to_index_spec(paddr)].usage
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].paths_in_pt == old(
                regions,
            ).slot_owners[frame_to_index_spec(paddr)].paths_in_pt
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.in_list == old(
                regions,
            ).slot_owners[frame_to_index_spec(paddr)].inner_perms.in_list
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.storage == old(
                regions,
            ).slot_owners[frame_to_index_spec(paddr)].inner_perms.storage
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.vtable_ptr
                == old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.vtable_ptr
        },
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::vm_space::Cursor::find_next`] /
/// [`crate::mm::vm_space::CursorMut::find_next`].
///
/// Exec requires `invariants(owner, regions, guards)`. Does NOT
/// require `in_locked_range()` (the method itself navigates from
/// wherever the cursor sits).
pub axiom fn cursor_find_next_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    tracked regions: &mut MetaRegionOwners,
    tracked guards: &mut Guards<'rcu>,
    len: usize,
)
    requires
        old(owner).inv(),
        old(regions).inv(),
        old(owner).children_not_locked(*old(guards)),
        old(owner).nodes_locked(*old(guards)),
        old(owner).metaregion_sound(*old(regions)),
        !old(owner).popped_too_high,
    ensures
        final(owner).inv(),
        final(regions).inv(),
        final(owner).children_not_locked(*final(guards)),
        final(owner).nodes_locked(*final(guards)),
        final(owner).metaregion_sound(*final(regions)),
        !final(owner).popped_too_high,
        // `find_next` navigates the cursor's internal `path` state but
        // does *not* touch any frame slot — it neither clones a leaf
        // frame (only `query` may do that) nor writes a PTE. So the
        // entire `slot_owners` map is preserved, which subsumes the
        // earlier `raw_count` / `in_list` clauses and lets
        // `accounting_inv` chain across this axiom.
        final(regions).slots =~= old(regions).slots,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] == old(regions).slot_owners[i],
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::vm_space::Cursor::jump`] /
/// [`crate::mm::vm_space::CursorMut::jump`].
///
/// Exec requires `invariants(owner, regions, guards)` (which includes
/// `!owner.popped_too_high`). It does **not** require
/// `owner.in_locked_range()`: the exec `requires` was relaxed. A drifted
/// cursor that cannot be repositioned within the target node aborts the
/// program (a sound `panic_diverge`, mirroring the real `pop_level`
/// `unwrap` panic), so an out-of-range cursor is a safety non-issue —
/// `in_locked_range` now only governs the success postcondition, and
/// this axiom soundly models the returning path.
pub axiom fn cursor_jump_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    tracked regions: &mut MetaRegionOwners,
    tracked guards: &mut Guards<'rcu>,
    va: Vaddr,
)
    requires
        old(owner).inv(),
        old(regions).inv(),
        old(owner).children_not_locked(*old(guards)),
        old(owner).nodes_locked(*old(guards)),
        old(owner).metaregion_sound(*old(regions)),
        !old(owner).popped_too_high,
    ensures
        final(owner).inv(),
        final(regions).inv(),
        final(owner).children_not_locked(*final(guards)),
        final(owner).nodes_locked(*final(guards)),
        final(owner).metaregion_sound(*final(regions)),
        !final(owner).popped_too_high,
        // `jump` repositions the cursor but touches no frame slot — no
        // PTE writes, no leaf clone. Full `slot_owners` preservation,
        // same shape as `find_next`.
        final(regions).slots =~= old(regions).slots,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] == old(regions).slot_owners[i],
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::vm_space::CursorMut::map`].
///
/// Exec requires:
/// - `tlb_model.inv()`
/// - `invariants(cursor_owner, regions, guards)` (incl. `!popped_too_high`)
/// - `item_wf(frame, prop, entry_owner, regions)` — MODEL GAP.
///
/// Does **not** require `in_locked_range()`: an out-of-range cursor
/// panics at `map`'s `assert!(va < barrier_va.end)` (the real
/// `map_panic_conditions` out-of-range abort); the exec re-derives
/// `in_locked_range` from that panic + the cursor invariant. This axiom
/// soundly models the returning path.
pub axiom fn cursor_mut_map_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    tracked regions: &mut MetaRegionOwners,
    tracked guards: &mut Guards<'rcu>,
    tracked tlb_model: &mut TlbModel,
    paddr: Paddr,
    prop: PageProperty,
)
    requires
        old(owner).inv(),
        old(regions).inv(),
        old(owner).children_not_locked(*old(guards)),
        old(owner).nodes_locked(*old(guards)),
        old(owner).metaregion_sound(*old(regions)),
        !old(owner).popped_too_high,
        old(tlb_model).inv(),
        // The mapped paddr is page-aligned and in-bounds (these come
        // from a consumed `FrameEntry`'s paddr; `has_safe_slot` is
        // guaranteed by the embedding's structural_inv `frames` clause).
        has_safe_slot(
            paddr,
        ),
// MODEL GAP: `item_wf(frame, prop, entry_owner, regions)`
// depends on a separate `EntryOwner<UserPtConfig>` arg we don't
// model. The exec call assumes the caller supplies one.

    ensures
        final(owner).inv(),
        final(regions).inv(),
        final(owner).children_not_locked(*final(guards)),
        final(owner).nodes_locked(*final(guards)),
        final(owner).metaregion_sound(*final(regions)),
        !final(owner).popped_too_high,
        final(tlb_model).inv(),
        final(regions).slots =~= old(regions).slots,
        // Universal `raw_count` / `in_list` preservation (map doesn't
        // forget references or touch the free-list).
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].raw_count == old(regions).slot_owners[i].raw_count
                && final(regions).slot_owners[i].inner_perms.in_list == old(
                regions,
            ).slot_owners[i].inner_perms.in_list,
        // Per exec cursor/mod.rs:2853 + 2836: at non-mapped slots that
        // were already in use (pre rc != UNUSED), the entire
        // slot_owner is preserved. NB: slots that were UNUSED pre may
        // transition to non-UNUSED as the cursor allocates fresh PT
        // nodes, so the "fully preserved" guard requires `pre rc != UNUSED`.
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index_spec(paddr) && old(
                regions,
            ).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
        // Per exec cursor/mod.rs:2844-2846: any pre-non-UNUSED slot
        // stays non-UNUSED.
        forall|i: usize|
            #![trigger final(regions).slot_owners[i].inner_perms.ref_count.value()]
            old(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                ==> final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED,
        // **`ref_count` PRESERVED at the mapped slot.** Faithful axiom
        // strengthening relative to the exec contract (which only says
        // `pre rc > 0 ⟹ post rc > 0`): exec map `ManuallyDrop`s the
        // input UFrame (so its handle's ref-count contribution stays
        // put rather than running `Drop`) and writes a PTE pointing to
        // the frame; the UFrame's ref is "transferred" to the new PTE,
        // net zero rc change. Combined with `Op::Map` consuming the
        // corresponding `FrameEntry` (`H_post = H_pre - 1`) and
        // `paths_in_pt += {cursor.path}` at the mapped slot
        // (`P_post = P_pre + 1`), `accounting_inv` clause 4
        // (`rc == H + P`) chains: `pre rc == pre H + pre P` ⟹
        // `post rc = pre rc = (H_post + 1) + (P_post - 1) = H_post + P_post`.
        final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value() == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value(),
        // **`paths_in_pt.len() += 1` at the mapped slot.** The cursor's
        // current path is inserted into the mapped slot's `paths_in_pt`
        // (this is the bookkeeping side of writing the PTE; see
        // [cursor/mod.rs:2613] for the exec insertion site).
        final(regions).slot_owners[frame_to_index_spec(paddr)].paths_in_pt.len() == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].paths_in_pt.len() + 1,
        // **`usage` / `storage` PRESERVED at the mapped slot.** Map
        // doesn't change the slot's identity or metadata — it only
        // updates the PTE and the bookkeeping `paths_in_pt`.
        final(regions).slot_owners[frame_to_index_spec(paddr)].usage == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].usage,
        final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.storage == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].inner_perms.storage,
        // Slots that stay UNUSED are fully preserved.
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
        // **Changed-slots clause.** At any slot *other* than the
        // mapped frame, a pre-UNUSED → post-non-UNUSED transition
        // means the cursor allocated a fresh PT node (not a data
        // frame), so `usage != Frame`. Combined with the other clauses
        // this lets `accounting_inv`'s Frame-scoped clauses 3 and 4
        // become vacuous at newly-allocated PT-node slots; the
        // mapped slot itself is handled by the per-slot ensures
        // above.
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index_spec(paddr) && old(
                regions,
            ).slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                && final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                ==> final(regions).slot_owners[i].usage != PageUsage::Frame,
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::vm_space::CursorMut::unmap`].
///
/// Exec requires (line 865-866):
/// - `invariants(cursor_owner, regions, guards)`
/// - `tlb_model.inv()`
///
/// Does NOT require `in_locked_range()` (the method walks `len` bytes
/// from the cursor, advancing into the locked range as needed).
pub axiom fn cursor_mut_unmap_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    tracked regions: &mut MetaRegionOwners,
    tracked guards: &mut Guards<'rcu>,
    tracked tlb_model: &mut TlbModel,
    len: usize,
)
    requires
        old(owner).inv(),
        old(regions).inv(),
        old(owner).children_not_locked(*old(guards)),
        old(owner).nodes_locked(*old(guards)),
        old(owner).metaregion_sound(*old(regions)),
        !old(owner).popped_too_high,
        old(tlb_model).inv(),
    ensures
        final(owner).inv(),
        final(regions).inv(),
        final(owner).children_not_locked(*final(guards)),
        final(owner).nodes_locked(*final(guards)),
        final(owner).metaregion_sound(*final(regions)),
        !final(owner).popped_too_high,
        final(tlb_model).inv(),
        // `slots` (the boot-fixed metadata perm map) preserved.
        final(regions).slots =~= old(regions).slots,
        // **Universal per-slot preservation.** Unmap doesn't change a
        // slot's identity (`usage`/`self_addr`/`raw_count`/`in_list`/
        // `vtable_ptr`) and never bumps `rc` to `UNIQUE` (UNIQUE is a
        // unique-handle sentinel produced only by
        // `Frame::into_unique`, not by unmap).
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            {
                &&& final(regions).slot_owners[i].raw_count == old(regions).slot_owners[i].raw_count
                &&& final(regions).slot_owners[i].self_addr == old(regions).slot_owners[i].self_addr
                &&& final(regions).slot_owners[i].usage == old(regions).slot_owners[i].usage
                &&& final(regions).slot_owners[i].inner_perms.in_list == old(
                    regions,
                ).slot_owners[i].inner_perms.in_list
                &&& final(regions).slot_owners[i].inner_perms.vtable_ptr == old(
                    regions,
                ).slot_owners[i].inner_perms.vtable_ptr
                // `rc` doesn't bump to UNIQUE.
                &&& old(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNIQUE
                    ==> final(regions).slot_owners[i].inner_perms.ref_count.value()
                    != REF_COUNT_UNIQUE
                // Storage preserved at slots that end non-UNUSED.
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    ==> final(regions).slot_owners[i].inner_perms.storage == old(
                    regions,
                ).slot_owners[i].inner_perms.storage
            },
        // **Frame-slot per-PTE accounting.** For each Frame-usage slot
        // affected by unmap, removing `k` PTEs decreases both `rc` and
        // `paths_in_pt.len()` by `k`, preserving the difference
        // (the "non-mapping count" = handles). Stated as
        // `final.rc + old.paths.len == old.rc + final.paths.len` to
        // avoid `nat` subtraction. The accompanying `rc ≤ old.rc` /
        // `paths.len ≤ old.paths.len` clauses pin the direction of
        // change (unmap only removes). The `post rc != 0` clause
        // rules out the transient "rc == 0" state at Frame slots:
        // exec teardown collapses Frame ∧ rc==0 to `REF_COUNT_UNUSED`
        // atomically; the embedding sees the post-teardown state.
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            old(regions).slot_owners[i].usage == PageUsage::Frame ==> {
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() + old(
                    regions,
                ).slot_owners[i].paths_in_pt.len() == old(
                    regions,
                ).slot_owners[i].inner_perms.ref_count.value()
                    + final(regions).slot_owners[i].paths_in_pt.len()
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() <= old(
                    regions,
                ).slot_owners[i].inner_perms.ref_count.value()
                &&& final(regions).slot_owners[i].paths_in_pt.len() <= old(
                    regions,
                ).slot_owners[i].paths_in_pt.len()
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() != 0
            },
        // **MMIO slots untouched.** Unmap only walks tracked user VAs;
        // MMIO PTEs (`PageUsage::MMIO`) require explicit
        // unmap-via-other-API. Without this, the
        // `MetaSlotOwner::inv` MMIO exception (UNUSED + MMIO allows
        // non-empty `paths_in_pt`) would block
        // `accounting_inv` clause 1 (UNUSED ⟹ paths empty) at
        // post-UNUSED MMIO slots.
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            old(regions).slot_owners[i].usage == PageUsage::MMIO ==> final(regions).slot_owners[i]
                == old(regions).slot_owners[i],
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::vm_space::CursorMut::protect_next`].
///
/// Exec requires (line 1443-1450):
/// - `invariants(owner, regions, guards)`
/// - `forall |p: PageProperty| op.requires((p,))` — MODEL GAP (closure).
/// - The trackedness-preservation closure constraint — MODEL GAP.
///
/// Does NOT require `in_locked_range()` directly.
pub axiom fn cursor_mut_protect_next_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    tracked regions: &mut MetaRegionOwners,
    tracked guards: &mut Guards<'rcu>,
    len: usize,
)
    requires
        old(owner).inv(),
        old(regions).inv(),
        old(owner).children_not_locked(*old(guards)),
        old(owner).nodes_locked(*old(guards)),
        old(owner).metaregion_sound(*old(regions)),
        !old(
            owner,
        ).popped_too_high,
// MODEL GAP: closure preconditions on `op`.

    ensures
        final(owner).inv(),
        final(regions).inv(),
        final(owner).children_not_locked(*final(guards)),
        final(owner).nodes_locked(*final(guards)),
        final(owner).metaregion_sound(*final(regions)),
        !final(owner).popped_too_high,
        // `protect_next` rewrites PTE `prop` fields in place but neither
        // bumps refcounts nor mutates `paths_in_pt` (the path set is
        // about *which* tree positions map a frame, not *how*). So the
        // entire `slot_owners` map is preserved.
        final(regions).slots =~= old(regions).slots,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] == old(regions).slot_owners[i],
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

// =============================================================================
// dispatch tags + step proofs
// =============================================================================
/// Internal: dispatch tag for cursor methods that also touch
/// `MetaRegionOwners` and `TlbModel`. `Map` is handled via its own
/// [`map_step`].
pub enum CursorMutRegionsMethod {
    Unmap(usize),
}

/// Per-op step for `Op::OpenCursor` (read-only [`Cursor`]). Calls the
/// embedded axiom; on `Some`, wraps the cursor owner + guards into a
/// `CursorEntry` with the supplied `vs` (so the resulting entry's
/// `vm_space` field correctly references the parent VmSpace).
///
/// Monomorphic in the cursor kind — read-only vs mutable are *separate*
/// functions, each calling a single `_embedded` axiom. This is
/// deliberate: a `match kind { ReadOnly => axiom_a, Mutable => axiom_b }`
/// wrapper blocks Verus from chaining the per-branch axioms' quantified
/// ensures (the Stage 5.3 changed-slots clause) into the wrapper's own
/// ensures. With one axiom call per function the forall flows straight
/// through. See [`open_cursor_mut_step`] for the mutable twin.
pub(super) proof fn open_cursor_step<'a, 'rcu>(
    tracked vm_space: &VmSpaceOwner,
    tracked regions: &mut MetaRegionOwners,
    vs: VmSpaceId,
    va: Range<Vaddr>,
) -> (tracked res: Option<CursorEntry<'rcu>>)
    requires
        vm_space.inv(),
        old(regions).inv(),
    ensures
        final(regions).inv(),
        // Page-table cursor ops never touch the metadata slot-perm map
        // (`slots` is the boot-fixed metadata region) nor the
        // ManuallyDrop `raw_count` / free-list `in_list` fields; only
        // `slot_owners` refcount / `paths_in_pt` changes. Preserving the
        // `slots` domain (#2 / #3b) and `raw_count` / `in_list` (#4
        // partial) keeps `VmStore::inv`'s coverage clauses chainable
        // across cursor methods.
        final(regions).slots =~= old(regions).slots,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].raw_count == old(regions).slot_owners[i].raw_count
                && final(regions).slot_owners[i].inner_perms.in_list == old(
                regions,
            ).slot_owners[i].inner_perms.in_list,
        // Stage 5.3: opening a cursor only allocates fresh PT nodes —
        // every *changed* slot was UNUSED before and becomes a
        // non-UNUSED PT node (usage != Frame). `accounting_inv` chains
        // from this single clause.
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] != old(regions).slot_owners[i] ==> {
                &&& old(regions).slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].usage != PageUsage::Frame
            },
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
        res matches Some(e) ==> e.inv(),
        res matches Some(e) ==> e.owner.metaregion_sound(*final(regions)),
        res matches Some(e) ==> e.kind == CursorKind::ReadOnly,
        res matches Some(e) ==> e.va == va,
        res matches Some(e) ==> e.vm_space == vs,
{
    let tracked owner_opt = vm_space_cursor_embedded(vm_space, regions, va);
    match owner_opt {
        Option::Some((owner, guards)) => {
            let tracked entry = axiom_cursor_entry_new(vs, CursorKind::ReadOnly, va, owner, guards);
            Option::Some(entry)
        },
        Option::None => Option::None,
    }
}

/// Per-op step for `Op::OpenCursorMut` (mutable [`CursorMut`]). The
/// mutable twin of [`open_cursor_step`]; see its docs for why the two
/// cursor kinds are separate monomorphic functions.
pub(super) proof fn open_cursor_mut_step<'a, 'rcu>(
    tracked vm_space: &VmSpaceOwner,
    tracked regions: &mut MetaRegionOwners,
    vs: VmSpaceId,
    va: Range<Vaddr>,
) -> (tracked res: Option<CursorEntry<'rcu>>)
    requires
        vm_space.inv(),
        old(regions).inv(),
    ensures
        final(regions).inv(),
        final(regions).slots =~= old(regions).slots,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].raw_count == old(regions).slot_owners[i].raw_count
                && final(regions).slot_owners[i].inner_perms.in_list == old(
                regions,
            ).slot_owners[i].inner_perms.in_list,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] != old(regions).slot_owners[i] ==> {
                &&& old(regions).slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                &&& final(regions).slot_owners[i].usage != PageUsage::Frame
            },
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
        res matches Some(e) ==> e.inv(),
        res matches Some(e) ==> e.owner.metaregion_sound(*final(regions)),
        res matches Some(e) ==> e.kind == CursorKind::Mutable,
        res matches Some(e) ==> e.va == va,
        res matches Some(e) ==> e.vm_space == vs,
{
    let tracked owner_opt = vm_space_cursor_mut_embedded(vm_space, regions, va);
    match owner_opt {
        Option::Some((owner, guards)) => {
            let tracked entry = axiom_cursor_entry_new(vs, CursorKind::Mutable, va, owner, guards);
            Option::Some(entry)
        },
        Option::None => Option::None,
    }
}

/// Per-op step for `Op::DropCursor`. The caller has already extracted
/// the entry from the store; this function drops it.
pub(super) proof fn drop_cursor_step<'rcu>(tracked _entry: CursorEntry<'rcu>) {
}

/// Per-op step for cursor methods that mutate only the cursor owner
/// (and thread `regions` / `guards`): query, find_next, jump,
/// protect_next.
///
/// None of these require `owner.in_locked_range()`. Exec `query`
/// handles an out-of-range cursor with a graceful `Err`; exec `jump`'s
/// `in_locked_range` precondition was relaxed (a drifted cursor that
/// cannot be repositioned aborts via a sound `panic_diverge`).
/// Per-op step for `Op::Query`. Mirrors
/// [`cursor_query_embedded`]'s `Option<Paddr>` result: `Some(paddr)`
/// when query returned a tracked `MappedItem` (and `rc` was bumped at
/// the leaf), `None` otherwise. The store-level [`step_query`]
/// (mod.rs) consumes that paddr to register a fresh `FrameEntry`,
/// closing accounting.
pub(super) proof fn cursor_query_step<'rcu>(
    tracked entry: &mut CursorEntry<'rcu>,
    tracked regions: &mut MetaRegionOwners,
) -> (res: Option<Paddr>)
    requires
        old(entry).inv(),
        old(regions).inv(),
        old(entry).owner.metaregion_sound(*old(regions)),
    ensures
        final(entry).vm_space == old(entry).vm_space,
        final(entry).kind == old(entry).kind,
        final(entry).va == old(entry).va,
        final(entry).inv(),
        final(regions).inv(),
        final(entry).owner.metaregion_sound(*final(regions)),
        final(regions).slots =~= old(regions).slots,
        res is None ==> forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] == old(regions).slot_owners[i],
        res matches Some(paddr) ==> {
            &&& has_safe_slot(paddr)
            &&& old(regions).slot_owners[frame_to_index_spec(paddr)].usage == PageUsage::Frame
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value()
                == (old(regions).slot_owners[frame_to_index_spec(
                paddr,
            )].inner_perms.ref_count.value() + 1) as nat
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value()
                <= REF_COUNT_MAX
            &&& forall|i: usize|
                #![trigger final(regions).slot_owners[i]]
                i != frame_to_index_spec(paddr) ==> final(regions).slot_owners[i] == old(
                    regions,
                ).slot_owners[i]
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].raw_count == old(
                regions,
            ).slot_owners[frame_to_index_spec(paddr)].raw_count
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].usage == old(
                regions,
            ).slot_owners[frame_to_index_spec(paddr)].usage
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].paths_in_pt == old(
                regions,
            ).slot_owners[frame_to_index_spec(paddr)].paths_in_pt
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.in_list == old(
                regions,
            ).slot_owners[frame_to_index_spec(paddr)].inner_perms.in_list
            &&& final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.storage == old(
                regions,
            ).slot_owners[frame_to_index_spec(paddr)].inner_perms.storage
        },
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    cursor_query_embedded(&mut entry.owner, regions, &mut entry.guards)
}

/// Per-op step for `Op::FindNext`. Navigates the cursor forward
/// without touching any frame slot — full `slot_owners` preservation.
pub(super) proof fn cursor_find_next_step<'rcu>(
    tracked entry: &mut CursorEntry<'rcu>,
    tracked regions: &mut MetaRegionOwners,
    len: usize,
)
    requires
        old(entry).inv(),
        old(regions).inv(),
        old(entry).owner.metaregion_sound(*old(regions)),
    ensures
        final(entry).vm_space == old(entry).vm_space,
        final(entry).kind == old(entry).kind,
        final(entry).va == old(entry).va,
        final(entry).inv(),
        final(regions).inv(),
        final(entry).owner.metaregion_sound(*final(regions)),
        final(regions).slots =~= old(regions).slots,
        // Full `slot_owners` preservation — `find_next` writes no PTE
        // and clones no leaf.
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] == old(regions).slot_owners[i],
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    cursor_find_next_embedded(&mut entry.owner, regions, &mut entry.guards, len)
}

/// Per-op step for `Op::Jump`. Repositions the cursor without
/// touching any frame slot — full `slot_owners` preservation.
pub(super) proof fn cursor_jump_step<'rcu>(
    tracked entry: &mut CursorEntry<'rcu>,
    tracked regions: &mut MetaRegionOwners,
    va: Vaddr,
)
    requires
        old(entry).inv(),
        old(regions).inv(),
        old(entry).owner.metaregion_sound(*old(regions)),
    ensures
        final(entry).vm_space == old(entry).vm_space,
        final(entry).kind == old(entry).kind,
        final(entry).va == old(entry).va,
        final(entry).inv(),
        final(regions).inv(),
        final(entry).owner.metaregion_sound(*final(regions)),
        final(regions).slots =~= old(regions).slots,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] == old(regions).slot_owners[i],
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    cursor_jump_embedded(&mut entry.owner, regions, &mut entry.guards, va)
}

/// Per-op step for `Op::ProtectNext`. Rewrites PTE `prop` fields in
/// place — no `rc` or `paths_in_pt` mutation; full `slot_owners`
/// preservation.
pub(super) proof fn cursor_protect_next_step<'rcu>(
    tracked entry: &mut CursorEntry<'rcu>,
    tracked regions: &mut MetaRegionOwners,
    len: usize,
)
    requires
        old(entry).inv(),
        old(regions).inv(),
        old(entry).owner.metaregion_sound(*old(regions)),
    ensures
        final(entry).vm_space == old(entry).vm_space,
        final(entry).kind == old(entry).kind,
        final(entry).va == old(entry).va,
        final(entry).inv(),
        final(regions).inv(),
        final(entry).owner.metaregion_sound(*final(regions)),
        final(regions).slots =~= old(regions).slots,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i] == old(regions).slot_owners[i],
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    cursor_mut_protect_next_embedded(&mut entry.owner, regions, &mut entry.guards, len)
}

/// Per-op step for cursor methods that mutate the cursor owner,
/// `MetaRegionOwners`, AND `TlbModel`: `unmap` (and `map`, via
/// [`map_step`]).
pub(super) proof fn cursor_mut_regions_step<'rcu>(
    tracked entry: &mut CursorEntry<'rcu>,
    tracked regions: &mut MetaRegionOwners,
    tracked tlb_model: &mut TlbModel,
    method: CursorMutRegionsMethod,
)
    requires
        old(entry).inv(),
        old(regions).inv(),
        old(entry).owner.metaregion_sound(*old(regions)),
        old(tlb_model).inv(),
    ensures
        final(entry).vm_space == old(entry).vm_space,
        final(entry).kind == old(entry).kind,
        final(entry).va == old(entry).va,
        final(entry).inv(),
        final(regions).inv(),
        final(entry).owner.metaregion_sound(*final(regions)),
        final(tlb_model).inv(),
        // Mirror the faithful `cursor_mut_unmap_embedded` ensures: per-
        // slot universal preservation (raw_count, in_list, usage,
        // self_addr, vtable_ptr); rc doesn't bump to UNIQUE; storage
        // preserved at non-UNUSED post; and at Frame slots, the
        // "non-mapping count" `rc - paths.len()` is invariant with
        // `rc` and `paths.len` monotonically non-increasing.
        final(regions).slots =~= old(regions).slots,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            {
                &&& final(regions).slot_owners[i].raw_count == old(regions).slot_owners[i].raw_count
                &&& final(regions).slot_owners[i].self_addr == old(regions).slot_owners[i].self_addr
                &&& final(regions).slot_owners[i].usage == old(regions).slot_owners[i].usage
                &&& final(regions).slot_owners[i].inner_perms.in_list == old(
                    regions,
                ).slot_owners[i].inner_perms.in_list
                &&& final(regions).slot_owners[i].inner_perms.vtable_ptr == old(
                    regions,
                ).slot_owners[i].inner_perms.vtable_ptr
                &&& old(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNIQUE
                    ==> final(regions).slot_owners[i].inner_perms.ref_count.value()
                    != REF_COUNT_UNIQUE
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    ==> final(regions).slot_owners[i].inner_perms.storage == old(
                    regions,
                ).slot_owners[i].inner_perms.storage
            },
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            old(regions).slot_owners[i].usage == PageUsage::Frame ==> {
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() + old(
                    regions,
                ).slot_owners[i].paths_in_pt.len() == old(
                    regions,
                ).slot_owners[i].inner_perms.ref_count.value()
                    + final(regions).slot_owners[i].paths_in_pt.len()
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() <= old(
                    regions,
                ).slot_owners[i].inner_perms.ref_count.value()
                &&& final(regions).slot_owners[i].paths_in_pt.len() <= old(
                    regions,
                ).slot_owners[i].paths_in_pt.len()
                &&& final(regions).slot_owners[i].inner_perms.ref_count.value() != 0
            },
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            old(regions).slot_owners[i].usage == PageUsage::MMIO ==> final(regions).slot_owners[i]
                == old(regions).slot_owners[i],
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    match method {
        CursorMutRegionsMethod::Unmap(len) => {
            cursor_mut_unmap_embedded(&mut entry.owner, regions, &mut entry.guards, tlb_model, len);
        },
    }
}

/// Per-op step for `Op::Map`. Mutates the cursor owner, the regions,
/// and the TLB model. Has its own function rather than a dispatch tag
/// because the argument shape (UFrame, PageProperty) doesn't match the
/// others.
///
/// Does NOT require `owner.in_locked_range()`: exec `map` panics on an
/// out-of-range cursor (`assert!(va < barrier_va.end)`) and re-derives
/// `in_locked_range` from that panic + the cursor invariant.
pub(super) proof fn map_step<'rcu>(
    tracked entry: &mut CursorEntry<'rcu>,
    tracked regions: &mut MetaRegionOwners,
    tracked tlb_model: &mut TlbModel,
    paddr: Paddr,
    prop: PageProperty,
)
    requires
        old(entry).inv(),
        old(regions).inv(),
        old(entry).owner.metaregion_sound(*old(regions)),
        old(tlb_model).inv(),
        has_safe_slot(paddr),
    ensures
        final(entry).vm_space == old(entry).vm_space,
        final(entry).kind == old(entry).kind,
        final(entry).va == old(entry).va,
        final(entry).inv(),
        final(regions).inv(),
        final(entry).owner.metaregion_sound(*final(regions)),
        final(tlb_model).inv(),
        final(regions).slots =~= old(regions).slots,
        // Mirror the strengthened `cursor_mut_map_embedded` ensures.
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].raw_count == old(regions).slot_owners[i].raw_count
                && final(regions).slot_owners[i].inner_perms.in_list == old(
                regions,
            ).slot_owners[i].inner_perms.in_list,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index_spec(paddr) && old(
                regions,
            ).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
        forall|i: usize|
            #![trigger final(regions).slot_owners[i].inner_perms.ref_count.value()]
            old(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                ==> final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED,
        final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value() == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value(),
        final(regions).slot_owners[frame_to_index_spec(paddr)].paths_in_pt.len() == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].paths_in_pt.len() + 1,
        final(regions).slot_owners[frame_to_index_spec(paddr)].usage == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].usage,
        final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.storage == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].inner_perms.storage,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index_spec(paddr) && old(
                regions,
            ).slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                && final(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                ==> final(regions).slot_owners[i].usage != PageUsage::Frame,
        forall|c: CursorOwner<'rcu, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    cursor_mut_map_embedded(&mut entry.owner, regions, &mut entry.guards, tlb_model, paddr, prop);
}

} // verus!
