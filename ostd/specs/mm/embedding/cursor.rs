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

use crate::mm::frame::UFrame;
use crate::mm::page_prop::PageProperty;
use crate::mm::vm_space::vm_space_specs::VmSpaceOwner;
use crate::mm::vm_space::UserPtConfig;
use crate::mm::Vaddr;
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
) -> (tracked res: Option<(CursorOwner<'rcu, UserPtConfig>, Guards<'rcu, UserPtConfig>)>)
    requires
        vm_space.inv(),
        old(regions).inv(),
    ensures
        final(regions).inv(),
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
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
) -> (tracked res: Option<(CursorOwner<'rcu, UserPtConfig>, Guards<'rcu, UserPtConfig>)>)
    requires
        vm_space.inv(),
        old(regions).inv(),
    ensures
        final(regions).inv(),
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
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
pub axiom fn cursor_query_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    tracked regions: &mut MetaRegionOwners,
    tracked guards: &mut Guards<'rcu, UserPtConfig>,
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
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
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
    tracked guards: &mut Guards<'rcu, UserPtConfig>,
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
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
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
    tracked guards: &mut Guards<'rcu, UserPtConfig>,
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
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
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
    tracked guards: &mut Guards<'rcu, UserPtConfig>,
    tracked tlb_model: &mut TlbModel,
    frame: UFrame,
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
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
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
    tracked guards: &mut Guards<'rcu, UserPtConfig>,
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
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
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
    tracked guards: &mut Guards<'rcu, UserPtConfig>,
    len: usize,
)
    requires
        old(owner).inv(),
        old(regions).inv(),
        old(owner).children_not_locked(*old(guards)),
        old(owner).nodes_locked(*old(guards)),
        old(owner).metaregion_sound(*old(regions)),
        !old(owner).popped_too_high,
        // MODEL GAP: closure preconditions on `op`.
    ensures
        final(owner).inv(),
        final(regions).inv(),
        final(owner).children_not_locked(*final(guards)),
        final(owner).nodes_locked(*final(guards)),
        final(owner).metaregion_sound(*final(regions)),
        !final(owner).popped_too_high,
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

// =============================================================================
// dispatch tags + step proofs
// =============================================================================

/// Internal: dispatch tag for [`cursor_method_step`] (cursor-only methods).
pub enum CursorMethod {
    Query,
    FindNext(usize),
    Jump(Vaddr),
    ProtectNext(usize),
}

/// Internal: dispatch tag for cursor methods that also touch
/// `MetaRegionOwners` and `TlbModel`. `Map` is handled via its own
/// [`map_step`].
pub enum CursorMutRegionsMethod {
    Unmap(usize),
}

/// Per-op step for `Op::OpenCursor` / `Op::OpenCursorMut`. Calls the
/// embedded axiom; on `Some`, wraps the cursor owner + guards into a
/// `CursorEntry` with the supplied `vs` (so the resulting entry's
/// `vm_space` field correctly references the parent VmSpace).
pub(super) proof fn open_cursor_step<'a, 'rcu>(
    tracked vm_space: &VmSpaceOwner,
    tracked regions: &mut MetaRegionOwners,
    vs: VmSpaceId,
    va: Range<Vaddr>,
    kind: CursorKind,
) -> (tracked res: Option<CursorEntry<'rcu>>)
    requires
        vm_space.inv(),
        old(regions).inv(),
    ensures
        final(regions).inv(),
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
        res matches Some(e) ==> e.inv(),
        res matches Some(e) ==> e.owner.metaregion_sound(*final(regions)),
        res matches Some(e) ==> e.kind == kind,
        res matches Some(e) ==> e.va == va,
        res matches Some(e) ==> e.vm_space == vs,
{
    let tracked owner_opt = match kind {
        CursorKind::ReadOnly => vm_space_cursor_embedded(vm_space, regions, va),
        CursorKind::Mutable => vm_space_cursor_mut_embedded(vm_space, regions, va),
    };
    match owner_opt {
        Option::Some((owner, guards)) => {
            let tracked entry = axiom_cursor_entry_new(vs, kind, va, owner, guards);
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
pub(super) proof fn cursor_method_step<'rcu>(
    tracked entry: &mut CursorEntry<'rcu>,
    tracked regions: &mut MetaRegionOwners,
    method: CursorMethod,
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
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    match method {
        CursorMethod::Query =>
            cursor_query_embedded(&mut entry.owner, regions, &mut entry.guards),
        CursorMethod::FindNext(len) =>
            cursor_find_next_embedded(&mut entry.owner, regions, &mut entry.guards, len),
        CursorMethod::Jump(va) =>
            cursor_jump_embedded(&mut entry.owner, regions, &mut entry.guards, va),
        CursorMethod::ProtectNext(len) =>
            cursor_mut_protect_next_embedded(&mut entry.owner, regions, &mut entry.guards, len),
    }
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
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    match method {
        CursorMutRegionsMethod::Unmap(len) => {
            cursor_mut_unmap_embedded(
                &mut entry.owner, regions, &mut entry.guards, tlb_model, len);
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
    frame: UFrame,
    prop: PageProperty,
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
        forall|c: CursorOwner<'rcu, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    cursor_mut_map_embedded(
        &mut entry.owner, regions, &mut entry.guards, tlb_model, frame, prop);
}

} // verus!
