//! Deep embedding of the `VmSpace` API.
//!
//! `VmStore` is the abstract state of a caller of the [`crate::mm::vm_space`]
//! API: it holds the [`MetaRegionOwners`] plus a registry of every owner
//! object ([`VmSpaceOwner`], [`CursorOwner`], `VmIoOwner`) the caller
//! currently has access to.
//!
//! [`Op`] is an ADT enumerating the public exec API of `vm_space.rs`.
//! [`step`] is a single proof-mode dispatcher: `step(s, op)` requires
//! `s.inv()` and ensures `s.inv()`. Because Verus chains pre/post
//! automatically, induction over arbitrary call sequences is implicit: any
//! program of the form `step(s, op0); step(s, op1); ...; step(s, opN);`
//! typechecks iff `s.inv()` holds at every intermediate state.
//!
//! # Soundness boundary: `_embedded` axioms
//!
//! Each axiom named `<exec_function_path>_embedded` mirrors the `ensures`
//! clause of one public exec function in [`crate::mm::vm_space`]. For the
//! embedding to be sound, every `_embedded` axiom must accurately reflect
//! what its exec counterpart guarantees. The naming convention exists so a
//! reviewer touching either side can grep for the partner. When the exec
//! `verus_spec` for `Foo::bar` changes, search for `foo_bar_embedded` in
//! this file and update it.
//!
//! Internal helpers that don't mirror an exec function (e.g. `axiom_*`
//! lemmas about `fresh_id`) keep the `axiom_` prefix to avoid being
//! confused with the soundness-boundary axioms.

use core::ops::Range;

use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::mm::frame::UFrame;
use crate::mm::io::VmIoOwner;
use crate::mm::page_prop::PageProperty;
use crate::mm::vm_space::vm_space_specs::VmSpaceOwner;
use crate::mm::vm_space::UserPtConfig;
use crate::mm::Vaddr;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::owners::CursorOwner;

verus! {

/// Logical identifier for a [`VmSpaceOwner`] in the store.
pub type VmSpaceId = int;

/// Logical identifier for a [`CursorOwner`] in the store.
pub type CursorId = int;

/// Logical identifier for a [`VmIoOwner`] in the store.
pub type VmIoId = int;

/// Whether a [`VmIoOwner`] backs a `VmReader` or a `VmWriter`.
pub enum VmIoKind {
    Reader,
    Writer,
}

/// Per-VmIo entry in the store.
pub tracked struct VmIoEntry {
    pub vm_space: VmSpaceId,
    pub kind: VmIoKind,
    pub owner: VmIoOwner,
}

/// Whether a cursor is a read-only [`Cursor`] or a mutable [`CursorMut`].
///
/// [`Cursor`]: crate::mm::vm_space::Cursor
/// [`CursorMut`]: crate::mm::vm_space::CursorMut
pub enum CursorKind {
    ReadOnly,
    Mutable,
}

/// Per-cursor entry in the store.
///
/// `'rcu` is the cursor session lifetime (existentially picked at each
/// `OpenCursor`/`OpenCursorMut` step, in practice unified across the store
/// because Verus's tracked `Map` cannot quantify over the value's lifetime
/// existentially per element).
pub tracked struct CursorEntry<'rcu> {
    pub vm_space: VmSpaceId,
    pub kind: CursorKind,
    pub owner: CursorOwner<'rcu, UserPtConfig>,
}

/// Resource store: the abstract state visible to a caller of the VmSpace
/// API.
///
/// Stage 2 tracks `regions`, `vm_spaces`, and `cursors`. Later stages add
/// `vm_ios`.
pub tracked struct VmStore<'rcu> {
    pub regions: MetaRegionOwners,
    pub vm_spaces: Map<VmSpaceId, VmSpaceOwner>,
    pub cursors: Map<CursorId, CursorEntry<'rcu>>,
    pub vm_ios: Map<VmIoId, VmIoEntry>,
}

impl<'a, 'rcu> VmStore<'rcu> {
    /// The store's top-level invariant. Aggregates the per-component
    /// invariants of every owner the store holds, plus cross-store
    /// consistency (every cursor and every VmIo refers to a live VmSpace).
    pub open spec fn inv(self) -> bool {
        &&& self.regions.inv()
        &&& forall|id: VmSpaceId|
                #[trigger] self.vm_spaces.dom().contains(id)
                    ==> self.vm_spaces[id].inv()
        &&& forall|id: CursorId|
                #[trigger] self.cursors.dom().contains(id)
                    ==> self.cursors[id].owner.inv()
        &&& forall|id: CursorId|
                #[trigger] self.cursors.dom().contains(id)
                    ==> self.vm_spaces.dom().contains(self.cursors[id].vm_space)
        &&& forall|id: VmIoId|
                #[trigger] self.vm_ios.dom().contains(id)
                    ==> self.vm_ios[id].owner.inv()
        &&& forall|id: VmIoId|
                #[trigger] self.vm_ios.dom().contains(id)
                    ==> self.vm_spaces.dom().contains(self.vm_ios[id].vm_space)
    }
}

/// Public exec API of `ostd::mm::vm_space`, lifted to data.
pub enum Op {
    /// `VmSpace::new`. Allocates a fresh `VmSpaceOwner` and registers it
    /// under a fresh `VmSpaceId`.
    NewVmSpace,
    /// Drop of a `VmSpace`. Removes the owner at `vs` (no-op if absent).
    DropVmSpace { vs: VmSpaceId },
    /// `VmSpace::cursor`. Opens a read-only cursor on the VmSpace at `vs`
    /// over the virtual range `va`. May fail (returns `Err` in exec); on
    /// failure the store is unchanged.
    OpenCursor { vs: VmSpaceId, va: Range<Vaddr> },
    /// `VmSpace::cursor_mut`. Same as `OpenCursor` but mutable.
    OpenCursorMut { vs: VmSpaceId, va: Range<Vaddr> },
    /// Drop of a `Cursor`/`CursorMut`. Removes the cursor entry at `c`
    /// (no-op if absent).
    DropCursor { c: CursorId },
    /// `Cursor::query` / `CursorMut::query`. Reads the current page state;
    /// internally advances the cursor.
    Query { c: CursorId },
    /// `Cursor::find_next` / `CursorMut::find_next`.
    FindNext { c: CursorId, len: usize },
    /// `Cursor::jump` / `CursorMut::jump`.
    Jump { c: CursorId, va: Vaddr },
    /// `Cursor::virt_addr` / `CursorMut::virt_addr`. Pure read; no state
    /// change at the embedding granularity.
    VirtAddr { c: CursorId },
    /// `CursorMut::map`. Maps `frame` with `prop` at the cursor's current
    /// position. Modifies the cursor owner and may modify
    /// `MetaRegionOwners`.
    Map { c: CursorId, frame: UFrame, prop: PageProperty },
    /// `CursorMut::unmap`. Unmaps up to `len` bytes starting at the
    /// cursor's current position.
    Unmap { c: CursorId, len: usize },
    /// `CursorMut::protect_next`. The exec method takes an
    /// `op: impl FnOnce(PageProperty) -> PageProperty`; we model only the
    /// length here (the per-page property update is opaque at this stage).
    ProtectNext { c: CursorId, len: usize },
    /// `VmSpace::reader`. May fail; on failure the store is unchanged.
    NewReader { vs: VmSpaceId, vaddr: Vaddr, len: usize },
    /// `VmSpace::writer`. May fail; on failure the store is unchanged.
    NewWriter { vs: VmSpaceId, vaddr: Vaddr, len: usize },
    /// Drop of a `VmReader`. Removes the corresponding [`VmIoOwner`].
    DropReader { vio: VmIoId },
    /// Drop of a `VmWriter`. Removes the corresponding [`VmIoOwner`].
    DropWriter { vio: VmIoId },
}

// =============================================================================
// Soundness-boundary axioms: each mirrors a public exec function's `ensures`.
// Convention: `<exec_function_path>_embedded`.
// =============================================================================

/// Mirror of [`crate::mm::vm_space::VmSpace::new`].
///
/// Real exec ensures: `regions.inv()` is preserved; new owner satisfies its
/// invariant. Stage 1 axiomatizes only this; later stages may strengthen
/// to capture the new owner's `page_table_owner` content.
pub axiom fn vm_space_new_embedded<'a>(tracked regions: &mut MetaRegionOwners)
    -> (tracked res: VmSpaceOwner)
    requires
        old(regions).inv(),
    ensures
        final(regions).inv(),
        res.inv(),
;

/// Mirror of [`crate::mm::vm_space::VmSpace::cursor`].
///
/// Real exec ensures (paraphrased from `vm_space.rs:201-209`): when
/// `cursor_new_success_conditions(va)` holds, the call returns
/// `Ok(Cursor)` with a tracked `Some(CursorOwner)` whose `inv()` holds.
/// Stage 2 axiomatizes a coarser model: returns `Some` (with `inv()`) or
/// `None`, with no precondition relating to the success conditions. This
/// over-approximates the success case (the embedding allows opens that
/// would fail in exec); it never *under*-approximates, which is what
/// matters for soundness of inductive invariant preservation.
pub axiom fn vm_space_cursor_embedded<'a, 'rcu>(
    tracked vm_space: &VmSpaceOwner,
    va: Range<Vaddr>,
) -> (tracked res: Option<CursorOwner<'rcu, UserPtConfig>>)
    requires
        vm_space.inv(),
    ensures
        res matches Some(c) ==> c.inv(),
;

/// Mirror of [`crate::mm::vm_space::VmSpace::cursor_mut`].
///
/// Same shape as [`vm_space_cursor_embedded`].
pub axiom fn vm_space_cursor_mut_embedded<'a, 'rcu>(
    tracked vm_space: &VmSpaceOwner,
    va: Range<Vaddr>,
) -> (tracked res: Option<CursorOwner<'rcu, UserPtConfig>>)
    requires
        vm_space.inv(),
    ensures
        res matches Some(c) ==> c.inv(),
;

/// Mirror of [`crate::mm::vm_space::Cursor::query`] /
/// [`crate::mm::vm_space::CursorMut::query`]. The exec method internally
/// advances the cursor; we model the position update as opaque.
pub axiom fn cursor_query_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
)
    requires
        old(owner).inv(),
    ensures
        final(owner).inv(),
;

/// Mirror of [`crate::mm::vm_space::Cursor::find_next`] /
/// [`crate::mm::vm_space::CursorMut::find_next`].
pub axiom fn cursor_find_next_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    len: usize,
)
    requires
        old(owner).inv(),
    ensures
        final(owner).inv(),
;

/// Mirror of [`crate::mm::vm_space::Cursor::jump`] /
/// [`crate::mm::vm_space::CursorMut::jump`].
pub axiom fn cursor_jump_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    va: Vaddr,
)
    requires
        old(owner).inv(),
    ensures
        final(owner).inv(),
;

// `Cursor::virt_addr` / `CursorMut::virt_addr` are pure reads; no axiom.

/// Mirror of [`crate::mm::vm_space::CursorMut::map`].
///
/// Modifies both the cursor owner and `MetaRegionOwners`.
pub axiom fn cursor_mut_map_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    tracked regions: &mut MetaRegionOwners,
    frame: UFrame,
    prop: PageProperty,
)
    requires
        old(owner).inv(),
        old(regions).inv(),
    ensures
        final(owner).inv(),
        final(regions).inv(),
;

/// Mirror of [`crate::mm::vm_space::CursorMut::unmap`].
///
/// Returns the number of bytes actually unmapped.
pub axiom fn cursor_mut_unmap_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    tracked regions: &mut MetaRegionOwners,
    len: usize,
)
    requires
        old(owner).inv(),
        old(regions).inv(),
    ensures
        final(owner).inv(),
        final(regions).inv(),
;

/// Mirror of [`crate::mm::vm_space::CursorMut::protect_next`].
pub axiom fn cursor_mut_protect_next_embedded<'rcu>(
    tracked owner: &mut CursorOwner<'rcu, UserPtConfig>,
    len: usize,
)
    requires
        old(owner).inv(),
    ensures
        final(owner).inv(),
;

/// Mirror of [`crate::mm::vm_space::VmSpace::reader`].
///
/// On success returns `Some` with a `VmIoOwner` whose `inv()` holds. The
/// real exec function may fail when `vaddr+len` exceeds the user-space
/// range or the active page table doesn't match this VmSpace; that
/// failure is modeled by returning `None`.
pub axiom fn vm_space_reader_embedded<'a>(
    tracked vm_space: &VmSpaceOwner,
    vaddr: Vaddr,
    len: usize,
) -> (tracked res: Option<VmIoOwner>)
    requires
        vm_space.inv(),
    ensures
        res matches Some(o) ==> o.inv(),
;

/// Mirror of [`crate::mm::vm_space::VmSpace::writer`].
pub axiom fn vm_space_writer_embedded<'a>(
    tracked vm_space: &VmSpaceOwner,
    vaddr: Vaddr,
    len: usize,
) -> (tracked res: Option<VmIoOwner>)
    requires
        vm_space.inv(),
    ensures
        res matches Some(o) ==> o.inv(),
;

// =============================================================================
// One-step soundness theorem and per-op proofs.
// =============================================================================

/// One-step soundness theorem.
pub proof fn step<'a, 'rcu>(tracked s: &mut VmStore<'rcu>, op: Op)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    match op {
        Op::NewVmSpace => new_vm_space_step(s),
        Op::DropVmSpace { vs } => drop_vm_space_step(s, vs),
        Op::OpenCursor { vs, va } => open_cursor_step(s, vs, va, CursorKind::ReadOnly),
        Op::OpenCursorMut { vs, va } => open_cursor_step(s, vs, va, CursorKind::Mutable),
        Op::DropCursor { c } => drop_cursor_step(s, c),
        Op::Query { c } => cursor_method_step(s, c, CursorMethod::Query),
        Op::FindNext { c, len } => cursor_method_step(s, c, CursorMethod::FindNext(len)),
        Op::Jump { c, va } => cursor_method_step(s, c, CursorMethod::Jump(va)),
        Op::VirtAddr { c: _ } => {} // pure read; no state change
        Op::Map { c, frame, prop } => map_step(s, c, frame, prop),
        Op::Unmap { c, len } => cursor_mut_regions_step(s, c, CursorMutRegionsMethod::Unmap(len)),
        Op::ProtectNext { c, len } => cursor_method_step(s, c, CursorMethod::ProtectNext(len)),
        Op::NewReader { vs, vaddr, len } => new_vm_io_step(s, vs, vaddr, len, VmIoKind::Reader),
        Op::NewWriter { vs, vaddr, len } => new_vm_io_step(s, vs, vaddr, len, VmIoKind::Writer),
        Op::DropReader { vio } => drop_vm_io_step(s, vio),
        Op::DropWriter { vio } => drop_vm_io_step(s, vio),
    }
}

/// Internal: dispatch tag for [`cursor_method_step`] (cursor-only methods).
pub enum CursorMethod {
    Query,
    FindNext(usize),
    Jump(Vaddr),
    ProtectNext(usize),
}

/// Internal: dispatch tag for cursor methods that also touch
/// `MetaRegionOwners`. `Map` is handled via its own [`map_step`] because
/// its argument shape (`UFrame`, `PageProperty`) doesn't match the others.
pub enum CursorMutRegionsMethod {
    Unmap(usize),
}

/// Picks an id not currently in `m.dom()`. Since the key type is `int`, an
/// unused id always exists.
pub open spec fn fresh_vm_space_id<'a>(m: Map<VmSpaceId, VmSpaceOwner>) -> VmSpaceId {
    choose|id: VmSpaceId| !m.dom().contains(id)
}

/// Picks a cursor id not currently in `m.dom()`. As above.
pub open spec fn fresh_cursor_id<'rcu>(m: Map<CursorId, CursorEntry<'rcu>>) -> CursorId {
    choose|id: CursorId| !m.dom().contains(id)
}

/// Witnesses that [`fresh_vm_space_id`] returns an id not in the map's
/// domain. (Internal helper, not a `_embedded` axiom.)
pub axiom fn axiom_fresh_vm_space_id_not_in_dom<'a>(
    m: Map<VmSpaceId, VmSpaceOwner>,
)
    ensures
        !m.dom().contains(fresh_vm_space_id(m)),
;

/// Witnesses that [`fresh_cursor_id`] returns an id not in the map's
/// domain. (Internal helper, not a `_embedded` axiom.)
pub axiom fn axiom_fresh_cursor_id_not_in_dom<'rcu>(
    m: Map<CursorId, CursorEntry<'rcu>>,
)
    ensures
        !m.dom().contains(fresh_cursor_id(m)),
;

/// Tracked constructor for [`CursorEntry`].
///
/// Verus does not let a `proof fn` construct a tracked struct via a
/// struct-literal when ghost-mode and tracked-mode fields are mixed; the
/// idiomatic workaround is a constructor axiom (cf.
/// [`CursorContinuation::new`]).
pub axiom fn axiom_cursor_entry_new<'rcu>(
    vm_space: VmSpaceId,
    kind: CursorKind,
    tracked owner: CursorOwner<'rcu, UserPtConfig>,
) -> (tracked res: CursorEntry<'rcu>)
    ensures
        res.vm_space == vm_space,
        res.kind == kind,
        res.owner == owner,
;

/// Picks a [`VmIoId`] not currently in `m.dom()`.
pub open spec fn fresh_vm_io_id<'a>(m: Map<VmIoId, VmIoEntry>) -> VmIoId {
    choose|id: VmIoId| !m.dom().contains(id)
}

/// Witnesses that [`fresh_vm_io_id`] returns an id not in the map's
/// domain. (Internal helper, not a `_embedded` axiom.)
pub axiom fn axiom_fresh_vm_io_id_not_in_dom<'a>(m: Map<VmIoId, VmIoEntry>)
    ensures
        !m.dom().contains(fresh_vm_io_id(m)),
;

/// Tracked constructor for [`VmIoEntry`].
pub axiom fn axiom_vm_io_entry_new<'a>(
    vm_space: VmSpaceId,
    kind: VmIoKind,
    tracked owner: VmIoOwner,
) -> (tracked res: VmIoEntry)
    ensures
        res.vm_space == vm_space,
        res.kind == kind,
        res.owner == owner,
;

proof fn new_vm_space_step<'a, 'rcu>(tracked s: &mut VmStore<'rcu>)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    let tracked owner = vm_space_new_embedded(&mut s.regions);
    let ghost id = fresh_vm_space_id(s.vm_spaces);
    axiom_fresh_vm_space_id_not_in_dom(s.vm_spaces);
    s.vm_spaces.tracked_insert(id, owner);
    assert(final(s).inv()) by {
        assert forall|j: VmSpaceId|
            #[trigger] final(s).vm_spaces.dom().contains(j)
            implies final(s).vm_spaces[j].inv()
        by {
            if j == id {
                assert(final(s).vm_spaces[j] == owner);
            } else {
                assert(old(s).vm_spaces.dom().contains(j));
            }
        };
        // cursor/vm_io->vm_space refs are still valid since we only added,
        // never removed, vm_spaces.
        assert forall|j: CursorId|
            #[trigger] final(s).cursors.dom().contains(j)
            implies final(s).vm_spaces.dom().contains(final(s).cursors[j].vm_space)
        by {
            assert(old(s).cursors.dom().contains(j));
            assert(old(s).vm_spaces.dom().contains(old(s).cursors[j].vm_space));
        };
        assert forall|j: VmIoId|
            #[trigger] final(s).vm_ios.dom().contains(j)
            implies final(s).vm_ios[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).vm_ios[j].vm_space)
        by {
            assert(old(s).vm_ios.dom().contains(j));
            assert(final(s).vm_ios[j] == old(s).vm_ios[j]);
        };
    };
}

proof fn drop_vm_space_step<'a, 'rcu>(tracked s: &mut VmStore<'rcu>, vs: VmSpaceId)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    // Real Rust drop only fires when the value exists, AND only when no
    // outstanding cursor or VmIo borrows the VmSpace. To preserve cross-
    // store referential integrity we make the step a no-op otherwise.
    if s.vm_spaces.dom().contains(vs)
        && (forall|c: CursorId|
            #[trigger] s.cursors.dom().contains(c)
                ==> s.cursors[c].vm_space != vs)
        && (forall|v: VmIoId|
            #[trigger] s.vm_ios.dom().contains(v)
                ==> s.vm_ios[v].vm_space != vs)
    {
        let _ = s.vm_spaces.tracked_remove(vs);
    }
    assert(final(s).inv()) by {
        assert forall|j: VmSpaceId|
            #[trigger] final(s).vm_spaces.dom().contains(j)
            implies final(s).vm_spaces[j].inv()
        by {
            assert(old(s).vm_spaces.dom().contains(j));
        };
        assert forall|j: CursorId|
            #[trigger] final(s).cursors.dom().contains(j)
            implies final(s).vm_spaces.dom().contains(final(s).cursors[j].vm_space)
        by {
            assert(old(s).cursors.dom().contains(j));
            assert(final(s).cursors[j] == old(s).cursors[j]);
        };
        assert forall|j: VmIoId|
            #[trigger] final(s).vm_ios.dom().contains(j)
            implies final(s).vm_ios[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).vm_ios[j].vm_space)
        by {
            assert(old(s).vm_ios.dom().contains(j));
            assert(final(s).vm_ios[j] == old(s).vm_ios[j]);
        };
    };
}

proof fn open_cursor_step<'a, 'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vs: VmSpaceId,
    va: Range<Vaddr>,
    kind: CursorKind,
)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    if s.vm_spaces.dom().contains(vs) {
        let tracked vm_space_ref = s.vm_spaces.tracked_borrow(vs);
        let tracked res = match kind {
            CursorKind::ReadOnly => vm_space_cursor_embedded(vm_space_ref, va),
            CursorKind::Mutable => vm_space_cursor_mut_embedded(vm_space_ref, va),
        };
        match res {
            Option::Some(owner) => {
                let ghost id = fresh_cursor_id(s.cursors);
                axiom_fresh_cursor_id_not_in_dom(s.cursors);
                let tracked entry = axiom_cursor_entry_new(vs, kind, owner);
                s.cursors.tracked_insert(id, entry);
                assert(final(s).inv()) by {
                    assert forall|j: CursorId|
                        #[trigger] final(s).cursors.dom().contains(j)
                        implies final(s).cursors[j].owner.inv()
                            && final(s).vm_spaces.dom().contains(final(s).cursors[j].vm_space)
                    by {
                        if j == id {
                            assert(final(s).cursors[j] == entry);
                        } else {
                            assert(old(s).cursors.dom().contains(j));
                        }
                    };
                    assert forall|j: VmIoId|
                        #[trigger] final(s).vm_ios.dom().contains(j)
                        implies final(s).vm_ios[j].owner.inv()
                            && final(s).vm_spaces.dom().contains(final(s).vm_ios[j].vm_space)
                    by {
                        assert(old(s).vm_ios.dom().contains(j));
                        assert(final(s).vm_ios[j] == old(s).vm_ios[j]);
                    };
                };
            },
            Option::None => {
                // Failure case: store unchanged.
            },
        }
    }
}

proof fn drop_cursor_step<'a, 'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    if s.cursors.dom().contains(c) {
        let _ = s.cursors.tracked_remove(c);
    }
    assert(final(s).inv()) by {
        assert forall|j: CursorId|
            #[trigger] final(s).cursors.dom().contains(j)
            implies final(s).cursors[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).cursors[j].vm_space)
        by {
            assert(old(s).cursors.dom().contains(j));
            assert(final(s).cursors[j] == old(s).cursors[j]);
        };
        assert forall|j: VmIoId|
            #[trigger] final(s).vm_ios.dom().contains(j)
            implies final(s).vm_ios[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).vm_ios[j].vm_space)
        by {
            assert(old(s).vm_ios.dom().contains(j));
            assert(final(s).vm_ios[j] == old(s).vm_ios[j]);
        };
    };
}

proof fn cursor_method_step<'a, 'rcu>(
    tracked s: &mut VmStore<'rcu>,
    c: CursorId,
    method: CursorMethod,
)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    if s.cursors.dom().contains(c) {
        let tracked mut entry = s.cursors.tracked_remove(c);
        let ghost old_vm_space = entry.vm_space;
        let ghost old_kind = entry.kind;
        match method {
            CursorMethod::Query => cursor_query_embedded(&mut entry.owner),
            CursorMethod::FindNext(len) => cursor_find_next_embedded(&mut entry.owner, len),
            CursorMethod::Jump(va) => cursor_jump_embedded(&mut entry.owner, va),
            CursorMethod::ProtectNext(len) => cursor_mut_protect_next_embedded(&mut entry.owner, len),
        }
        assert(entry.vm_space == old_vm_space);
        assert(entry.kind == old_kind);
        s.cursors.tracked_insert(c, entry);
    }
    assert(final(s).inv()) by {
        assert forall|j: CursorId|
            #[trigger] final(s).cursors.dom().contains(j)
            implies final(s).cursors[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).cursors[j].vm_space)
        by {
            assert(old(s).cursors.dom().contains(j));
            if j == c {
                // entry's owner.inv() comes from the axiom; vm_space is preserved.
            } else {
                assert(final(s).cursors[j] == old(s).cursors[j]);
            }
        };
        assert forall|j: VmIoId|
            #[trigger] final(s).vm_ios.dom().contains(j)
            implies final(s).vm_ios[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).vm_ios[j].vm_space)
        by {
            assert(old(s).vm_ios.dom().contains(j));
            assert(final(s).vm_ios[j] == old(s).vm_ios[j]);
        };
    };
}

proof fn cursor_mut_regions_step<'a, 'rcu>(
    tracked s: &mut VmStore<'rcu>,
    c: CursorId,
    method: CursorMutRegionsMethod,
)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    if s.cursors.dom().contains(c) {
        let tracked mut entry = s.cursors.tracked_remove(c);
        let ghost old_vm_space = entry.vm_space;
        match method {
            CursorMutRegionsMethod::Unmap(len) => {
                cursor_mut_unmap_embedded(&mut entry.owner, &mut s.regions, len);
            },
        }
        assert(entry.vm_space == old_vm_space);
        s.cursors.tracked_insert(c, entry);
    }
    assert(final(s).inv()) by {
        // vm_spaces unchanged.
        assert forall|j: VmSpaceId|
            #[trigger] final(s).vm_spaces.dom().contains(j)
            implies final(s).vm_spaces[j].inv()
        by {
            assert(old(s).vm_spaces.dom().contains(j));
            assert(final(s).vm_spaces[j] == old(s).vm_spaces[j]);
        };
        assert forall|j: CursorId|
            #[trigger] final(s).cursors.dom().contains(j)
            implies final(s).cursors[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).cursors[j].vm_space)
        by {
            assert(old(s).cursors.dom().contains(j));
            if j == c {
                // entry's owner.inv() comes from the axiom; vm_space preserved.
            } else {
                assert(final(s).cursors[j] == old(s).cursors[j]);
            }
        };
        assert forall|j: VmIoId|
            #[trigger] final(s).vm_ios.dom().contains(j)
            implies final(s).vm_ios[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).vm_ios[j].vm_space)
        by {
            assert(old(s).vm_ios.dom().contains(j));
            assert(final(s).vm_ios[j] == old(s).vm_ios[j]);
        };
    };
}

proof fn map_step<'a, 'rcu>(
    tracked s: &mut VmStore<'rcu>,
    c: CursorId,
    frame: UFrame,
    prop: PageProperty,
)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    if s.cursors.dom().contains(c) {
        let tracked mut entry = s.cursors.tracked_remove(c);
        let ghost old_vm_space = entry.vm_space;
        cursor_mut_map_embedded(&mut entry.owner, &mut s.regions, frame, prop);
        assert(entry.vm_space == old_vm_space);
        s.cursors.tracked_insert(c, entry);
    }
    assert(final(s).inv()) by {
        assert forall|j: VmSpaceId|
            #[trigger] final(s).vm_spaces.dom().contains(j)
            implies final(s).vm_spaces[j].inv()
        by {
            assert(old(s).vm_spaces.dom().contains(j));
            assert(final(s).vm_spaces[j] == old(s).vm_spaces[j]);
        };
        assert forall|j: CursorId|
            #[trigger] final(s).cursors.dom().contains(j)
            implies final(s).cursors[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).cursors[j].vm_space)
        by {
            assert(old(s).cursors.dom().contains(j));
            if j == c {
                // entry's owner.inv() comes from the axiom; vm_space preserved.
            } else {
                assert(final(s).cursors[j] == old(s).cursors[j]);
            }
        };
        assert forall|j: VmIoId|
            #[trigger] final(s).vm_ios.dom().contains(j)
            implies final(s).vm_ios[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).vm_ios[j].vm_space)
        by {
            assert(old(s).vm_ios.dom().contains(j));
            assert(final(s).vm_ios[j] == old(s).vm_ios[j]);
        };
    };
}

proof fn new_vm_io_step<'a, 'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vs: VmSpaceId,
    vaddr: Vaddr,
    len: usize,
    kind: VmIoKind,
)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    if s.vm_spaces.dom().contains(vs) {
        let tracked vm_space_ref = s.vm_spaces.tracked_borrow(vs);
        let tracked res = match kind {
            VmIoKind::Reader => vm_space_reader_embedded(vm_space_ref, vaddr, len),
            VmIoKind::Writer => vm_space_writer_embedded(vm_space_ref, vaddr, len),
        };
        match res {
            Option::Some(owner) => {
                let ghost id = fresh_vm_io_id(s.vm_ios);
                axiom_fresh_vm_io_id_not_in_dom(s.vm_ios);
                let tracked entry = axiom_vm_io_entry_new(vs, kind, owner);
                s.vm_ios.tracked_insert(id, entry);
                assert(final(s).inv()) by {
                    assert forall|j: VmSpaceId|
                        #[trigger] final(s).vm_spaces.dom().contains(j)
                        implies final(s).vm_spaces[j].inv()
                    by {
                        assert(old(s).vm_spaces.dom().contains(j));
                        assert(final(s).vm_spaces[j] == old(s).vm_spaces[j]);
                    };
                    assert forall|j: CursorId|
                        #[trigger] final(s).cursors.dom().contains(j)
                        implies final(s).cursors[j].owner.inv()
                            && final(s).vm_spaces.dom().contains(final(s).cursors[j].vm_space)
                    by {
                        assert(old(s).cursors.dom().contains(j));
                        assert(final(s).cursors[j] == old(s).cursors[j]);
                    };
                    assert forall|j: VmIoId|
                        #[trigger] final(s).vm_ios.dom().contains(j)
                        implies final(s).vm_ios[j].owner.inv()
                            && final(s).vm_spaces.dom().contains(final(s).vm_ios[j].vm_space)
                    by {
                        if j == id {
                            assert(final(s).vm_ios[j] == entry);
                        } else {
                            assert(old(s).vm_ios.dom().contains(j));
                        }
                    };
                };
            },
            Option::None => {
                // Failure case: store unchanged.
            },
        }
    }
}

/// Smoke test: applies a chain of `step` calls and asserts `s.inv()` at
/// the end without any intermediate lemma calls. The fact that this
/// `proof fn` typechecks is the implicit-induction property — Verus
/// chains each step's `ensures` into the next step's `requires` for free,
/// and the final `s.inv()` falls out of the last step's `ensures`.
///
/// The specific ids passed (`0`) need not match any actual id allocated
/// during the chain; per-op steps that find no matching id are no-ops,
/// which still preserve `inv()`.
pub proof fn smoke_test<'a, 'rcu>(tracked s: &mut VmStore<'rcu>)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    step(s, Op::NewVmSpace);
    step(s, Op::OpenCursorMut { vs: 0int, va: 0..0 });
    step(s, Op::Query { c: 0int });
    step(s, Op::FindNext { c: 0int, len: 0 });
    step(s, Op::DropCursor { c: 0int });
    step(s, Op::NewReader { vs: 0int, vaddr: 0, len: 0 });
    step(s, Op::DropReader { vio: 0int });
    step(s, Op::DropVmSpace { vs: 0int });
}

proof fn drop_vm_io_step<'a, 'rcu>(tracked s: &mut VmStore<'rcu>, vio: VmIoId)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    if s.vm_ios.dom().contains(vio) {
        let _ = s.vm_ios.tracked_remove(vio);
    }
    assert(final(s).inv()) by {
        assert forall|j: VmSpaceId|
            #[trigger] final(s).vm_spaces.dom().contains(j)
            implies final(s).vm_spaces[j].inv()
        by {
            assert(old(s).vm_spaces.dom().contains(j));
            assert(final(s).vm_spaces[j] == old(s).vm_spaces[j]);
        };
        assert forall|j: CursorId|
            #[trigger] final(s).cursors.dom().contains(j)
            implies final(s).cursors[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).cursors[j].vm_space)
        by {
            assert(old(s).cursors.dom().contains(j));
            assert(final(s).cursors[j] == old(s).cursors[j]);
        };
        assert forall|j: VmIoId|
            #[trigger] final(s).vm_ios.dom().contains(j)
            implies final(s).vm_ios[j].owner.inv()
                && final(s).vm_spaces.dom().contains(final(s).vm_ios[j].vm_space)
        by {
            assert(old(s).vm_ios.dom().contains(j));
            assert(final(s).vm_ios[j] == old(s).vm_ios[j]);
        };
    };
}

} // verus!
