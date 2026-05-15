//! Deep embedding of the `VmSpace` and `VmReader`/`VmWriter` API.
//!
//! `VmStore` is the abstract state of a caller of these APIs: it holds
//! the [`MetaRegionOwners`] plus a registry of every owner object the
//! caller currently has access to.
//!
//! [`Op`] is an ADT enumerating the public exec API. [`step`] is the
//! single proof-mode dispatcher; it requires `s.inv()` *and* the
//! per-op precondition [`op_pre`] (which says the ids referenced in
//! `op` resolve to existing entries with the right cross-store
//! relationships). Every per-op step takes the relevant *tracked
//! entries directly* (extracted from the store by helpers like
//! [`VmStore::extract_cursor`]); the step bodies have neither
//! preconditions nor `if`-guards on store membership — that burden
//! lives only in `op_pre` (caller-discharged) and the extract/insert
//! store helpers.
//!
//! # Module layout
//!
//! - [`vm_space`]: ops on the [`crate::mm::vm_space::VmSpace`] type
//!   (`new`, drop).
//! - [`cursor`]: ops on `Cursor` / `CursorMut` (open, drop, `query`,
//!   `find_next`, `jump`, `map`, `unmap`, `protect_next`).
//! - [`io`]: ops on `VmReader` / `VmWriter` (creation, drop, the
//!   user-space and kernel-space IO methods).
//! - [`trace`]: explicit-induction theorems over `Seq<Op>`.
//!
//! # Soundness boundary: `_embedded` axioms
//!
//! Each axiom named `<exec_function_path>_embedded` mirrors the
//! `ensures` clause of one public exec function. Naming is the only
//! mechanism keeping the axiom in sync with its exec counterpart;
//! reviewers touching either side should grep for the partner.

pub mod vm_space;
pub mod cursor;
pub mod io;
pub mod trace;

use core::ops::Range;

use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::mm::frame::UFrame;
use crate::specs::mm::io::VmIoOwner;
use crate::mm::page_prop::PageProperty;
use crate::mm::vm_space::vm_space_specs::VmSpaceOwner;
use crate::mm::vm_space::UserPtConfig;
use crate::mm::{Vaddr, MAX_USERSPACE_VADDR};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::owners::CursorOwner;
use crate::specs::mm::page_table::node::Guards;
use crate::specs::mm::tlb::TlbModel;

verus! {

// =============================================================================
// Types
// =============================================================================

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
///
/// `vm_space` is `None` for VmIoOwners that have no parent `VmSpace` —
/// kernel-space readers/writers from `VmReader::from_kernel_space` /
/// `VmWriter::from_kernel_space`, and val_owners produced by
/// `read`. `Some(vs)` for entries created by `VmSpace::reader` /
/// `writer`.
///
/// View state is fully determined by `vm_space` + `kind`:
/// - `Some(_)` (userspace, Fallible): `mem_view: None`, exactly as
///   `VmSpace::reader`/`writer` ensure ([vm_space.rs:323/382](crate::mm::vm_space)).
///   Fallible methods are handle-only — no owner-side activation step
///   exists or is needed.
/// - `None && Reader` (kernel reader): `read_view_initialized()`, per
///   `VmReader<Infallible>::from_kernel_space` ensures.
/// - `None && Writer` (kernel writer or `consumed_w` val_owner from
///   `read`): `has_write_view()`, per `from_kernel_space` /
///   [`io::read_step`] ensures.
pub tracked struct VmIoEntry {
    pub vm_space: Option<VmSpaceId>,
    pub kind: VmIoKind,
    pub vaddr: Vaddr,
    pub len: usize,
    pub owner: VmIoOwner,
}

impl VmIoEntry {
    /// Per-entry invariant: derives view state from `vm_space` + `kind`.
    pub open spec fn inv(self) -> bool {
        &&& self.owner.inv()
        &&& match self.vm_space {
            Some(_) => self.owner.mem_view is None,
            None => match self.kind {
                VmIoKind::Reader => self.owner.read_view_initialized(),
                VmIoKind::Writer => self.owner.has_write_view(),
            },
        }
    }
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
/// `guards` is the lock-protocol state for the page-table nodes the
/// cursor holds locked; mirrors what the exec `Cursor` carries via
/// `path: [Option<PageTableGuard<'rcu, C>>; NR_LEVELS]`.
pub tracked struct CursorEntry<'rcu> {
    pub vm_space: VmSpaceId,
    pub kind: CursorKind,
    pub va: Range<Vaddr>,
    pub owner: CursorOwner<'rcu, UserPtConfig>,
    pub guards: Guards<'rcu, UserPtConfig>,
}

impl<'rcu> CursorEntry<'rcu> {
    /// The portion of the exec `Cursor::invariants(owner, regions, guards)`
    /// expressible from the entry alone (no `regions`).
    ///
    /// Mirrors `crate::mm::page_table::Cursor::invariants` minus
    /// `regions.inv()`, `metaregion_sound(regions)`, and the exec-handle
    /// pieces (`self.inv()` / `self.wf(owner)`). Those live in
    /// [`VmStore::inv`] (regions-touching) and are MODEL GAPS (handle).
    pub open spec fn inv(self) -> bool {
        &&& self.owner.inv()
        &&& self.owner.children_not_locked(self.guards)
        &&& self.owner.nodes_locked(self.guards)
        &&& !self.owner.popped_too_high
    }
}

/// Resource store: the abstract state visible to a caller of the
/// VmSpace + VmReader/VmWriter API.
///
/// `tlb_model` is the global TLB model; mirrors the per-CPU `TlbModel`
/// that `CursorMut::map`/`unmap` and `flusher` operate on. We keep one
/// per store on the conservative assumption that any cursor mutation
/// interacts with it.
pub tracked struct VmStore<'rcu> {
    pub regions: MetaRegionOwners,
    pub tlb_model: TlbModel,
    pub vm_spaces: Map<VmSpaceId, VmSpaceOwner>,
    pub cursors: Map<CursorId, CursorEntry<'rcu>>,
    pub vm_ios: Map<VmIoId, VmIoEntry>,
}

impl<'a, 'rcu> VmStore<'rcu> {
    /// The store's top-level invariant.
    pub open spec fn inv(self) -> bool {
        &&& self.regions.inv()
        &&& self.tlb_model.inv()
        &&& forall|id: VmSpaceId|
                #[trigger] self.vm_spaces.dom().contains(id)
                    ==> self.vm_spaces[id].inv()
        &&& forall|id: CursorId|
                #[trigger] self.cursors.dom().contains(id)
                    ==> self.cursors[id].inv()
        &&& forall|id: CursorId|
                #[trigger] self.cursors.dom().contains(id)
                    ==> self.cursors[id].owner.metaregion_sound(self.regions)
        &&& forall|id: CursorId|
                #[trigger] self.cursors.dom().contains(id)
                    ==> self.vm_spaces.dom().contains(self.cursors[id].vm_space)
        &&& forall|id: VmIoId|
                #[trigger] self.vm_ios.dom().contains(id)
                    ==> self.vm_ios[id].inv()
        &&& forall|id: VmIoId|
                #[trigger] self.vm_ios.dom().contains(id)
                    ==> (self.vm_ios[id].vm_space matches Some(vs)
                            ==> self.vm_spaces.dom().contains(vs))
        &&& forall|id: VmIoId|
                #[trigger] self.vm_ios.dom().contains(id)
                    ==> self.vm_ios[id].vm_space is Some
                            ==> (self.vm_ios[id].vaddr as nat)
                                + (self.vm_ios[id].len as nat)
                                <= MAX_USERSPACE_VADDR as nat
    }
}

// =============================================================================
// Op enum + per-op precondition
// =============================================================================

/// Public exec API of `ostd::mm::vm_space` and `ostd::mm::io`, lifted
/// to data.
pub enum Op {
    NewVmSpace,
    DropVmSpace { vs: VmSpaceId },
    OpenCursor { vs: VmSpaceId, va: Range<Vaddr> },
    OpenCursorMut { vs: VmSpaceId, va: Range<Vaddr> },
    DropCursor { c: CursorId },
    Query { c: CursorId },
    FindNext { c: CursorId, len: usize },
    Jump { c: CursorId, va: Vaddr },
    VirtAddr { c: CursorId },
    Map { c: CursorId, frame: UFrame, prop: PageProperty },
    Unmap { c: CursorId, len: usize },
    ProtectNext { c: CursorId, len: usize },
    NewReader { vs: VmSpaceId, vaddr: Vaddr, len: usize },
    NewWriter { vs: VmSpaceId, vaddr: Vaddr, len: usize },
    NewKernelReader { vaddr: Vaddr, len: usize },
    NewKernelWriter { vaddr: Vaddr, len: usize },
    DropReader { vio: VmIoId },
    DropWriter { vio: VmIoId },
    /// Fallible `VmReader::read_val<T>`. The exec spec carries no
    /// tracked owner params (handle MODEL GAP); the embedding step
    /// is consequently a no-op on `VmStore`.
    ReaderReadVal { source: VmIoId },
    /// Fallible `VmReader::collect`. Same shape as `ReaderReadVal`.
    ReaderCollect { source: VmIoId },
    ReaderLimit { vio: VmIoId, max: usize },
    ReaderSkip { vio: VmIoId, n: usize },
    ReaderQuery { vio: VmIoId },
    /// Fallible `VmWriter::write_val<T>`. Same shape as `ReaderReadVal`.
    WriterWriteVal { writer: VmIoId },
    WriterFillZeros { vio: VmIoId, len: usize },
    WriterLimit { vio: VmIoId, max: usize },
    WriterSkip { vio: VmIoId, n: usize },
    WriterQuery { vio: VmIoId },
    /// Infallible `VmReader::read`. Produces a `consumed_w` val_owner
    /// (registered as a fresh activated Writer entry).
    Read { source: VmIoId, dest: VmIoId },
    /// Infallible `VmWriter::write`. The exec no longer surfaces
    /// `consumed_w`; the embedding does NOT create a fresh entry.
    Write { source: VmIoId, dest: VmIoId },
}

/// Per-op precondition — the conjunction of facts about the store that
/// must hold for an `Op` to be applied. Encodes id-existence,
/// distinctness, cross-store ref-integrity, and the *expressible*
/// portion of the exec-method preconditions (per-op `requires` from
/// the verus_spec annotations). MODEL GAPS (handle inv/wf,
/// `tlb_model.inv()` is in `VmStore::inv`, closure preconditions on
/// `protect_next`, `size_of::<T>()` range bounds on
/// `read_val`/`write_val`/`collect`) are documented in
/// [`super::cursor`] and [`super::io`] axiom comments.
///
/// [`step`] requires `op_pre(*old(s), op)`. Callers must establish the
/// precondition for the specific Op variant they're about to apply.
pub open spec fn op_pre<'rcu>(s: VmStore<'rcu>, op: Op) -> bool {
    match op {
        Op::NewVmSpace => true,
        Op::DropVmSpace { vs } =>
            s.vm_spaces.dom().contains(vs)
            && (forall|c: CursorId|
                #[trigger] s.cursors.dom().contains(c)
                    ==> s.cursors[c].vm_space != vs)
            && (forall|v: VmIoId|
                #[trigger] s.vm_ios.dom().contains(v)
                    ==> s.vm_ios[v].vm_space != Some(vs)),
        Op::OpenCursor { vs, va: _ } => s.vm_spaces.dom().contains(vs),
        Op::OpenCursorMut { vs, va: _ } => s.vm_spaces.dom().contains(vs),
        Op::DropCursor { c } => s.cursors.dom().contains(c),
        // exec `Cursor::query` / `CursorMut::query` requires
        // `owner.in_locked_range()`.
        Op::Query { c } =>
            s.cursors.dom().contains(c)
            && s.cursors[c].owner.in_locked_range(),
        Op::FindNext { c, len: _ } => s.cursors.dom().contains(c),
        // exec `Cursor::jump` / `CursorMut::jump` requires
        // `owner.in_locked_range()`.
        Op::Jump { c, va: _ } =>
            s.cursors.dom().contains(c)
            && s.cursors[c].owner.in_locked_range(),
        Op::VirtAddr { c } => s.cursors.dom().contains(c),
        // exec `CursorMut::map` requires `owner.in_locked_range()` (and
        // `tlb_model.inv()` from `VmStore::inv`, plus MODEL GAP `item_wf`).
        Op::Map { c, frame: _, prop: _ } =>
            s.cursors.dom().contains(c)
            && s.cursors[c].owner.in_locked_range(),
        Op::Unmap { c, len: _ } => s.cursors.dom().contains(c),
        Op::ProtectNext { c, len: _ } => s.cursors.dom().contains(c),
        Op::NewReader { vs, vaddr: _, len: _ } => s.vm_spaces.dom().contains(vs),
        Op::NewWriter { vs, vaddr: _, len: _ } => s.vm_spaces.dom().contains(vs),
        Op::NewKernelReader { vaddr: _, len: _ } => true,
        Op::NewKernelWriter { vaddr: _, len: _ } => true,
        Op::DropReader { vio } => s.vm_ios.dom().contains(vio),
        Op::DropWriter { vio } => s.vm_ios.dom().contains(vio),
        // exec Fallible `read_val` (line 1610): no tracked owner
        // params — only `self.inv()` (handle MODEL GAP). op_pre is
        // purely structural.
        Op::ReaderReadVal { source } => s.vm_ios.dom().contains(source),
        // exec Fallible `collect` (line 1652): same — handle-only.
        Op::ReaderCollect { source } => s.vm_ios.dom().contains(source),
        Op::ReaderLimit { vio, max: _ } => s.vm_ios.dom().contains(vio),
        Op::ReaderSkip { vio, n: _ } => s.vm_ios.dom().contains(vio),
        Op::ReaderQuery { vio } => s.vm_ios.dom().contains(vio),
        // exec Fallible `write_val` (line 2361): no tracked owner
        // params — handle-only.
        Op::WriterWriteVal { writer } => s.vm_ios.dom().contains(writer),
        Op::WriterFillZeros { vio, len: _ } => s.vm_ios.dom().contains(vio),
        Op::WriterLimit { vio, max: _ } => s.vm_ios.dom().contains(vio),
        Op::WriterSkip { vio, n: _ } => s.vm_ios.dom().contains(vio),
        Op::WriterQuery { vio } => s.vm_ios.dom().contains(vio),
        // exec Infallible `read`: source must be a kernel Reader (gives
        // `read_view_initialized` via `VmIoEntry::inv`); dest must be a
        // kernel Writer (gives `has_write_view`). Userspace (vm_space:
        // Some) entries can never serve as the operands here — exec is
        // typed `VmReader<Infallible>` / `VmWriter<Infallible>`.
        Op::Read { source, dest } =>
            s.vm_ios.dom().contains(source)
            && s.vm_ios.dom().contains(dest)
            && source != dest
            && s.vm_ios[source].vm_space is None
            && (s.vm_ios[source].kind == VmIoKind::Reader)
            && s.vm_ios[dest].vm_space is None
            && (s.vm_ios[dest].kind == VmIoKind::Writer),
        // exec Infallible `write`: same shape as `read`.
        Op::Write { source, dest } =>
            s.vm_ios.dom().contains(source)
            && s.vm_ios.dom().contains(dest)
            && source != dest
            && s.vm_ios[source].vm_space is None
            && (s.vm_ios[source].kind == VmIoKind::Reader)
            && s.vm_ios[dest].vm_space is None
            && (s.vm_ios[dest].kind == VmIoKind::Writer),
    }
}

// =============================================================================
// Store helpers: extract / insert. These are the *only* functions that
// have preconditions about store membership; per-op steps don't.
// =============================================================================

impl<'rcu> VmStore<'rcu> {
    /// Removes the VmSpaceOwner at `vs` from the store and returns it.
    /// Requires no cursor or VmIo refers to `vs`, and no activated
    /// ranges remain on `vs` (otherwise `inv` would break after the
    /// removal).
    pub proof fn extract_vm_space(tracked &mut self, vs: VmSpaceId) -> (tracked res: VmSpaceOwner)
        requires
            old(self).inv(),
            old(self).vm_spaces.dom().contains(vs),
            forall|c: CursorId|
                #[trigger] old(self).cursors.dom().contains(c)
                    ==> old(self).cursors[c].vm_space != vs,
            forall|v: VmIoId|
                #[trigger] old(self).vm_ios.dom().contains(v)
                    ==> old(self).vm_ios[v].vm_space != Some(vs),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces.remove(vs),
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            res == old(self).vm_spaces[vs],
            final(self).inv(),
    {
        self.vm_spaces.tracked_remove(vs)
    }

    /// Inserts a VmSpaceOwner at the given fresh id. Requires the id is
    /// not already used and the owner satisfies its invariant.
    pub proof fn insert_vm_space(
        tracked &mut self,
        vs: VmSpaceId,
        tracked owner: VmSpaceOwner,
    )
        requires
            old(self).inv(),
            !old(self).vm_spaces.dom().contains(vs),
            owner.inv(),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces.insert(vs, owner),
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).inv(),
    {
        self.vm_spaces.tracked_insert(vs, owner);
    }

    /// Removes the cursor entry at `c` from the store and returns it.
    pub proof fn extract_cursor(tracked &mut self, c: CursorId)
        -> (tracked res: CursorEntry<'rcu>)
        requires
            old(self).inv(),
            old(self).cursors.dom().contains(c),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors.remove(c),
            final(self).vm_ios == old(self).vm_ios,
            res == old(self).cursors[c],
            final(self).inv(),
    {
        self.cursors.tracked_remove(c)
    }

    /// Inserts a cursor entry at the given fresh id. Requires the id is
    /// not already used, the entry satisfies its inv, the entry's
    /// `vm_space` is in the store, and the entry's owner is sound w.r.t.
    /// the store's regions.
    pub proof fn insert_cursor(
        tracked &mut self,
        c: CursorId,
        tracked entry: CursorEntry<'rcu>,
    )
        requires
            old(self).inv(),
            !old(self).cursors.dom().contains(c),
            entry.inv(),
            entry.owner.metaregion_sound(old(self).regions),
            old(self).vm_spaces.dom().contains(entry.vm_space),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors.insert(c, entry),
            final(self).vm_ios == old(self).vm_ios,
            final(self).inv(),
    {
        self.cursors.tracked_insert(c, entry);
    }

    /// Removes the VmIo entry at `vio` from the store and returns it.
    pub proof fn extract_vm_io(tracked &mut self, vio: VmIoId)
        -> (tracked res: VmIoEntry)
        requires
            old(self).inv(),
            old(self).vm_ios.dom().contains(vio),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios.remove(vio),
            res == old(self).vm_ios[vio],
            final(self).inv(),
    {
        self.vm_ios.tracked_remove(vio)
    }

    /// Inserts a VmIo entry at the given fresh id. Requires the id is
    /// not already used, the entry satisfies its inv, the entry's
    /// `vm_space` (if `Some`) refers to a live VmSpace, the range
    /// bound holds when `vm_space` is `Some`, and (if the entry is
    /// activated) its owner range is disjoint from every existing
    /// activated entry's owner range (preserves the pairwise-disjoint
    /// invariant in [`VmStore::inv`]).
    pub proof fn insert_vm_io(
        tracked &mut self,
        vio: VmIoId,
        tracked entry: VmIoEntry,
    )
        requires
            old(self).inv(),
            !old(self).vm_ios.dom().contains(vio),
            entry.inv(),
            entry.vm_space matches Some(vs)
                ==> old(self).vm_spaces.dom().contains(vs),
            entry.vm_space is Some
                ==> (entry.vaddr as nat) + (entry.len as nat)
                        <= MAX_USERSPACE_VADDR as nat,
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios.insert(vio, entry),
            final(self).inv(),
    {
        self.vm_ios.tracked_insert(vio, entry);
    }
}

// =============================================================================
// One-step soundness theorem.
// =============================================================================

/// One-step soundness theorem.
///
/// `op_pre(*old(s), op)` is the per-op precondition. Each match arm
/// extracts the relevant entries from the store, calls the per-op step
/// (which has neither preconditions nor `if`-guards on store membership),
/// and inserts any modified or freshly-produced entries back.
pub proof fn step<'rcu>(tracked s: &mut VmStore<'rcu>, op: Op)
    requires
        old(s).inv(),
        op_pre(*old(s), op),
    ensures
        final(s).inv(),
{
    match op {
        Op::NewVmSpace => step_new_vm_space(s),
        Op::DropVmSpace { vs } => step_drop_vm_space(s, vs),
        Op::OpenCursor { vs, va } => step_open_cursor(s, vs, va, CursorKind::ReadOnly),
        Op::OpenCursorMut { vs, va } => step_open_cursor(s, vs, va, CursorKind::Mutable),
        Op::DropCursor { c } => step_drop_cursor(s, c),
        Op::Query { c } => step_cursor_method(s, c, cursor::CursorMethod::Query),
        Op::FindNext { c, len } => step_cursor_method(s, c, cursor::CursorMethod::FindNext(len)),
        Op::Jump { c, va } => step_cursor_method(s, c, cursor::CursorMethod::Jump(va)),
        Op::VirtAddr { c: _ } => {},
        Op::Map { c, frame, prop } => step_map(s, c, frame, prop),
        Op::Unmap { c, len } => step_unmap(s, c, len),
        Op::ProtectNext { c, len } =>
            step_cursor_method(s, c, cursor::CursorMethod::ProtectNext(len)),
        Op::NewReader { vs, vaddr, len } => step_new_vm_io(s, vs, vaddr, len, VmIoKind::Reader),
        Op::NewWriter { vs, vaddr, len } => step_new_vm_io(s, vs, vaddr, len, VmIoKind::Writer),
        Op::NewKernelReader { vaddr, len } => step_new_kernel_vm_io(s, vaddr, len, VmIoKind::Reader),
        Op::NewKernelWriter { vaddr, len } => step_new_kernel_vm_io(s, vaddr, len, VmIoKind::Writer),
        Op::DropReader { vio } => step_drop_vm_io(s, vio),
        Op::DropWriter { vio } => step_drop_vm_io(s, vio),
        // Fallible variants: handle-only, no embedding state changes.
        Op::ReaderReadVal { source: _ } => {},
        Op::ReaderCollect { source: _ } => {},
        Op::WriterWriteVal { writer: _ } => {},
        Op::ReaderLimit { vio, max } =>
            step_vm_io_method(s, vio, io::VmIoMethod::ReaderLimit(max)),
        Op::ReaderSkip { vio, n } =>
            step_vm_io_method(s, vio, io::VmIoMethod::ReaderSkip(n)),
        Op::ReaderQuery { vio: _ } => {},
        Op::WriterFillZeros { vio, len } =>
            step_vm_io_method(s, vio, io::VmIoMethod::WriterFillZeros(len)),
        Op::WriterLimit { vio, max } =>
            step_vm_io_method(s, vio, io::VmIoMethod::WriterLimit(max)),
        Op::WriterSkip { vio, n } =>
            step_vm_io_method(s, vio, io::VmIoMethod::WriterSkip(n)),
        Op::WriterQuery { vio: _ } => {},
        // Infallible `read`: produces a fresh activated-Writer val_owner.
        Op::Read { source, dest } => step_read(s, source, dest),
        // Infallible `write`: no longer surfaces consumed_w; just
        // mutates source/dest owners.
        Op::Write { source, dest } => step_write(s, source, dest),
    }
}

// --- Per-arm proof helpers (kept individually so SMT context stays small) ---

proof fn step_new_vm_space<'rcu>(tracked s: &mut VmStore<'rcu>)
    requires old(s).inv()
    ensures final(s).inv()
{
    let tracked owner = vm_space::new_vm_space_step(&mut s.regions);
    let ghost id = fresh_vm_space_id(s.vm_spaces);
    axiom_fresh_vm_space_id_not_in_dom(s.vm_spaces);
    s.insert_vm_space(id, owner);
}

proof fn step_drop_vm_space<'rcu>(tracked s: &mut VmStore<'rcu>, vs: VmSpaceId)
    requires
        old(s).inv(),
        old(s).vm_spaces.dom().contains(vs),
        forall|c: CursorId|
            #[trigger] old(s).cursors.dom().contains(c)
                ==> old(s).cursors[c].vm_space != vs,
        forall|v: VmIoId|
            #[trigger] old(s).vm_ios.dom().contains(v)
                ==> old(s).vm_ios[v].vm_space != Some(vs),
    ensures final(s).inv()
{
    let tracked owner = s.extract_vm_space(vs);
    vm_space::drop_vm_space_step(owner);
}

proof fn step_open_cursor<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vs: VmSpaceId,
    va: Range<Vaddr>,
    kind: CursorKind,
)
    requires
        old(s).inv(),
        old(s).vm_spaces.dom().contains(vs),
    ensures final(s).inv()
{
    let tracked vm_space_ref = s.vm_spaces.tracked_borrow(vs);
    let tracked res = cursor::open_cursor_step(vm_space_ref, &mut s.regions, vs, va, kind);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_cursor_id(s.cursors);
            axiom_fresh_cursor_id_not_in_dom(s.cursors);
            s.insert_cursor(id, entry);
        },
        Option::None => {},
    }
}

proof fn step_drop_cursor<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
    ensures final(s).inv()
{
    let tracked entry = s.extract_cursor(c);
    cursor::drop_cursor_step(entry);
}

proof fn step_cursor_method<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    c: CursorId,
    method: cursor::CursorMethod,
)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
        match method {
            cursor::CursorMethod::Query => old(s).cursors[c].owner.in_locked_range(),
            cursor::CursorMethod::Jump(_) => old(s).cursors[c].owner.in_locked_range(),
            _ => true,
        },
    ensures final(s).inv()
{
    let tracked mut entry = s.extract_cursor(c);
    cursor::cursor_method_step(&mut entry, &mut s.regions, method);
    s.insert_cursor(c, entry);
}

proof fn step_map<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    c: CursorId,
    frame: UFrame,
    prop: PageProperty,
)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
        old(s).cursors[c].owner.in_locked_range(),
    ensures final(s).inv()
{
    let tracked mut entry = s.extract_cursor(c);
    cursor::map_step(&mut entry, &mut s.regions, &mut s.tlb_model, frame, prop);
    s.insert_cursor(c, entry);
}

proof fn step_unmap<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId, len: usize)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
    ensures final(s).inv()
{
    let tracked mut entry = s.extract_cursor(c);
    cursor::cursor_mut_regions_step(
        &mut entry,
        &mut s.regions,
        &mut s.tlb_model,
        cursor::CursorMutRegionsMethod::Unmap(len),
    );
    s.insert_cursor(c, entry);
}

proof fn step_new_vm_io<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vs: VmSpaceId,
    vaddr: Vaddr,
    len: usize,
    kind: VmIoKind,
)
    requires
        old(s).inv(),
        old(s).vm_spaces.dom().contains(vs),
    ensures final(s).inv()
{
    let tracked vm_space_ref = s.vm_spaces.tracked_borrow(vs);
    let tracked res = io::new_vm_io_step(vm_space_ref, Some(vs), vaddr, len, kind);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_vm_io_id(s.vm_ios);
            axiom_fresh_vm_io_id_not_in_dom(s.vm_ios);
            s.insert_vm_io(id, entry);
        },
        Option::None => {},
    }
}

proof fn step_new_kernel_vm_io<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vaddr: Vaddr,
    len: usize,
    kind: VmIoKind,
)
    requires old(s).inv()
    ensures final(s).inv()
{
    let tracked entry = io::new_kernel_vm_io_step(vaddr, len, kind);
    let ghost id = fresh_vm_io_id(s.vm_ios);
    axiom_fresh_vm_io_id_not_in_dom(s.vm_ios);
    s.insert_vm_io(id, entry);
}

proof fn step_drop_vm_io<'rcu>(tracked s: &mut VmStore<'rcu>, vio: VmIoId)
    requires
        old(s).inv(),
        old(s).vm_ios.dom().contains(vio),
    ensures final(s).inv()
{
    let tracked entry = s.extract_vm_io(vio);
    io::drop_vm_io_step(entry);
}

proof fn step_vm_io_method<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vio: VmIoId,
    method: io::VmIoMethod,
)
    requires
        old(s).inv(),
        old(s).vm_ios.dom().contains(vio),
    ensures final(s).inv()
{
    let tracked mut entry = s.extract_vm_io(vio);
    io::vm_io_method_step(&mut entry, method);
    s.insert_vm_io(vio, entry);
}

proof fn step_read<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    source: VmIoId,
    dest: VmIoId,
)
    requires
        old(s).inv(),
        old(s).vm_ios.dom().contains(source),
        old(s).vm_ios.dom().contains(dest),
        source != dest,
        old(s).vm_ios[source].vm_space is None,
        old(s).vm_ios[source].kind == VmIoKind::Reader,
        old(s).vm_ios[dest].vm_space is None,
        old(s).vm_ios[dest].kind == VmIoKind::Writer,
    ensures final(s).inv()
{
    let tracked mut src = s.extract_vm_io(source);
    let tracked mut dst = s.extract_vm_io(dest);
    let tracked val = io::read_step(&mut src, &mut dst);
    s.insert_vm_io(source, src);
    s.insert_vm_io(dest, dst);
    let ghost id = fresh_vm_io_id(s.vm_ios);
    axiom_fresh_vm_io_id_not_in_dom(s.vm_ios);
    s.insert_vm_io(id, val);
}

proof fn step_write<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    source: VmIoId,
    dest: VmIoId,
)
    requires
        old(s).inv(),
        old(s).vm_ios.dom().contains(source),
        old(s).vm_ios.dom().contains(dest),
        source != dest,
        old(s).vm_ios[source].vm_space is None,
        old(s).vm_ios[source].kind == VmIoKind::Reader,
        old(s).vm_ios[dest].vm_space is None,
        old(s).vm_ios[dest].kind == VmIoKind::Writer,
    ensures final(s).inv()
{
    let tracked mut src = s.extract_vm_io(source);
    let tracked mut dst = s.extract_vm_io(dest);
    io::write_step(&mut src, &mut dst);
    s.insert_vm_io(source, src);
    s.insert_vm_io(dest, dst);
}

// =============================================================================
// Internal helpers: fresh-id picking and tracked entry constructors.
// =============================================================================

/// Picks an id not currently in `m.dom()`. Since the key type is `int`,
/// an unused id always exists.
pub open spec fn fresh_vm_space_id<'a>(m: Map<VmSpaceId, VmSpaceOwner>) -> VmSpaceId {
    choose|id: VmSpaceId| !m.dom().contains(id)
}

/// Picks a cursor id not currently in `m.dom()`.
pub open spec fn fresh_cursor_id<'rcu>(m: Map<CursorId, CursorEntry<'rcu>>) -> CursorId {
    choose|id: CursorId| !m.dom().contains(id)
}

/// Picks a [`VmIoId`] not currently in `m.dom()`.
pub open spec fn fresh_vm_io_id<'a>(m: Map<VmIoId, VmIoEntry>) -> VmIoId {
    choose|id: VmIoId| !m.dom().contains(id)
}

pub axiom fn axiom_fresh_vm_space_id_not_in_dom<'a>(
    m: Map<VmSpaceId, VmSpaceOwner>,
)
    ensures
        !m.dom().contains(fresh_vm_space_id(m)),
;

pub axiom fn axiom_fresh_cursor_id_not_in_dom<'rcu>(
    m: Map<CursorId, CursorEntry<'rcu>>,
)
    ensures
        !m.dom().contains(fresh_cursor_id(m)),
;

pub axiom fn axiom_fresh_vm_io_id_not_in_dom<'a>(m: Map<VmIoId, VmIoEntry>)
    ensures
        !m.dom().contains(fresh_vm_io_id(m)),
;

/// Tracked constructor for [`CursorEntry`].
pub axiom fn axiom_cursor_entry_new<'rcu>(
    vm_space: VmSpaceId,
    kind: CursorKind,
    va: Range<Vaddr>,
    tracked owner: CursorOwner<'rcu, UserPtConfig>,
    tracked guards: Guards<'rcu, UserPtConfig>,
) -> (tracked res: CursorEntry<'rcu>)
    ensures
        res.vm_space == vm_space,
        res.kind == kind,
        res.va == va,
        res.owner == owner,
        res.guards == guards,
;

/// Tracked constructor for [`VmIoEntry`].
pub axiom fn axiom_vm_io_entry_new<'a>(
    vm_space: Option<VmSpaceId>,
    kind: VmIoKind,
    vaddr: Vaddr,
    len: usize,
    tracked owner: VmIoOwner,
) -> (tracked res: VmIoEntry)
    ensures
        res.vm_space == vm_space,
        res.kind == kind,
        res.vaddr == vaddr,
        res.len == len,
        res.owner == owner,
;

} // verus!
