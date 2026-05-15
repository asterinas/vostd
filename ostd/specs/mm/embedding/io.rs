//! Embedding of `VmReader` / `VmWriter` operations.
//!
//! Per-op steps operate on tracked owners directly — no store lookups,
//! no preconditions on store membership, no `if`-guards. The store-side
//! extract / insert and id-management lives in
//! [`super::VmStore`]'s methods and the [`super::step`] dispatcher.
//!
//! Methods modeled (per the visibility audit against upstream
//! `/home/sean/vostd/ostd/src/mm/io.rs`):
//!
//! - **VmReader<Fallible>**: `read_val<T>`, `collect`, `limit`, `skip`.
//! - **VmWriter<Fallible>**: `write_val<T>`, `fill_zeros`, `limit`, `skip`.
//! - **VmReader<Infallible>**: `from_kernel_space`, `read`.
//! - **VmWriter<Infallible>**: `from_kernel_space`, `write`.
//! - **Pure-read methods** (`remain`, `has_remain`, `cursor` on reader;
//!   `avail`, `has_avail`, `cursor` on writer): grouped under
//!   [`super::Op::ReaderQuery`] and [`super::Op::WriterQuery`] —
//!   handled directly by the dispatcher (no per-op step needed).
//!
//! # Mirroring exec preconditions
//!
//! After the most recent exec spec changes, only Infallible `read` /
//! `write` carry tracked owner params. The Fallible variants
//! (`read_val`, `collect`, `write_val`) and Infallible `read_val` /
//! `write_val` are handle-only — exec `requires` reduces to
//! `self.inv()` (handle MODEL GAP). Their embedding ops are
//! consequently no-ops on `VmStore`.
//!
//! For Infallible `read` / `write`, the exec `requires`:
//! - `owner.inv()` — expressible.
//! - `owner.has_write_view()`, `owner.read_view_initialized()` —
//!   discharged via `VmIoEntry::inv` from `activated && Writer/Reader`.
//!
//! # Model gaps
//!
//! - **Exec `VmReader` / `VmWriter` handle**: exec `requires` includes
//!   `self.inv()` and `self.wf(owner)` over the runtime handle. We
//!   don't model the handle, so these conjuncts are MODEL GAPS.
//! - **`remain_spec` / `avail_spec`-bound preconditions**: `skip`
//!   requires `nbytes <= self.remain_spec()`. Handle-derived,
//!   inexpressible without the handle.
//! - **`from_kernel_space`**: exec ensures `read_view_initialized()` /
//!   `has_write_view()` only under a kernel-VA range guard
//!   (`KERNEL_BASE_VADDR <= ptr.vaddr && ptr.vaddr+len <= KERNEL_END_VADDR`).
//!   We assume that branch (i.e., the axioms commit to
//!   `read_view_initialized()` / `has_write_view()` unconditionally) —
//!   formally a slight strengthening pending kernel-VA modeling.

use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::specs::mm::io::VmIoOwner;
use crate::mm::vm_space::vm_space_specs::VmSpaceOwner;
use crate::mm::{Vaddr, MAX_USERSPACE_VADDR};

use super::{axiom_vm_io_entry_new, VmIoEntry, VmIoKind, VmSpaceId};

verus! {

// =============================================================================
// _embedded axioms
// =============================================================================

/// Mirror of [`crate::mm::vm_space::VmSpace::reader`].
///
/// Exec ensures `reader_owner@.unwrap().mem_view is None` ([vm_space.rs:323](crate::mm::vm_space)).
pub axiom fn vm_space_reader_embedded<'a>(
    tracked vm_space: &VmSpaceOwner,
    vaddr: Vaddr,
    len: usize,
) -> (tracked res: Option<VmIoOwner>)
    requires
        vm_space.inv(),
    ensures
        res matches Some(o) ==> o.inv(),
        res matches Some(o) ==> o.mem_view is None,
        res is Some ==> (vaddr as nat) + (len as nat) <= MAX_USERSPACE_VADDR as nat,
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
        res matches Some(o) ==> o.mem_view is None,
        res is Some ==> (vaddr as nat) + (len as nat) <= MAX_USERSPACE_VADDR as nat,
;

/// Mirror of [`crate::mm::io::VmReader<Infallible>::from_kernel_space`].
///
/// Exec ensures (line 1247-1255) that under the kernel-VA range guard,
/// the produced owner satisfies `read_view_initialized()`. We
/// instantiate the axiom on that branch — the resulting entry is
/// pre-activated as a Reader.
pub axiom fn vm_reader_from_kernel_space_embedded(vaddr: Vaddr, len: usize)
    -> (tracked res: VmIoOwner)
    ensures
        res.inv(),
        res.read_view_initialized(),
;

/// Mirror of [`crate::mm::io::VmWriter<Infallible>::from_kernel_space`].
///
/// Exec ensures (line 787-795) that with `fallible = false` and under
/// the kernel-VA range guard, the produced owner satisfies
/// `has_write_view()`. Pre-activated as a Writer.
pub axiom fn vm_writer_from_kernel_space_embedded(vaddr: Vaddr, len: usize)
    -> (tracked res: VmIoOwner)
    ensures
        res.inv(),
        res.has_write_view(),
;

/// Mirror of [`crate::mm::io::VmReader::read`] (Infallible).
///
/// Exec requires: `self.inv()`, `writer.inv()`, `self.wf(owner_r)`,
/// `writer.wf(owner_w)`, `owner_w.has_write_view()`, `owner_r.read_view_initialized()`.
///
/// Expressible: owner inv, has_write_view, read_view_initialized.
/// MODEL GAP: handle inv/wf.
pub axiom fn vm_reader_read_embedded(
    tracked source_owner: &mut VmIoOwner,
    tracked dest_owner: &mut VmIoOwner,
) -> (tracked consumed_w: VmIoOwner)
    requires
        old(source_owner).inv(),
        old(dest_owner).inv(),
        old(source_owner).read_view_initialized(),
        old(dest_owner).has_write_view(),
    ensures
        final(source_owner).inv(),
        final(dest_owner).inv(),
        final(source_owner).read_view_initialized(),
        final(dest_owner).has_write_view(),
        // Source/dest ranges only shrink (start advances).
        final(source_owner).range@.start >= old(source_owner).range@.start,
        final(source_owner).range@.end == old(source_owner).range@.end,
        final(dest_owner).range@.start >= old(dest_owner).range@.start,
        final(dest_owner).range@.end == old(dest_owner).range@.end,
        consumed_w.inv(),
        consumed_w.has_write_view(),
        // consumed_w covers the just-written portion of dest.
        consumed_w.range@.start >= old(dest_owner).range@.start,
        consumed_w.range@.end <= final(dest_owner).range@.start,
;

/// Mirror of [`crate::mm::io::VmReader::limit`].
///
/// Exec only mutates the handle's `end` field (no owner mutation), so
/// owner state is fully preserved.
pub axiom fn vm_reader_limit_embedded(tracked owner: &mut VmIoOwner, max_remain: usize)
    requires
        old(owner).inv(),
    ensures
        final(owner).inv(),
        *final(owner) == *old(owner),
;

/// Mirror of [`crate::mm::io::VmReader::skip`].
///
/// Exec only mutates the handle's `cursor` field (no owner mutation).
pub axiom fn vm_reader_skip_embedded(tracked owner: &mut VmIoOwner, nbytes: usize)
    requires
        old(owner).inv(),
    ensures
        final(owner).inv(),
        *final(owner) == *old(owner),
;

/// Mirror of [`crate::mm::io::VmWriter::write`] (Infallible).
///
/// Exec no longer surfaces `consumed_w` (the body delegates to
/// `reader.read(self)` and discards its split-off output). So this
/// axiom mutates both owners but produces nothing new.
pub axiom fn vm_writer_write_embedded(
    tracked source_owner: &mut VmIoOwner,
    tracked dest_owner: &mut VmIoOwner,
)
    requires
        old(source_owner).inv(),
        old(dest_owner).inv(),
        old(source_owner).read_view_initialized(),
        old(dest_owner).has_write_view(),
    ensures
        final(source_owner).inv(),
        final(dest_owner).inv(),
        final(source_owner).read_view_initialized(),
        final(dest_owner).has_write_view(),
        // Ranges only shrink (start advances; end fixed).
        final(source_owner).range@.start >= old(source_owner).range@.start,
        final(source_owner).range@.end == old(source_owner).range@.end,
        final(dest_owner).range@.start >= old(dest_owner).range@.start,
        final(dest_owner).range@.end == old(dest_owner).range@.end,
;

/// Mirror of [`crate::mm::io::VmWriter::fill_zeros`].
///
/// Exec body writes through `self.cursor` and then advances the
/// handle's cursor; the owner's `mem_view` shape is preserved (write
/// view stays a write view).
pub axiom fn vm_writer_fill_zeros_embedded(tracked owner: &mut VmIoOwner, len: usize)
    requires
        old(owner).inv(),
    ensures
        final(owner).inv(),
        final(owner).mem_view == old(owner).mem_view,
        final(owner).range == old(owner).range,
;

/// Mirror of [`crate::mm::io::VmWriter::limit`].
pub axiom fn vm_writer_limit_embedded(tracked owner: &mut VmIoOwner, max_avail: usize)
    requires
        old(owner).inv(),
    ensures
        final(owner).inv(),
        *final(owner) == *old(owner),
;

/// Mirror of [`crate::mm::io::VmWriter::skip`].
pub axiom fn vm_writer_skip_embedded(tracked owner: &mut VmIoOwner, nbytes: usize)
    requires
        old(owner).inv(),
    ensures
        final(owner).inv(),
        *final(owner) == *old(owner),
;

// =============================================================================
// dispatch tags + step proofs
// =============================================================================

/// Dispatch tag for [`vm_io_method_step`] (single-owner mutator methods).
pub enum VmIoMethod {
    ReaderLimit(usize),
    ReaderSkip(usize),
    WriterFillZeros(usize),
    WriterLimit(usize),
    WriterSkip(usize),
}

/// Per-op step for `Op::NewReader` / `Op::NewWriter` (Fallible). On
/// `Some`, wraps the produced VmIoOwner into a `VmIoEntry` with the
/// supplied `vs` (parent VmSpace).
pub(super) proof fn new_vm_io_step<'a>(
    tracked vm_space: &VmSpaceOwner,
    vs: Option<VmSpaceId>,
    vaddr: Vaddr,
    len: usize,
    kind: VmIoKind,
) -> (tracked res: Option<VmIoEntry>)
    requires
        vm_space.inv(),
        vs is Some,  // Fallible creation always has a VmSpace parent.
    ensures
        res matches Some(e) ==> e.inv(),
        res matches Some(e) ==> e.kind == kind,
        res matches Some(e) ==> e.vaddr == vaddr,
        res matches Some(e) ==> e.len == len,
        res matches Some(e) ==> e.vm_space == vs,
        res matches Some(_) ==> (vaddr as nat) + (len as nat) <= MAX_USERSPACE_VADDR as nat,
{
    let tracked owner_opt = match kind {
        VmIoKind::Reader => vm_space_reader_embedded(vm_space, vaddr, len),
        VmIoKind::Writer => vm_space_writer_embedded(vm_space, vaddr, len),
    };
    match owner_opt {
        Option::Some(owner) => {
            let tracked entry = axiom_vm_io_entry_new(vs, kind, vaddr, len, owner);
            Option::Some(entry)
        },
        Option::None => Option::None,
    }
}

/// Per-op step for `Op::NewKernelReader` / `Op::NewKernelWriter`.
/// `from_kernel_space` ensures `read_view_initialized()` /
/// `has_write_view()` directly (under the kernel-VA range guard), so
/// the produced entry satisfies its `inv()` for kernel kind.
pub(super) proof fn new_kernel_vm_io_step(
    vaddr: Vaddr,
    len: usize,
    kind: VmIoKind,
) -> (tracked res: VmIoEntry)
    ensures
        res.inv(),
        res.kind == kind,
        res.vaddr == vaddr,
        res.len == len,
        res.vm_space is None,
{
    let tracked owner = match kind {
        VmIoKind::Reader => vm_reader_from_kernel_space_embedded(vaddr, len),
        VmIoKind::Writer => vm_writer_from_kernel_space_embedded(vaddr, len),
    };
    axiom_vm_io_entry_new(Option::<VmSpaceId>::None, kind, vaddr, len, owner)
}

/// Per-op step for `Op::DropReader` / `Op::DropWriter`. The caller has
/// already extracted the entry; this function drops it.
pub(super) proof fn drop_vm_io_step(tracked _entry: VmIoEntry) {
}

/// Per-op step for single-owner mutator methods.
///
/// All methods here preserve `mem_view` exactly (limit/skip don't
/// touch the owner; fill_zeros preserves the WriteView), so
/// `VmIoEntry::inv` is preserved automatically.
pub(super) proof fn vm_io_method_step(
    tracked entry: &mut VmIoEntry,
    method: VmIoMethod,
)
    requires
        old(entry).inv(),
    ensures
        final(entry).vm_space == old(entry).vm_space,
        final(entry).kind == old(entry).kind,
        final(entry).vaddr == old(entry).vaddr,
        final(entry).len == old(entry).len,
        final(entry).inv(),
{
    match method {
        VmIoMethod::ReaderLimit(max) => vm_reader_limit_embedded(&mut entry.owner, max),
        VmIoMethod::ReaderSkip(n) => vm_reader_skip_embedded(&mut entry.owner, n),
        VmIoMethod::WriterFillZeros(len) => vm_writer_fill_zeros_embedded(&mut entry.owner, len),
        VmIoMethod::WriterLimit(max) => vm_writer_limit_embedded(&mut entry.owner, max),
        VmIoMethod::WriterSkip(n) => vm_writer_skip_embedded(&mut entry.owner, n),
    }
}

/// Per-op step for `Op::Read` (Infallible `VmReader::read`). Mutates
/// both source and dest, and produces a fresh `consumed_w` entry
/// (registered as a detached kernel Writer — `vm_space: None`,
/// `kind: Writer`, which by `VmIoEntry::inv` already implies
/// `has_write_view()`).
pub(super) proof fn read_step(
    tracked source: &mut VmIoEntry,
    tracked dest: &mut VmIoEntry,
) -> (tracked res: VmIoEntry)
    requires
        old(source).inv(),
        old(dest).inv(),
        old(source).vm_space is None,
        old(source).kind == VmIoKind::Reader,
        old(dest).vm_space is None,
        old(dest).kind == VmIoKind::Writer,
    ensures
        final(source).vm_space == old(source).vm_space,
        final(source).kind == old(source).kind,
        final(source).vaddr == old(source).vaddr,
        final(source).len == old(source).len,
        final(source).inv(),
        final(dest).vm_space == old(dest).vm_space,
        final(dest).kind == old(dest).kind,
        final(dest).vaddr == old(dest).vaddr,
        final(dest).len == old(dest).len,
        final(dest).inv(),
        // consumed_w wrapped as a detached kernel Writer.
        res.inv(),
        res.kind == VmIoKind::Writer,
        res.vm_space is None,
{
    let tracked val_owner = vm_reader_read_embedded(&mut source.owner, &mut dest.owner);
    axiom_vm_io_entry_new(
        Option::<VmSpaceId>::None,
        VmIoKind::Writer,
        0usize,
        0usize,
        val_owner,
    )
}

/// Per-op step for `Op::Write` (Infallible `VmWriter::write`). Mutates
/// both owners; the exec no longer surfaces `consumed_w`, so no fresh
/// entry is produced.
pub(super) proof fn write_step(
    tracked source: &mut VmIoEntry,
    tracked dest: &mut VmIoEntry,
)
    requires
        old(source).inv(),
        old(dest).inv(),
        old(source).vm_space is None,
        old(source).kind == VmIoKind::Reader,
        old(dest).vm_space is None,
        old(dest).kind == VmIoKind::Writer,
    ensures
        final(source).vm_space == old(source).vm_space,
        final(source).kind == old(source).kind,
        final(source).vaddr == old(source).vaddr,
        final(source).len == old(source).len,
        final(source).inv(),
        final(dest).vm_space == old(dest).vm_space,
        final(dest).kind == old(dest).kind,
        final(dest).vaddr == old(dest).vaddr,
        final(dest).len == old(dest).len,
        final(dest).inv(),
{
    vm_writer_write_embedded(&mut source.owner, &mut dest.owner);
}

} // verus!
