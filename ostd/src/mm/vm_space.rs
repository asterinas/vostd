// SPDX-License-Identifier: MPL-2.0
//! Virtual memory space management.
//!
//! The [`VmSpace`] struct is provided to manage the virtual memory space of a
//! user. Cursors are used to traverse and modify over the virtual memory space
//! concurrently. The VM space cursor [`self::Cursor`] is just a wrapper over
//! the page table cursor, providing efficient, powerful concurrent accesses
//! to the page table.
use alloc::vec::Vec;
use vstd::pervasive::{arbitrary, proof_from_false};
use vstd::prelude::*;

use crate::specs::mm::virt_mem_newer::{MemView, VirtPtr};

use crate::error::Error;
use crate::mm::frame::untyped::UFrame;
use crate::mm::io::VmIoMemView;
use crate::mm::page_table::*;
use crate::mm::page_table::{EntryOwner, PageTableFrag, PageTableGuard};
use crate::specs::arch::*;
use crate::specs::mm::frame::mapping::meta_to_frame;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::owners::CursorOwner;
use crate::specs::mm::page_table::*;
use crate::specs::mm::tlb::TlbModel;
use crate::specs::task::InAtomicMode;
use core::marker::PhantomData;
use core::{ops::Range, sync::atomic::Ordering};
use vstd_extra::ghost_tree::*;

use crate::mm::tlb::*;
use crate::specs::mm::cpu::AtomicCpuSet;

use crate::{
    // cpu::{AtomicCpuSet, CpuSet, PinCurrentCpu},
    // cpu_local_cell,
    mm::{
        io::{VmIoOwner, VmReader, VmWriter},
        // io::Fallible,
        // kspace::KERNEL_PAGE_TABLE,
        // page_table,
        // tlb::{TlbFlushOp, TlbFlusher},
        page_prop::PageProperty,
        Paddr,
        PagingConstsTrait,
        PagingLevel,
        Vaddr,
        MAX_USERSPACE_VADDR,
    },
    prelude::*,
    //    task::{atomic_mode::AsAtomicModeGuard, disable_preempt, DisabledPreemptGuard},
};

use alloc::sync::Arc;

#[path = "../../specs/mm/vm_space.rs"]
pub mod vm_space_specs;
use vm_space_specs::*;

verus! {

/// A virtual address space for user-mode tasks, enabling safe manipulation of user-space memory.
///
/// The `VmSpace` type provides memory isolation guarantees between user-space and
/// kernel-space. For example, given an arbitrary user-space pointer, one can read and
/// write the memory location referred to by the user-space pointer without the risk of
/// breaking the memory safety of the kernel space.
///
/// # Task Association Semantics
///
/// As far as OSTD is concerned, a `VmSpace` is not necessarily associated with a task. Once a
/// `VmSpace` is activated (see [`VmSpace::activate`]), it remains activated until another
/// `VmSpace` is activated **possibly by another task running on the same CPU**.
///
/// This means that it's up to the kernel to ensure that a task's `VmSpace` is always activated
/// while the task is running. This can be done by using the injected post schedule handler
/// (see [`inject_post_schedule_handler`]) to always activate the correct `VmSpace` after each
/// context switch.
///
/// If the kernel otherwise decides not to ensure that the running task's `VmSpace` is always
/// activated, the kernel must deal with race conditions when calling methods that require the
/// `VmSpace` to be activated, e.g., [`UserMode::execute`], [`VmSpace::reader`],
/// [`VmSpace::writer`]. Otherwise, the behavior is unspecified, though it's guaranteed _not_ to
/// compromise the kernel's memory safety.
///
/// # Memory Backing
///
/// A newly-created `VmSpace` is not backed by any physical memory pages. To
/// provide memory pages for a `VmSpace`, one can allocate and map physical
/// memory ([`UFrame`]s) to the `VmSpace` using the cursor.
///
/// A `VmSpace` can also attach a page fault handler, which will be invoked to
/// handle page faults generated from user space.
///
/// [`inject_post_schedule_handler`]: crate::task::inject_post_schedule_handler
/// [`UserMode::execute`]: crate::user::UserMode::execute
/// # Verification Design
///
/// A `VmSpace` has a corresponding [`VmSpaceOwner`] object that is used to track its state,
/// and against which its invariants are stated. The `VmSpaceOwner` catalogues the readers and writers
/// that are associated with the `VmSpace`, and the `MemView` which encodes the active page table and
/// the subset of the TLB that covers the same virtual address space.
/// All proofs about the correctness of the readers and writers are founded on the well-formedness of the `MemView`:
/// ```rust
/// open spec fn mem_view_wf(self) -> bool {
///    &&& self.mem_view is Some <==> self.mv_range@ is Some
///    // This requires that TotalMapping (mvv) = mv ∪ writer mappings ∪ reader mappings
///    &&& self.mem_view matches Some(remaining_view)
///        ==> self.mv_range@ matches Some(total_view)
///        ==> {
///        &&& remaining_view.mappings_are_disjoint()
///        &&& remaining_view.mappings.finite()
///        &&& total_view.mappings_are_disjoint()
///        &&& total_view.mappings.finite()
///        // ======================
///        // Remaining Consistency
///        // ======================
///        &&& remaining_view.mappings.subset_of(total_view.mappings)
///        &&& remaining_view.memory.dom().subset_of(
///            total_view.memory.dom(),
///        )
///        // =====================
///        // Total View Consistency
///        // =====================
///        &&& forall|va: usize|
///            remaining_view.addr_transl(va) == total_view.addr_transl(
///                va,
///            )
///        // =====================
///        // Writer correctness
///        // =====================
///        &&& forall|i: int|
///            0 <= i < self.writers.len() as int ==> {
///                &&& self.writers[i].inv()
///            }
///        }
///    }
/// }
/// ```
pub struct VmSpace<'a> {
    pub pt: PageTable<UserPtConfig>,
    /// Whether we allow shared reading.
    pub shared_reader: bool,
    /// All readers belonging to this VM space.
    pub readers: Vec<&'a VmReader<'a>>,
    /// All writers belonging to this VM space.
    pub writers: Vec<&'a VmWriter<'a>>,
    pub cpus: AtomicCpuSet,
    pub marker: PhantomData<&'a ()>,
}

impl Inv for VmSpace<'_> {
    open spec fn inv(self) -> bool {
        &&& forall|i: int|
            #![trigger self.readers@[i]]
            0 <= i < self.readers@.len() as int ==> self.readers@[i].inv()
        &&& forall|i: int|
            #![trigger self.writers@[i]]
            0 <= i < self.writers@.len() as int ==> self.writers@[i].inv()
    }
}

type Result<A> = core::result::Result<A, Error>;

#[verus_verify]
impl<'a> VmSpace<'a> {
    pub uninterp spec fn new_spec() -> Self;

    pub open spec fn reader_requires(
        &self,
        vm_owner: VmSpaceOwner<'a>,
        vaddr: Vaddr,
        len: usize,
    ) -> bool {
        &&& self.inv()
        &&& vm_owner.inv_with(*self)
        &&& vm_owner.inv()
        &&& vm_owner.active
        &&& vm_owner.can_create_reader(vaddr, len)
        &&& vaddr != 0 && len > 0 && vaddr + len <= MAX_USERSPACE_VADDR
        &&& current_page_table_paddr_spec() == self.pt.root_paddr_spec()
    }

    pub open spec fn writer_requires(
        &self,
        vm_owner: VmSpaceOwner<'a>,
        vaddr: Vaddr,
        len: usize,
    ) -> bool {
        &&& self.inv()
        &&& vm_owner.inv_with(*self)
        &&& vm_owner.inv()
        &&& vm_owner.active
        &&& vm_owner.can_create_writer(vaddr, len)
        &&& vaddr != 0 && len > 0 && vaddr + len <= MAX_USERSPACE_VADDR
        &&& current_page_table_paddr_spec() == self.pt.root_paddr_spec()
    }

    pub open spec fn reader_ensures(
        &self,
        vm_owner_old: VmSpaceOwner<'_>,
        vm_owner_new: VmSpaceOwner<'_>,
        vaddr: Vaddr,
        len: usize,
        r: Result<VmReader<'_>>,
        r_owner: Option<VmIoOwner<'_>>,
    ) -> bool {
        &&& vm_owner_new.inv()
        &&& vm_owner_new.readers == vm_owner_old.readers
        &&& vm_owner_new.writers == vm_owner_old.writers
        &&& r matches Ok(reader) && r_owner matches Some(owner) ==> {
            &&& reader.inv()
            &&& owner.inv_with_reader(reader)
            &&& owner.mem_view is None
        }
    }

    pub open spec fn writer_ensures(
        &self,
        vm_owner_old: VmSpaceOwner<'a>,
        vm_owner_new: VmSpaceOwner<'a>,
        vaddr: Vaddr,
        len: usize,
        r: Result<VmWriter<'a>>,
        r_owner: Option<VmIoOwner<'a>>,
    ) -> bool {
        &&& vm_owner_new.inv()
        &&& vm_owner_new.readers == vm_owner_old.readers
        &&& vm_owner_new.writers == vm_owner_old.writers
        &&& r matches Ok(writer) && r_owner matches Some(owner) ==> {
            &&& writer.inv()
            &&& owner.inv_with_writer(writer)
            &&& owner.mem_view is None
        }
    }

    /// Creates a new VM address space.
    #[inline]
    #[verifier::external_body]
    #[verifier::when_used_as_spec(new_spec)]
    #[verus_spec(r =>
        ensures
            r == Self::new_spec(),
            r.inv(),
    )]
    pub fn new() -> Self {
        unimplemented!()
    }

    /// Gets an immutable cursor in the virtual address range.
    ///
    /// The cursor behaves like a lock guard, exclusively owning a sub-tree of
    /// the page table, preventing others from creating a cursor in it. So be
    /// sure to drop the cursor as soon as possible.
    ///
    /// The creation of the cursor may block if another cursor having an
    /// overlapping range is alive.
    #[verifier::external_body]
    pub fn cursor<G: InAtomicMode>(&'a self, guard: &'a G, va: &Range<Vaddr>) -> Result<Cursor<'a, G>> {
        Ok(self.pt.cursor(guard, va).map(|pt_cursor| Cursor(pt_cursor.0))?)
    }

    /// Gets an mutable cursor in the virtual address range.
    ///
    /// The same as [`Self::cursor`], the cursor behaves like a lock guard,
    /// exclusively owning a sub-tree of the page table, preventing others
    /// from creating a cursor in it. So be sure to drop the cursor as soon as
    /// possible.
    ///
    /// The creation of the cursor may block if another cursor having an
    /// overlapping range is alive. The modification to the mapping by the
    /// cursor may also block or be overridden the mapping of another cursor.
    pub fn cursor_mut<G: InAtomicMode>(&'a self, guard: &'a G, va: &Range<Vaddr>) -> Result<CursorMut<'a, G>> {
        Ok(
            self.pt.cursor_mut(guard, va).map(
                |pt_cursor|
                    CursorMut {
                        pt_cursor:
                            pt_cursor.0,
                        flusher: TlbFlusher::new(&self.cpus/*, disable_preempt()*/),
                    },
            )?,
        )
    }

    /// Activates the given reader to read data from the user space of the current task.
    /// # Verified Properties
    /// ## Preconditions
    /// - The `VmSpace` invariants must hold with respect to the `VmSpaceOwner`, which must be active.
    /// - The reader must be well-formed with respect to the `VmSpaceOwner`.
    /// - The reader's virtual address range must be mapped within the `VmSpaceOwner`'s memory view.
    /// ## Postconditions
    /// - The reader will be added to the `VmSpace`'s readers list.
    /// - The reader will be activated with a view of its virtual address range taken from the `VmSpaceOwner`'s memory view.
    /// ## Safety
    /// - The function preserves all memory invariants.
    /// - The `MemView` invariants ensure that the reader has a consistent view of memory.
    /// - The `VmSpaceOwner` invariants ensure that the viewed memory is owned exclusively by this `VmSpace`.
    #[inline(always)]
    #[verus_spec(r =>
        with
            Tracked(vm_space_owner): Tracked<&'a mut VmSpaceOwner<'a>>,
            Tracked(owner_r): Tracked<&'a mut VmIoOwner<'a>>,
        requires
            old(self).inv(),
            old(vm_space_owner).mem_view matches Some(mv) &&
                forall |va: usize|
                #![auto]
                    old(owner_r).range@.start <= va < old(owner_r).range@.end ==>
                        mv.addr_transl(va) is Some
            ,
            old(vm_space_owner).inv_with(*old(self)),
            old(vm_space_owner).inv(),
            old(vm_space_owner).active,
            old(owner_r).inv_with_reader(*reader),
            old(owner_r).mem_view is None,
            reader.inv(),
        ensures
            self.inv(),
            self.shared_reader == old(self).shared_reader,
            self.readers@ == old(self).readers@.push(reader),
            owner_r.inv_with_reader(*reader),
            owner_r.mem_view == Some(VmIoMemView::ReadView(&old(vm_space_owner).mem_view@.unwrap().borrow_at_spec(
                old(owner_r).range@.start,
                (old(owner_r).range@.end - old(owner_r).range@.start) as usize,
            ))),
    )]
    pub fn activate_reader(&mut self, reader: &'a VmReader<'a>) {
        self.readers.push(reader);

        proof {
            let tracked mv = match vm_space_owner.mem_view {
                Some(ref mv) => mv,
                _ => { proof_from_false() },
            };
            let tracked borrowed_mv = mv.borrow_at(
                owner_r.range@.start,
                (owner_r.range@.end - owner_r.range@.start) as usize,
            );

            owner_r.mem_view = Some(VmIoMemView::ReadView(borrowed_mv));

            assert forall|va: usize|
                #![auto]
                owner_r.range@.start <= va < owner_r.range@.end implies borrowed_mv.addr_transl(
                va,
            ) is Some by {
                if owner_r.range@.start <= va && va < owner_r.range@.end {
                    assert(borrowed_mv.mappings =~= mv.mappings.filter(
                        |m: Mapping|
                            m.va_range.start < (owner_r.range@.end) && m.va_range.end
                                > owner_r.range@.start,
                    ));
                    let o_borrow_mv = borrowed_mv.mappings.filter(
                        |m: Mapping| m.va_range.start <= va < m.va_range.end,
                    );
                    let o_mv = mv.mappings.filter(
                        |m: Mapping| m.va_range.start <= va < m.va_range.end,
                    );
                    assert(mv.addr_transl(va) is Some);
                    assert(o_mv.len() > 0);
                    assert(o_borrow_mv.len() > 0) by {
                        let m = o_mv.choose();
                        assert(o_mv.contains(m)) by {
                            vstd::set::axiom_set_choose_len(o_mv);
                        }
                        assert(o_borrow_mv.contains(m));
                    }
                }
            }
        }
    }

    /// Activates the given writer to write data to the user space of the current task.
    /// # Verified Properties
    /// ## Preconditions
    /// - The `VmSpace` invariants must hold with respect to the `VmSpaceOwner`, which must be active.
    /// - The writer must be well-formed with respect to the `VmSpaceOwner`.
    /// - The writer's virtual address range must be mapped within the `VmSpaceOwner`'s memory view.
    /// ## Postconditions
    /// - The writer will be added to the `VmSpace`'s writers list.
    /// - The writer will be activated with a view of its virtual address range taken from the `VmSpaceOwner`'s memory view.
    /// ## Safety
    /// - The function preserves all memory invariants.
    /// - The `MemView` invariants ensure that the writer has a consistent view of memory.
    /// - The `VmSpaceOwner` invariants ensure that the viewed memory is owned exclusively by this `VmSpace`.
    #[inline(always)]
    #[verus_spec(r =>
        with
            Tracked(vm_space_owner): Tracked<&'a mut VmSpaceOwner<'a>>,
            Tracked(owner_w): Tracked<&'a mut VmIoOwner<'a>>,
        requires
            old(self).inv(),
            old(vm_space_owner).mem_view matches Some(mv) &&
                forall |va: usize|
                #![auto]
                    old(owner_w).range@.start <= va < old(owner_w).range@.end ==>
                        mv.addr_transl(va) is Some
            ,
            old(vm_space_owner).inv_with(*old(self)),
            old(vm_space_owner).inv(),
            old(vm_space_owner).active,
            old(owner_w).inv_with_writer(*writer),
            old(owner_w).mem_view is None,
            writer.inv(),
        ensures
            self.inv(),
            self.shared_reader == old(self).shared_reader,
            self.writers@ == old(self).writers@.push(writer),
            owner_w.inv_with_writer(*writer),
            owner_w.mem_view == Some(VmIoMemView::WriteView(old(vm_space_owner).mem_view@.unwrap().split_spec(
                old(owner_w).range@.start,
                (old(owner_w).range@.end - old(owner_w).range@.start) as usize,
            ).0)),
    )]
    pub fn activate_writer(&mut self, writer: &'a VmWriter<'a>) {
        self.writers.push(writer);

        proof {
            let tracked mut mv = vm_space_owner.mem_view.tracked_take();
            let ghost old_mv = mv;
            let tracked (lhs, rhs) = mv.split(
                owner_w.range@.start,
                (owner_w.range@.end - owner_w.range@.start) as usize,
            );

            owner_w.mem_view = Some(VmIoMemView::WriteView(lhs));
            vm_space_owner.mem_view = Some(rhs);

            assert forall|va: usize|
                #![auto]
                owner_w.range@.start <= va < owner_w.range@.end implies lhs.addr_transl(
                va,
            ) is Some by {
                if owner_w.range@.start <= va && va < owner_w.range@.end {
                    assert(lhs.mappings =~= old_mv.mappings.filter(
                        |m: Mapping|
                            m.va_range.start < (owner_w.range@.end) && m.va_range.end
                                > owner_w.range@.start,
                    ));
                    let o_lhs = lhs.mappings.filter(
                        |m: Mapping| m.va_range.start <= va < m.va_range.end,
                    );
                    let o_mv = old_mv.mappings.filter(
                        |m: Mapping| m.va_range.start <= va < m.va_range.end,
                    );

                    assert(old_mv.addr_transl(va) is Some);
                    assert(o_mv.len() > 0);
                    assert(o_lhs.len() > 0) by {
                        broadcast use vstd::set::axiom_set_choose_len;

                        let m = o_mv.choose();
                        assert(o_mv.contains(m));
                        assert(m.va_range.start <= va < m.va_range.end);
                        assert(o_lhs.contains(m));
                    }
                }
            }
        }
    }

    /// Creates a reader to read data from the user space of the current task.
    ///
    /// Returns [`Err`] if this [`VmSpace`] is not belonged to the user space of the current task
    /// or the `vaddr` and `len` do not represent a user space memory range.
    ///
    /// Users must ensure that no other page table is activated in the current task during the
    /// lifetime of the created [`VmReader`]. This guarantees that the [`VmReader`] can operate
    /// correctly.
    /// # Verified Properties
    /// ## Preconditions
    /// - The `VmSpace` invariants must hold with respect to the `VmSpaceOwner`, which must be active.
    /// - The range `vaddr..vaddr + len` must represent a user space memory range.
    /// - The `VmSpaceOwner` must not have any active writers overlapping with the range `vaddr..vaddr + len`.
    /// ## Postconditions
    /// - An inactive `VmReader` will be created with the range `vaddr..vaddr + len`.
    /// ## Safety
    /// - The function preserves all memory invariants.
    /// - By requiring that the `VmSpaceOwner` must not have any active writers overlapping with the target range,
    /// it prevents data races between the reader and any writers.
    #[inline]
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&'a mut VmSpaceOwner<'a>>,
                -> vm_reader_owner: Tracked<Option<VmIoOwner<'a>>>,
        requires
            self.reader_requires(*old(owner), vaddr, len),
        ensures
            self.reader_ensures(*old(owner), *owner, vaddr, len, r, vm_reader_owner@),
    )]
    pub fn create_reader(&self, vaddr: Vaddr, len: usize) -> Result<VmReader<'a>> {
        let vptr = VirtPtr::from_vaddr(vaddr, len);
        let ghost id = owner.new_vm_io_id();
        proof_decl! {
            let tracked mut vm_reader_owner;
        }
        // SAFETY: The memory range is in user space, as checked above.
        let reader = unsafe {
            proof_with!(Ghost(id) => Tracked(vm_reader_owner));
            VmReader::from_user_space(vptr)
        };

        proof_with!(|= Tracked(Some(vm_reader_owner)));
        Ok(reader)
    }

    /// Returns `Err` if this `VmSpace` is not belonged to the user space of the current task
    /// or the `vaddr` and `len` do not represent a user space memory range.
    ///
    /// Users must ensure that no other page table is activated in the current task during the
    /// lifetime of the created `VmWriter`. This guarantees that the `VmWriter` can operate correctly.
    /// # Verified Properties
    /// ## Preconditions
    /// - The `VmSpace` invariants must hold with respect to the `VmSpaceOwner`, which must be active.
    /// - The range `vaddr..vaddr + len` must represent a user space memory range.
    /// - The `VmSpaceOwner` must not have any active readers or writers overlapping with the range `vaddr..vaddr + len`.
    /// ## Postconditions
    /// - An inactive `VmWriter` will be created with the range `vaddr..vaddr + len`.
    /// ## Safety
    /// - The function preserves all memory invariants.
    /// - By requiring that the `VmSpaceOwner` must not have any active readers or writers overlapping with the target range,
    /// it prevents data races.
    #[inline]
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmSpaceOwner<'a>>,
                -> new_owner: Tracked<Option<VmIoOwner<'a>>>,
        requires
            self.writer_requires(*old(owner), vaddr, len),
        ensures
            self.writer_ensures(*old(owner), *owner, vaddr, len, r, new_owner@),
    )]
    pub fn create_writer(self, vaddr: Vaddr, len: usize) -> Result<VmWriter<'a>> {
        let vptr = VirtPtr::from_vaddr(vaddr, len);
        let ghost id = owner.new_vm_io_id();
        proof_decl! {
            let tracked mut vm_writer_owner;
        }

        // `VmWriter` is neither `Sync` nor `Send`, so it will not live longer than the current
        // task. This ensures that the correct page table is activated during the usage period of
        // the `VmWriter`.
        //
        // SAFETY: The memory range is in user space, as checked above.
        let writer = unsafe {
            proof_with!(Ghost(id) => Tracked(vm_writer_owner));
            VmWriter::from_user_space(vptr)
        };

        proof_with!(|= Tracked(Some(vm_writer_owner)));
        Ok(writer)
    }
}

/*
impl Default for VmSpace {
    fn default() -> Self {
        Self::new()
    }
}
*/

/// The cursor for querying over the VM space without modifying it.
///
/// It exclusively owns a sub-tree of the page table, preventing others from
/// reading or modifying the same sub-tree. Two read-only cursors can not be
/// created from the same virtual address range either.
pub struct Cursor<'a, A: InAtomicMode>(pub crate::mm::page_table::Cursor<'a, UserPtConfig, A>);

/*
impl<A: InAtomicMode> Iterator for Cursor<'_, A> {
    type Item = (Range<Vaddr>, Option<MappedItem>);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}
*/

#[verus_verify]
impl<'rcu, A: InAtomicMode> Cursor<'rcu, A> {
    pub open spec fn query_success_requires(self) -> bool {
        self.0.barrier_va.start <= self.0.va < self.0.barrier_va.end
    }

    pub open spec fn query_success_ensures(
        self,
        view: CursorView<UserPtConfig>,
        range: Range<Vaddr>,
        item: Option<MappedItem>,
    ) -> bool {
        if view.present() {
            &&& item is Some
            &&& view.query_item_spec(item.unwrap()) == Some(range)
        } else {
            &&& range.start == self.0.va
            &&& item is None
        }
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the mapped item.
    /// ## Preconditions
    /// - All system invariants must hold
    /// - **Liveness**: The function will return an error if the cursor is not within the locked range
    /// ## Postconditions
    /// - If there is a mapped item at the current virtual address ([`query_some_condition`]),
    /// it is returned along with the virtual address range that it maps ([`query_success_ensures`]).
    /// - The mapping that is returned corresponds to the abstract mapping given by [`query_item_spec`](CursorView::query_item_spec).
    /// - If there is no mapped item at the current virtual address ([`query_none_condition`]),
    /// it returns `None`, and the virtual address range of the cursor's current position.
    /// ## Safety
    /// - This function preserves all memory invariants.
    /// - The locking mechanism prevents data races.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, UserPtConfig>>
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
        ensures
            self.0.invariants(*owner, *regions, *guards),
            self.0.query_some_condition(*owner) ==> {
                &&& r is Ok
                &&& self.0.query_some_ensures(*owner, r.unwrap())
            },
            !self.0.query_some_condition(*owner) ==> {
                &&& r is Ok
                &&& self.0.query_none_ensures(*owner, r.unwrap())
            },
    )]
    pub fn query(&mut self) -> Result<(Range<Vaddr>, Option<MappedItem>)> {
        Ok(
            #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
            self.0.query()?,
        )
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// If there is mapped virtual address following the current address within
    /// next `len` bytes, it will return that mapped address. In this case,
    /// the cursor will stop at the mapped address.
    ///
    /// Otherwise, it will return `None`. And the cursor may stop at any
    /// address after `len` bytes.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Liveness**: The cursor must be within the locked range and below the guard level.
    /// - **Liveness**: The length must be page-aligned and less than or equal to the remaining range of the cursor.
    /// ## Postconditions
    /// - If there is a mapped address after the current address within the next `len` bytes,
    /// it will move the cursor to the next mapped address and return it.
    /// - If not, it will return `None`. The cursor may stop at any
    /// address after `len` bytes, but it will not move past the barrier address.
    /// ## Panics
    /// This method panics if the length is longer than the remaining range of the cursor.
    /// ## Safety
    /// This function preserves all memory invariants.
    /// Because it panics rather than move the cursor to an invalid address,
    /// it ensures that the cursor is safe to use after the call.
    /// The locking mechanism prevents data races.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, UserPtConfig>>
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            old(self).0.level < old(self).0.guard_level,
            old(owner).in_locked_range(),
            len % PAGE_SIZE == 0,
            old(self).0.va + len <= old(self).0.barrier_va.end,
        ensures
            self.0.invariants(*owner, *regions, *guards),
            res is Some ==> {
                &&& res.unwrap() == self.0.va
                &&& owner.level < owner.guard_level
                &&& owner.in_locked_range()
            },
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.find_next(len)
    }

    /// Jump to the virtual address.
    ///
    /// This function will move the cursor to the given virtual address.
    /// If the target address is not in the locked range, it will return an error.
    /// # Verified Properties
    /// ## Preconditions
    /// The cursor must be within the locked range and below the guard level.
    /// ## Postconditions
    /// - If the target address is in the locked range, it will move the cursor to the given address.
    /// - If the target address is not in the locked range, it will return an error.
    /// ## Panics
    /// This method panics if the target address is not aligned to the page size.
    /// ## Safety
    /// This function preserves all memory invariants.
    /// Because it throws an error rather than move the cursor to an invalid address,
    /// it ensures that the cursor is safe to use after the call.
    /// The locking mechanism prevents data races.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, UserPtConfig>>
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            old(self).0.level < old(self).0.guard_level,
            old(owner).in_locked_range(),
            old(self).0.jump_panic_condition(va),
        ensures
            self.0.invariants(*owner, *regions, *guards),
            self.0.barrier_va.start <= va < self.0.barrier_va.end ==> {
                &&& res is Ok
                &&& self.0.va == va
            },
            !(self.0.barrier_va.start <= va < self.0.barrier_va.end) ==> res is Err,
    )]
    pub fn jump(&mut self, va: Vaddr) -> Result<()> {
        (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.jump(va))?;
        Ok(())
    }

    /// Get the virtual address of the current slot.
    pub fn virt_addr(&self) -> Vaddr
        returns
            self.0.va,
    {
        self.0.virt_addr()
    }
}

/// The cursor for modifying the mappings in VM space.
///
/// It exclusively owns a sub-tree of the page table, preventing others from
/// reading or modifying the same sub-tree.
pub struct CursorMut<'a, A: InAtomicMode> {
    pub pt_cursor: crate::mm::page_table::CursorMut<'a, UserPtConfig, A>,
    // We have a read lock so the CPU set in the flusher is always a superset
    // of actual activated CPUs.
    pub flusher: TlbFlusher<'a/*, DisabledPreemptGuard*/>,
}

impl<'a, A: InAtomicMode> CursorMut<'a, A> {
    pub open spec fn query_requires(
        cursor: Self,
        owner: CursorOwner<'a, UserPtConfig>,
        guard_perm: vstd::simple_pptr::PointsTo<PageTableGuard<'a, UserPtConfig>>,
        regions: MetaRegionOwners,
    ) -> bool {
        &&& cursor.pt_cursor.inner.wf(owner)
        &&& owner.inv()
        &&& regions.inv()
    }

    pub open spec fn query_ensures(
        old_cursor: Self,
        new_cursor: Self,
        owner: CursorOwner<'a, UserPtConfig>,
        guard_perm: vstd::simple_pptr::PointsTo<PageTableGuard<'a, UserPtConfig>>,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        r: Result<(Range<Vaddr>, Option<MappedItem>)>,
    ) -> bool {
        &&& new_regions.inv()
        &&& new_cursor.pt_cursor.inner.wf(owner)
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// This is the same as [`Cursor::query`].
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the mapped item.
    /// ## Preconditions
    /// - All system invariants must hold
    /// - **Liveness**: The function will return an error if the cursor is not within the locked range
    /// ## Postconditions
    /// - If there is a mapped item at the current virtual address ([`query_some_condition`]),
    /// it is returned along with the virtual address range that it maps ([`query_success_ensures`]).
    /// - The mapping that is returned corresponds to the abstract mapping given by [`query_item_spec`](CursorView::query_item_spec).
    /// - If there is no mapped item at the current virtual address ([`query_none_condition`]),
    /// it returns `None`, and the virtual address range of the cursor's current position.
    /// ## Safety
    /// - This function preserves all memory invariants.
    /// - The locking mechanism prevents data races.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>
        requires
            old(self).pt_cursor.inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
        ensures
            self.pt_cursor.inner.invariants(*owner, *regions, *guards),
            old(self).pt_cursor.inner.query_some_condition(*owner) ==> {
                &&& res is Ok
                &&& self.pt_cursor.inner.query_some_ensures(*owner, res.unwrap())
            },
            !old(self).pt_cursor.inner.query_some_condition(*owner) ==> {
                &&& res is Ok
                &&& self.pt_cursor.inner.query_none_ensures(*owner, res.unwrap())
            },
    )]
    pub fn query(&mut self) -> Result<(Range<Vaddr>, Option<MappedItem>)> {
        Ok(
            #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
            self.pt_cursor.query()?,
        )
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// This is the same as [`Cursor::find_next`].
    /// 
    /// # Verified Properties
    /// ## Preconditions
    /// - **Liveness**: The cursor must be within the locked range and below the guard level.
    /// The length must be page-aligned and less than or equal to the remaining range of the cursor.
    /// ## Postconditions
    /// - If there is a mapped address after the current address within the next `len` bytes,
    /// it will move the cursor to the next mapped address and return it.
    /// - If not, it will return `None`. The cursor may stop at any
    /// address after `len` bytes, but it will not move past the barrier address.
    /// ## Panics
    /// This method panics if the length is longer than the remaining range of the cursor.
    /// ## Safety
    /// This function preserves all memory invariants.
    /// Because it panics rather than move the cursor to an invalid address,
    /// it ensures that the cursor is safe to use after the call.
    /// The locking mechanism prevents data races.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(self).pt_cursor.inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(self).pt_cursor.inner.level < old(self).pt_cursor.inner.guard_level,
            old(owner).in_locked_range(),
            len % PAGE_SIZE == 0,
            old(self).pt_cursor.inner.va + len <= old(self).pt_cursor.inner.barrier_va.end,
        ensures
            self.pt_cursor.inner.invariants(*owner, *regions, *guards),
            res is Some ==> {
                &&& res.unwrap() == self.pt_cursor.inner.va
                &&& owner.level < owner.guard_level
                &&& owner.in_locked_range()
            },
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.pt_cursor.find_next(len)
    }

    /// Jump to the virtual address.
    ///
    /// This is the same as [`Cursor::jump`].
    ///
    /// This function will move the cursor to the given virtual address.
    /// If the target address is not in the locked range, it will return an error.
    /// # Verified Properties
    /// ## Preconditions
    /// The cursor must be within the locked range and below the guard level.
    /// ## Postconditions
    /// - If the target address is in the locked range, it will move the cursor to the given address.
    /// - If the target address is not in the locked range, it will return an error.
    /// ## Panics
    /// This method panics if the target address is not aligned to the page size.
    /// ## Safety
    /// This function preserves all memory invariants.
    /// Because it throws an error rather than move the cursor to an invalid address,
    /// it ensures that the cursor is safe to use after the call.
    /// The locking mechanism prevents data races.
    #[verus_spec(res =>
        with
            Tracked(owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>
        requires
            old(self).pt_cursor.inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(self).pt_cursor.inner.level < old(self).pt_cursor.inner.guard_level,
            old(owner).in_locked_range(),
            old(self).pt_cursor.inner.jump_panic_condition(va),
        ensures
            self.pt_cursor.inner.invariants(*owner, *regions, *guards),
            self.pt_cursor.inner.barrier_va.start <= va < self.pt_cursor.inner.barrier_va.end ==> {
                &&& res is Ok
                &&& self.pt_cursor.inner.va == va
            },
            !(self.pt_cursor.inner.barrier_va.start <= va < self.pt_cursor.inner.barrier_va.end) ==> res is Err,
    )]
    pub fn jump(&mut self, va: Vaddr) -> Result<()> {
        (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.pt_cursor.jump(va))?;
        Ok(())
    }

    /// Get the virtual address of the current slot.
    #[verus_spec(r =>
        returns
            self.pt_cursor.inner.va,
    )]
    pub fn virt_addr(&self) -> Vaddr {
        self.pt_cursor.virt_addr()
    }

    /// Get the dedicated TLB flusher for this cursor.
    pub fn flusher(&self) -> &TlbFlusher<'a> {
        &self.flusher
    }
    
    /// Collects the invariants of the cursor, its owner, and associated tracked structures.
    /// The cursor must be well-formed with respect to its owner. This will hold before and after the call to `map`.
    pub open spec fn map_cursor_inv(
        self,
        cursor_owner: CursorOwner<'a, UserPtConfig>,
        guards: Guards<'a, UserPtConfig>,
        regions: MetaRegionOwners,
    ) -> bool {
        &&& cursor_owner.inv()
        &&& self.pt_cursor.inner.wf(cursor_owner)
        &&& self.pt_cursor.inner.inv()
        &&& cursor_owner.children_not_locked(guards)
        &&& cursor_owner.nodes_locked(guards)
        &&& cursor_owner.relate_region(regions)
        &&& !cursor_owner.popped_too_high
        &&& regions.inv()
    }

    /// These conditions must hold before the call to `map` but may not be maintained after the call.
    /// The cursor must be within the locked range and below the guard level, but it may move outside the
    /// range if the frame being mapped is exactly the length of the remaining range.
    pub open spec fn map_cursor_requires(
        self,
        cursor_owner: CursorOwner<'a, UserPtConfig>,
    ) -> bool {
        &&& cursor_owner.in_locked_range()
        &&& self.pt_cursor.inner.level < self.pt_cursor.inner.guard_level
        &&& self.pt_cursor.inner.va < self.pt_cursor.inner.barrier_va.end
    }

    /// Collects the conditions that must hold on the frame being mapped.
    /// The frame must be well-formed with respect to the entry owner. When converted into a `MappedItem`,
    /// its physical address must also match, and its level must be between 1 and the highest translation level.
    pub open spec fn map_item_requires(
        self,
        frame: UFrame,
        prop: PageProperty,
        entry_owner: EntryOwner<UserPtConfig>,
    ) -> bool {
        let item = MappedItem { frame: frame, prop: prop };
        let (paddr, level, prop0) = UserPtConfig::item_into_raw_spec(item);
        &&& prop == prop0
        &&& entry_owner.frame.unwrap().mapped_pa == paddr
        &&& entry_owner.frame.unwrap().prop == prop
        &&& level <= UserPtConfig::HIGHEST_TRANSLATION_LEVEL()
        &&& 1 <= level <= NR_LEVELS  // Should be property of item_into_raw
        &&& Child::Frame(paddr, level, prop0).wf(entry_owner)
        &&& self.pt_cursor.inner.va + page_size(level) <= self.pt_cursor.inner.barrier_va.end
        &&& entry_owner.inv()
        &&& self.pt_cursor.inner.va % page_size(level) == 0
    }

    /// The result of a call to `map`. Constructs a `Mapping` from the frame being mapped and the cursor's current virtual address.
    /// The page table's cursor view will be updated with this mapping, replacing the previous mapping (if any).
    pub open spec fn map_item_ensures(
        self,
        frame: UFrame,
        prop: PageProperty,
        old_cursor_view: CursorView<UserPtConfig>,
        cursor_view: CursorView<UserPtConfig>,
    ) -> bool {
        let item = MappedItem { frame: frame, prop: prop };
        let (paddr, level, prop0) = UserPtConfig::item_into_raw_spec(item);
        cursor_view == old_cursor_view.map_spec(paddr, page_size(level), prop)
    }

    /// Map a frame into the current slot.
    ///
    /// This method will bring the cursor to the next slot after the modification.
    /// # Verified Properties
    /// ## Preconditions
    /// - The cursor must be within the locked range and below the guard level,
    /// and the frame must fit within the remaining range of the cursor.
    /// - The cursor must satisfy all invariants, and the frame must be well-formed when converted into a `MappedItem` ([`map_item_requires`](Self::map_item_requires)).
    /// ## Postconditions
    /// After the call, the cursor will satisfy all invariants, and will map the frame into the current slot according to [`map_spec`](CursorView::map_spec).
    /// After the call, the TLB will not contain any entries for the virtual address range being mapped (TODO).
    /// ## Safety
    /// The preconditions of this function require that the frame to be mapped is disjoint from any other mapped frames.
    /// If this is not the case, the global memory invariants will be violated. If the allocator implementation is correct,
    /// the user shouldn't be able to create such a frame object in the first place, but currently a proof of that is
    /// outside of the verification boundary.
    /// Because this function flushes the TLB if it unmaps a page, it preserves TLB consistency.
    #[verus_spec(
        with Tracked(cursor_owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(entry_owner): Tracked<EntryOwner<UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>,
            Tracked(tlb_model): Tracked<&mut TlbModel>
        requires
            old(tlb_model).inv(),
            old(self).map_cursor_requires(*old(cursor_owner)),
            old(self).map_cursor_inv(*old(cursor_owner), *old(guards), *old(regions)),
            old(self).map_item_requires(frame, prop, entry_owner),
        ensures
            self.map_cursor_inv(*cursor_owner, *guards, *regions),
            old(self).map_item_ensures(
                frame,
                prop,
                old(self).pt_cursor.inner.model(*old(cursor_owner)),
                self.pt_cursor.inner.model(*cursor_owner),
            ),
    )]
    pub fn map(&mut self, frame: UFrame, prop: PageProperty)
    {
        let start_va = self.virt_addr();
        let item = MappedItem { frame: frame, prop: prop };

        assert(crate::mm::page_table::CursorMut::<'a, UserPtConfig, A>::item_not_mapped(
            item,
            *old(regions),
        )) by { admit() };

        // SAFETY: It is safe to map untyped memory into the userspace.
        let Err(frag) = (
        #[verus_spec(with Tracked(cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))]
        self.pt_cursor.map(item)) else {
            return ;  // No mapping exists at the current address.
        };

        match frag {
            PageTableFrag::Mapped { va, item } => {
                //debug_assert_eq!(va, start_va);
                let old_frame = item.frame;

                #[verus_spec(with Tracked(tlb_model))]
                self.flusher
                    .issue_tlb_flush_with(TlbFlushOp::Address(start_va), old_frame.into());
                #[verus_spec(with Tracked(tlb_model))]
                self.flusher.dispatch_tlb_flush();
            },
            PageTableFrag::StrayPageTable { .. } => {
                assert(false) by { admit() };
                //panic!("`UFrame` is base page sized but re-mapping out a child PT");
            }
        }
    }

    /// Clears the mapping starting from the current slot,
    /// and returns the number of unmapped pages.
    ///
    /// This method will bring the cursor forward by `len` bytes in the virtual
    /// address space after the modification.
    ///
    /// Already-absent mappings encountered by the cursor will be skipped. It
    /// is valid to unmap a range that is not mapped.
    ///
    /// It must issue and dispatch a TLB flush after the operation. Otherwise,
    /// the memory safety will be compromised. Please call this function less
    /// to avoid the overhead of TLB flush. Using a large `len` is wiser than
    /// splitting the operation into multiple small ones.
    ///
    /// # Panics
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    #[verus_spec(r =>
        with Tracked(cursor_owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>,
            Tracked(tlb_model): Tracked<&mut TlbModel>
        requires
            len > 0,
            len % PAGE_SIZE == 0,
            old(self).pt_cursor.inner.va % PAGE_SIZE == 0,
            old(self).pt_cursor.inner.va + len <= KERNEL_VADDR_RANGE.end as int,
            old(self).pt_cursor.inner.invariants(*old(cursor_owner), *old(regions), *old(guards)),
            old(cursor_owner).in_locked_range(),
            old(self).pt_cursor.inner.va + len <= old(self).pt_cursor.inner.barrier_va.end,
            old(tlb_model).inv(),
        ensures
            self.pt_cursor.inner.invariants(*cursor_owner, *regions, *guards),
            old(self).pt_cursor.inner.model(*old(cursor_owner)).unmap_spec(len, self.pt_cursor.inner.model(*cursor_owner), r),
            tlb_model.inv(),
    )]
    pub fn unmap(&mut self, len: usize) -> usize {
        proof {
            assert(cursor_owner.va.reflect(self.pt_cursor.inner.va));
            assert(cursor_owner.inv());
            cursor_owner.va.reflect_prop(self.pt_cursor.inner.va);
        }

        let end_va = self.virt_addr() + len;
        let mut num_unmapped: usize = 0;

        let ghost start_mappings: Set<Mapping> = cursor_owner@.mappings;
        let ghost start_va: Vaddr = cursor_owner@.cur_va;

        proof {
            assert((self.pt_cursor.inner.va + len) % PAGE_SIZE as int == 0) by (compute);

            assert(end_va as int == start_va + len);
            assert(start_mappings.filter(|m: Mapping| start_va <= m.va_range.start < start_va)
                =~= Set::<Mapping>::empty());
            assert(start_mappings.difference(Set::<Mapping>::empty()) =~= start_mappings);
            assume(start_mappings.finite());
        }

        #[verus_spec(
            invariant
                self.pt_cursor.inner.va <= end_va,
                self.pt_cursor.inner.va % PAGE_SIZE == 0,
                end_va % PAGE_SIZE == 0,
                self.pt_cursor.inner.invariants(*cursor_owner, *regions, *guards),
                cursor_owner.in_locked_range(),
                end_va <= self.pt_cursor.inner.barrier_va.end,
                tlb_model.inv(),
                start_va <= cursor_owner@.cur_va,
                cursor_owner@.mappings =~= start_mappings.difference(
                    start_mappings.filter(|m: Mapping| start_va <= m.va_range.start < cursor_owner@.cur_va)),
                num_unmapped as nat == start_mappings.filter(
                    |m: Mapping| start_va <= m.va_range.start < cursor_owner@.cur_va).len(),
                start_mappings =~= old(cursor_owner)@.mappings,
                start_va == old(cursor_owner)@.cur_va,
                start_mappings.finite(),
            invariant_except_break
                self.pt_cursor.inner.va < end_va,
            ensures
                self.pt_cursor.inner.va >= end_va,
            decreases end_va - self.pt_cursor.inner.va
        )]
        loop {
            let ghost prev_va: Vaddr = cursor_owner@.cur_va;
            let ghost prev_mappings: Set<Mapping> = cursor_owner@.mappings;
            let ghost num_unmapped_before: nat = num_unmapped as nat;

            proof {
                assert(self.pt_cursor.inner.wf(*cursor_owner));
                assert(cursor_owner.inv());
                cursor_owner.va.reflect_prop(self.pt_cursor.inner.va);
                assert(prev_va == self.pt_cursor.inner.va);
            }

            // SAFETY: It is safe to un-map memory in the userspace.
            let Some(frag) = (unsafe {
                #[verus_spec(with Tracked(cursor_owner), Tracked(regions), Tracked(guards))]
                self.pt_cursor.take_next(end_va - self.virt_addr())
            }) else {
                proof {
                    assert(self.pt_cursor.inner.wf(*cursor_owner));
                    assert(cursor_owner.inv());
                    cursor_owner.va.reflect_prop(self.pt_cursor.inner.va);

                    assert(cursor_owner@.cur_va == end_va);
                    assert(cursor_owner@.cur_va >= end_va);
                    assert(self.pt_cursor.inner.va == end_va);

                    assert(start_mappings.filter(
                        |m: Mapping| prev_va <= m.va_range.start < end_va)
                        =~= Set::<Mapping>::empty()) by {
                        assert forall |m: Mapping| #![auto]
                            start_mappings.contains(m)
                            && prev_va <= m.va_range.start
                            && m.va_range.start < end_va
                        implies false
                        by {
                            assert(!(start_va <= m.va_range.start && m.va_range.start < prev_va));
                            assert(prev_mappings.contains(m));
                            assert(prev_mappings.filter(
                                |m: Mapping| prev_va <= m.va_range.start < end_va).contains(m));
                        };
                    };

                    assert forall |m: Mapping|
                        start_mappings.contains(m)
                        && prev_va <= m.va_range.start
                    implies
                        m.va_range.start >= end_va
                    by {
                        if start_mappings.contains(m) && prev_va <= m.va_range.start && m.va_range.start < end_va {
                            assert(!(start_va <= m.va_range.start && m.va_range.start < prev_va));
                            assert(prev_mappings.contains(m));
                            assert(prev_mappings.filter(
                                |m: Mapping| prev_va <= m.va_range.start < end_va).contains(m));
                        }
                    };

                    // filter([start_va, end_va)) == filter([start_va, prev_va))
                    assert(start_mappings.filter(
                        |m: Mapping| start_va <= m.va_range.start < end_va)
                        =~= start_mappings.filter(
                            |m: Mapping| start_va <= m.va_range.start < prev_va));

                    // filter([start_va, cursor_va)) == filter([start_va, end_va))
                    assert(start_mappings.filter(
                        |m: Mapping| start_va <= m.va_range.start < cursor_owner@.cur_va)
                        =~= start_mappings.filter(
                            |m: Mapping| start_va <= m.va_range.start < prev_va));
                    // Since cursor_owner@.cur_va == end_va, the filter predicates are identical
                    assert(start_mappings.filter(
                        |m: Mapping| start_va <= m.va_range.start < cursor_owner@.cur_va)
                        =~= start_mappings.filter(
                            |m: Mapping| start_va <= m.va_range.start < end_va));
                    assert(start_mappings.filter(
                        |m: Mapping| start_va <= m.va_range.start < cursor_owner@.cur_va)
                        =~= start_mappings.filter(
                            |m: Mapping| start_va <= m.va_range.start < prev_va));
                }
                break ;
            };

            let ghost step_removed_len: nat = prev_mappings.filter(
                |m: Mapping| prev_va <= m.va_range.start < cursor_owner@.cur_va).len();

            proof {
                // Re-establish reflect for post-call state
                assert(self.pt_cursor.inner.wf(*cursor_owner));
                assert(cursor_owner.inv());
                cursor_owner.va.reflect_prop(self.pt_cursor.inner.va);

                let new_va = cursor_owner@.cur_va;

                assert(cursor_owner@.mappings =~= start_mappings.difference(
                    start_mappings.filter(
                        |m: Mapping| start_va <= m.va_range.start < new_va))) by {
                    assert forall |m: Mapping| #![auto]
                        cursor_owner@.mappings.contains(m) <==>
                        (start_mappings.contains(m) &&
                         !(start_va <= m.va_range.start && m.va_range.start < new_va))
                    by {
                        // LHS: m in prev_mappings AND NOT in step_removed
                        // RHS: m in start_mappings AND NOT in [start_va, new_va)
                        if start_mappings.contains(m) {
                            if start_va <= m.va_range.start && m.va_range.start < prev_va {
                                // m in removed_before => not in prev_mappings => not in LHS
                                assert(!prev_mappings.contains(m));
                                assert(!cursor_owner@.mappings.contains(m));
                            } else if prev_va <= m.va_range.start && m.va_range.start < new_va {
                                // m not in removed_before => in prev_mappings
                                // m in step_removed => not in LHS
                                assert(prev_mappings.contains(m));
                                assert(!cursor_owner@.mappings.contains(m));
                            } else {
                                // m not in removed_before => in prev_mappings
                                // m not in step_removed => in LHS
                                assert(prev_mappings.contains(m));
                                assert(cursor_owner@.mappings.contains(m));
                            }
                        }
                    };
                };

                let f_prev = start_mappings.filter(
                    |m: Mapping| start_va <= m.va_range.start < prev_va);
                let f_step = start_mappings.filter(
                    |m: Mapping| prev_va <= m.va_range.start < new_va);
                let f_all = start_mappings.filter(
                    |m: Mapping| start_va <= m.va_range.start < new_va);

                assert(f_step =~= prev_mappings.filter(
                    |m: Mapping| prev_va <= m.va_range.start < new_va)) by {
                    assert forall |m: Mapping| #![auto]
                        f_step.contains(m) <==> prev_mappings.filter(
                            |m: Mapping| prev_va <= m.va_range.start < new_va).contains(m)
                    by {
                        if start_mappings.contains(m) && prev_va <= m.va_range.start && m.va_range.start < new_va {
                            assert(!(start_va <= m.va_range.start && m.va_range.start < prev_va));
                            assert(prev_mappings.contains(m));
                        }
                    };
                };

                assert(f_all =~= f_prev + f_step);
                // Disjoint finite sets: |A + B| = |A| + |B|
                vstd::set_lib::lemma_set_disjoint_lens(f_prev, f_step);
            }

            let ghost mut step_delta: nat = 0;
            match frag {
                PageTableFrag::Mapped { va, item, .. } => {
                    let frame = item.frame;
                    assume(num_unmapped < usize::MAX);
                    num_unmapped += 1;
                    proof { step_delta = 1; }
                    #[verus_spec(with Tracked(tlb_model))]
                    self.flusher
                        .issue_tlb_flush_with(TlbFlushOp::Address(va), frame.into());
                },
                PageTableFrag::StrayPageTable { pt, va, len, num_frames } => {
                    assume(num_unmapped + num_frames < usize::MAX);
                    num_unmapped += num_frames;
                    proof { step_delta = num_frames as nat; }
                    assume(va + len <= usize::MAX);
                    #[verus_spec(with Tracked(tlb_model))]
                    self.flusher
                        .issue_tlb_flush_with(TlbFlushOp::Range(va..va + len), pt);
                },
            }

            proof {
                assert(num_unmapped as nat == start_mappings.filter(
                    |m: Mapping| start_va <= m.va_range.start < cursor_owner@.cur_va).len());
                assert(self.pt_cursor.inner.va < end_va) by { admit() };
            }
        }

        proof {
            cursor_owner.va.reflect_prop(self.pt_cursor.inner.va);
        }

        #[verus_spec(with Tracked(tlb_model))]
        self.flusher.dispatch_tlb_flush();

        num_unmapped
    }

    /// Applies the operation to the next slot of mapping within the range.
    ///
    /// The range to be found in is the current virtual address with the
    /// provided length.
    ///
    /// The function stops and yields the actually protected range if it has
    /// actually protected a page, no matter if the following pages are also
    /// required to be protected.
    ///
    /// It also makes the cursor moves forward to the next page after the
    /// protected one. If no mapped pages exist in the following range, the
    /// cursor will stop at the end of the range and return [`None`].
    ///
    /// Note that it will **NOT** flush the TLB after the operation. Please
    /// make the decision yourself on when and how to flush the TLB using
    /// [`Self::flusher`].
    ///
    /// # Panics
    ///
    /// Panics if the length is longer than the remaining range of the cursor.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>,
        requires
            old(regions).inv(),
            old(owner).inv(),
            !old(owner).cur_entry_owner().is_absent(),
            old(self).pt_cursor.inner.wf(*old(owner)),
            old(self).pt_cursor.inner.inv(),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
            len % PAGE_SIZE == 0,
            old(self).pt_cursor.inner.level < NR_LEVELS,
            old(self).pt_cursor.inner.va + len <= old(self).pt_cursor.inner.barrier_va.end,
            op.requires((old(owner).cur_entry_owner().frame.unwrap().prop,)),
        ensures
    )]
    pub fn protect_next(
        &mut self,
        len: usize,
        op: impl FnOnce(PageProperty) -> PageProperty,
    ) -> Option<Range<Vaddr>> {
        // SAFETY: It is safe to protect memory in the userspace.
        unsafe {
            #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
            self.pt_cursor.protect_next(len, op)
        }
    }
}

/*cpu_local_cell! {
    /// The `Arc` pointer to the activated VM space on this CPU. If the pointer
    /// is NULL, it means that the activated page table is merely the kernel
    /// page table.
    // TODO: If we are enabling ASID, we need to maintain the TLB state of each
    // CPU, rather than merely the activated `VmSpace`. When ASID is enabled,
    // the non-active `VmSpace`s can still have their TLB entries in the CPU!
    static ACTIVATED_VM_SPACE: *const VmSpace = core::ptr::null();
}*/

/*#[cfg(ktest)]
pub(super) fn get_activated_vm_space() -> *const VmSpace {
    ACTIVATED_VM_SPACE.load()
}*/

/// The configuration for user page tables.
#[derive(Clone, Debug)]
pub struct UserPtConfig {}

/// The item that can be mapped into the [`VmSpace`].
#[derive(Clone)]
pub struct MappedItem {
    pub frame: UFrame,
    pub prop: PageProperty,
}

// SAFETY: `item_into_raw` and `item_from_raw` are implemented correctly,
unsafe impl PageTableConfig for UserPtConfig {
    open spec fn TOP_LEVEL_INDEX_RANGE_spec() -> Range<usize> {
        0..256
    }

    open spec fn TOP_LEVEL_CAN_UNMAP_spec() -> (b: bool) {
        true
    }

    fn TOP_LEVEL_INDEX_RANGE() -> Range<usize> {
        0..256
    }

    fn TOP_LEVEL_CAN_UNMAP() -> (b: bool) {
        true
    }

    type E = PageTableEntry;

    type C = PagingConsts;

    type Item = MappedItem;

    uninterp spec fn item_into_raw_spec(item: Self::Item) -> (Paddr, PagingLevel, PageProperty);

    #[verifier::external_body]
    fn item_into_raw(item: Self::Item) -> (Paddr, PagingLevel, PageProperty) {
        let MappedItem { frame, prop } = item;
        let level = frame.map_level();
        let paddr = frame.into_raw();
        (paddr, level, prop)
    }

    uninterp spec fn item_from_raw_spec(
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
    ) -> Self::Item;

    #[verifier::external_body]
    fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item {
        let frame = unsafe { UFrame::from_raw(paddr) };
        MappedItem { frame, prop }
    }

    axiom fn axiom_nr_subpage_per_huge_eq_nr_entries();

    axiom fn item_roundtrip(item: Self::Item, paddr: Paddr, level: PagingLevel, prop: PageProperty);
}
} // verus!
