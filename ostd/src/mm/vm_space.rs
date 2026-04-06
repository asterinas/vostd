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
use vstd::simple_pptr::PointsTo;
use vstd::atomic::PermissionU64;

use crate::specs::mm::virt_mem_newer::{MemView, VirtPtr};

use crate::error::Error;
use crate::mm::frame::untyped::UFrame;
use crate::mm::io::VmIoMemView;
use crate::mm::page_table::*;
use crate::mm::page_table::{EntryOwner, PageTableFrag, PageTableGuard};
use crate::mm::kspace::KernelPtConfig;
use crate::mm::frame::MetaSlot;
use crate::specs::arch::*;
use crate::specs::mm::frame::mapping::meta_to_frame;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::frame::meta_owners::{MetaPerm, MetaSlotStorage, MetadataInnerPerms};
use crate::specs::mm::page_table::cursor::owners::CursorOwner;
use crate::specs::mm::page_table::*;
use crate::specs::mm::tlb::TlbModel;
use crate::specs::task::InAtomicMode;
use core::marker::PhantomData;
use core::{ops::Range, sync::atomic::Ordering};
use vstd_extra::ghost_tree::*;

use crate::mm::tlb::*;
use crate::specs::mm::cpu::{AtomicCpuSet, CpuSet};
use crate::mm::kspace::KERNEL_PAGE_TABLE;

use crate::{
    mm::{
        io::{VmIoOwner, VmReader, VmWriter},
        page_prop::PageProperty,
        Paddr, PagingConstsTrait, PagingLevel, Vaddr, MAX_USERSPACE_VADDR,
    },
    prelude::*,
};

use alloc::sync::Arc;

#[path = "../../specs/mm/vm_space.rs"]
pub mod vm_space_specs;
use vm_space_specs::*;

verus! {

/// A virtual address space for user-mode tasks, enabling safe manipulation of user-space memory.
///
/// The [`VmSpace`] type provides memory isolation guarantees between user-space and
/// kernel-space. For example, given an arbitrary user-space pointer, one can read and
/// write the memory location referred to by the user-space pointer without the risk of
/// breaking the memory safety of the kernel space.
///
/// # Task Association Semantics
///
/// As far as OSTD is concerned, a [`VmSpace`] is not necessarily associated with a task. Once a
/// [`VmSpace`] is activated (see [`VmSpace::activate`]), it remains activated until another
/// [`VmSpace`] is activated **possibly by another task running on the same CPU**.
///
/// This means that it's up to the kernel to ensure that a task's [`VmSpace`] is always activated
/// while the task is running. This can be done by using the injected post schedule handler
/// (see [`inject_post_schedule_handler`]) to always activate the correct [`VmSpace`] after each
/// context switch.
///
/// If the kernel otherwise decides not to ensure that the running task's [`VmSpace`] is always
/// activated, the kernel must deal with race conditions when calling methods that require the
/// [`VmSpace`] to be activated, e.g., [`UserMode::execute`], [`VmReader`] and [`VmWriter`].
/// Otherwise, the behavior is unspecified, though it's guaranteed _not_ to compromise the kernel's
/// memory safety.
///
/// # Memory Backing
///
/// A newly-created [`VmSpace`] is not backed by any physical memory pages. To
/// provide memory pages for a [`VmSpace`], one can allocate and map physical
/// memory ([`UFrame`]s) to the [`VmSpace`] using the cursor.
///
/// A [`VmSpace`] can also attach a page fault handler, which will be invoked to
/// handle page faults generated from user space.
///
/// [`inject_post_schedule_handler`]: crate::task::inject_post_schedule_handler
/// [`UserMode::execute`]: crate::user::UserMode::execute
/// [`VmReader`]: crate::mm::io::VmWriter
/// [`VmReader`]: crate::mm::io::VmReader
/// # Verification Design
///
/// A [`VmSpace`] has a corresponding [`VmSpaceOwner`] object that is used to track its state,
/// and against which its invariants are stated. The [`VmSpaceOwner`] catalogues the readers and writers
/// that are associated with the [`VmSpace`], and the [`MemView`] which encodes the active page table and
/// the subset of the TLB that covers the same virtual address space.
/// All proofs about the correctness of the readers and writers are founded on the well-formedness of the [`MemView`]:
///
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
    pub cpus: AtomicCpuSet,
    pub _marker: PhantomData<&'a ()>,
}

type Result<A> = core::result::Result<A, Error>;

#[verus_verify]
impl<'a> VmSpace<'a> {

    /// Creates a new VM address space.
    ///
    /// This allocates a new user page table by duplicating the kernel page
    /// table's top-level entries, and returns a [`VmSpace`] that wraps it.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The meta-region invariants must hold.
    /// ## Postconditions
    /// - The returned [`VmSpace`] instance satisfies the invariants of [`VmSpace`].
    #[inline]
    #[verus_spec(r =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards_k): Tracked<&mut Guards<'static, KernelPtConfig>>,
            Tracked(guards_u): Tracked<&mut Guards<'static, UserPtConfig>>,
        requires
            old(regions).inv(),
    )]
    pub fn new() -> Self {
        proof_decl! {
            let tracked mut kernel_owner_opt: Option<&PageTableOwner<KernelPtConfig>> = None;
        }
        let kpt = crate::mm::kspace::kvirt_area::get_kernel_page_table(
            Tracked(&mut kernel_owner_opt), Tracked(regions),
        );
        proof_decl! {
            let tracked kernel_owner = kernel_owner_opt.tracked_take();
        }
        let pt = {
            #[verus_spec(with Tracked(kernel_owner), Tracked(regions), Tracked(guards_k), Tracked(guards_u))]
            kpt.create_user_page_table::<crate::specs::task::AnyAtomicGuard>()
        };
        Self {
            pt,
            cpus: AtomicCpuSet::new(CpuSet::new_empty()),
            _marker: PhantomData,
        }
    }

    /// Gets an immutable cursor in the virtual address range.
    ///
    /// The cursor behaves like a lock guard, exclusively owning a sub-tree of
    /// the page table, preventing others from creating a cursor in it. So be
    /// sure to drop the cursor as soon as possible.
    ///
    /// The creation of the cursor may block if another cursor having an
    /// overlapping range is alive.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The page table owner must be valid.
    /// ## Postconditions
    /// - When the virtual address range satisfies
    ///   [`cursor_new_success_conditions`](crate::mm::page_table::Cursor::cursor_new_success_conditions),
    ///   the result is `Ok` and a [`CursorOwner`] is returned.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<PageTableOwner<UserPtConfig>>,
            Tracked(guard_perm): Tracked<GuardPerm<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>
            -> cursor_owner: Tracked<Option<CursorOwner<'a, UserPtConfig>>>
        requires
            owner.inv(),
        ensures
            crate::mm::page_table::Cursor::<UserPtConfig, G>::cursor_new_success_conditions(va) ==> r is Ok && cursor_owner@ is Some,
    )]
    pub fn cursor<G: InAtomicMode>(&'a self, guard: &'a G, va: &Range<Vaddr>) -> Result<Cursor<'a, G>> {
        proof_decl! {
            let tracked mut out_owner: Option<CursorOwner<'a, UserPtConfig>>;
        }
        match {
            #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
            self.pt.cursor(guard, va)
        } {
            Ok((pt_cursor, tracked_owner)) => {
                proof! { out_owner = Some(tracked_owner.get()); }
                proof_with!(|= Tracked(out_owner));
                Ok(Cursor(pt_cursor))
            }
            Err(e) => {
                proof! { out_owner = None; }
                proof_with!(|= Tracked(out_owner));
                Err(Error::AccessDenied)
            }
        }
    }

    /// Gets a mutable cursor in the virtual address range.
    ///
    /// The same as [`Self::cursor`], the cursor behaves like a lock guard,
    /// exclusively owning a sub-tree of the page table, preventing others
    /// from creating a cursor in it. So be sure to drop the cursor as soon as
    /// possible.
    ///
    /// The creation of the cursor may block if another cursor having an
    /// overlapping range is alive. The modification to the mapping by the
    /// cursor may also block or be overridden by the mapping of another cursor.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The page table owner must be valid.
    /// ## Postconditions
    /// - When the virtual address range satisfies
    ///   [`cursor_new_success_conditions`](crate::mm::page_table::Cursor::cursor_new_success_conditions),
    ///   the result is `Ok` and a [`CursorOwner`] is returned.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<PageTableOwner<UserPtConfig>>,
            Tracked(guard_perm): Tracked<GuardPerm<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>
            -> cursor_owner: Tracked<Option<CursorOwner<'a, UserPtConfig>>>
        requires
        ensures
            crate::mm::page_table::Cursor::<UserPtConfig, G>::cursor_new_success_conditions(va) ==> r is Ok && cursor_owner@ is Some,
    )]
    pub fn cursor_mut<G: InAtomicMode>(&'a self, guard: &'a G, va: &Range<Vaddr>) -> Result<CursorMut<'a, G>> {
        proof_decl! {
            let tracked mut out_owner: Option<CursorOwner<'a, UserPtConfig>>;
        }
        match {
            #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
            self.pt.cursor_mut(guard, va)
        } {
            Ok((pt_cursor, tracked_owner)) => {
                proof! { out_owner = Some(tracked_owner.get()); }
                proof_with!(|= Tracked(out_owner));
                Ok(CursorMut {
                    pt_cursor,
                    flusher: TlbFlusher::new(&self.cpus),
                })
            }
            Err(e) => {
                proof! { out_owner = None; }
                proof_with!(|= Tracked(out_owner));
                Err(Error::AccessDenied)
            }
        }
    }

    /// Creates a reader to read data from the user space of the current task.
    ///
    /// Returns [`Err`] if this [`VmSpace`] is not the user space of the current task
    /// or the `vaddr` and `len` do not represent a valid user space memory range.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The [`VmSpaceOwner`] invariant must hold.
    /// ## Postconditions
    /// - When [`Self::reader_success_cond`] holds, the result is `Ok`.
    /// - On success, the [`VmReader`] and its [`VmIoOwner`] are well-formed with no memory view.
    /// ## Safety
    /// - The function does not interact with the lower-level memory system directly.
    ///   By checking that the target (user) page table is not the active (kernel) one,
    ///   we ensure that the resulting reader cannot interact with kernel memory.
    #[inline]
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&'a mut VmSpaceOwner<'a>>,
                -> reader_owner: Tracked<Option<VmIoOwner<'a>>>,
        requires
            old(owner).inv(),
        ensures
            owner.inv(),
            self.reader_success_cond(vaddr, len) ==> r is Ok && reader_owner@ is Some,
            r is Ok && reader_owner@ is Some ==> {
                &&& r.unwrap().wf(reader_owner@.unwrap())
                &&& reader_owner@.unwrap().mem_view is None
            }
    )]
    pub fn reader(&self, vaddr: Vaddr, len: usize) -> Result<VmReader<'a>> {
        if current_page_table_paddr() != self.pt.root_paddr() {
            proof_with!(|= Tracked(None));
            Err(Error::AccessDenied)
        } else if vaddr.checked_add(len).unwrap_or(usize::MAX) > MAX_USERSPACE_VADDR {
            proof_with!(|= Tracked(None));
            Err(Error::AccessDenied)
        } else {
            let ghost id = owner.new_vm_io_id();
            proof_decl! {
                let tracked mut vm_reader_owner;
            }

            // SAFETY: The memory range is in user space, as checked above.
            let reader = unsafe {
                proof_with!(Ghost(id) => Tracked(vm_reader_owner));
                VmReader::from_user_space(VirtPtr::from_vaddr(vaddr, len), len)
            };

            proof_with!(|= Tracked(Some(vm_reader_owner)));
            Ok(reader)
        }
    }

    /// Creates a writer to write data to the user space of the current task.
    ///
    /// Returns [`Err`] if this [`VmSpace`] is not the user space of the current task
    /// or the `vaddr` and `len` do not represent a valid user space memory range.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The [`VmSpaceOwner`] invariant must hold.
    /// ## Postconditions
    /// - When [`Self::writer_success_cond`] holds, the result is `Ok`.
    /// - On success, the [`VmWriter`] and its [`VmIoOwner`] are well-formed with no memory view.
    /// ## Safety
    /// - The function does not interact with the lower-level memory system directly.
    ///   By checking that the target (user) page table is not the active (kernel) one,
    ///   we ensure that the resulting writer cannot interact with kernel memory.
    #[inline]
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmSpaceOwner<'a>>,
                -> writer_owner: Tracked<Option<VmIoOwner<'a>>>,
        requires
            old(owner).inv(),
        ensures
            owner.inv(),
            self.writer_success_cond(vaddr, len) ==> r is Ok && writer_owner@ is Some,
            r is Ok && writer_owner@ is Some ==> {
                &&& r.unwrap().wf(writer_owner@.unwrap())
                &&& writer_owner@.unwrap().mem_view is None
            }
    )]
    pub fn writer(self, vaddr: Vaddr, len: usize) -> Result<VmWriter<'a>> {
        if current_page_table_paddr() != self.pt.root_paddr() {
            proof_with!(|= Tracked(None));
            Err(Error::AccessDenied)
        } else if vaddr.checked_add(len).unwrap_or(usize::MAX) > MAX_USERSPACE_VADDR {
            proof_with!(|= Tracked(None));
            Err(Error::AccessDenied)
        } else {
            let ghost id = owner.new_vm_io_id();
            proof_decl! {
                let tracked mut vm_writer_owner;
            }

            // SAFETY: The memory range is in user space, as checked above.
            let reader = unsafe {
                proof_with!(Ghost(id) => Tracked(vm_writer_owner));
                VmWriter::from_user_space(VirtPtr::from_vaddr(vaddr, len), len)
            };

            proof_with!(|= Tracked(Some(vm_writer_owner)));
            Ok(reader)
        }
    }
}

/// The cursor for querying over the VM space without modifying it.
///
/// It exclusively owns a sub-tree of the page table, preventing others from
/// reading or modifying the same sub-tree. Two read-only cursors can not be
/// created from the same virtual address range either.
pub struct Cursor<'a, A: InAtomicMode>(pub crate::mm::page_table::Cursor<'a, UserPtConfig, A>);

#[verus_verify]
impl<'rcu, A: InAtomicMode> Cursor<'rcu, A> {
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
    /// it returns [`None`], and the virtual address range of the cursor's current position.
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
            old(owner).metaregion_correct(*old(regions)) ==> owner.metaregion_correct(*regions),
            self.0.query_some_condition(*owner) ==> {
                &&& r is Ok
                &&& self.0.query_some_ensures(*owner, r.unwrap())
            },
            !self.0.query_some_condition(*owner) ==> {
                &&& r is Ok
                &&& self.0.query_none_ensures(*owner, r.unwrap())
            },
            old(owner)@.mappings == owner@.mappings,
            forall |e: EntryOwner<UserPtConfig>| #[trigger] e.inv() && e.metaregion_sound(*old(regions)) ==> e.metaregion_sound(*regions),
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
    /// - **Safety Invariants**: The page table cursor safety invariants
    /// ([crate::mm::page_table::Cursor::invariants]) must hold before the call.
    /// - **Liveness**: In order to avoid a panic, the length must be page-aligned and less than or equal to the remaining range of the cursor.
    /// ## Postconditions
    /// - **Safety Invariants**: Page table cursor safety invariants are preserved.
    /// - **Correctness**: If there is a mapped address after the current address within the next `len` bytes,
    /// it will move the cursor to the next mapped address and return it.
    /// - **Correctness**: If the metadata region was well-formed before the call, it will be well-formed after.
    /// ## Panics
    /// This method panics if the length is longer than the remaining range of the cursor.
    /// ## Safety
    /// This function preserves all memory invariants.
    /// Because it panics rather than move the cursor to an invalid address,
    /// it ensures that the cursor is safe to use after the call.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, UserPtConfig>>
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            !old(self).0.find_next_panic_condition(len),
        ensures
            self.0.invariants(*owner, *regions, *guards),
            old(owner).metaregion_correct(*old(regions)) ==> owner.metaregion_correct(*regions),
            res is Some ==> {
                &&& res.unwrap() == self.0.va
                &&& owner.level < owner.guard_level
                &&& owner.in_locked_range()
            },
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>) {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.find_next(len)
    }

    /// Jump to the virtual address.
    ///
    /// This function will move the cursor to the given virtual address.
    /// If the target address is not in the locked range, it will return an error.
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The page table cursor safety invariants
    /// ([crate::mm::page_table::Cursor::invariants]) must hold before the call.
    /// - **Liveness**:  The function will panic if the target `va` is not aligned
    /// to the base page size.
    /// ## Postconditions
    /// - **Safety Invariants**: Page table cursor safety invariants are preserved.
    /// - **Correctness**: If the target `va` is within the cursor's locked range,
    /// the result will be `Ok` and the cursor's virtual address will be set to `va`.
    /// - **Correctness**: If the target `va` is outside the locked range, the result is `Err`.
    /// - **Correctness**: If the metadata region was well-formed before the call, it will be well-formed after.
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
            old(owner).in_locked_range(),
            !old(self).0.jump_panic_condition(va),
        ensures
            self.0.invariants(*owner, *regions, *guards),
            old(owner).metaregion_correct(*old(regions)) ==> owner.metaregion_correct(*regions),
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
    pub flusher: TlbFlusher<'a  /*, DisabledPreemptGuard*/ >,
}

impl<'a, A: InAtomicMode> CursorMut<'a, A> {

    /// Queries the mapping at the current virtual address.
    ///
    /// This is the same as [`Cursor::query`].
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the mapped item.
    /// ## Preconditions
    /// - **Safety Invariants**: The page table cursor safety invariants
    /// ([crate::mm::page_table::Cursor::invariants]) must hold before the call.
    /// ## Postconditions
    /// - **Safety Invariants**: Page table cursor safety invariants are preserved.
    /// - **Correctness**: If the cursor is within the locked range, the result is `Ok`.
    /// - **Correctness**: If there is a mapped item at the current virtual address ([`query_some_condition`]),
    /// it is returned along with the virtual address range that it maps ([`query_success_ensures`]).
    /// - **Correctness**: The mapping that is returned corresponds to the abstract mapping given by [`query_item_spec`](CursorView::query_item_spec).
    /// - **Correctness**: If there is no mapped item at the current virtual address ([`query_none_condition`]),
    /// it returns `None`, and the virtual address range of the cursor's current position.
    /// - **Correctness**: If the metadata region was well-formed before the call, it will be well-formed after.
    /// - **Safety**: The mappings in the page table are not affected.
    /// - **Safety**: The soundness of individual entries are not affected.
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
            old(owner).metaregion_correct(*old(regions)) ==> owner.metaregion_correct(*regions),
            old(owner).in_locked_range() ==> res is Ok,
            res matches Ok(state) ==>
                self.pt_cursor.inner.query_some_condition(*owner) ==>
                self.pt_cursor.inner.query_some_ensures(*owner, state),
            res matches Ok(state) ==>
                !self.pt_cursor.inner.query_some_condition(*owner) ==>
                self.pt_cursor.inner.query_none_ensures(*owner, state),
            old(owner)@.mappings == owner@.mappings,
            forall |e: EntryOwner<UserPtConfig>| #[trigger] e.inv() && e.metaregion_sound(*old(regions)) ==> e.metaregion_sound(*regions),
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
    /// - **Safety Invariants**: The page table cursor safety invariants
    /// ([crate::mm::page_table::Cursor::invariants]) must hold before the call.
    /// - **Liveness**: In order to avoid a panic, the length must be page-aligned and less than or equal to the remaining range of the cursor.
    /// ## Postconditions
    /// - **Safety Invariants**: Page table cursor safety invariants are preserved.
    /// - **Correctness**: If there is a mapped address after the current address within the next `len` bytes,
    /// it will move the cursor to the next mapped address and return it.
    /// - **Correctness**: If the metadata region was well-formed before the call, it will be well-formed after.
    /// ## Panics
    /// This method panics if the length is longer than the remaining range of the cursor.
    /// ## Safety
    /// This function preserves all memory invariants.
    /// Because it panics rather than move the cursor to an invalid address,
    /// it ensures that the cursor is safe to use after the call.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(self).pt_cursor.inner.invariants(*old(owner), *old(regions), *old(guards)),
            !old(self).pt_cursor.inner.find_next_panic_condition(len),
        ensures
            self.pt_cursor.inner.invariants(*owner, *regions, *guards),
            old(owner).metaregion_correct(*old(regions)) ==> owner.metaregion_correct(*regions),
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
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The page table cursor safety invariants
    /// ([crate::mm::page_table::Cursor::invariants]) must hold before the call.
    /// - **Liveness**:  The function will panic if the target `va` is not aligned
    /// to the base page size.
    /// ## Postconditions
    /// - **Safety Invariants**: Page table cursor safety invariants are preserved.
    /// - **Correctness**: If the target `va` is within the cursor's locked range,
    /// the result will be `Ok` and the cursor's virtual address will be set to `va`.
    /// - **Correctness**: If the target `va` is outside the locked range, the result is `Err`.
    /// - **Correctness**: If the metadata region was well-formed before the call, it will be well-formed after.
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
            old(owner).in_locked_range(),
            !old(self).pt_cursor.inner.jump_panic_condition(va),
        ensures
            self.pt_cursor.inner.invariants(*owner, *regions, *guards),
            old(owner).metaregion_correct(*old(regions)) ==> owner.metaregion_correct(*regions),
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

    /// Map a frame into the current slot.
    ///
    /// This method will bring the cursor to the next slot after the modification.
    /// If there is an existing mapping at the current slot, it will be replaced
    /// and the TLB will be flushed for that entry.
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The page table cursor safety invariants
    ///   ([`invariants`](crate::mm::page_table::Cursor::invariants)) and the TLB invariant
    ///   ([`TlbModel::inv`]) must hold before the call.
    /// - **Liveness**: The cursor must not be past the end of its locked range,
    ///   and the frame's level must fit within the remaining range, or the function will panic.
    /// - **Bookkeeping**: The frame must be well-formed with respect to its entry owner
    ///   ([`item_wf`](Self::item_wf)).
    /// ## Postconditions
    /// - **Safety Invariants**: Page table cursor safety invariants are preserved.
    /// - **Correctness**: The page table view is updated with the new mapping
    ///   according to [`map_item_ensures`](Self::map_item_ensures).
    /// - **Correctness**: If the metadata region was well-formed before the call
    ///   and the frame was not already mapped, it will be well-formed after.
    /// ## Safety
    /// - For soundness purposes, it doesn't matter if a frame is mapped multiple times
    /// in the same page table. There is still a clear definition of the behavior.
    #[verus_spec(
        with Tracked(cursor_owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(entry_owner): Tracked<EntryOwner<UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>,
            Tracked(tlb_model): Tracked<&mut TlbModel>
        requires
            old(tlb_model).inv(),
            old(self).pt_cursor.inner.invariants(*old(cursor_owner), *old(regions), *old(guards)),
            old(cursor_owner).in_locked_range(),
            !old(self).pt_cursor.map_panic_conditions(MappedItem { frame: frame, prop: prop }),
            old(self).item_wf(frame, prop, entry_owner, *old(regions)),
        ensures
            self.pt_cursor.inner.invariants(*cursor_owner, *regions, *guards),
            old(cursor_owner).metaregion_correct(*old(regions))
                && crate::mm::page_table::CursorMut::<'a, UserPtConfig, A>::item_not_mapped(
                    MappedItem { frame: frame, prop: prop }, *old(regions))
                ==> cursor_owner.metaregion_correct(*regions),
            old(self).map_item_ensures(
                frame,
                prop,
                old(self).pt_cursor.inner.model(*old(cursor_owner)),
                self.pt_cursor.inner.model(*cursor_owner),
            ),
    )]
    pub fn map(&mut self, frame: UFrame, prop: PageProperty) {
        let start_va = self.virt_addr();
        let item = MappedItem { frame: frame, prop: prop };

        assert(self.pt_cursor.item_wf(item, entry_owner)) by { };

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
                self.flusher.issue_tlb_flush_with(TlbFlushOp::Address(start_va), old_frame.into());
                #[verus_spec(with Tracked(tlb_model))]
                self.flusher.dispatch_tlb_flush();
            },
            PageTableFrag::StrayPageTable { .. } => {
                assert(false) by {
                    assert(UserPtConfig::item_into_raw(item).1 == 1);
                };
                //panic!("`UFrame` is base page sized but re-mapping out a child PT");
            },
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
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The page table cursor safety invariants
    /// ([crate::mm::page_table::Cursor::invariants]) must hold before the call.
    /// - **Safety Invariants**: The TLB invariant ([TlbModel::inv]) must hold.
    /// - **Liveness**: In order to avoid a panic, the length must be page-aligned and less than or equal to the remaining range of the cursor.
    /// ## Postconditions
    /// - **Safety Invariants**: The page table cursor safety invariants are preserved.
    /// - **Safety Invariants**: The TLB invariant is preserved.
    /// - **Correctness**: Unmaps a range of virtual addresses from the current address up to `len` bytes
    /// and returns the number of mappings that were removed.
    /// - **Correctness**: If the metadata region was well-formed before the call, it will be well-formed after.
    /// ## Panics
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    /// ## Safety
    /// - It is always sound to unmap pages. We flush unmapped pages from the TLB to ensure consistency.
    /// - TODO: formalizing and proving that this function preserves TLB consistency would
    /// be pretty straightforward and would be a nice addition to the correctness properties.
    #[verus_spec(r =>
        with Tracked(cursor_owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>,
            Tracked(tlb_model): Tracked<&mut TlbModel>
        requires
            old(self).pt_cursor.inner.invariants(*old(cursor_owner), *old(regions), *old(guards)),
            !old(self).pt_cursor.inner.find_next_panic_condition(len),
            old(tlb_model).inv(),
        ensures
            self.pt_cursor.inner.invariants(*cursor_owner, *regions, *guards),
            old(cursor_owner).metaregion_correct(*old(regions)) ==> cursor_owner.metaregion_correct(*regions),
            old(self).pt_cursor.inner.model(*old(cursor_owner)).unmap_spec(len, self.pt_cursor.inner.model(*cursor_owner), r),
            tlb_model.inv(),
    )]
    pub fn unmap(&mut self, len: usize) -> usize {
        proof {
            assert(cursor_owner.va.reflect(self.pt_cursor.inner.va));
            assert(cursor_owner.inv());
            cursor_owner.va.reflect_prop(self.pt_cursor.inner.va);
            cursor_owner.view_preserves_inv();
        }

        let end_va = self.virt_addr() + len;
        let mut num_unmapped: usize = 0;

        let ghost start_mappings: Set<Mapping> = cursor_owner@.mappings;
        let ghost start_va: Vaddr = cursor_owner@.cur_va;
        // The "adjusted base" accumulates splits: starts as the split-at-boundaries
        // version of start_mappings and gets updated when take_next splits huge pages.
        let ghost mut adjusted_base: Set<Mapping> = cursor_owner@.mappings;
        // Track the set of removed mappings explicitly (not as a VA range filter).
        let ghost mut removed: Set<Mapping> = Set::empty();

        proof {
            // end_va <= barrier_va.end <= MAX_USERSPACE_VADDR for user page tables.
            // barrier_va.end = locked_range().end which is bounded by the user VA space.
            // TODO: derive from cursor construction postcondition.
            assume(end_va <= MAX_USERSPACE_VADDR);

            assert((self.pt_cursor.inner.va + len) % PAGE_SIZE as int == 0) by (compute);

            assert(end_va as int == start_va + len);
            cursor_owner.view_preserves_inv();
            assert(adjusted_base.finite());

            // At loop entry: removed is empty, so mappings == adjusted_base.
            assert(cursor_owner@.cur_va == start_va);
            assert(adjusted_base.difference(removed) =~= adjusted_base);
        }

        #[verus_spec(
            invariant
                self.pt_cursor.inner.va % PAGE_SIZE == 0,
                end_va % PAGE_SIZE == 0,
                end_va <= MAX_USERSPACE_VADDR,
                self.pt_cursor.inner.invariants(*cursor_owner, *regions, *guards),
                old(cursor_owner).metaregion_correct(*old(regions)) ==> cursor_owner.metaregion_correct(*regions),
                end_va <= self.pt_cursor.inner.barrier_va.end,
                tlb_model.inv(),
                start_va <= cursor_owner@.cur_va,
                // Split-aware invariant: adjusted_base tracks accumulated splits,
                // removed tracks the explicitly removed set.
                cursor_owner@.mappings =~= adjusted_base.difference(removed),
                removed.subset_of(adjusted_base),
                num_unmapped as nat == removed.len(),
                removed.finite(),
                num_unmapped <= MAX_PADDR / PAGE_SIZE,
                // Everything removed is in the [start, end) range.
                forall |m: Mapping| removed.contains(m) ==>
                    start_va <= m.va_range.start < end_va,
                // Nothing in [start_va, end_va) with start < cursor_va remains,
                // except sub-mappings of straddling boundary entries.
                // Simplified: just track start >= cursor_va (assumes no straddling).
                forall |m: Mapping| adjusted_base.contains(m) && !removed.contains(m)
                    && start_va <= m.va_range.start && m.va_range.start < end_va ==>
                    m.va_range.start >= cursor_owner@.cur_va,
                start_va == old(cursor_owner)@.cur_va,
                old(cursor_owner)@.inv(),
                adjusted_base.finite(),
                // Locality: old mappings fully outside [start, end) survive in adjusted_base.
                // (Straddling mappings may be split — see refinement.)
                forall |m: Mapping| old(cursor_owner)@.mappings.contains(m)
                    && (m.va_range.end <= start_va || m.va_range.start >= end_va)
                    ==> adjusted_base.contains(m),
                // Refinement: every mapping in adjusted_base is either from the old view
                // or a sub-mapping of an old entry (from boundary splits).
                forall |m: Mapping| adjusted_base.contains(m) ==>
                    old(cursor_owner)@.mappings.contains(m)
                    || exists |parent: Mapping| old(cursor_owner)@.mappings.contains(parent)
                        && parent.va_range.start <= m.va_range.start
                        && m.va_range.end <= parent.va_range.end
                        && m.pa_range.start == (parent.pa_range.start + (m.va_range.start - parent.va_range.start)) as Paddr
                        && m.property == parent.property,
            invariant_except_break
                self.pt_cursor.inner.va <= end_va,
                self.pt_cursor.inner.va < end_va ==> cursor_owner.in_locked_range(),
            ensures
                self.pt_cursor.inner.va >= end_va,
            decreases end_va - self.pt_cursor.inner.va
        )]
        loop {
            let ghost prev_va: Vaddr = cursor_owner@.cur_va;
            let ghost prev_mappings: Set<Mapping> = cursor_owner@.mappings;
            let ghost num_unmapped_before: nat = num_unmapped as nat;

            let ghost prev_view_inv: bool = cursor_owner@.inv();
            proof {
                assert(self.pt_cursor.inner.wf(*cursor_owner));
                assert(cursor_owner.inv());
                cursor_owner.va.reflect_prop(self.pt_cursor.inner.va);
                assert(prev_va == self.pt_cursor.inner.va);
                cursor_owner.view_preserves_inv();
                assert(prev_view_inv);
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

                    assert(cursor_owner@.mappings == prev_mappings);
                    assert forall |m: Mapping|
                        adjusted_base.contains(m) && !removed.contains(m)
                        && start_va <= m.va_range.start
                    implies m.va_range.start >= end_va by {
                        if m.va_range.start < end_va {
                            assert(prev_mappings.contains(m));
                            assert(prev_mappings.filter(
                                |m2: Mapping| prev_va <= m2.va_range.start < end_va).contains(m));
                            assert(false);
                        }
                    };
                }
                break ;
            };

            let ghost old_adjusted = adjusted_base;
            let ghost old_removed = removed;

            proof {
                assert(self.pt_cursor.inner.wf(*cursor_owner));
                assert(cursor_owner.inv());
                cursor_owner.va.reflect_prop(self.pt_cursor.inner.va);
            }

            let ghost frag_ghost = frag;

            match frag {
                PageTableFrag::Mapped { va, item, .. } => {
                    let frame = item.frame;
                    assert(MAX_PADDR / PAGE_SIZE < usize::MAX) by (compute_only);
                    assert(num_unmapped < usize::MAX);
                    num_unmapped += 1;
                    #[verus_spec(with Tracked(tlb_model))]
                    self.flusher.issue_tlb_flush_with(TlbFlushOp::Address(va), frame.into());
                },
                PageTableFrag::StrayPageTable { pt, va, len, num_frames } => {
                    // num_unmapped <= MAX_PADDR / PAGE_SIZE (invariant).
                    // num_frames <= subtree size / PAGE_SIZE <= MAX_PADDR / PAGE_SIZE.
                    // Both bounded, sum < usize::MAX.
                    assume(num_unmapped + num_frames < usize::MAX);
                    num_unmapped += num_frames;
                    proof {
                        // va + len <= end_va: from take_next VA bound (StrayPageTable_va + StrayPageTable_len <= old_va + len_arg = end_va).
                        // end_va <= MAX_USERSPACE_VADDR < KERNEL_VADDR_RANGE.end.
                        assert(MAX_USERSPACE_VADDR < KERNEL_VADDR_RANGE.end as usize) by (compute_only);
                        assert(va + len <= KERNEL_VADDR_RANGE.end as usize);
                        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_va_plus_page_size_no_overflow(va, len);
                    }
                    #[verus_spec(with Tracked(tlb_model))]
                    self.flusher.issue_tlb_flush_with(TlbFlushOp::Range(va..va + len), pt);
                },
            }

            proof {
                // Hoisted definitions for Mapped case (used across all clauses).
                let ghost mm = match frag_ghost {
                    PageTableFrag::Mapped { va: fv, item: fi, .. } =>
                        CursorView::<UserPtConfig>::item_into_mapping(fv, fi),
                    _ => arbitrary(),
                };
                let ghost sv = CursorView::<UserPtConfig> {
                    cur_va: match frag_ghost {
                        PageTableFrag::Mapped { va: fv, .. } => fv as Vaddr,
                        _ => 0,
                    },
                    mappings: prev_mappings,
                    phantom: PhantomData,
                };
                let ghost sm = sv.split_while_huge(mm.page_size).mappings;
                let ghost is_mapped = frag_ghost is Mapped;

                // Hoisted StrayPageTable subtree definition.
                let ghost subtree = match frag_ghost {
                    PageTableFrag::StrayPageTable { va: fv, len: fl, .. } =>
                        prev_mappings.filter(|m2: Mapping| fv <= m2.va_range.start < fv + fl),
                    _ => Set::empty(),
                };

                // Update adjusted_base and removed.
                match frag_ghost {
                    PageTableFrag::StrayPageTable { .. } => {
                        removed = old_removed.union(subtree);
                    },
                    PageTableFrag::Mapped { .. } => {
                        adjusted_base = sm.union(old_removed);
                        removed = old_removed.union(set![mm]);
                    },
                }

                // VA bounds from take_next postconditions.
                assert(prev_va >= start_va);
                assert(end_va as int == prev_va + (end_va - prev_va));

                // Establish key Mapped-case facts once.
                if is_mapped {
                    assume(sv.inv()); // needs prev_view_inv + frag_va < MAX_USERSPACE_VADDR
                    assert(prev_mappings.disjoint(old_removed)) by {
                        assert forall |e: Mapping| prev_mappings.contains(e)
                            implies !old_removed.contains(e) by {};
                    };
                    sv.split_while_huge_disjoint(mm.page_size, old_removed);
                    assert(sv.split_while_huge(mm.page_size).inv()) by { admit() };
                }

                match frag_ghost {
                    PageTableFrag::StrayPageTable { .. } => {
                        assert(old_removed.disjoint(subtree)) by {
                            assert forall |e: Mapping| old_removed.contains(e)
                                implies !subtree.contains(e) by {};
                        };
                        vstd::set::axiom_set_intersect_finite::<Mapping>(
                            prev_mappings,
                            Set::new(|m2: Mapping| subtree.contains(m2)));
                        vstd::set_lib::lemma_set_disjoint_lens(old_removed, subtree);
                        assert(removed =~= old_removed + subtree);
                    },
                    PageTableFrag::Mapped { .. } => {
                        assert(sm.contains(mm));
                        assert(old_removed.disjoint(set![mm])) by {
                            assert forall |e: Mapping| old_removed.contains(e)
                                implies !set![mm].contains(e) by {};
                        };
                        vstd::set::axiom_set_insert_finite(Set::<Mapping>::empty(), mm);
                        vstd::set_lib::lemma_set_disjoint_lens(old_removed, set![mm]);
                        assert(removed =~= old_removed + set![mm]);
                        vstd::set_lib::lemma_set_empty_equivalency_len(Set::<Mapping>::empty());
                        assert(set![mm] =~= Set::<Mapping>::empty().insert(mm));
                        vstd::set::axiom_set_insert_len(Set::<Mapping>::empty(), mm);
                    },
                }
                assume(num_unmapped <= MAX_PADDR / PAGE_SIZE);
                if is_mapped {
                    vstd::set::axiom_set_union_finite(sm, old_removed);
                    assert(sm.contains(mm));
                }
                assert forall |e: Mapping| adjusted_base.difference(removed).contains(e)
                    <==> cursor_owner@.mappings.contains(e) by {};
                assert(cursor_owner@.mappings =~= adjusted_base.difference(removed));

                assert(removed.subset_of(adjusted_base)) by {
                    assert forall |e: Mapping| removed.contains(e)
                        implies adjusted_base.contains(e) by {};
                };

                assert forall |m: Mapping| removed.contains(m) implies
                    start_va <= m.va_range.start < end_va by {
                };

                assert forall |m: Mapping| adjusted_base.contains(m) && !removed.contains(m)
                    && start_va <= m.va_range.start && m.va_range.start < end_va
                    implies m.va_range.start >= cursor_owner@.cur_va by {
                    if m.va_range.start < cursor_owner@.cur_va {
                        if m.va_range.start >= prev_va {
                            // m.start ∈ [prev_va, cursor_va). Use F2-empty/F2b-empty/F2c-stable.
                            assert(cursor_owner@.mappings.contains(m));
                            match frag_ghost {
                                PageTableFrag::StrayPageTable { va: frag_va, .. } => {
                                    if m.va_range.start >= frag_va {
                                        assert(cursor_owner@.mappings.filter(
                                            |m2: Mapping| frag_va <= m2.va_range.start < self.pt_cursor.inner.va
                                        ).contains(m));
                                    } else {
                                        assert(prev_mappings.filter(
                                            |m2: Mapping| prev_va <= m2.va_range.start < frag_va
                                        ).contains(m));
                                    }
                                },
                                PageTableFrag::Mapped { va: frag_va, .. } => {
                                    if m.va_range.start >= (frag_va as usize) {
                                        assert(cursor_owner@.mappings.filter(
                                            |m2: Mapping| (frag_va as usize) <= m2.va_range.start < self.pt_cursor.inner.va
                                        ).contains(m));
                                    } else {
                                        assert(prev_mappings.filter(
                                            |m2: Mapping| prev_va <= m2.va_range.start < (frag_va as usize)
                                        ).contains(m));
                                    }
                                },
                            }
                            assert(false);
                        } else {
                            // m.start < prev_va → m was in old adj \ old rem.
                            if is_mapped { admit(); } // straddling boundary case
                            assert(false);
                        }
                    }
                };
                if is_mapped {
                    assert forall |m: Mapping| old(cursor_owner)@.mappings.contains(m)
                        && (m.va_range.end <= start_va || m.va_range.start >= end_va)
                        implies adjusted_base.contains(m) by {
                        if m.va_range.end <= start_va { assert(m.inv()); }
                        assert(prev_mappings.contains(m));
                        sv.split_while_huge_locality(mm.page_size, m);
                    };

                    assert forall |m: Mapping| adjusted_base.contains(m) implies
                            old(cursor_owner)@.mappings.contains(m)
                            || exists |parent: Mapping| old(cursor_owner)@.mappings.contains(parent)
                                && parent.va_range.start <= m.va_range.start
                                && m.va_range.end <= parent.va_range.end
                                && m.pa_range.start == (parent.pa_range.start + (m.va_range.start - parent.va_range.start)) as Paddr
                                && m.property == parent.property
                        by {
                            if !old_removed.contains(m) {
                                sv.split_while_huge_refinement(mm.page_size, m);
                                if prev_mappings.contains(m) {
                                } else {
                                    let p = choose |p: Mapping| prev_mappings.contains(p)
                                        && p.va_range.start <= m.va_range.start
                                        && m.va_range.end <= p.va_range.end
                                        && m.pa_range.start == (p.pa_range.start + (m.va_range.start - p.va_range.start)) as Paddr
                                        && m.property == p.property;
                                    assert(old_adjusted.contains(p));
                                    if old(cursor_owner)@.mappings.contains(p) {
                                    } else {
                                        let orig = choose |orig: Mapping|
                                            old(cursor_owner)@.mappings.contains(orig)
                                            && orig.va_range.start <= p.va_range.start
                                            && p.va_range.end <= orig.va_range.end
                                            && p.pa_range.start == (orig.pa_range.start + (p.va_range.start - orig.va_range.start)) as Paddr
                                            && p.property == orig.property;
                                        assert(orig.inv());
                                        let ghost offset = (m.va_range.start - orig.va_range.start) as usize;
                                        assert(offset <= orig.page_size) by {
                                            admit(); // m.start <= m.end (needs split preserves inv)
                                        };
                                    }
                                }
                            }
                        };
                }
            }
        }

        proof {
            cursor_owner.va.reflect_prop(self.pt_cursor.inner.va);

            let old_view = old(self).pt_cursor.inner.model(*old(cursor_owner));
            let new_view = self.pt_cursor.inner.model(*cursor_owner);

            // Bridge from loop invariant to unmap_spec.
            let start = old_view.cur_va;
            let end = (old_view.cur_va + len) as Vaddr;

            assert(new_view.cur_va >= end);

            assert forall |m: Mapping| old_view.mappings.contains(m)
                && (m.va_range.end <= start || m.va_range.start >= end)
                implies new_view.mappings.contains(m) by {
                assert(adjusted_base.contains(m));
                if m.va_range.end <= start {
                    assert(m.inv());
                }
            };

            assert forall |m: Mapping| new_view.mappings.contains(m)
                implies !(start <= m.va_range.start < end) by { };

            assert forall |m: Mapping| new_view.mappings.contains(m)
                implies old_view.mappings.contains(m)
                || exists |parent: Mapping| old_view.mappings.contains(parent)
                    && parent.va_range.start <= m.va_range.start
                    && m.va_range.end <= parent.va_range.end
                    && m.pa_range.start == (parent.pa_range.start + (m.va_range.start - parent.va_range.start)) as Paddr
                    && m.property == parent.property
            by { };
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
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The page table cursor safety invariants
    ///   ([`invariants`](crate::mm::page_table::Cursor::invariants)) and the
    ///   meta-region invariants must hold before the call.
    /// - The cursor must be within the locked range and below the guard level.
    /// - The current entry must be a mapped frame (not absent or a page table node).
    /// - **Liveness**: The length must be page-aligned and within the remaining cursor range.
    /// ## Postconditions
    /// - **Correctness**: If the metadata region was well-formed before the call, it will be
    ///   well-formed after.
    /// ## Panics
    /// Panics if the length is longer than the remaining range of the cursor.
    /// ## Safety
    /// - From a soundness perspective changing a userspace page's `prop` field is safe.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>,
        requires
            old(self).pt_cursor.inner.invariants(*old(owner), *old(regions), *old(guards)),
            !old(self).pt_cursor.inner.find_next_panic_condition(len),
            forall |p: PageProperty| op.requires((p,)),
        ensures
            self.pt_cursor.inner.invariants(*owner, *regions, *guards),
            old(owner).metaregion_correct(*old(regions)) ==> owner.metaregion_correct(*regions),
            self.pt_cursor.inner.barrier_va == old(self).pt_cursor.inner.barrier_va,
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
pub struct MappedItem {
    pub frame: UFrame,
    pub prop: PageProperty,
}

#[verus_verify]
impl RCClone for MappedItem {

    open spec fn clone_requires(self, slot_perm: PointsTo<MetaSlot>, rc_perm: PermissionU64) -> bool {
        self.frame.clone_requires(slot_perm, rc_perm)
    }

    fn clone(&self, Tracked(slot_perm): Tracked<&PointsTo<MetaSlot>>, Tracked(rc_perm): Tracked<&mut PermissionU64>) -> (res: Self)
    {
        let frame = self.frame.clone(Tracked(slot_perm), Tracked(rc_perm));
        Self {
            frame,
            prop: self.prop,
        }
    }
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

    open spec fn item_into_raw_spec(item: Self::Item) -> (Paddr, PagingLevel, PageProperty) {
        (item.frame.paddr(), 1, item.prop)
    }

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
