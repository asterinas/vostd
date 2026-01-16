// SPDX-License-Identifier: MPL-2.0
//! Virtual memory space management.
//!
//! The [`VmSpace`] struct is provided to manage the virtual memory space of a
//! user. Cursors are used to traverse and modify over the virtual memory space
//! concurrently. The VM space cursor [`self::Cursor`] is just a wrapper over
//! the page table cursor, providing efficient, powerful concurrent accesses
//! to the page table.
use vstd::pervasive::arbitrary;
use vstd::prelude::*;
use vstd_extra::virtual_ptr::{MemView, VirtPtr};

use crate::error::Error;
use crate::mm::frame::untyped::UFrame;
use crate::mm::page_table::*;
use crate::mm::page_table::{EntryOwner, PageTableFrag, PageTableGuard};
use crate::specs::arch::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::owners::CursorOwner;
use crate::specs::mm::page_table::*;
use crate::specs::task::InAtomicMode;
use core::marker::PhantomData;
use core::{ops::Range, sync::atomic::Ordering};
use vstd_extra::ghost_tree::*;

use crate::{
    //    cpu::{AtomicCpuSet, CpuSet, PinCurrentCpu},
    //    cpu_local_cell,
    mm::{
        io::{VmIoOwner, VmReader, VmWriter},
        //        io::Fallible,
        // kspace::KERNEL_PAGE_TABLE,
        // page_table,
        //        tlb::{TlbFlushOp, TlbFlusher},
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

verus! {

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
#[rustc_has_incoherent_inherent_impls]
pub struct VmSpace<'a> {
    pub pt: PageTable<UserPtConfig>,
    /// Whether we allow shared reading.
    pub shared_reader: bool,
    //    cpus: AtomicCpuSet,
    pub marker: PhantomData<&'a ()>,
}

impl Inv for VmSpace<'_> {
    open spec fn inv(self) -> bool {
        true
    }
}

/// This struct is used for reading/writing memories represented by the
/// [`VmReader`] or [`VmWriter`]. We also requrie a valid `vmspace_owner`
/// must be present in this struct to ensure that the reader/writer is
/// not created out of thin air.
pub tracked struct VmIoPermission<'a> {
    pub vmio_owner: VmIoOwner<'a>,
    pub vmspace_owner: VmSpaceOwner<'a>,
}

/// A tracked struct for reasoning about verification-only properties of a [`VmSpace`].
pub tracked struct VmSpaceOwner<'a> {
    /// The owner of the page table of this VM space.
    pub page_table_owner: OwnerSubtree<'a, UserPtConfig>,
    /// Whether this VM space is currently active.
    pub active: bool,
    /// Active readers for this VM space.
    pub readers: Map<nat, VmIoOwner<'a>>,
    /// Active writers for this VM space.
    pub writers: Map<nat, VmIoOwner<'a>>,
    /// The memory view is the abstract view of memory.
    /// Models what is actually mapped and the memory points.
    /// How page table invariants
    pub mem_view: MemView,
    /// Whether we allow shared reading.
    pub shared_reader: bool,
}

impl<'a> Inv for VmSpaceOwner<'a> {
    /// Defines the invariant for `VmSpaceOwner`.
    ///
    /// This specification ensures the consistency of the VM space, particularly
    /// regarding memory access permissions and overlapping ranges.
    ///
    /// # Invariants
    /// 1. **Recursion**: The underlying `page_table_owner` must satisfy its own invariant.
    /// 2. **Finiteness**: The sets of readers and writers must be finite.
    /// 3. **Active State Consistency**: If the VM space is marked as `active`:
    ///    - **ID Separation**: A handle ID cannot be both a reader and a writer simultaneously.
    ///    - **Element Validity**: All stored `VmIoOwner` instances must be valid and
    ///                             their stored ID must match their map key.
    ///    - **Memory Isolation (Read-Write)**: No Reader memory range may overlap with any Writer memory range.
    ///    - **Memory Isolation (Write-Write)**: No Writer memory range may overlap with any other Writer memory range.
    ///    - **Conditional Read Isolation**: If `shared_reader` is set, Readers must be mutually disjoint (cannot overlap).
    open spec fn inv(self) -> bool {
        &&& self.page_table_owner.inv()
        &&& self.readers.dom().finite()
        &&& self.writers.dom().finite()
        &&& self.active ==> {
            // Readers and writers are valid.
            &&& forall|i: nat, reader: VmIoOwner<'a>|
                #![trigger self.readers.kv_pairs().contains((i, reader))]
                self.readers.kv_pairs().contains((i, reader)) ==> reader.inv() && reader.id@ == i
            &&& forall|i: nat, writer: VmIoOwner<'a>|
                #![trigger self.writers.kv_pairs().contains((i, writer))]
                self.writers.kv_pairs().contains((i, writer))
                    ==> writer.inv() && writer.id@ == i

            // --- Memory Range Overlap Checks ---
            // Readers do not overlap with other readers, and writers do not overlap with other writers.
            &&& forall|i, j: nat, reader: VmIoOwner<'a>, writer: VmIoOwner<'a>|
                #![trigger self.readers.kv_pairs().contains((i, reader)), self.writers.kv_pairs().contains((j, writer))]
                self.readers.kv_pairs().contains((i, reader)) && self.writers.kv_pairs().contains(
                    (j, writer),
                ) && i != j ==> !reader.overlaps(writer)
            &&& !self.shared_reader ==>
            forall|i, j: nat, reader1: VmIoOwner<'a>, reader2: VmIoOwner<'a>|
                #![trigger self.readers.kv_pairs().contains((i, reader1)), self.readers.kv_pairs().contains((j, reader2))]
                self.readers.kv_pairs().contains((i, reader1)) && self.readers.kv_pairs().contains(
                    (j, reader2),
                ) && i != j ==> !reader1.overlaps(reader2)
            &&& forall|i, j: nat, writer1: VmIoOwner<'a>, writer2: VmIoOwner<'a>|
                #![trigger self.writers.kv_pairs().contains((i, writer1)), self.writers.kv_pairs().contains((j, writer2))]
                self.writers.kv_pairs().contains((i, writer1)) && self.writers.kv_pairs().contains(
                    (j, writer2),
                ) && i != j ==> !writer1.overlaps(writer2)
        }
    }
}

impl VmSpaceOwner<'_> {
    /// The basic invariant between a VM space and its owner.
    pub open spec fn inv_with(&self, vm_space: VmSpace<'_>) -> bool {
        &&& self.shared_reader == vm_space.shared_reader
        /* self.page_table_owner.is_for(vm_space.page_table) */
    }

    /// Checks if this given reader is valid under this VM space owner.
    #[verifier::inline]
    pub open spec fn valid_reader(&self, reader: VmReader<'_>, owner: VmIoOwner<'_>) -> bool
        recommends
            self.inv(),
            reader.inv(),
            owner.inv(),
    {
        &&& owner.inv_with_reader(reader)
        &&& self.readers.contains_key(owner.id@)
    }

    /// Checks if this given writer is valid under this VM space owner.
    pub open spec fn valid_writer(&self, writer: VmWriter<'_>, owner: VmIoOwner<'_>) -> bool
        recommends
            self.inv(),
            writer.inv(),
            owner.inv(),
    {
        &&& owner.inv_with_writer(writer)
        &&& self.writers.contains_key(owner.id@)
    }

    /// Checks if we can create a new reader under this VM space owner.
    ///
    /// This requires no active writers overlapping with the new reader.
    pub open spec fn can_create_reader(&self, vaddr: Vaddr, len: usize) -> bool
        recommends
            self.inv(),
    {
        let reader = VmIoOwner {
            id: arbitrary(),
            range: Ghost(vaddr..(vaddr + len) as usize),
            phantom: PhantomData,
            is_fallible: false,
            is_kernel: false,
        };

        &&& forall|i: nat, writer: VmIoOwner<'_>|
            #![trigger self.writers.kv_pairs().contains((i, writer))]
            self.writers.kv_pairs().contains((i, writer))
                ==> !writer.overlaps(reader)
    }

    /// Checks if we can create a new writer under this VM space owner.
    ///
    /// Similar to [`can_create_reader`], but checks both active readers and writers.
    pub open spec fn can_create_writer(&self, vaddr: Vaddr, len: usize) -> bool
        recommends
            self.inv(),
    {
        let writer = VmIoOwner {
            id: arbitrary(),
            range: Ghost(vaddr..(vaddr + len) as usize),
            phantom: PhantomData,
            is_fallible: false,
            is_kernel: false,
        };

        &&& forall|i: nat, reader: VmIoOwner<'_>|
            #![trigger self.readers.kv_pairs().contains((i, reader))]
            self.readers.kv_pairs().contains((i, reader))
                ==> !reader.overlaps(writer)
        &&& forall|i: nat, writer2: VmIoOwner<'_>|
            #![trigger self.writers.kv_pairs().contains((i, writer2))]
            self.writers.kv_pairs().contains((i, writer2))
                ==> !writer2.overlaps(writer)
    }

    /// Generates a new unique ID for VM IO owners.
    /// 
    /// This assumes that we always generate a fresh ID that is not used by any existing
    /// readers or writers. This should be safe as the ID space is unbounded and only used
    /// to reason about different VM IO owners in verification.
    #[verifier::external_body]
    #[verus_spec(r =>
        requires
            self.inv(),
        ensures
            forall |i: nat|
                #![auto]
                !self.readers.contains_key(i) && !self.writers.contains_key(i),
    )]
    pub proof fn new_vm_io_id(&self) -> nat {
        unimplemented!()
    }
}

}  // verus!

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

    #[verifier::external_body]
    fn item_into_raw(item: Self::Item) -> (Paddr, PagingLevel, PageProperty) {
        unimplemented!()/*
        let (frame, prop) = item;
        let level = frame.map_level();
        let paddr = frame.into_raw();
        (paddr, level, prop)
        */

    }

    uninterp spec fn item_from_raw_spec(
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
    ) -> Self::Item;

    #[verifier::external_body]
    fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item {
        unimplemented!()/*
        debug_assert_eq!(level, 1);
        // SAFETY: The caller ensures safety.
        let frame = unsafe { Frame::<dyn AnyUFrameMeta>::from_raw(paddr) };
        (frame, prop)
        */

    }
}

type Result<A> = core::result::Result<A, Error>;

#[verus_verify]
impl VmSpace<'_> {
    pub uninterp spec fn new_spec() -> Self;

    pub open spec fn reader_requires(
        &self,
        vm_owner: VmSpaceOwner<'_>,
        vaddr: Vaddr,
        len: usize,
    ) -> bool {
        &&& self.inv()
        &&& vm_owner.inv_with(*self)
        &&& vm_owner.inv()
        &&& vm_owner.active
        &&& vm_owner.can_create_reader(vaddr, len)
        &&& vaddr != 0 && len > 0 && vaddr + len <= MAX_USERSPACE_VADDR_SPEC()
        &&& current_page_table_paddr_spec() == self.pt.root_paddr_spec()
    }

    pub open spec fn writer_requires(
        &self,
        vm_owner: VmSpaceOwner<'_>,
        vaddr: Vaddr,
        len: usize,
    ) -> bool {
        &&& self.inv()
        &&& vm_owner.inv_with(*self)
        &&& vm_owner.inv()
        &&& vm_owner.active
        &&& vm_owner.can_create_writer(vaddr, len)
        &&& vaddr != 0 && len > 0 && vaddr + len <= MAX_USERSPACE_VADDR_SPEC()
        &&& current_page_table_paddr_spec() == self.pt.root_paddr_spec()
    }

    pub open spec fn reader_ensures(
        &self,
        vm_owner_old: VmSpaceOwner<'_>,
        vm_owner_new: VmSpaceOwner<'_>,
        vaddr: Vaddr,
        len: usize,
        r: Result<VmReader<'_>>,
    ) -> bool {
        &&& vm_owner_new.inv()
        &&& r matches Ok(reader) && vm_owner_new.readers == vm_owner_old.readers.insert(
            reader.id@,
            VmIoOwner {
                id: reader.id,
                range: Ghost(vaddr..(vaddr + len) as usize),
                phantom: PhantomData,
                is_fallible: false,
                is_kernel: false,
            },
        )
    }

    pub open spec fn writer_ensures(
        &self,
        vm_owner_old: VmSpaceOwner<'_>,
        vm_owner_new: VmSpaceOwner<'_>,
        vaddr: Vaddr,
        len: usize,
        r: Result<VmWriter<'_>>,
    ) -> bool {
        &&& vm_owner_new.inv()
        &&& r matches Ok(writer) && vm_owner_new.writers == vm_owner_old.writers.insert(
            writer.id@,
            VmIoOwner {
                id: writer.id,
                range: Ghost(vaddr..(vaddr + len) as usize),
                phantom: PhantomData,
                is_fallible: false,
                is_kernel: false,
            },
        )
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
    pub fn cursor<'a, G: InAtomicMode>(&'a self, guard: &'a G, va: &Range<Vaddr>) -> Result<Cursor<'a, G>> {
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
    pub fn cursor_mut<'a, G: InAtomicMode>(&'a self, guard: &'a G, va: &Range<Vaddr>) -> Result<CursorMut<'a, G>> {
        Ok(
            self.pt.cursor_mut(guard, va).map(
                |pt_cursor|
                    CursorMut {
                        pt_cursor:
                            pt_cursor.0,
                        //            flusher: TlbFlusher::new(&self.cpus, disable_preempt()),
                    },
            )?,
        )
    }

    /// Creates a reader to read data from the user space of the current task.
    ///
    /// Returns `Err` if this `VmSpace` is not belonged to the user space of the current task
    /// or the `vaddr` and `len` do not represent a user space memory range.
    ///
    /// Users must ensure that no other page table is activated in the current task during the
    /// lifetime of the created `VmReader`. This guarantees that the `VmReader` can operate correctly.
    ///
    /// Note that this function will not return the reader's owner explicitly and the caller should
    /// always consult the [`VmSpaceOwner`] to ensure the validity of the created reader and "borrow"
    /// the reader from the owner.
    #[inline]
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmSpaceOwner<'_>>,
        requires
            self.reader_requires(*old(owner), vaddr, len),
        ensures
            self.reader_ensures(*old(owner), *owner, vaddr, len, r),
    )]
    pub fn reader(&self, vaddr: Vaddr, len: usize) -> Result<VmReader<'_>> {
        let vptr = VirtPtr::from_vaddr(vaddr, len);
        let ghost id = owner.new_vm_io_id();

        proof_decl! {
            let tracked mut vm_reader_owner;
        }

        // SAFETY: The memory range is in user space, as checked above.
        let reader = unsafe {
            proof_with!(Ghost(id) => Tracked(mut vm_reader_owner));
            VmReader::from_user_space(vptr)
        };

        proof {
            owner.readers.tracked_insert(
                vm_reader_owner.id@,
                vm_reader_owner,
            );
        }


        Ok(reader)
    }
    /// Creates a writer to write data into the user space.
    ///
    /// Returns `Err` if this `VmSpace` is not belonged to the user space of the current task
    /// or the `vaddr` and `len` do not represent a user space memory range.
    ///
    /// Users must ensure that no other page table is activated in the current task during the
    /// lifetime of the created `VmWriter`. This guarantees that the `VmWriter` can operate correctly.
    #[inline]
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmSpaceOwner<'_>>,
        requires
            self.writer_requires(*old(owner), vaddr, len),
        ensures
            self.writer_ensures(*old(owner), *owner, vaddr, len, r),
    )]
    pub fn writer(&self, vaddr: Vaddr, len: usize) -> Result<VmWriter<'_>> {
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
            proof_with!(Ghost(id) => Tracked(mut vm_writer_owner));
            VmWriter::from_user_space(vptr)
        };

        proof {
            owner.writers.tracked_insert(
                vm_writer_owner.id@,
                vm_writer_owner,
            );
        }

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
    pub open spec fn query_requries(
        cursor: Self,
        owner: CursorOwner<'rcu, UserPtConfig>,
        guard_perm: vstd::simple_pptr::PointsTo<PageTableGuard<'rcu, UserPtConfig>>,
        regions: MetaRegionOwners,
    ) -> bool {
        &&& cursor.0.wf(owner)
        &&& owner.inv()
        &&& regions.inv()
    }

    pub open spec fn query_ensures(
        old_cursor: Self,
        new_cursor: Self,
        owner: CursorOwner<'rcu, UserPtConfig>,
        guard_perm: vstd::simple_pptr::PointsTo<PageTableGuard<'rcu, UserPtConfig>>,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        r: Result<(Range<Vaddr>, Option<MappedItem>)>,
    ) -> bool {
        &&& new_regions.inv()
        &&& new_cursor.0.wf(owner)
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the mapped item.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn query(&mut self) -> Result<(Range<Vaddr>, Option<MappedItem>)>
        requires
            old(owner).inv(),
            old(self).0.wf(*old(owner)),
            old(self).0.inv(),
            old(regions).inv(),
    {
        Ok(
            #[verus_spec(with Tracked(owner), Tracked(regions))]
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
    /// # Panics
    ///
    /// Panics if the length is longer than the remaining range of the cursor.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, UserPtConfig>>,
            Tracked(guard_perm): Tracked<&vstd::simple_pptr::PointsTo<PageTableGuard<'rcu, UserPtConfig>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(owner).inv(),
            old(self).0.wf(*old(owner)),
            old(regions).inv(),
            old(self).0.level < old(self).0.guard_level,
            old(self).0.inv(),
        ensures
            owner.inv(),
            self.0.wf(*owner),
            regions.inv(),
    {
        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions))]
        self.0.find_next(len)
    }

    /// Jump to the virtual address.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, UserPtConfig>>,
    )]
    pub fn jump(&mut self, va: Vaddr) -> Result<()>
        requires
            old(owner).inv(),
            old(self).0.wf(*old(owner)),
            old(self).0.level < old(self).0.guard_level,
            old(self).0.inv(),
    {
        (#[verus_spec(with Tracked(owner))]
        self.0.jump(va))?;
        Ok(())
    }

    /// Get the virtual address of the current slot.
    pub fn virt_addr(&self) -> Vaddr {
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
    //    flusher: TlbFlusher<'a, DisabledPreemptGuard>,
}

impl<'a, A: InAtomicMode> CursorMut<'a, A> {
    pub open spec fn query_requries(
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn query(&mut self) -> Result<(Range<Vaddr>, Option<MappedItem>)>
        requires
            old(owner).inv(),
            old(self).pt_cursor.inner.wf(*old(owner)),
            old(regions).inv(),
            old(self).pt_cursor.inner.inv(),
    {
        Ok(
            #[verus_spec(with Tracked(owner), Tracked(regions))]
            self.pt_cursor.query()?,
        )
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// This is the same as [`Cursor::find_next`].
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(guard_perm): Tracked<&vstd::simple_pptr::PointsTo<PageTableGuard<'a, UserPtConfig>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(owner).inv(),
            old(self).pt_cursor.inner.wf(*old(owner)),
            old(regions).inv(),
            old(self).pt_cursor.inner.level < old(self).pt_cursor.inner.guard_level,
            old(self).pt_cursor.inner.inv(),
        ensures
            owner.inv(),
            self.pt_cursor.inner.wf(*owner),
            regions.inv(),
    {
        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions))]
        self.pt_cursor.find_next(len)
    }

    /// Jump to the virtual address.
    ///
    /// This is the same as [`Cursor::jump`].
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>
    )]
    pub fn jump(&mut self, va: Vaddr) -> Result<()>
        requires
            old(owner).inv(),
            old(self).pt_cursor.inner.wf(*old(owner)),
            old(self).pt_cursor.inner.level < old(self).pt_cursor.inner.guard_level,
            old(self).pt_cursor.inner.inv(),
    {
        (#[verus_spec(with Tracked(owner))]
        self.pt_cursor.jump(va))?;
        Ok(())
    }

    /// Get the virtual address of the current slot.
    pub fn virt_addr(&self) -> Vaddr
        returns
            self.pt_cursor.inner.va,
    {
        self.pt_cursor.virt_addr()
    }

    /* TODO: come back after TLB
    /// Get the dedicated TLB flusher for this cursor.
    pub fn flusher(&mut self) -> &mut TlbFlusher<'a, DisabledPreemptGuard> {
        &mut self.flusher
    }
    */
    /// Map a frame into the current slot.
    ///
    /// This method will bring the cursor to the next slot after the modification.
    #[verus_spec(
        with Tracked(cursor_owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
            Tracked(entry_owner): Tracked<EntryOwner<'a, UserPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn map(&mut self, frame: UFrame, prop: PageProperty)
        requires
            old(cursor_owner).inv(),
            old(self).pt_cursor.inner.wf(*old(cursor_owner)),
            old(regions).inv(),
            entry_owner.inv(),
            old(self).pt_cursor.inner.inv(),
            old(self).pt_cursor.inner.level < old(self).pt_cursor.inner.guard_level,
    {
        let start_va = self.virt_addr();
        let item = MappedItem { frame: frame, prop: prop };

        let tracked lv = (5 - cursor_owner.level) as nat;

        let tracked mut new_owner = OwnerSubtree::new_val_tracked(entry_owner, lv);

        // SAFETY: It is safe to map untyped memory into the userspace.
        let Err(frag) = (
        #[verus_spec(with Tracked(cursor_owner), Tracked(new_owner), Tracked(regions))]
        self.pt_cursor.map(item)) else {
            return ;  // No mapping exists at the current address.
        };

        /*        match frag {
            PageTableFrag::Mapped { va, item } => {
                debug_assert_eq!(va, start_va);
                let old_frame = item.frame;
                self.flusher
                    .issue_tlb_flush_with(TlbFlushOp::Address(start_va), old_frame.into());
                self.flusher.dispatch_tlb_flush();
            }
            PageTableFrag::StrayPageTable { .. } => {
                panic!("`UFrame` is base page sized but re-mapping out a child PT");
            }
        }
*/
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
        requires
            len % PAGE_SIZE() == 0,
            old(self).pt_cursor.inner.va % PAGE_SIZE() == 0,
            old(self).pt_cursor.inner.va + len <= KERNEL_VADDR_RANGE().end as int,
    )]
    #[verifier::external_body]
    pub fn unmap(&mut self, len: usize) -> usize {
        let end_va = self.virt_addr() + len;
        let mut num_unmapped: usize = 0;

        proof {
            assert((self.pt_cursor.inner.va + len) % PAGE_SIZE() as int == 0) by (compute);
        }

        #[verus_spec(
            invariant_except_break
                self.pt_cursor.inner.va % PAGE_SIZE() == 0,
                end_va % PAGE_SIZE() == 0,
        )]
        loop {
            // SAFETY: It is safe to un-map memory in the userspace.
            let Some(frag) = (unsafe { self.pt_cursor.take_next(end_va - self.virt_addr()) }) else {
                break ;  // No more mappings in the range.
            };

            match frag {
                PageTableFrag::Mapped { va, item, .. } => {
                    let frame = item.frame;
                    num_unmapped += 1;
                    //                    self.flusher
                    //                        .issue_tlb_flush_with(TlbFlushOp::Address(va), frame.into());
                },
                PageTableFrag::StrayPageTable { pt, va, len, num_frames } => {
                    num_unmapped += num_frames;
                    //                    self.flusher
                    //                        .issue_tlb_flush_with(TlbFlushOp::Range(va..va + len), pt);
                },
            }
        }

        //        self.flusher.dispatch_tlb_flush();

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
            Tracked(guard_perm): Tracked<&mut vstd::simple_pptr::PointsTo<PageTableGuard<'a, UserPtConfig>>>,
            Tracked(regions): Tracked<&MetaRegionOwners>
        requires
            regions.inv(),
            !old(owner).cur_entry_owner().is_absent(),
    )]
    pub fn protect_next(
        &mut self,
        len: usize,
        op: impl FnOnce(PageProperty) -> PageProperty,
    ) -> Option<Range<Vaddr>> {
        // SAFETY: It is safe to protect memory in the userspace.
        unsafe {
            #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions))]
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
} // verus!
