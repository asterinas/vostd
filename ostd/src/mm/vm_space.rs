// SPDX-License-Identifier: MPL-2.0
//! Virtual memory space management.
//!
//! The [`VmSpace`] struct is provided to manage the virtual memory space of a
//! user. Cursors are used to traverse and modify over the virtual memory space
//! concurrently. The VM space cursor [`self::Cursor`] is just a wrapper over
//! the page table cursor, providing efficient, powerful concurrent accesses
//! to the page table.
use vstd::prelude::*;

use core::{ops::Range, sync::atomic::Ordering};

use crate::aster_common::frame::{MetaRegionOwners, MetaSlotOwner};
use crate::mm::frame::untyped::UFrame;
use crate::aster_common::page_table::*;
use crate::aster_common::*;
use crate::mm::page_table::{CursorOwner, PageTableFrag};

use vstd_extra::ghost_tree::*;

use crate::{
    //    cpu::{AtomicCpuSet, CpuSet, PinCurrentCpu},
    //    cpu_local_cell,
    mm::{
        //        io::Fallible,
        // kspace::KERNEL_PAGE_TABLE,
        // page_table,
        //        tlb::{TlbFlushOp, TlbFlusher},
        page_prop::PageProperty,
        PagingLevel,
        io::{VmReader, VmWriter},
        MAX_USERSPACE_VADDR,
    },
    prelude::*,
    //    task::{atomic_mode::AsAtomicModeGuard, disable_preempt, DisabledPreemptGuard},
};

use alloc::sync::Arc;

verus! {

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
pub struct VmSpace {
    pub pt: PageTable<UserPtConfig>,
    //    cpus: AtomicCpuSet,
}

type Result<A> = core::result::Result<A, Error>;

#[verus_verify]
impl VmSpace {
    // /// Creates a new VM address space.
    // #[verus_spec(r =>
    //     ensures
    //         true,
    // )]
    // pub fn new() -> Self {
    //     // Self { pt: KERNEL_PAGE_TABLE.get().unwrap().create_user_page_table() }
    // }
    /// Gets an immutable cursor in the virtual address range.
    ///
    /// The cursor behaves like a lock guard, exclusively owning a sub-tree of
    /// the page table, preventing others from creating a cursor in it. So be
    /// sure to drop the cursor as soon as possible.
    ///
    /// The creation of the cursor may block if another cursor having an
    /// overlapping range is alive.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn cursor<'a, G: InAtomicMode>(&'a self, guard: &'a G, va: &Range<Vaddr>) -> Result<
        Cursor<'a, G>,
    > {
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
    #[rustc_allow_incoherent_impl]
    pub fn cursor_mut<'a, G: InAtomicMode>(&'a self, guard: &'a G, va: &Range<Vaddr>) -> Result<
        CursorMut<'a, G>,
    > {
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
    }/* TODO: We don't currently do per-CPU stuff
    /// Activates the page table on the current CPU.
    pub fn activate(self: &Arc<Self>) {
        let preempt_guard = disable_preempt();
        let cpu = preempt_guard.current_cpu();

        let last_ptr = ACTIVATED_VM_SPACE.load();

        if last_ptr == Arc::as_ptr(self) {
            return;
        }

        // Record ourselves in the CPU set and the activated VM space pointer.
        // `Acquire` to ensure the modification to the PT is visible by this CPU.
        self.cpus.add(cpu, Ordering::Acquire);

        let self_ptr = Arc::into_raw(Arc::clone(self)) as *mut VmSpace;
        ACTIVATED_VM_SPACE.store(self_ptr);

        if !last_ptr.is_null() {
            // SAFETY: The pointer is cast from an `Arc` when it's activated
            // the last time, so it can be restored and only restored once.
            let last = unsafe { Arc::from_raw(last_ptr) };
            last.cpus.remove(cpu, Ordering::Relaxed);
        }

        self.pt.activate();
    }
    */
    /* TODO: come back after IO
    /// Creates a reader to read data from the user space of the current task.
    ///
    /// Returns `Err` if this `VmSpace` is not belonged to the user space of the current task
    /// or the `vaddr` and `len` do not represent a user space memory range.
    ///
    /// Users must ensure that no other page table is activated in the current task during the
    /// lifetime of the created `VmReader`. This guarantees that the `VmReader` can operate correctly.
    #[rustc_allow_incoherent_impl]
    pub fn reader(&self, vaddr: Vaddr, len: usize) -> Result<VmReader<'_>> {
        if current_page_table_paddr() != self.pt.root_paddr() {
            return Err(Error::AccessDenied);
        }

        if vaddr.checked_add(len).unwrap_or(usize::MAX) > MAX_USERSPACE_VADDR {
            return Err(Error::AccessDenied);
        }

        // SAFETY: The memory range is in user space, as checked above.
        Ok(unsafe { VmReader::from_user_space(vaddr as *const u8, len) })
    }

    /// Creates a writer to write data into the user space.
    ///
    /// Returns `Err` if this `VmSpace` is not belonged to the user space of the current task
    /// or the `vaddr` and `len` do not represent a user space memory range.
    ///
    /// Users must ensure that no other page table is activated in the current task during the
    /// lifetime of the created `VmWriter`. This guarantees that the `VmWriter` can operate correctly.
    #[rustc_allow_incoherent_impl]
    pub fn writer(&self, vaddr: Vaddr, len: usize) -> Result<VmWriter<'_>> {
        if current_page_table_paddr() != self.pt.root_paddr() {
            return Err(Error::AccessDenied);
        }

        if vaddr.checked_add(len).unwrap_or(usize::MAX) > MAX_USERSPACE_VADDR {
            return Err(Error::AccessDenied);
        }

        // `VmWriter` is neither `Sync` nor `Send`, so it will not live longer than the current
        // task. This ensures that the correct page table is activated during the usage period of
        // the `VmWriter`.
        //
        // SAFETY: The memory range is in user space, as checked above.
        Ok(unsafe { VmWriter::from_user_space(vaddr as *mut u8, len) })
    }
    */

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
pub struct Cursor<'a, A: InAtomicMode>(
    pub crate::mm::page_table::Cursor<'a, UserPtConfig, A>,
);

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
    {
        let start_va = self.virt_addr();
        let item = MappedItem { frame: frame, prop: prop };

        let tracked lv = (5 - cursor_owner.level) as nat;

        let tracked mut new_owner = OwnerSubtree::new_val_tracked(entry_owner, lv);

        // SAFETY: It is safe to map untyped memory into the userspace.
        let Err(frag) = (#[verus_spec(with Tracked(cursor_owner), Tracked(new_owner), Tracked(regions))] self.pt_cursor.map(item)) else {
            return; // No mapping exists at the current address.
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
    #[rustc_allow_incoherent_impl]
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
            old(owner).cur_entry_owner() is Some,
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
