// SPDX-License-Identifier: MPL-2.0
//! The page table cursor for mapping and querying over the page table.
//!
//! # The page table lock protocol
//!
//! We provide a fine-grained ranged mutual-exclusive lock protocol to allow
//! concurrent accesses to non-overlapping virtual ranges in the page table.
//!
//! [`CursorMut::new`] will lock a range in the virtual space and all the
//! operations on the range with the cursor will be atomic as a transaction.
//!
//! The guarantee of the lock protocol is that, if two cursors' ranges overlap,
//! all of one's operation must be finished before any of the other's
//! operation. The order depends on the scheduling of the threads. If a cursor
//! is ordered after another cursor, it will see all the changes made by the
//! previous cursor.
//!
//! The implementation of the lock protocol resembles two-phase locking (2PL).
//! [`CursorMut::new`] accepts an address range, which indicates the page table
//! entries that may be visited by this cursor. Then, [`CursorMut::new`] finds
//! an intermediate page table (not necessarily the last-level or the top-
//! level) which represents an address range that fully contains the whole
//! specified address range. Then it locks all the nodes in the sub-tree rooted
//! at the intermediate page table node, with a pre-order DFS order. The cursor
//! will only be able to access the page table entries in the locked range.
//! Upon destruction, the cursor will release the locks in the reverse order of
//! acquisition.
mod locking;

use vstd::prelude::*;

use vstd::simple_pptr::*;

use vstd_extra::ownership::*;

use aster_common::prelude::frame::{Frame, MetaSlotOwner};
use aster_common::prelude::page_table::*;
use aster_common::prelude::*;

use core::{fmt::Debug, marker::PhantomData, mem::ManuallyDrop, ops::Range};

//use align_ext::AlignExt;

use crate::{
    mm::page_table::is_valid_range,
    //    task::atomic_mode::InAtomicMode,
};

use super::{
    pte_index, Child, ChildRef, Entry, PageTable, PageTableConfig, PageTableError, PageTableGuard,
    PagingConstsTrait, PagingLevel,
};

verus! {

/// A fragment of a page table that can be taken out of the page table.
#[must_use]
pub enum PageTableFrag<C: PageTableConfig> {
    /// A mapped page table item.
    Mapped { va: Vaddr, item: C::Item },
    /// A sub-tree of a page table that is taken out of the page table.
    ///
    /// The caller is responsible for dropping it after TLB coherence.
    StrayPageTable {
        pt: Frame<PageTablePageMeta<C>>,  // TODO: this was a dyn AnyFrameMeta, but we can't support that...
        va: Vaddr,
        len: usize,
        num_frames: usize,
    },
}

impl<C: PageTableConfig> PageTableFrag<C> {
    #[cfg(ktest)]
    pub fn va_range(&self) -> Range<Vaddr> {
        match self {
            PageTableFrag::Mapped { va, item } => {
                let (pa, level, prop) = C::item_into_raw(item.clone());
                drop(unsafe { C::item_from_raw(pa, level, prop) });
                *va..*va + page_size(level)
            },
            PageTableFrag::StrayPageTable { va, len, .. } => *va..*va + *len,
        }
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> Cursor<'rcu, C, A> {
    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(pt_own): Tracked<&mut PageTableOwner<C>>
    )]
    #[verusfmt::skip]
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>)
        -> Result<Self, PageTableError> {
        if !is_valid_range::<C>(va) || va.start >= va.end {
            return Err(PageTableError::InvalidVaddrRange(va.start, va.end));
        }
        if va.start % C::BASE_PAGE_SIZE() != 0 || va.end % C::BASE_PAGE_SIZE() != 0 {
            return Err(PageTableError::UnalignedVaddr);
        }
        //        const { assert!(C::NR_LEVELS() as usize <= MAX_NR_LEVELS()) };

        Ok(
            #[verus_spec(with Tracked(pt_own))]
            locking::lock_range(pt, guard, va)
        )
    }

    /// Gets the current virtual address.
    #[rustc_allow_incoherent_impl]
    pub fn virt_addr(&self) -> Vaddr {
        self.va
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn query(&mut self) -> Result<PagesState<C>, PageTableError> {
        if self.va >= self.barrier_va.end {
            return Err(PageTableError::InvalidVaddr(self.va));
        }
        let rcu_guard = self.rcu_guard;

        loop
            decreases self.level,
        {
            let cur_va = self.va;
            let level = self.level;

            let cur_child = self.cur_entry().to_ref();
            let item = match cur_child {
                ChildRef::PageTable(pt) => {
                    // SAFETY: The `pt` must be locked and no other guards exist.
                    let guard = pt.make_guard_unchecked(rcu_guard);
                    assert(1 < self.level <= 4) by { admit() };
                    self.push_level(guard);
                    continue ;
                },
                ChildRef::None => None,
                ChildRef::Frame(pa, ch_level, prop) => {
                    //                    debug_assert_eq!(ch_level, level);
                    // SAFETY:
                    // This is part of (if `split_huge` happens) a page table item mapped
                    // with a previous call to `C::item_into_raw`, where:
                    //  - The physical address and the paging level match it;
                    //  - The item part is still mapped so we don't take its ownership.
                    //
                    // For page table configs that require the `AVAIL1` flag to be kept
                    // (currently, only kernel page tables), the callers of the unsafe
                    // `protect_next` method uphold this invariant.
                    let item =   /*ManuallyDrop::new(unsafe {*/
                    C::item_from_raw(pa, level, prop)  /*})*/
                    ;
                    // TODO: Provide a `PageTableItemRef` to reduce copies.
                    Some(item.clone())
                },
            };

            assert(cur_va + page_size(level) < usize::MAX) by { admit() };
            return Ok((cur_va..cur_va + page_size(level), item));
        }
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// If there is mapped virtual address following the current address within
    /// next `len` bytes, it will return that mapped address. In this case, the
    /// cursor will stop at the mapped address.
    ///
    /// Otherwise, it will return `None`. And the cursor may stop at any
    /// address after `len` bytes.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn find_next(&mut self, len: usize) -> Option<Vaddr> {
        self.find_next_impl(len, false, false)
    }

    /// Moves the cursor forward to the next fragment in the range.
    ///
    /// See [`Self::find_next`] for more details. Other than the semantics
    /// provided by [`Self::find_next`], this method also supports finding non-
    /// leaf entries and splitting huge pages if necessary.
    ///
    /// `find_unmap_subtree` specifies whether the cursor should stop at the
    /// highest possible level for unmapping. If `false`, the cursor will only
    /// stop at leaf entries.
    ///
    /// `split_huge` specifies whether the cursor should split huge pages when
    /// it finds a huge page that is mapped over the required range (`len`).
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(entry_own): Tracked<EntryOwner<C>>
    )]
    #[verifier::external_body]
    fn find_next_impl(&mut self, len: usize, find_unmap_subtree: bool, split_huge: bool) -> Option<
        Vaddr,
    > {
        //        assert_eq!(len % C::BASE_PAGE_SIZE(), 0);
        let end = self.va + len;
        //        assert!(end <= self.barrier_va.end);
        //        debug_assert_eq!(end % C::BASE_PAGE_SIZE(), 0);

        let rcu_guard = self.rcu_guard;

        while self.va < end
            decreases end - self.va,
        {
            let cur_va = self.va;
            let cur_va_range = self.cur_va_range();
            let cur_entry_fits_range = cur_va == cur_va_range.start && cur_va_range.end <= end;

            let mut cur_entry = self.cur_entry();
            match cur_entry.to_ref() {
                ChildRef::PageTable(pt) => {
                    if find_unmap_subtree && cur_entry_fits_range && (C::TOP_LEVEL_CAN_UNMAP()
                        || self.level != C::NR_LEVELS()) {
                        return Some(cur_va);
                    }
                    // SAFETY: The `pt` must be locked and no other guards exist.

                    let pt_guard = pt.make_guard_unchecked(rcu_guard);
                    let pt_guard_val = pt_guard.borrow(Tracked(entry_own.guard_perm.borrow()));

                    // If there's no mapped PTEs in the next level, we can
                    // skip to save time.
                    if pt_guard_val.nr_children() != 0 {
                        self.push_level(pt_guard);
                    } else {
                        let _ = ManuallyDrop::new(pt_guard);
                        self.move_forward();
                    }
                    continue ;
                },
                ChildRef::None => {
                    self.move_forward();
                    continue ;
                },
                ChildRef::Frame(_, _, _) => {
                    if cur_entry_fits_range || !split_huge {
                        return Some(cur_va);
                    }
                    let split_child = cur_entry.split_if_mapped_huge(rcu_guard).expect(
                        "The entry must be a huge page",
                    );
                    self.push_level(split_child);
                    continue ;
                },
            }
        }

        None
    }

    /// Jumps to the given virtual address.
    /// If the target address is out of the range, this method will return `Err`.
    ///
    /// # Panics
    ///
    /// This method panics if the address has bad alignment.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError> {
        //        assert!(va % C::BASE_PAGE_SIZE() == 0);
        if !self.barrier_va.contains(&va) {
            return Err(PageTableError::InvalidVaddr(va));
        }
        loop {
            let cur_node_start = self.va & !(page_size(self.level + 1) - 1);
            let cur_node_end = cur_node_start + page_size(self.level + 1);
            // If the address is within the current node, we can jump directly.
            if cur_node_start <= va && va < cur_node_end {
                self.va = va;
                return Ok(());
            }
            // There is a corner case that the cursor is depleted, sitting at the start of the
            // next node but the next node is not locked because the parent is not locked.

            if self.va >= self.barrier_va.end && self.level == self.guard_level {
                self.va = va;
                return Ok(());
            }
            //            debug_assert!(self.level < self.guard_level);

            self.pop_level();
        }
    }

    /// Traverses forward to the end of [`Self::cur_va_range`].
    //
    /// If reached the end of the current page table node, it (recursively)
    /// moves itself up to the next page of the parent page.
    #[rustc_allow_incoherent_impl]
    fn move_forward(&mut self) {
        let next_va = self.cur_va_range().end;
        while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0
            decreases self.guard_level - self.level,
        {
            assert(1 <= self.level < 4) by { admit() };
            self.pop_level();
        }
        self.va = next_va;
    }

    /// Goes up a level.
    #[rustc_allow_incoherent_impl]
    fn pop_level(&mut self)
        requires
            1 <= old(self).level < 4,
        ensures
            self.level == old(self).level + 1,
            self.guard_level == old(self).guard_level,
    {
        let opt_taken = self.path.get(self.level as usize - 1);

        /*        let Some(taken) = self.path[self.level as usize - 1].take() else {
            panic!("Popping a level without a lock");
        };
        let _ = ManuallyDrop::new(taken);
*/
        self.level = self.level + 1;
    }

    /// Goes down a level to a child page table.
    #[rustc_allow_incoherent_impl]
    fn push_level(&mut self, child_pt: PPtr<PageTableGuard<'rcu, C>>)
        requires
            1 < old(self).level
                <= 4,
    //            old(self).path[old(self).level as int - 1] is Some,

        ensures
            self.level == old(self).level - 1,
    {
        self.level = self.level - 1;
        //        debug_assert_eq!(self.level, child_pt.level());

        //        let old = self.path.get(self.level as usize - 1);
        self.path.set(self.level as usize - 1, Some(child_pt));

        //        debug_assert!(old.is_none());
    }

    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(pt_own): Tracked<&mut PageTableOwner<C>>,
            Tracked(slot_own): Tracked<&MetaSlotOwner>
    )]
    fn cur_entry(&mut self) -> Entry<'rcu, C>
        requires
            1 <= old(self).level <= 4,
            old(self).path[old(self).level as int - 1] is Some,
            old(pt_own).tree.root.value.tree_node.tracked_is_some(),
            old(pt_own).tree.root.value.tree_node.unwrap().inv(),
            old(pt_own).tree.root.value.tree_node.unwrap().relate_slot_owner(slot_own),
            old(pt_own).tree.root.value.tree_node.unwrap().guard_perm@.addr() == old(self).path[old(
                self,
            ).level as usize - 1].unwrap().addr(),
    {
        let node = self.path[self.level as usize - 1].unwrap();
        let tracked entry_own = pt_own.tree.root.value.tree_node.tracked_take();
        #[verus_spec(with Tracked(entry_own), Tracked(slot_own))]
        PageTableGuard::<'rcu, C>::entry(node, pte_index::<C>(self.va, self.level))
    }

    /// Gets the virtual address range that the current entry covers.
    #[rustc_allow_incoherent_impl]
    fn cur_va_range(&self) -> Range<Vaddr> {
        let page_size = page_size(self.level);
        assert(page_size > 0) by { admit() };
        let start = align_down(self.va, page_size);
        assert(start + page_size < usize::MAX) by { admit() };
        start..start + page_size
    }
}

/*
impl<C: PageTableConfig> Drop for Cursor<'_, C> {
    fn drop(&mut self) {
        locking::unlock_range(self);
    }
}
*/

impl<'rcu, C: PageTableConfig, A: InAtomicMode> CursorMut<'rcu, C, A> {
    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to map, query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>) -> Result<
        Self,
        PageTableError,
    > {
        Cursor::new(pt, guard, va).map(|inner| Self { inner })
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// This is the same as [`Cursor::find_next`].
    #[rustc_allow_incoherent_impl]
    pub fn find_next(&mut self, len: usize) -> Option<Vaddr> {
        self.inner.find_next(len)
    }

    /// Jumps to the given virtual address.
    ///
    /// This is the same as [`Cursor::jump`].
    ///
    /// # Panics
    ///
    /// This method panics if the address is out of the range where the cursor is required to operate,
    /// or has bad alignment.
    #[rustc_allow_incoherent_impl]
    pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError> {
        self.inner.jump(va)
    }

    /// Gets the current virtual address.
    #[rustc_allow_incoherent_impl]
    pub fn virt_addr(&self) -> Vaddr {
        self.inner.virt_addr()
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    #[rustc_allow_incoherent_impl]
    pub fn query(&mut self) -> Result<PagesState<C>, PageTableError> {
        self.inner.query()
    }

    /// Maps the item starting from the current address to a physical address range.
    ///
    /// If the current address has already mapped pages, it will do a re-map,
    /// taking out the old physical address and replacing it with the new one.
    /// This function will return [`Err`] with a [`PageTableFrag`], the not
    /// mapped item. The caller should drop it after TLB coherence.
    ///
    /// If there is no mapped pages in the specified virtual address range,
    /// the function will return [`None`].
    ///
    /// # Panics
    ///
    /// This function will panic if
    ///  - the virtual address range to be mapped is out of the locked range;
    ///  - the current virtual address is not aligned to the page size of the
    ///    item to be mapped;
    ///
    /// # Safety
    ///
    /// The caller should ensure that
    ///  - the range being mapped does not affect kernel's memory safety;
    ///  - the physical address to be mapped is valid and safe to use;
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub unsafe fn map(&mut self, item: C::Item) -> Result<(), PageTableFrag<C>> {
        //        assert!(self.0.va < self.0.barrier_va.end);
        let (pa, level, prop) = C::item_into_raw(item);
        //        assert!(level <= C::HIGHEST_TRANSLATION_LEVEL());
        let size = page_size(level);
        //        assert_eq!(self.0.va % size, 0);
        let end = self.inner.va + size;
        //        assert!(end <= self.0.barrier_va.end);

        let rcu_guard = self.inner.rcu_guard;

        // Adjust ourselves to the level of the item.
        while self.inner.level != level
            decreases level - self.inner.level,
        {
            if self.inner.level < level {
                self.inner.pop_level();
                continue ;
            }
            // We are at a higher level, go down.

            let mut cur_entry = self.inner.cur_entry();
            match cur_entry.to_ref() {
                ChildRef::PageTable(pt) => {
                    // SAFETY: The `pt` must be locked and no other guards exist.
                    let pt_guard = unsafe { pt.make_guard_unchecked(rcu_guard) };
                    self.inner.push_level(pt_guard);
                },
                ChildRef::None => {
                    let child_guard = cur_entry.alloc_if_none(rcu_guard).unwrap();
                    self.inner.push_level(child_guard);
                },
                ChildRef::Frame(_, _, _) => {
                    let split_child = cur_entry.split_if_mapped_huge(rcu_guard).unwrap();
                    self.inner.push_level(split_child);
                },
            }
        }

        let frag = self.replace_cur_entry(Child::Frame(pa, level, prop));

        self.inner.move_forward();

        if let Some(frag) = frag {
            Err(frag)
        } else {
            Ok(())
        }
    }

    /// Finds and removes the first page table fragment in the following range.
    ///
    /// The range to be found in is the current virtual address with the
    /// provided length.
    ///
    /// The function stops and yields the fragment if it has actually removed a
    /// fragment, no matter if the following pages are also required to be
    /// unmapped. The returned virtual address is the virtual page that existed
    /// before the removal but having just been unmapped.
    ///
    /// It also makes the cursor moves forward to the next page after the
    /// removed one, when an actual page is removed. If no mapped pages exist
    /// in the following range, the cursor will stop at the end of the range
    /// and return [`None`].
    ///
    /// The caller should handle TLB coherence if necessary, using the returned
    /// virtual address range.
    ///
    /// # Safety
    ///
    /// The caller should ensure that the range being unmapped does not affect
    /// kernel's memory safety.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn take_next(&mut self, len: usize) -> Option<PageTableFrag<C>> {
        self.inner.find_next_impl(len, true, true)?;

        let frag = self.replace_cur_entry(Child::None);

        self.inner.move_forward();

        frag
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
    /// # Safety
    ///
    /// The caller should ensure that:
    ///  - the range being protected with the operation does not affect
    ///    kernel's memory safety;
    ///  - the privileged flag `AVAIL1` should not be altered if in the kernel
    ///    page table (the restriction may be lifted in the futures).
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(pt_own): Tracked<&mut PageTableOwner<'rcu, C>>,
            Tracked(slot_own): Tracked<&MetaSlotOwner>
    )]
    #[verifier::external_body]
    pub fn protect_next(
        &mut self,
        len: usize,
        op: impl FnOnce(PageProperty) -> PageProperty,
    ) -> Option<Range<Vaddr>>
        requires
            slot_own.inv(),
            old(pt_own).tree.root.value.tree_node.tracked_is_some(),
    {
        self.inner.find_next_impl(len, false, true)?;

        #[verus_spec(with Tracked(pt_own), Tracked(slot_own))]
        let mut entry = self.inner.cur_entry();
        let tracked mut entry_own = pt_own.tree.root.value.tree_node.tracked_take();
        assert(entry_own.inv()) by { admit() };
        assert(entry_own.relate_slot_owner(slot_own)) by { admit() };
        assert(entry.wf(entry_own)) by { admit() };
        assert(op.requires((entry.pte.prop(),))) by { admit() };

        #[verus_spec(with Tracked(&mut entry_own), Tracked(slot_own))]
        entry.protect(op);

        let protected_va = self.inner.cur_va_range();

        self.inner.move_forward();

        Some(protected_va)
    }

    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(entry_own): Tracked<&mut EntryOwner<'rcu, C>>
    )]
    #[verifier::external_body]
    fn replace_cur_entry(&mut self, new_child: Child<C>) -> Option<PageTableFrag<C>> {
        let rcu_guard = self.inner.rcu_guard;

        let va = self.inner.va;
        let level = self.inner.level;

        let mut cur_entry = self.inner.cur_entry();

        let old = cur_entry.replace(new_child);
        match old {
            Child::None => None,
            Child::Frame(pa, ch_level, prop) => {
                //                debug_assert_eq!(ch_level, level);
                // SAFETY:
                // This is part of (if `split_huge` happens) a page table item mapped
                // with a previous call to `C::item_into_raw`, where:
                //  - The physical address and the paging level match it;
                //  - The item part is now unmapped so we can take its ownership.
                //
                // For page table configs that require the `AVAIL1` flag to be kept
                // (currently, only kernel page tables), the callers of the unsafe
                // `protect_next` method uphold this invariant.
                let item = C::item_from_raw(pa, level, prop);
                Some(PageTableFrag::Mapped { va, item })
            },
            Child::PageTable(pt) => {
                //                debug_assert_eq!(pt.level(), level - 1);
                if !C::TOP_LEVEL_CAN_UNMAP() && level == C::NR_LEVELS() {
                    //let _ = ManuallyDrop::new(pt); // leak it to make shared PTs stay `'static`.
                    assert(false);
                    return None;
                    //                    panic!("Unmapping shared kernel page table nodes");
                }
                // SAFETY: We must have locked this node.

                let locked_pt = pt.borrow().make_guard_unchecked(rcu_guard);
                // SAFETY:
                //  - We checked that we are not unmapping shared kernel page table nodes.
                //  - We must have locked the entire sub-tree since the range is locked.
                let num_frames = locking::dfs_mark_stray_and_unlock(rcu_guard, locked_pt);

                let pt_val = locked_pt.take(Tracked(entry_own.guard_perm.borrow_mut()));

                Some(
                    PageTableFrag::StrayPageTable {
                        pt: pt.into(),
                        va,
                        len: page_size(self.inner.level),
                        num_frames,
                    },
                )
            },
        }
    }
}

} // verus!
