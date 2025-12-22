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

use vstd::math::abs;
use vstd::simple_pptr::*;

use vstd_extra::ownership::*;
use vstd_extra::ghost_tree::*;

use aster_common::prelude::frame::{
    frame_to_index, meta_to_frame, Frame, MetaRegionOwners, MetaSlotOwner,
};
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

/*pub assume_specification<C: PageTableConfig>[ C::Item::clone ](item: &C::Item) -> (res: C::Item)
    ensures
        res == *item,
;*/


impl<C: PageTableConfig> PageTableFrag<C> {
    #[cfg(ktest)]
    #[rustc_allow_incoherent_impl]
    pub fn va_range(&self) -> Range<Vaddr> {
        match self {
            PageTableFrag::Mapped { va, item } => {
                let (pa, level, prop) = C::item_into_raw(item.clone());
                // SAFETY: All the arguments match those returned from the previous call
                // to `item_into_raw`, and we are taking ownership of the cloned item.
                drop(unsafe { C::item_from_raw(pa, level, prop) });
                *va..*va + page_size(level)
            },
            PageTableFrag::StrayPageTable { va, len, .. } => *va..*va + *len,
        }
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> Cursor<'rcu, C, A> {
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn clone_item(item: &C::Item) -> C::Item
        returns item
    {
        item.clone()
    }

    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(pt_own): Tracked<&mut PageTableOwner<C>>,
            Tracked(guard_perm): Tracked<&PointsTo<PageTableGuard<'rcu, C>>>
    )]
    #[verifier::external_body]
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>)
        -> (res: (Result<(Self, Tracked<CursorOwner<'rcu, C>>), PageTableError>))
        ensures
            old(pt_own).new_spec() == (*pt_own, res.unwrap().1@)
    {
        if !is_valid_range::<C>(va) || va.start >= va.end {
            return Err(PageTableError::InvalidVaddrRange(va.start, va.end));
        }
        if va.start % C::BASE_PAGE_SIZE() != 0 || va.end % C::BASE_PAGE_SIZE() != 0 {
            return Err(PageTableError::UnalignedVaddr);
        }
        //        const { assert!(C::NR_LEVELS() as usize <= MAX_NR_LEVELS()) };

        Ok(
            #[verus_spec(with Tracked(pt_own), Tracked(guard_perm))]
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn query(&mut self) -> (res: Result<PagesState<C>, PageTableError>)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(regions).inv(),
        ensures
            self.model(*owner).present() ==> {
                &&& res is Ok
                &&& res.unwrap().0.start == self.va
                &&& res.unwrap().0.end == self.va + self.model(*owner).scope
                &&& res.unwrap().1 is Some
                &&& res.unwrap().1.unwrap() == self.model(*owner).query_item_spec()
            },
            !old(self).model(*owner).present() ==> res is Ok && res.unwrap().1 is None,
            owner.inv(),
            self.wf(*owner),
            regions.inv()
    {
        if self.va >= self.barrier_va.end {
            assert(false) by { admit() };
            return Err(PageTableError::InvalidVaddr(self.va));
        }
        let rcu_guard = self.rcu_guard;

        let ghost initial_va = self.va;

        loop
            invariant
                owner.inv(),
                self.wf(*owner),
                regions.inv(),
                self.va == initial_va,
            decreases self.level,
        {
            let cur_va = self.va;
            let level = self.level;

            assert(regions.slot_owners.contains_key(frame_to_index(meta_to_frame(
                owner.continuations[(owner.level-1) as int].entry_own.node.unwrap().as_node.meta_perm.addr)))) by { admit() };
            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let entry = self.cur_entry();

            assert(regions.dropped_slots.contains_key(frame_to_index(entry.pte.paddr()))) by { admit() };

            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let tracked child_owner = continuation.take_child(owner.index);
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner), Tracked(regions) )]
            let cur_child = entry.to_ref();

            proof {
                continuation.put_child(owner.index, child_owner);
                owner.continuations.tracked_insert(owner.level - 1, continuation);
            }

            let item = match cur_child {
                ChildRef::PageTable(pt) => {
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner_opt = continuation.children.tracked_remove(owner.index as int);
                    let tracked mut child_owner = child_owner_opt.tracked_take();
                    let tracked mut child_node = child_owner.value.node.tracked_take();
                    let ghost child_node0 = child_node;

                    // SAFETY: The `pt` must be locked and no other guards exist.
                    #[verus_spec(with Tracked(&mut child_node.guard_perm))]
                    let guard = pt.make_guard_unchecked(rcu_guard);

                    proof {
                        child_owner.value.node = Some(child_node);
                        continuation.children.tracked_insert(owner.index as int, Some(child_owner));
                        owner.continuations.tracked_insert(owner.level - 1, continuation);
                    };

                    #[verus_spec(with Tracked(owner))]
                    self.push_level(guard);

                    continue;
                },
                ChildRef::None => {
                    assert(owner.cur_entry_owner().unwrap().is_absent());
                    proof { owner.present_not_absent(); }
                    None
                },
                ChildRef::Frame(pa, ch_level, prop) => {
                    assert(owner.cur_entry_owner().unwrap().is_frame());
                    proof { owner.present_frame(); }
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
                    let item =   /*ManuallyDrop::new(unsafe {*/ C::item_from_raw(pa, level, prop)  /*})*/;

                    // TODO: Provide a `PageTableItemRef` to reduce copies.
                    Some(Self::clone_item(&item))
                },
            };

            assert(1 <= level <= 4) by { admit() };
            let size = page_size(level);

            assert(cur_va + size < usize::MAX) by { admit() };

            return Ok((cur_va..cur_va + size, item));
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(guard_perm): Tracked<&PointsTo<PageTableGuard<'rcu, C>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(regions).inv(),
//            old(self).model(old(owner)).
        ensures
            owner.inv(),
            self.wf(*owner),
            regions.inv(),
    {
        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions))]
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
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(guard_perm): Tracked<&PointsTo<PageTableGuard<'rcu, C>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    fn find_next_impl(&mut self, len: usize, find_unmap_subtree: bool, split_huge: bool) -> (res: Option<Vaddr>)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(regions).inv(),
//            old(self).model(old(owner)).
        ensures
            owner.inv(),
            self.wf(*owner),
            regions.inv(),
    {
        assert(self.va + len < usize::MAX) by { admit() };

        //        assert_eq!(len % C::BASE_PAGE_SIZE(), 0);
        let end = self.va + len;
        //        assert!(end <= self.barrier_va.end);
        //        debug_assert_eq!(end % C::BASE_PAGE_SIZE(), 0);

        let rcu_guard = self.rcu_guard;

        let tracked mut guard_perm = guard_perm;

        while self.va < end
            invariant
                owner.inv(),
                self.wf(*owner),
                regions.inv()
            decreases owner.max_steps_partial((self.level - 1) as usize),
        {
            let ghost owner0 = *owner;

            let cur_va = self.va;
            #[verus_spec(with Tracked(owner))]
            let cur_va_range = self.cur_va_range();
            let cur_entry_fits_range = cur_va == cur_va_range.start && cur_va_range.end <= end;

            assert(regions.slot_owners.contains_key(frame_to_index(meta_to_frame(
                owner.continuations[(owner.level-1) as int].entry_own.node.unwrap().as_node.meta_perm.addr)))) by { admit() };

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let mut cur_entry = self.cur_entry();

            assert(owner == owner0);

            assert(regions.dropped_slots.contains_key(frame_to_index(cur_entry.pte.paddr()))) by { admit() };

            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let ghost cont0 = continuation;
            let tracked child_owner = continuation.take_child(owner.index);

            let tracked node_owner = continuation.entry_own.node.tracked_borrow();

            assert(child_owner.value.relate_parent_guard_perm(node_owner.guard_perm)) by { admit() };

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&node_owner), Tracked(regions))]
            let cur_child = cur_entry.to_ref();

            proof {
                continuation.put_child(owner.index, child_owner);
                assert(continuation.children == cont0.children);
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                assert(owner.continuations == owner0.continuations);
            }

            match cur_child {
                ChildRef::PageTable(pt) => {
                    if find_unmap_subtree && cur_entry_fits_range && (C::TOP_LEVEL_CAN_UNMAP()
                        || self.level != C::NR_LEVELS()) {
                        return Some(cur_va);
                    }

                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let ghost cont0 = continuation;
                    let tracked mut child_owner = continuation.take_child(owner.index);
                    let tracked mut parent_node_owner = continuation.entry_own.node.tracked_take();
                    let tracked mut child_node_owner = child_owner.value.node.tracked_take();

                    // SAFETY: The `pt` must be locked and no other guards exist.

                    #[verus_spec(with Tracked(&mut child_node_owner.guard_perm))]
                    let pt_guard = pt.make_guard_unchecked(rcu_guard);

                    #[verus_spec(with Tracked(&mut child_node_owner.as_node))]
                    let nr_children = pt_guard.borrow(Tracked(&mut child_node_owner.guard_perm)).nr_children();

                    proof {
                        child_owner.value.node = Some(child_node_owner);
                        continuation.put_child(owner.index, child_owner);
                        continuation.entry_own.node = Some(parent_node_owner);
                        assert(cont0.children == continuation.children);
                        owner.continuations.tracked_insert(self.level - 1, continuation);
                        assert(owner.continuations == owner0.continuations);
                    }

                    // If there's no mapped PTEs in the next level, we can
                    // skip to save time.
                    if (nr_children != 0) {
                        #[verus_spec(with Tracked(owner))]
                        self.push_level(pt_guard);

                    } else {
                        let _ = ManuallyDrop::new(pt_guard);

                        #[verus_spec(with Tracked(owner))]
                        self.move_forward();
                    }
                    continue ;
                },
                ChildRef::None => {
                    #[verus_spec(with Tracked(owner))]
                    self.move_forward();

                    continue ;
                },
                ChildRef::Frame(_, _, _) => {
                    if cur_entry_fits_range || !split_huge {
                        return Some(cur_va);
                    }

                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner = continuation.take_child(owner.index);

                    assert(child_owner.value.is_frame()) by { admit() };
                    let split_child = (#[verus_spec(with Tracked(&mut child_owner))] cur_entry.split_if_mapped_huge(rcu_guard)).expect(
                        "The entry must be a huge page",
                    );

                    proof {
                        continuation.put_child(owner.index, child_owner);
                    }

                    assert(self.wf(*owner)) by { admit() };
                    #[verus_spec(with Tracked(owner))]
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
    )]
    pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError>
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
    {
        //        assert!(va % C::BASE_PAGE_SIZE() == 0);
        if !self.barrier_va.contains(&va) {
            return Err(PageTableError::InvalidVaddr(va));
        }
        loop
            invariant
                owner.inv(),
                self.wf(*owner),
            decreases NR_LEVELS() - owner.level
        {
            assert(page_size((self.level + 1) as u8) > 0) by { admit() };

            let node_size = page_size(self.level + 1);
            let node_start = align_down(self.va, node_size);

            // If we're at level 4 already, `page_size(self.level + 1)` is by definition larger than the entire
            // page table, so these bounds will hold
            assert(self.level == 4 ==> node_start < va < node_start + node_size) by { admit() };

            assert(node_start + node_size < usize::MAX) by { admit() };

            // If the address is within the current node, we can jump directly.
            if node_start <= va && va < node_start + node_size {
                self.va = va;
                return Ok(());
            }

            #[verus_spec(with Tracked(owner))]
            self.pop_level();
        }
    }

    /// Traverses forward to the end of [`Self::cur_va_range`].
    //
    /// If reached the end of the current page table node, it (recursively)
    /// moves itself up to the next page of the parent page.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>
    )]
    #[verifier::external_body]
    fn move_forward(&mut self)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
        ensures
            self.model(*owner) == old(self).model(*old(owner)).move_forward_spec(),
            owner.inv(),
            self.wf(*owner),
            owner.max_steps() < old(owner).max_steps()
    {
        let next_va = self.cur_va_range().end;
        while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0
            invariant
                owner.inv(),
                self.wf(*owner),
            decreases self.guard_level - self.level,
        {
            let ghost level = self.level;
            assert(1 <= self.level < 4) by { admit() };
            #[verus_spec(with Tracked(owner))]
            self.pop_level();
            assert(self.level == level - 1);
        }
        self.va = next_va;

        assert(self.model(*owner) == old(self).model(*old(owner)).move_forward_spec()) by { admit() };
    }

    /// Goes up a level.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>
    )]
    fn pop_level(&mut self)
        requires
            1 <= old(self).level < 4,
            old(owner).inv(),
            old(self).wf(*old(owner)),
        ensures
            self.model(*owner) == old(self).model(*old(owner)).pop_level_spec(),
            owner.inv(),
            self.wf(*owner),
            self.level == old(self).level + 1
    {
        let opt_taken = self.path.get(self.level as usize - 1);

        /* let taken = self.path[self.level as usize - 1]
            .take()
            .expect("Popping a level without a lock");
        let _ = ManuallyDrop::new(taken);
*/
        self.level = self.level + 1;

        assert(self.model(*owner) == old(self).model(*old(owner)).pop_level_spec()) by { admit() };
        assert(owner.inv()) by { admit() };
        assert(self.wf(*owner)) by { admit() };
    }

    /// Goes down a level to a child page table.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>
    )]
    fn push_level(&mut self, child_pt: PPtr<PageTableGuard<'rcu, C>>)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(owner).cur_entry_owner() is Some,
            old(owner).cur_entry_owner().unwrap().is_node(),
            old(owner).cur_entry_owner().unwrap().node.unwrap().guard_perm.addr() == child_pt.addr(),
        ensures
            owner.inv(),
            self.wf(*owner),
            self.level == old(self).level - 1,
            self.va == old(self).va,
            self.model(*owner) == old(self).model(*old(owner)).push_level_spec(),
            owner.max_steps() < old(owner).max_steps()
    {
        let ghost owner0 = *owner;

        self.level = self.level - 1;
        //        debug_assert_eq!(self.level, child_pt.level());

        //        let old = self.path.get(self.level as usize - 1);
        self.path.set(self.level as usize - 1, Some(child_pt));

        proof { 
            let tracked mut cont = owner.continuations.tracked_remove(owner.level-1);
            let tracked mut child = cont.make_cont(owner.index);
            owner.continuations.tracked_insert(owner.level-1, cont);
            owner.continuations.tracked_insert(owner.level-2, child);
            owner.path.0.push(owner.index);
            owner.level = (owner.level - 1) as u8;
            owner.index = 0;
        }

        assert(owner.index == self.va % page_size_spec(self.level)) by { admit() };
        assert(owner@ == owner0@.push_level_spec()) by { admit() };
        assert(owner.max_steps() < owner0.max_steps()) by { admit() };
        //        debug_assert!(old.is_none());
    }

    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&MetaRegionOwners>
    )]
    fn cur_entry(&mut self) -> (res: Entry<'rcu, C>)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            1 <= old(self).level <= 4,
            old(self).path[old(self).level as int - 1] is Some,
            regions.slot_owners.contains_key(frame_to_index(meta_to_frame(
                old(owner).continuations[(old(owner).level-1) as int].entry_own.node.unwrap().as_node.meta_perm.addr))),
        ensures
            owner.inv(),
            self.wf(*owner),
            owner.cur_entry_owner() is Some ==> res.wf(owner.cur_entry_owner().unwrap()),
            self == old(self),
            owner == old(owner)
    {
        let ghost owner0 = *owner;

        let node = self.path[self.level as usize - 1].unwrap();
        let tracked mut parent_continuation = owner.continuations.tracked_remove((owner.level - 1) as int);
        let ghost cont0 = parent_continuation;
        let tracked parent_own = parent_continuation.entry_own.node.tracked_take();
        let tracked child = parent_continuation.take_child(owner.index);

        let ghost index = frame_to_index(meta_to_frame(parent_own.as_node.meta_perm.addr));

        #[verus_spec(with Tracked(&child.value),
            Tracked(&parent_own.guard_perm),
            Tracked(regions.slot_owners.tracked_borrow(index)))]
        let res = PageTableGuard::entry(node, pte_index::<C>(self.va, self.level));

        proof {
            parent_continuation.entry_own.node = Some(parent_own);
            parent_continuation.put_child(owner.index, child);
            assert(parent_continuation.children == cont0.children);
            owner.continuations.tracked_insert((owner.level - 1) as int, parent_continuation);
            assert(owner.continuations == owner0.continuations);
        }

        res
    }

    /// Gets the virtual address range that the current entry covers.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<C>>
    )]
    #[verifier::external_body]
    fn cur_va_range(&self) -> (res: Range<Vaddr>)
        ensures
            res == self.model(*old(owner)).cur_va_range_spec(),
            owner == old(owner)
    {
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
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>) -> Result<(Self, Tracked<CursorOwner<'rcu, C>>), PageTableError> {
        Cursor::new(pt, guard, va).map(|inner| (Self { inner: inner.0 }, inner.1))
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// This is the same as [`Cursor::find_next`].
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(guard_perm): Tracked<&vstd::simple_pptr::PointsTo<PageTableGuard<'rcu, C>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(owner).inv(),
            old(self).inner.wf(*old(owner)),
            old(regions).inv(),
        ensures
            owner.inv(),
            self.inner.wf(*owner),
            regions.inv(),
    {
        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions))]
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>
    )]
    pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError>
        requires
            old(owner).inv(),
            old(self).inner.wf(*old(owner))
    {
        #[verus_spec(with Tracked(owner))]
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn query(&mut self) -> (res: Result<PagesState<C>, PageTableError>)
        requires
            old(owner).inv(),
            old(self).inner.wf(*old(owner)),
            old(regions).inv(),
    {
        #[verus_spec(with Tracked(owner), Tracked(regions))]
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(entry_own): Tracked<EntryOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn map(&mut self, item: C::Item) -> Result<(), PageTableFrag<C>>
        requires
            old(owner).inv(),
            old(self).inner.wf(*old(owner)),
            old(regions).inv(),
            entry_own.inv(),
    {
        //        assert!(self.0.va < self.0.barrier_va.end);
        let (pa, level, prop) = C::item_into_raw(item);
        //        assert!(level <= C::HIGHEST_TRANSLATION_LEVEL());
        let size = page_size(level);
        //        assert_eq!(self.0.va % size, 0);
        assert(self.inner.va + size < usize::MAX) by { admit() };

        let end = self.inner.va + size;
        //        assert!(end <= self.0.barrier_va.end);

        let rcu_guard = self.inner.rcu_guard;

        // Adjust ourselves to the level of the item.
        while self.inner.level != level
            invariant
                owner.inv(),
                entry_own.inv(),
                self.inner.wf(*owner),
                1 <= level <= NR_LEVELS(),
                regions.inv()
            decreases abs(level - self.inner.level),
        {
            if self.inner.level < level {
                #[verus_spec(with Tracked(owner))]
                self.inner.pop_level();
                continue ;
            }
            // We are at a higher level, go down.

            assert(regions.slot_owners.contains_key(
                frame_to_index(meta_to_frame(
                    owner.continuations[(owner.level-1) as int].entry_own.node.unwrap().as_node.meta_perm.addr)))) by { admit() };

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let mut cur_entry = self.inner.cur_entry();

            assert(regions.dropped_slots.contains_key(frame_to_index(cur_entry.pte.paddr()))) by { admit() };

            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let tracked child_owner = continuation.take_child(owner.index);
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner), Tracked(regions) )]
            let cur_child = cur_entry.to_ref();

            proof {
                continuation.put_child(owner.index, child_owner);
                owner.continuations.tracked_insert(owner.level - 1, continuation);
            }

            match cur_child {
                ChildRef::PageTable(pt) => {
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner_opt = continuation.children.tracked_remove(owner.index as int);
                    let tracked mut child_owner = child_owner_opt.tracked_take();
                    let tracked mut child_node = child_owner.value.node.tracked_take();
                    let ghost child_node0 = child_node;

                    // SAFETY: The `pt` must be locked and no other guards exist.
                    #[verus_spec(with Tracked(&mut child_node.guard_perm))]
                    let pt_guard = pt.make_guard_unchecked(rcu_guard);

                    proof {
                        child_owner.value.node = Some(child_node);
                        continuation.children.tracked_insert(owner.index as int, Some(child_owner));
                        owner.continuations.tracked_insert(owner.level - 1, continuation);
                    };

                    #[verus_spec(with Tracked(owner))]
                    self.inner.push_level(pt_guard);
                },
                ChildRef::None => {
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner = continuation.take_child(owner.index);

                    assert(child_owner.value.is_absent()) by { admit() };

                    let child_guard = (#[verus_spec(with Tracked(&mut child_owner))] cur_entry.alloc_if_none(rcu_guard)).unwrap();

                    proof {
                        continuation.put_child(owner.index, child_owner);
                        owner.continuations.tracked_insert(owner.level - 1, continuation);
                    }

                    #[verus_spec(with Tracked(owner))]
                    self.inner.push_level(child_guard);
                },
                ChildRef::Frame(_, _, _) => {
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner = continuation.take_child(owner.index);

                    assert(child_owner.value.is_frame()) by { admit() };
                    let split_child = (#[verus_spec(with Tracked(&mut child_owner))] cur_entry.split_if_mapped_huge(rcu_guard)).unwrap();

                    proof {
                        continuation.put_child(owner.index, child_owner);
                        assert(continuation.inv());
                        owner.continuations.tracked_insert(owner.level - 1, continuation);
                    }

                    #[verus_spec(with Tracked(owner))]
                    self.inner.push_level(split_child);
                },
            }
        }

        #[verus_spec(with Tracked(owner), Tracked(entry_own))]
        let frag = self.replace_cur_entry(Child::Frame(pa, level, prop));

        #[verus_spec(with Tracked(owner))]
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
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(guard_perm): Tracked<&mut PointsTo<PageTableGuard<'rcu, C>>>,
            Tracked(regions): Tracked<&MetaRegionOwners>
    )]
    #[verifier::external_body]
    pub fn protect_next(
        &mut self,
        len: usize,
        op: impl FnOnce(PageProperty) -> PageProperty,
    ) -> Option<Range<Vaddr>>
        requires
            regions.inv(),
            old(owner).cur_entry_owner() is Some,
    {
        unimplemented!()
        /*
        self.inner.find_next_impl(len, false, true)?;

        #[verus_spec(with Tracked(owner), Tracked(regions))]
        let mut entry = self.inner.cur_entry();
        let tracked mut entry_own = owner.subtree.value;
        assert(entry_own.inv()) by { admit() };
        //        assert(entry_own.relate_slot_owner(slot_own)) by { admit() };
        assert(entry.wf(entry_own)) by { admit() };
        assert(op.requires((entry.pte.prop(),))) by { admit() };

        #[verus_spec(with Tracked(&mut entry_own), Tracked(guard_perm), Tracked(slot_own))]
        entry.protect(op);

        let protected_va = self.inner.cur_va_range();

        self.inner.move_forward();

        Some(protected_va)
        */
    }

    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(entry_own): Tracked<EntryOwner<'rcu, C>>
    )]
    #[verifier::external_body]
    fn replace_cur_entry(&mut self, new_child: Child<C>) -> (res: Option<PageTableFrag<C>>)
        requires
            old(owner).inv(),
            entry_own.inv(),
            old(self).inner.wf(*old(owner)),
        ensures
            owner.inv(),
            self.inner.wf(*owner),
    {
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

                let pt_val = locked_pt.borrow(Tracked(&owner.continuations[owner.level as int].entry_own.node.unwrap().guard_perm));

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
