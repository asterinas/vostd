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

use vstd::arithmetic::power2::pow2;
use vstd::math::abs;
use vstd::simple_pptr::*;

use vstd_extra::arithmetic::*;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;
use vstd_extra::undroppable::NeverDrop;

use crate::mm::frame::Frame;
use crate::mm::page_table::*;
use crate::mm::{Paddr, Vaddr, MAX_NR_LEVELS};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::mm::frame::mapping::{frame_to_index, meta_to_frame, META_SLOT_SIZE};
use crate::specs::mm::frame::meta_owners::MetaSlotOwner;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use core::{fmt::Debug, marker::PhantomData, mem::ManuallyDrop, ops::Range};

use align_ext::AlignExt;

use crate::{
    mm::{page_prop::PageProperty, page_table::is_valid_range},
    specs::task::InAtomicMode,
};

use super::{
    pte_index, Child, ChildRef, Entry, EntryOwner, FrameView, PageTable, PageTableConfig,
    PageTableError, PageTableGuard, PageTablePageMeta, PagingConstsTrait, PagingLevel,
};

verus! {

/// The state of virtual pages represented by a page table.
///
/// This is the return type of the [`Cursor::query`] method.
pub type PagesState<C> = (Range<Vaddr>, Option<<C as PageTableConfig>::Item>);

/// The cursor for traversal over the page table.
///
/// A slot is a PTE at any levels, which correspond to a certain virtual
/// memory range sized by the "page size" of the current level.
///
/// A cursor is able to move to the next slot, to read page properties,
/// and even to jump to a virtual address directly.
#[rustc_has_incoherent_inherent_impls]
pub struct Cursor<'rcu, C: PageTableConfig, A: InAtomicMode> {
    /// The current path of the cursor.
    ///
    /// The level 1 page table lock guard is at index 0, and the level N page
    /// table lock guard is at index N - 1.
    pub path: [Option<PPtr<PageTableGuard<'rcu, C>>>; CONST_NR_LEVELS],
    /// The cursor should be used in a RCU read side critical section.
    pub rcu_guard: &'rcu A,
    /// The level of the page table that the cursor currently points to.
    pub level: PagingLevel,
    /// The top-most level that the cursor is allowed to access.
    ///
    /// From `level` to `guard_level`, the nodes are held in `path`.
    pub guard_level: PagingLevel,
    /// The virtual address that the cursor currently points to.
    pub va: Vaddr,
    /// The virtual address range that is locked.
    pub barrier_va: Range<Vaddr>,
    pub _phantom: PhantomData<&'rcu PageTable<C>>,
}

/// The cursor of a page table that is capable of map, unmap or protect pages.
///
/// It has all the capabilities of a [`Cursor`], which can navigate over the
/// page table corresponding to the address range. A virtual address range
/// in a page table can only be accessed by one cursor, regardless of the
/// mutability of the cursor.
#[rustc_has_incoherent_inherent_impls]
pub struct CursorMut<'rcu, C: PageTableConfig, A: InAtomicMode> {
    pub inner: Cursor<'rcu, C, A>,
}

impl<C: PageTableConfig, A: InAtomicMode> Iterator for Cursor<'_, C, A> {
    type Item = PagesState<C>;

    #[verifier::external_body]
    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!()
    }
}

pub open spec fn page_size_spec(level: PagingLevel) -> usize {
    PAGE_SIZE() << (nr_subpage_per_huge::<PagingConsts>().ilog2() * (level - 1))
}

/// The page size at a given level.
#[verifier::when_used_as_spec(page_size_spec)]
#[verifier::external_body]
pub fn page_size(level: PagingLevel) -> (ret: usize)
    requires
        1 <= level <= NR_LEVELS() + 1,
    ensures
        ret == page_size_spec(level),
        exists|e| ret == pow2(e),
        ret >= 2,
{
    PAGE_SIZE() << (nr_subpage_per_huge::<PagingConsts>().ilog2() as usize * (level as usize - 1))
}

/// A fragment of a page table that can be taken out of the page table.
#[must_use]
#[rustc_has_incoherent_inherent_impls]
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

#[verus_verify]
impl<'rcu, C: PageTableConfig, A: InAtomicMode> Cursor<'rcu, C, A> {
    #[verifier::external_body]
    pub fn clone_item(item: &C::Item) -> C::Item
        returns
            item,
    {
        item.clone()
    }

    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[verus_spec(
        with Tracked(pt_own): Tracked<&mut OwnerSubtree<C>>,
            Tracked(guard_perm): Tracked<&PointsTo<PageTableGuard<'rcu, C>>>
    )]
    #[verifier::external_body]
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>) -> (res: (Result<
        (Self, Tracked<CursorOwner<'rcu, C>>),
        PageTableError,
    >))
    //        ensures
    //            old(pt_own).new_spec() == (*pt_own, res.unwrap().1@),
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
            locking::lock_range(pt, guard, va),
        )
    }

    /// Gets the current virtual address.
    #[rustc_allow_incoherent_impl]
    pub fn virt_addr(&self) -> Vaddr
        returns
            self.va,
    {
        self.va
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn query(&mut self) -> (res: Result<PagesState<C>, PageTableError>)
        requires
            old(owner).inv(),
            old(self).inv(),
            old(self).wf(*old(owner)),
            old(regions).inv(),
        ensures
            owner.in_locked_range() && self.model(*owner).present() ==> {
                &&& res is Ok
                &&& res.unwrap().0.start == self.va
                &&& res.unwrap().0.end == self.va + page_size(self.level)
                &&& res.unwrap().1 is Some
                &&& res.unwrap().1.unwrap() == self.model(*owner).query_item_spec()
            },
            owner.in_locked_range() && !old(self).model(*owner).present() ==> res is Ok
                && res.unwrap().1 is None,
            owner.inv(),
            self.inv(),
            self.wf(*owner),
            regions.inv(),
    {
        if self.va >= self.barrier_va.end {
            proof {
                owner.va.reflect_prop(self.va);
            }
            return Err(PageTableError::InvalidVaddr(self.va));
        }
        let rcu_guard = self.rcu_guard;

        let ghost initial_va = self.va;

        loop
            invariant
                owner.inv(),
                self.inv(),
                self.wf(*owner),
                regions.inv(),
                self.va == initial_va,
            decreases self.level,
        {
            let cur_va = self.va;
            let level = self.level;

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let entry = self.cur_entry();

            assert(owner.inv());

            assert(regions.dropped_slots.contains_key(frame_to_index(entry.pte.paddr()))) by {
                admit()
            };

            let ghost continuations0 = owner.continuations;
            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let ghost cont0 = continuation;
            let tracked child_owner = continuation.take_child();
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();

            let tracked Tracked(guard_perm) = guards.guards.tracked_remove(parent_owner.meta_perm.addr());

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner), Tracked(regions), Tracked(&guard_perm) )]
            let cur_child = entry.to_ref();

            proof {
                assert(cur_child.wf(child_owner.value));
                continuation.put_child(child_owner);
                cont0.take_put_child();
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                assert(owner.continuations == continuations0);
                guards.guards.tracked_insert(parent_owner.meta_perm.addr(), Tracked(guard_perm));
            }

            let item = match cur_child {
                ChildRef::PageTable(pt) => {
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut child_node = child_owner.value.node.tracked_take();
                    let ghost child_node0 = child_node;

                    // SAFETY: The `pt` must be locked and no other guards exist.

                    #[verus_spec(with Tracked(&child_node), Tracked(guards))]
                    let guard = pt.make_guard_unchecked(rcu_guard);

                    let tracked Tracked(guard_perm) = guards.guards.tracked_remove(child_node.meta_perm.addr());

                    proof {
                        child_owner.value.node = Some(child_node);
                        continuation.put_child(child_owner);
                        owner.continuations.tracked_insert(owner.level - 1, continuation);
                    }

                    #[verus_spec(with Tracked(owner), Tracked(guard_perm))]
                    self.push_level(guard);

                    continue ;
                },
                ChildRef::None => {
                    assert(owner.cur_entry_owner().is_absent());
                    proof {
                        owner.present_not_absent();
                    }
                    None
                },
                ChildRef::Frame(pa, ch_level, prop) => {
                    assert(owner.cur_entry_owner().is_frame());
                    proof {
                        owner.present_frame();
                    }
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
                    Some(Self::clone_item(&item))
                },
            };

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
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(regions).inv(),
            old(self).inv(),
            old(self).level < old(self).guard_level,
            old(owner).in_locked_range(),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).va + len <= old(self).barrier_va.end,
        ensures
            owner.inv(),
            self.wf(*owner),
            regions.inv(),
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
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
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    fn find_next_impl(&mut self, len: usize, find_unmap_subtree: bool, split_huge: bool) -> (res:
        Option<Vaddr>)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(regions).inv(),
            old(self).inv(),
            old(owner).in_locked_range(),
            old(self).level < NR_LEVELS(),
            // Panic conditions as preconditions
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).va + len <= old(self).barrier_va.end,
        ensures
            owner.inv(),
            self.wf(*owner),
            regions.inv(),
            res is Some ==> res.unwrap() == self.va,
    {
        let end = self.va + len;
        //        debug_assert_eq!(end % C::BASE_PAGE_SIZE(), 0);

        let rcu_guard = self.rcu_guard;

        while self.va < end
            invariant
                owner.inv(),
                self.wf(*owner),
                regions.inv(),
                self.inv(),
                owner.in_locked_range() || self.va >= end,
                end <= self.barrier_va.end,
            decreases owner.max_steps(),
        {
            let ghost owner0 = *owner;

            let cur_va = self.va;
            #[verus_spec(with Tracked(owner))]
            let cur_va_range = self.cur_va_range();
            let cur_entry_fits_range = cur_va == cur_va_range.start && cur_va_range.end <= end;

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let mut cur_entry = self.cur_entry();

            assert(regions.dropped_slots.contains_key(frame_to_index(cur_entry.pte.paddr()))) by {
                admit()
            };

            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let ghost cont0 = continuation;
            let tracked child_owner = continuation.take_child();
            let tracked node_owner = continuation.entry_own.node.tracked_borrow();

            let tracked Tracked(guard_perm) = guards.guards.tracked_remove(node_owner.meta_perm.addr());

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&node_owner), Tracked(regions), Tracked(&guard_perm))]
            let cur_child = cur_entry.to_ref();

            proof {
                continuation.put_child(child_owner);
                assert(continuation.children == cont0.children);
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                assert(owner.continuations == owner0.continuations);
                guards.guards.tracked_insert(node_owner.meta_perm.addr(), Tracked(guard_perm));
            }

            match cur_child {
                ChildRef::PageTable(pt) => {
                    if find_unmap_subtree && cur_entry_fits_range && (C::TOP_LEVEL_CAN_UNMAP()
                        || self.level != C::NR_LEVELS()) {
                        return Some(cur_va);
                    }
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let ghost cont0 = continuation;
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut parent_node_owner = continuation.entry_own.node.tracked_take();
                    let tracked mut child_node_owner = child_owner.value.node.tracked_take();

                    // SAFETY: The `pt` must be locked and no other guards exist.
                    #[verus_spec(with Tracked(&child_node_owner), Tracked(guards))]
                    let pt_guard = pt.make_guard_unchecked(rcu_guard);

                    let tracked Tracked(guard_perm) = guards.guards.tracked_remove(child_node_owner.meta_perm.addr());

                    #[verus_spec(with Tracked(&mut child_node_owner))]
                    let nr_children = pt_guard.borrow(Tracked(&guard_perm)).nr_children();

                    proof {
                        child_owner.value.node = Some(child_node_owner);
                        continuation.put_child(child_owner);
                        continuation.entry_own.node = Some(parent_node_owner);
                        assert(cont0.children == continuation.children);
                        owner.continuations.tracked_insert(self.level - 1, continuation);
                        assert(owner.continuations == owner0.continuations);
                    }

                    // If there's no mapped PTEs in the next level, we can
                    // skip to save time.
                    if (nr_children != 0) {
                        #[verus_spec(with Tracked(owner), Tracked(guard_perm))]
                        self.push_level(pt_guard);
                    } else {
//                        let _ = NeverDrop::new(pt_guard, Tracked(regions));

                        proof {
                            owner.move_forward_increases_va();
                            
                        }

                        #[verus_spec(with Tracked(owner), Tracked(regions))]
                        self.move_forward();

                        proof {
                            owner.va.reflect_prop(self.va);
                        }
                    }

                    continue ;
                },
                ChildRef::None => {
                    proof {
                        owner.move_forward_increases_va();
                    }

                    #[verus_spec(with Tracked(owner), Tracked(regions))]
                    self.move_forward();

                    proof {
                        owner.va.reflect_prop(self.va);
                    }

                    continue ;
                },
                ChildRef::Frame(_, _, _) => {
                    assert(owner.max_steps() == owner0.max_steps());
                    if cur_entry_fits_range || !split_huge {
                        return Some(cur_va);
                    }
                    let tracked mut continuation = owner.continuations.tracked_remove(
                        owner.level - 1,
                    );
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

                    assert(child_owner.value.is_frame()) by { admit() };

                    let tracked Tracked(guard_perm) = guards.guards.tracked_remove(parent_owner.meta_perm.addr());

                    let split_child = (
                    #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions),
                        Tracked(guards), Tracked(&mut guard_perm))]
                    cur_entry.split_if_mapped_huge(rcu_guard)).expect("The entry must be a huge page");

                    proof {
                        continuation.put_child(child_owner);
                        continuation.entry_own.node = Some(parent_owner);
                        owner.continuations.tracked_insert(owner.level - 1, continuation);

                        owner0.max_steps_partial_inv(*owner, owner.level as usize);
                    }

                    #[verus_spec(with Tracked(owner), Tracked(guard_perm))]
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
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError>
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(self).inv(),
            old(self).level < old(self).guard_level,
    {
        //        assert!(va % C::BASE_PAGE_SIZE() == 0);
        if !self.barrier_va.contains(&va) {
            return Err(PageTableError::InvalidVaddr(va));
        }
        loop
            invariant
                owner.inv(),
                self.wf(*owner),
                self.inv(),
                self.level <= self.guard_level,
                self.barrier_va.start <= va < self.barrier_va.end,
            decreases self.guard_level - self.level,
        {
            let node_size = page_size(self.level + 1);
            let node_start = self.va.align_down(node_size);

            // If we're at `guard_level` already, then `node_start == self.barrier_va.start`
            // and `node_start + node_size == self.barrier_va.end`
            assert(node_start == self.barrier_va.start) by { admit() };
            assert(node_start + node_size == self.barrier_va.end) by { admit() };

            // If the address is within the current node, we can jump directly.
            if node_start <= va && va < node_start + node_size {
                self.va = va;
                return Ok(());
            }
            #[verus_spec(with Tracked(owner), Tracked(regions))]
            self.pop_level();
        }
    }

    /// Traverses forward to the end of [`Self::cur_va_range`].
    //
    /// If reached the end of the current page table node, it (recursively)
    /// moves itself up to the next page of the parent page.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    fn move_forward(&mut self)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(self).inv(),
            old(regions).inv(),
            old(
                owner,
            ).in_locked_range(),
    //            old(self).level < NR_LEVELS()

        ensures
    //            self.model(*owner) == old(self).model(*old(owner)).move_forward_spec(),

            owner.inv(),
            self.wf(*owner),
            self.inv(),
            regions.inv(),
            owner == old(owner).move_forward_owner_spec(),
            owner.max_steps() < old(owner).max_steps(),
            self.barrier_va == old(self).barrier_va,
            self.guard_level == old(self).guard_level,
    {
        let ghost owner0 = *owner;
        proof {
            owner.move_forward_owner_decreases_steps();
        }

        let ghost start_level = self.level;
        let ghost guard_level = self.guard_level;
        let ghost barrier_va = self.barrier_va;
        let ghost va = self.va;

        let next_va = (#[verus_spec(with Tracked(owner))]
        self.cur_va_range()).end;

        let ghost abs_va = AbstractVaddr::from_vaddr(va);
        let ghost abs_va_down = abs_va.align_down((start_level - 1) as int);
        let ghost abs_next_va = AbstractVaddr::from_vaddr(next_va);

        proof {
            AbstractVaddr::reflect_from_vaddr(va);
            AbstractVaddr::reflect_from_vaddr(next_va);
            abs_va.reflect_prop(va);
            abs_next_va.reflect_prop(next_va);

            assert(abs_next_va == abs_va.align_up(start_level as int)) by { admit() };
            assert(abs_next_va == abs_va_down.next_index(start_level as int)) by { admit() };

            AbstractVaddr::from_vaddr_wf(self.va);
            abs_va.align_down_inv((start_level - 1) as int);
            abs_va_down.next_index_wrap_condition(start_level as int);
        }

        assert(forall|i: int|
            start_level <= i < NR_LEVELS() ==> #[trigger] abs_va.index[i - 1]
                == owner.continuations[i - 1].idx) by { admit() };

        while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0
            invariant
                owner.inv(),
                self.wf(*owner),
                self.inv(),
                regions.inv(),
                self.guard_level == guard_level,
                self.barrier_va == barrier_va,
                abs_va == AbstractVaddr::from_vaddr(va),
                abs_next_va == AbstractVaddr::from_vaddr(next_va),
                owner.move_forward_owner_spec() == owner0.move_forward_owner_spec(),
                abs_va_down.next_index(start_level as int) == abs_next_va,
                abs_va_down.wrapped(start_level as int, self.level as int),
                1 <= start_level <= self.level <= self.guard_level <= NR_LEVELS(),
                forall|i: int|
                    start_level <= i < NR_LEVELS() ==> #[trigger] abs_va.index[i - 1]
                        == abs_va_down.index[i - 1],
                forall|i: int|
                    self.level <= i < NR_LEVELS() ==> #[trigger] abs_va.index[i - 1]
                        == owner.continuations[i - 1].idx,
            decreases self.guard_level - self.level,
        {
            proof {
                assert(abs_next_va.index[self.level - 1] == 0);
                abs_va_down.wrapped_unwrap(start_level as int, self.level as int);
                abs_va_down.use_wrapped(start_level as int, self.level as int);
                assert(abs_va.index[self.level - 1] + 1 == NR_ENTRIES());
                assert(owner.move_forward_owner_spec()
                    == owner.pop_level_owner_spec().0.move_forward_owner_spec());
            }

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            self.pop_level();
        }

        let ghost index = abs_next_va.index[self.level - 1];
        assert(self.level >= self.guard_level || index != 0);
        assert(self.level < self.guard_level) by { admit() };

        assert(abs_va.index[self.level - 1] + 1 < NR_ENTRIES());
        assert(owner.move_forward_owner_spec() == owner0.move_forward_owner_spec());
        assert(owner.move_forward_owner_spec() == owner.inc_index());

        self.va = next_va;

        proof {
            owner.do_inc_index();
            assert(owner.va == abs_next_va) by { admit() };
        }
    }

    /// Goes up a level.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    fn pop_level(&mut self)
        requires
            old(self).level < old(self).guard_level,
            old(self).inv(),
            old(owner).inv(),
            old(regions).inv(),
            old(self).wf(*old(owner)),
        ensures
    //            self.model(*owner) == old(self).model(*old(owner)).pop_level_spec(),

            owner.inv(),
            self.wf(*owner),
            self.inv(),
            regions.inv(),
            self.guard_level == old(self).guard_level,
            *owner == old(owner).pop_level_owner_spec().0,
    {
        let ghost owner0 = *owner;

        let tracked cont = owner.continuations.tracked_remove(owner.level - 1);
        let tracked node_owner = cont.entry_own.node.tracked_take();

        //        let taken_val = taken.take(Tracked(&mut node_owner.guard_perm));
        //        let _ = NeverDrop::new(taken_val, Tracked(regions));
        //        taken.put(Tracked(&mut node_owner.guard_perm), taken_val);

        proof {
            cont.entry_own.node = Some(node_owner);
            owner.continuations.tracked_insert(owner.level - 1, cont);
            assert(owner.continuations == owner0.continuations);
        }

        self.level = self.level + 1;

        proof {
            let ghost child_cont = owner.continuations[owner.level - 1];
            assert(child_cont.all_some());
            assert(child_cont.inv());
            owner.pop_level_owner();

            assert(self.wf(*owner));
        }
    }

    /// Goes down a level to a child page table.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(guard_perm): Tracked<GuardPerm<'rcu, C>>
    )]
    fn push_level(&mut self, child_pt: PPtr<PageTableGuard<'rcu, C>>)
        requires
            old(owner).inv(),
            old(self).inv(),
            old(self).wf(*old(owner)),
            old(owner).cur_entry_owner().is_node(),
            guard_perm.addr() == child_pt.addr(),
        ensures
            owner.inv(),
            self.inv(),
            self.wf(*owner),
            self.guard_level == old(self).guard_level,
            self.level == old(self).level - 1,
            self.va == old(self).va,
            //            self.model(*owner) == old(self).model(*old(owner)).push_level_spec(),
            owner == old(owner).push_level_owner_spec(guard_perm),
            owner.max_steps() < old(owner).max_steps(),
    {
        assert(owner.va.index.contains_key(owner.level - 2));

        self.level = self.level - 1;
        //        debug_assert_eq!(self.level, child_pt.level());

        //        let old = self.path.get(self.level as usize - 1);
        self.path.set(self.level as usize - 1, Some(child_pt));

        proof {
            owner.push_level_owner_decreases_steps(guard_perm);
            owner.push_level_owner_preserves_va(guard_perm);
            owner.push_level_owner(Tracked(guard_perm));
        }
        //        debug_assert!(old.is_none());
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&MetaRegionOwners>
    )]
    fn cur_entry(&mut self) -> (res: Entry<'rcu, C>)
        requires
            old(self).inv(),
            old(owner).inv(),
            old(self).wf(*old(owner)),
            1 <= old(self).level <= 4,
            old(self).path[old(self).level as int - 1] is Some,
        ensures
            owner.inv(),
            self.inv(),
            self.wf(*owner),
            res.wf(owner.cur_entry_owner()),
            self == old(self),
            owner == old(owner),
    {
        let ghost owner0 = *owner;

        let node = self.path[self.level as usize - 1].unwrap();
        let tracked mut parent_continuation = owner.continuations.tracked_remove((owner.level - 1) as int);

        assert(parent_continuation.inv());
        let tracked parent_own = parent_continuation.entry_own.node.tracked_take();
        let tracked child = parent_continuation.take_child();

        let ghost index = frame_to_index(meta_to_frame(parent_own.meta_perm.addr));

        assert(regions.slot_owners.contains_key(index)) by { admit() };

        #[verus_spec(with Tracked(&child),
            Tracked(&mut parent_continuation.guard_perm))]
        let res = PageTableGuard::entry(node, pte_index::<C>(self.va, self.level));

        proof {
            parent_continuation.entry_own.node = Some(parent_own);
            parent_continuation.put_child(child);
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
    fn cur_va_range(&self) -> (res: Range<Vaddr>)
        requires
            old(owner).inv(),
            self.wf(*old(owner)),
        ensures
            old(owner).va.align_down(self.level as int).reflect(res.start),
            old(owner).va.align_up(self.level as int).reflect(res.end),
            owner == old(owner),
    {
        let page_size = page_size(self.level);
        let start = self.va.align_down(page_size);

        proof {
            owner.va.reflect_prop(self.va);
            owner.va.align_down_concrete(self.level as int);
            owner.va.align_up_concrete(self.level as int);
            owner.va.align_diff(self.level as int);
        }

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
        (Self, Tracked<CursorOwner<'rcu, C>>),
        PageTableError,
    > {
        Cursor::new(pt, guard, va).map(|inner| (Self { inner: inner.0 }, inner.1))
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// This is the same as [`Cursor::find_next`].
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>, 
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(owner).inv(),
            old(self).inner.wf(*old(owner)),
            old(regions).inv(),
            old(self).inner.inv(),
            old(self).inner.level < old(self).inner.guard_level,
            old(owner).in_locked_range(),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).inner.va + len <= old(self).inner.barrier_va.end,
        ensures
            owner.inv(),
            self.inner.wf(*owner),
            regions.inv(),
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
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
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError>
        requires
            old(owner).inv(),
            old(self).inner.wf(*old(owner)),
            old(self).inner.inv(),
            old(self).inner.level < old(self).inner.guard_level,
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.jump(va)
    }

    /// Gets the current virtual address.
    #[rustc_allow_incoherent_impl]
    pub fn virt_addr(&self) -> Vaddr
        returns
            self.inner.va,
    {
        self.inner.virt_addr()
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn query(&mut self) -> (res: Result<PagesState<C>, PageTableError>)
        requires
            old(owner).inv(),
            old(self).inner.wf(*old(owner)),
            old(self).inner.inv(),
            old(regions).inv(),
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
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
            Tracked(new_owner): Tracked<OwnerSubtree<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn map(&mut self, item: C::Item) -> Result<(), PageTableFrag<C>>
        requires
            old(owner).inv(),
            old(self).inner.wf(*old(owner)),
            old(regions).inv(),
            new_owner.inv(),
            old(self).inner.inv(),
            C::item_into_raw(item).1 < old(self).inner.guard_level,
            old(owner).in_locked_range(),
            // Panic conditions as preconditions
            old(self).inner.va < old(self).inner.barrier_va.end,
            C::item_into_raw(item).1 <= C::HIGHEST_TRANSLATION_LEVEL(),
            !C::TOP_LEVEL_CAN_UNMAP_spec() ==> C::item_into_raw(item).1 < C::NR_LEVELS(),
            old(self).inner.va % page_size(C::item_into_raw(item).1) == 0,
            old(self).inner.va + page_size(C::item_into_raw(item).1) < old(self).inner.barrier_va.end,
    {
        let (pa, level, prop) = C::item_into_raw(item);
        let size = page_size(level);
        let rcu_guard = self.inner.rcu_guard;

        let ghost guard_level = self.inner.guard_level;

        // Adjust ourselves to the level of the item.
        while self.inner.level != level
            invariant
                owner.inv(),
                new_owner.inv(),
                self.inner.wf(*owner),
                regions.inv(),
                self.inner.inv(),
                self.inner.guard_level == guard_level,
                level < guard_level,
                owner.in_locked_range(),
            decreases abs(level - self.inner.level),
        {

            if self.inner.level < level {
                #[verus_spec(with Tracked(owner), Tracked(regions))]
                self.inner.pop_level();
                continue ;
            }
            // We are at a higher level, go down.

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let mut cur_entry = self.inner.cur_entry();

            assert(regions.dropped_slots.contains_key(frame_to_index(cur_entry.pte.paddr()))) by {
                admit()
            };

            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let tracked child_owner = continuation.take_child();
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();

            let tracked Tracked(guard_perm) = guards.guards.tracked_remove(parent_owner.meta_perm.addr());

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner), Tracked(regions), Tracked(&guard_perm))]
            let cur_child = cur_entry.to_ref();

            proof {
                continuation.put_child(child_owner);
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                guards.guards.tracked_insert(parent_owner.meta_perm.addr(), Tracked(guard_perm));
            }

            match cur_child {
                ChildRef::PageTable(pt) => {
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut child_node = child_owner.value.node.tracked_take();

                    // SAFETY: The `pt` must be locked and no other guards exist.
                    #[verus_spec(with Tracked(&child_node), Tracked(guards))]
                    let pt_guard = pt.make_guard_unchecked(rcu_guard);

                    let tracked Tracked(guard_perm) = guards.guards.tracked_remove(child_node.meta_perm.addr());

                    proof {
                        child_owner.value.node = Some(child_node);
                        continuation.put_child(child_owner);
                        assert(continuation.inv());
                        owner.continuations.tracked_insert(owner.level - 1, continuation);
                    }

                    #[verus_spec(with Tracked(owner), Tracked(guard_perm))]
                    self.inner.push_level(pt_guard);
                },
                ChildRef::None => {
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner = continuation.take_child();

                    assert(child_owner.value.is_absent()) by { admit() };

                    proof_decl! {
                        let tracked mut guard_perm;
                    }

                    let child_guard = (
                    #[verus_spec(with Tracked(&mut child_owner), Tracked(regions), Tracked(guards) => Tracked(guard_perm))]
                    cur_entry.alloc_if_none(rcu_guard)).unwrap();

                    proof {
                        continuation.put_child(child_owner);
                        assert(continuation.inv());
                        owner.continuations.tracked_insert(owner.level - 1, continuation);
                    }

                    #[verus_spec(with Tracked(owner), Tracked(guard_perm.tracked_unwrap()))]
                    self.inner.push_level(child_guard);
                },
                ChildRef::Frame(_, _, _) => {
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

                    assert(child_owner.value.is_frame()) by { admit() };

                    let tracked Tracked(guard_perm) = guards.guards.tracked_remove(parent_owner.meta_perm.addr());

                    let split_child = (
                        #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions),
                            Tracked(guards), Tracked(&mut guard_perm))]
                        cur_entry.split_if_mapped_huge(rcu_guard)).unwrap();

                    proof {
                        continuation.put_child(child_owner);
                        continuation.entry_own.node = Some(parent_owner);
                        assert(continuation.inv());
                        owner.continuations.tracked_insert(owner.level - 1, continuation);
                    }

                    #[verus_spec(with Tracked(owner), Tracked(guard_perm))]
                    self.inner.push_level(split_child);
                },
            }
        }

        #[verus_spec(with Tracked(owner), Tracked(new_owner), Tracked(regions), Tracked(guards))]
        let frag = self.replace_cur_entry(Child::Frame(pa, level, prop));

        assert(owner.in_locked_range()) by { admit() };

        #[verus_spec(with Tracked(owner), Tracked(regions))]
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
    pub fn take_next(&mut self, len: usize) -> (r: Option<PageTableFrag<C>>)
        ensures
            self.inner.va == old(self).inner.va + PAGE_SIZE(),
    {
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
        requires
            regions.inv(),
            !old(owner).cur_entry_owner().is_absent(),
    )]
    #[verifier::external_body]
    pub fn protect_next(
        &mut self,
        len: usize,
        op: impl FnOnce(PageProperty) -> PageProperty,
    ) -> Option<Range<Vaddr>> {
        unimplemented!();
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
            mut new_owner: Tracked<OwnerSubtree<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    fn replace_cur_entry(&mut self, new_child: Child<C>) -> (res: Option<PageTableFrag<C>>)
        requires
            old(owner).inv(),
            old(self).inner.inv(),
            new_owner@.inv(),
            old(self).inner.wf(*old(owner)),
            old(regions).inv(),
            !C::TOP_LEVEL_CAN_UNMAP_spec() ==> old(owner).level < C::NR_LEVELS(),
            old(owner).in_locked_range(),
        ensures
            owner.inv(),
            self.inner.inv(),
            self.inner.wf(*owner),
            regions.inv(),
            owner.guard_level == old(owner).guard_level,
            owner.in_locked_range(),
    {
        let ghost guard_level = owner.guard_level;
        let rcu_guard = self.inner.rcu_guard;

        let va = self.inner.va;
        let level = self.inner.level;

        #[verus_spec(with Tracked(owner), Tracked(regions))]
        let mut cur_entry = self.inner.cur_entry();

        assert(regions.dropped_slots.contains_key(frame_to_index(cur_entry.pte.paddr()))) by { admit() };
        assert(!regions.slots.contains_key(frame_to_index(cur_entry.pte.paddr()))) by { admit() };

        let tracked mut continuation = owner.continuations.tracked_remove((owner.level - 1) as int);
        let ghost cont0 = continuation;
        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();
        let tracked old_child_owner = continuation.take_child();

        assert(old_child_owner.level == new_owner@.level) by { admit() };

        let tracked Tracked(guard_perm) = guards.guards.tracked_remove(parent_owner.meta_perm.addr());

        #[verus_spec(with Tracked(regions),
            Tracked(&old_child_owner.value),
            Tracked(&mut new_owner.borrow_mut().value),
            Tracked(&mut parent_owner),
            Tracked(&mut guard_perm)
        )]
        let old = cur_entry.replace(new_child);

        proof {
            assert(old.wf(old_child_owner.value));

            continuation.entry_own.node = Some(parent_owner);
            continuation.put_child(new_owner.get());

            assert(continuation.base_va == cont0.base_va);

            owner.continuations.tracked_insert((owner.level - 1) as int, continuation);
            guards.guards.tracked_insert(parent_owner.meta_perm.addr(), Tracked(guard_perm));
        }

        assert(owner.inv());
        assert(owner.guard_level == guard_level);

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
                if !C::TOP_LEVEL_CAN_UNMAP() {
                    assert(!C::TOP_LEVEL_CAN_UNMAP_spec());
                    if level == C::NR_LEVELS() {
                        assert(owner.level == NR_LEVELS());

                        let _ = NeverDrop::new(pt, Tracked(regions));  // leak it to make shared PTs stay `'static`.
                        assert(false);
                        return None;
                        //                    panic!("Unmapping shared kernel page table nodes");
                    }
                }
                // SAFETY: We must have locked this node.

                assert(old_child_owner.value.is_node()) by { admit() };

                let tracked mut old_node_owner = old_child_owner.value.node.tracked_take();

                assert(pt.paddr() % PAGE_SIZE() == 0) by { admit() };
                assert(pt.paddr() < MAX_PADDR()) by { admit() };
                assert(!regions.slots.contains_key(pt.index())) by { admit() };
                assert(regions.dropped_slots.contains_key(pt.index())) by { admit() };
                assert(pt.ptr == old_node_owner.meta_perm.points_to.pptr()) by { admit() };
                assert(FRAME_METADATA_RANGE().start
                    <= old_node_owner.meta_perm.points_to.addr()
                    < FRAME_METADATA_RANGE().end) by { admit() };
                assert(old_node_owner.meta_perm.points_to.addr() % META_SLOT_SIZE() == 0)
                    by { admit() };

                #[verus_spec(with Tracked(regions), Tracked(&old_node_owner.meta_perm))]
                let borrow_pt = pt.borrow();

                #[verus_spec(with Tracked(&old_node_owner), Tracked(guards))]
                let locked_pt = borrow_pt.make_guard_unchecked(rcu_guard);
                
                let tracked Tracked(guard_perm) = guards.guards.tracked_remove(old_node_owner.meta_perm.addr());

                // SAFETY:
                //  - We checked that we are not unmapping shared kernel page table nodes.
                //  - We must have locked the entire sub-tree since the range is locked.
                #[verus_spec(with Tracked(owner))]
                let num_frames = locking::dfs_mark_stray_and_unlock(rcu_guard, locked_pt);

                assert(regions.inv()) by { admit() };
                assert(owner.inv()) by { admit() };
                assert(self.inner.wf(*owner)) by { admit() };
                assert(owner.guard_level == guard_level) by { admit() };
                assert(owner.in_locked_range()) by { admit() };

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
