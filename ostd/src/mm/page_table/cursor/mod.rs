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
    (PAGE_SIZE() * pow2((nr_subpage_per_huge::<PagingConsts>().ilog2() * (level - 1)) as nat)) as usize
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
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>) -> (res: (Result<(Self, Tracked<CursorOwner<'rcu, C>>), PageTableError>))
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
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
        ensures
            owner.in_locked_range() && self.model(*owner).present() ==> {
                &&& res is Ok
                &&& res.unwrap().0.start == self.va
                &&& res.unwrap().0.end == self.va + page_size(self.level)
                &&& res.unwrap().1 is Some
//                &&& res.unwrap().1.unwrap() == self.model(*owner).query_item_spec()
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
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.relate_region(*regions),
                owner.in_locked_range(),
                !owner.popped_too_high,
            decreases self.level,
        {
            let cur_va = self.va;
            let level = self.level;

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let entry = self.cur_entry();

            let ghost continuations0 = owner.continuations;
            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let ghost cont0 = continuation;
            let tracked child_owner = continuation.take_child();
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner), Tracked(regions), Tracked(&continuation.guard_perm) )]
            let cur_child = entry.to_ref();

            proof {
                assert(cur_child.wf(child_owner.value));
                continuation.put_child(child_owner);
                cont0.take_put_child();
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                assert(owner.continuations == continuations0);
            }

            let item = match cur_child {
                ChildRef::PageTable(pt) => {
                    assert(owner.relate_region(*regions)) by { admit() };

                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut child_node = child_owner.value.node.tracked_take();

                    proof_decl! {
                        let tracked mut guard_perm: Tracked<GuardPerm<'rcu, C>>;
                    }

                    let ghost guards0 = *guards;

                    // SAFETY: The `pt` must be locked and no other guards exist.

                    #[verus_spec(with Tracked(&child_node), Tracked(guards) => Tracked(guard_perm))]
                    let guard = pt.make_guard_unchecked(rcu_guard);

                    proof {
                        child_owner.value.node = Some(child_node);
                        continuation.put_child(child_owner);
                        owner.continuations.tracked_insert(owner.level - 1, continuation);

                        owner.map_children_implies(CursorOwner::node_unlocked(guards0),
                            CursorOwner::node_unlocked_except(*guards, child_node.meta_perm.addr()));

                        assert(owner.relate_region(*regions));
                    }

                    #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
                    self.push_level(guard);

                    continue ;
                },
                ChildRef::None => {
                    assert(owner.cur_entry_owner().is_absent());
                    proof {
                        owner.cur_entry_absent_not_present();
                    }
                    None
                },
                ChildRef::Frame(pa, ch_level, prop) => {
                    assert(owner.cur_entry_owner().is_frame());
                    assert(owner@.present()) by { admit() };

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
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).va + len <= old(self).barrier_va.end,
            !old(owner).popped_too_high,
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
    fn find_next_impl(&mut self, len: usize, find_unmap_subtree: bool, split_huge: bool) -> (res: Option<Vaddr>)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(regions).inv(),
            old(self).inv(),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
            // Panic conditions as preconditions
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).va + len <= old(self).barrier_va.end,
        ensures
            owner.inv(),
            self.inv(),
            self.wf(*owner),
            regions.inv(),
            owner.children_not_locked(*guards),
            owner.nodes_locked(*guards),
            owner.relate_region(*regions),
            res is Some ==> {
                &&& res.unwrap() == self.va
                &&& owner.level < owner.guard_level
                &&& !find_unmap_subtree ==> owner.cur_entry_owner().is_frame()
            },
    {
        let end = self.va + len;
        //        debug_assert_eq!(end % C::BASE_PAGE_SIZE(), 0);

        let rcu_guard = self.rcu_guard;

        while self.va < end
            invariant
                owner.inv(),
                self.inv(),
                self.wf(*owner),
                regions.inv(),
                self.inv(),
                owner.in_locked_range() || self.va >= end,
                end <= self.barrier_va.end,
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.relate_region(*regions),
                !owner.popped_too_high,
            decreases owner.max_steps(),
        {
            let ghost owner0 = *owner;

            let cur_va = self.va;
            #[verus_spec(with Tracked(owner))]
            let cur_va_range = self.cur_va_range();
            let cur_entry_fits_range = cur_va == cur_va_range.start && cur_va_range.end <= end;

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let mut cur_entry = self.cur_entry();

            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let ghost cont0 = continuation;
            let tracked child_owner = continuation.take_child();
            let tracked node_owner = continuation.entry_own.node.tracked_borrow();

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&node_owner), Tracked(regions), Tracked(&continuation.guard_perm))]
            let cur_child = cur_entry.to_ref();

            proof {
                continuation.put_child(child_owner);
                assert(continuation.children == cont0.children);
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                assert(owner.continuations == owner0.continuations);
            }

            assert(owner.relate_region(*regions)) by { admit() };

            match cur_child {
                ChildRef::PageTable(pt) => {
                    if find_unmap_subtree && cur_entry_fits_range &&
                        (C::TOP_LEVEL_CAN_UNMAP() || self.level != C::NR_LEVELS()) {
                        return Some(cur_va);
                    }
                    assert(owner.children_not_locked(*guards));

                    let tracked mut continuation = owner.continuations.tracked_remove(
                        owner.level - 1,
                    );
                    let ghost cont0 = continuation;
                    let tracked mut child_owner = continuation.take_child();

                    let tracked mut parent_node_owner = continuation.entry_own.node.tracked_take();
                    let tracked mut child_node_owner = child_owner.value.node.tracked_take();

                    proof_decl! {
                        let tracked mut guard_perm: Tracked<GuardPerm<'rcu, C>>;
                    }

                    let ghost guards0 = *guards;

                    // SAFETY: The `pt` must be locked and no other guards exist.
                    #[verus_spec(with Tracked(&child_node_owner), Tracked(guards) => Tracked(guard_perm))]
                    let pt_guard = pt.make_guard_unchecked(rcu_guard);

                    #[verus_spec(with Tracked(&mut child_node_owner))]
                    let nr_children = pt_guard.borrow(Tracked(&guard_perm)).nr_children();

                    proof {
                        child_owner.value.node = Some(child_node_owner);
                        continuation.put_child(child_owner);
                        continuation.entry_own.node = Some(parent_node_owner);
                        assert(cont0.children == continuation.children);
                        owner.continuations.tracked_insert(self.level - 1, continuation);
                        assert(owner.continuations == owner0.continuations);

                        owner.map_children_implies(CursorOwner::node_unlocked(guards0),
                            CursorOwner::node_unlocked_except(*guards, child_node_owner.meta_perm.addr()));
                    }

                    assert(owner.only_current_locked(*guards));

                    // If there's no mapped PTEs in the next level, we can
                    // skip to save time.
                    if (nr_children != 0) {
                        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
                        self.push_level(pt_guard);
                    } else {
                        let ghost guards0 = *guards;

                        let _ = NeverDrop::new(pt_guard.take(Tracked(&mut guard_perm)), Tracked(guards));
                        proof {
                            assert(owner.children_not_locked(*guards)) by { admit() };

                            owner.move_forward_increases_va();
                            owner.move_forward_not_popped_too_high();
                        }

                        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
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
                        owner.move_forward_not_popped_too_high();
                    }

                    // These predicates are established by the loop invariants

                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
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
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

                    let split_child = (
                    #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions),
                        Tracked(guards), Tracked(&mut continuation.guard_perm))]
                    cur_entry.split_if_mapped_huge(rcu_guard)).expect("The entry must be a huge page");

                    assert(guards.locked(child_owner.value.node.unwrap().meta_perm.addr()));
                    assert(guards.guards[child_owner.value.node.unwrap().meta_perm.addr()] is Some);
                    let tracked guard_perm = guards.take(child_owner.value.node.unwrap().meta_perm.addr());

                    proof {
                        continuation.put_child(child_owner);
                        continuation.entry_own.node = Some(parent_owner);
                        assert(continuation.inv()) by { admit() };
                        owner.continuations.tracked_insert(owner.level - 1, continuation);

                        owner0.max_steps_partial_inv(*owner, owner.level as usize);

                        assert(guard_perm.addr() == child_owner.value.node.unwrap().meta_perm.addr());
                        assert(guard_perm.addr() == split_child.addr());
                    }

                    assert(owner.relate_region(*regions)) by { admit() };
                    assert(owner.children_not_locked(*guards)) by { admit() };
                    assert(owner.nodes_locked(*guards)) by { admit() };

                    #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
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
            #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
            self.pop_level();
        }
    }

    /// Traverses forward to the end of [`Self::cur_va_range`].
    //
    /// If reached the end of the current page table node, it (recursively)
    /// moves itself up to the next page of the parent page.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    fn move_forward(&mut self)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(self).inv(),
            old(regions).inv(),
            old(owner).in_locked_range(),
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
        ensures
    //            self.model(*owner) == old(self).model(*old(owner)).move_forward_spec(),
            owner.inv(),
            self.wf(*owner),
            self.inv(),
            regions.inv(),
            *owner == old(owner).move_forward_owner_spec(),
            owner.max_steps() < old(owner).max_steps(),
            self.barrier_va == old(self).barrier_va,
            self.guard_level == old(self).guard_level,
            !owner.popped_too_high,
            owner.children_not_locked(*guards),
            owner.nodes_locked(*guards),
            owner.relate_region(*regions),
            owner.va == old(owner).va.align_up(old(self).level as int),
    {
        let ghost owner0 = *owner;
        proof {
            owner.move_forward_owner_decreases_steps();
            old(owner).move_forward_not_popped_too_high();
        }

        let ghost start_level = self.level;
        let ghost guard_level = self.guard_level;
        let ghost barrier_va = self.barrier_va;
        let ghost va = self.va;

        let next_va = (#[verus_spec(with Tracked(owner))] self.cur_va_range()).end;
        
        let ghost abs_va_down = owner0.va.align_down((start_level - 1) as int);
        let ghost abs_next_va = AbstractVaddr::from_vaddr(next_va);

        proof {
            AbstractVaddr::reflect_from_vaddr(next_va);
            owner0.va.reflect_prop(va);
            owner0.va.align_down_inv((start_level - 1) as int);
            owner0.va.align_down_concrete(start_level - 1);
            owner0.va.align_down(start_level - 1).reflect_prop(nat_align_down(va as nat, page_size((start_level-1) as PagingLevel) as nat) as Vaddr);
            abs_next_va.reflect_prop(next_va);
            
            AbstractVaddr::reflect_eq(abs_next_va, owner0.va.align_up(start_level as int), next_va);
            assert(abs_next_va == owner0.va.align_up(start_level as int));
            assert(abs_next_va == owner0.va.align_down((start_level - 1) as int).next_index(start_level as int));

            AbstractVaddr::from_vaddr_wf(self.va);
            abs_va_down.next_index_wrap_condition(start_level as int);
        }

        while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0
            invariant
                owner.inv(),
                self.wf(*owner),
                self.inv(),
                regions.inv(),
                self.guard_level == guard_level,
                self.barrier_va == barrier_va,
                owner0.va.reflect(va),
                abs_next_va == AbstractVaddr::from_vaddr(next_va),
                owner.move_forward_owner_spec() == owner0.move_forward_owner_spec(),
                abs_va_down.next_index(start_level as int) == abs_next_va,
                abs_va_down.wrapped(start_level as int, self.level as int),
                1 <= start_level <= self.level <= self.guard_level <= NR_LEVELS(),
                forall|i: int|
                    start_level <= i < NR_LEVELS() ==> #[trigger] owner0.va.index[i - 1]
                        == abs_va_down.index[i - 1],
                forall|i: int|
                    self.level <= i < NR_LEVELS() ==> #[trigger] owner0.va.index[i - 1]
                        == owner.continuations[i - 1].idx,
                owner.in_locked_range(),
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.relate_region(*regions),
            decreases self.guard_level - self.level,
        {
            proof {
                assert(abs_next_va.index[self.level - 1] == 0);
                abs_va_down.wrapped_unwrap(start_level as int, self.level as int);
                abs_va_down.use_wrapped(start_level as int, self.level as int);
                assert(owner0.va.index[self.level - 1] + 1 == NR_ENTRIES());
                assert(owner.move_forward_owner_spec()
                    == owner.pop_level_owner_spec().0.move_forward_owner_spec());
                owner.pop_level_owner_preserves_invs(*guards, *regions);
            }

            #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
            self.pop_level();
        }

        let ghost index = abs_next_va.index[self.level - 1];
        assert(self.level >= self.guard_level || index != 0);
        assert(self.level < self.guard_level) by { admit() };

        assert(owner0.va.index[self.level - 1] + 1 < NR_ENTRIES());
        assert(owner.move_forward_owner_spec() == owner0.move_forward_owner_spec());
        assert(owner.move_forward_owner_spec() == owner.inc_index().zero_below_level());
        
        self.va = next_va;

        proof {
            owner.do_inc_index();
            owner.zero_preserves_all_but_va();
            owner.do_zero_below_level();
            assert(abs_next_va == owner0.va.align_up(start_level as int));
            assert(owner.va == abs_next_va) by { admit() };
        }
    }

    /// Goes up a level.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    fn pop_level(&mut self)
        requires
            old(self).level < old(self).guard_level,
            old(self).inv(),
            old(owner).inv(),
            old(regions).inv(),
            old(self).wf(*old(owner)),
            old(owner).in_locked_range(),
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
        ensures
            owner.inv(),
            self.wf(*owner),
            self.inv(),
            regions.inv(),
            self.guard_level == old(self).guard_level,
            *owner == old(owner).pop_level_owner_spec().0,
            owner.children_not_locked(*guards),
            owner.nodes_locked(*guards),
            owner.relate_region(*regions),
    {
        proof {
            let ghost child_cont = owner.continuations[owner.level - 1];
            assert(child_cont.all_some());
            assert(child_cont.inv());
            assert(self.path[self.level as usize - 1] is Some);
            assert(self.path[self.level as usize - 1].unwrap().addr() == owner.continuations[owner.level - 1].guard_perm.addr());
            assert(guards.lock_held(owner.continuations[owner.level - 1].guard_perm.value().inner.inner@.ptr.addr()));
            owner.pop_level_owner_preserves_invs(*guards, *regions);
        }
        let tracked Tracked(guard_perm) = owner.pop_level_owner();

        let ghost owner0 = *owner;
        let ghost guards0 = *guards;
        let ghost guard = guard_perm.value();

        let taken : Option<PPtr<PageTableGuard<'rcu, C>>> = *self.path.get(self.level as usize - 1).unwrap();
        let _ = NeverDrop::new(taken.unwrap().take(Tracked(&mut guard_perm)), Tracked(guards));

        proof {
            owner.never_drop_preserves_children_not_locked(guard, guards0, *guards);
        }

        self.level = self.level + 1;

        assert(self.wf(*owner));
    }

    /// Goes down a level to a child page table.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(guard_perm): Tracked<GuardPerm<'rcu, C>>,
            Tracked(regions): Tracked<&MetaRegionOwners>,
            Tracked(guards): Tracked<&Guards<'rcu, C>>
    )]
    fn push_level(&mut self, child_pt: PPtr<PageTableGuard<'rcu, C>>)
        requires
            old(owner).inv(),
            regions.inv(),
            old(self).inv(),
            old(self).wf(*old(owner)),
            old(owner).cur_entry_owner().is_node(),
            old(owner).cur_entry_owner().node.unwrap().relate_guard_perm(guard_perm),
            guard_perm.addr() == child_pt.addr(),
            old(owner).in_locked_range(),
            old(owner).only_current_locked(*guards),
            old(owner).nodes_locked(*guards),
            old(owner).relate_region(*regions),
            !old(owner).popped_too_high,
        ensures
            owner.inv(),
            owner.children_not_locked(*guards),
            owner.nodes_locked(*guards),
            owner.relate_region(*regions),
            self.inv(),
            self.wf(*owner),
            self.guard_level == old(self).guard_level,
            self.level == old(self).level - 1,
            self.va == old(self).va,
            owner == old(owner).push_level_owner_spec(guard_perm),
            owner.max_steps() < old(owner).max_steps(),
    {
        assert(owner.va.index.contains_key(owner.level - 2));

        self.level = self.level - 1;
        //        debug_assert_eq!(self.level, child_pt.level());

        //        let old = self.path.get(self.level as usize - 1);
        self.path.set(self.level as usize - 1, Some(child_pt));

        proof {
            owner.push_level_owner_preserves_invs(guard_perm, *regions, *guards);
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
            old(owner).relate_region(*regions),
        ensures
            owner.inv(),
            self.inv(),
            self.wf(*owner),
            res.wf(owner.cur_entry_owner()),
            self == old(self),
            owner == old(owner),
            owner.continuations[owner.level - 1].guard_perm.addr() == res.node.addr(),
            owner.relate_region(*regions),
    {
        let ghost owner0 = *owner;

        let node = self.path[self.level as usize - 1].unwrap();
        let tracked mut parent_continuation = owner.continuations.tracked_remove(owner.level - 1);

        assert(parent_continuation.inv());
        let ghost cont0 = parent_continuation;
        let tracked parent_own = parent_continuation.entry_own.node.tracked_take();
        let tracked child = parent_continuation.take_child();

        let ghost index = frame_to_index(meta_to_frame(parent_own.meta_perm.addr));

        let ghost ptei = AbstractVaddr::from_vaddr(self.va).index[owner.level - 1];

        proof {
            AbstractVaddr::from_vaddr_wf(self.va);
            let ghost abs_va = AbstractVaddr::from_vaddr(self.va);
            assert(abs_va.inv());

            let ghost i = owner.level - 1;
            assert(0 <= i < NR_LEVELS());
            assert(abs_va.index.contains_key(i));
            assert(abs_va.index[i] < NR_ENTRIES());
        }

        // TODO: this requires the relation between OwnerSubtree and NodeOwner
        assert(child.value.match_pte(
            parent_own.children_perm.value()[ptei as int],
            parent_own.level,
        )) by { admit() };

        #[verus_spec(with Tracked(&parent_own),
            Tracked(&child.value),
            Tracked(&parent_continuation.guard_perm))]
        let res = PageTableGuard::entry(node, pte_index::<C>(self.va, self.level));

        proof {
            parent_continuation.entry_own.node = Some(parent_own);
            parent_continuation.put_child(child);
            assert(parent_continuation.children == cont0.children);
            owner.continuations.tracked_insert((owner.level - 1) as int, parent_continuation);
            assert(owner.continuations == owner0.continuations);
        }

        res
    }

    /// Gets the virtual address range that the current entry covers.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&CursorOwner<C>>
    )]
    fn cur_va_range(&self) -> (res: Range<Vaddr>)
        requires
            owner.inv(),
            self.wf(*owner),
        ensures
            owner.va.align_down(self.level as int).reflect(res.start),
            owner.va.align_up(self.level as int).reflect(res.end),
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

#[verus_verify]
impl<'rcu, C: PageTableConfig, A: InAtomicMode> CursorMut<'rcu, C, A> {
    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to map, query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>)
        -> Result<(Self, Tracked<CursorOwner<'rcu, C>>), PageTableError> {
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
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).inner.va + len <= old(self).inner.barrier_va.end,
            !old(owner).popped_too_high,
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
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.query()
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(owner).inv(),
            old(self).inner.wf(*old(owner)),
            old(self).inner.inv(),
            old(regions).inv(),
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
            ChildRef::PageTable(pt).wf(old(owner).cur_entry_owner())
        ensures
            owner.inv(),
            owner.va == old(owner).va,
            self.inner.wf(*owner),
            regions.inv(),
            self.inner.inv(),
            owner.in_locked_range(),
            owner.children_not_locked(*guards),
            owner.nodes_locked(*guards),
            owner.relate_region(*regions),
            !owner.popped_too_high,
            self.inner.level == old(self).inner.level - 1,
            self.inner.guard_level == old(self).inner.guard_level,
    )]
    fn map_branch_pt(&mut self, pt: PageTableNodeRef<'rcu, C>, rcu_guard: &'rcu A)
    {
        let ghost guards0 = *guards;

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let tracked mut child_owner = continuation.take_child();
        let tracked mut child_node = child_owner.value.node.tracked_take();

        proof_decl! {
            let tracked mut guard_perm: Tracked<GuardPerm<'rcu, C>>;
        }

        // SAFETY: The `pt` must be locked and no other guards exist.
        #[verus_spec(with Tracked(&child_node), Tracked(guards) => Tracked(guard_perm))]
        let pt_guard = pt.make_guard_unchecked(rcu_guard);

        proof {
            child_owner.value.node = Some(child_node);
            continuation.put_child(child_owner);
            owner.continuations.tracked_insert(owner.level - 1, continuation);

            owner.map_children_implies(CursorOwner::node_unlocked(guards0),
                CursorOwner::node_unlocked_except(*guards, child_node.meta_perm.addr()));
        }

        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
        self.inner.push_level(pt_guard);
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    requires
        old(owner).inv(),
        old(self).inner.wf(*old(owner)),
        old(self).inner.inv(),
        old(regions).inv(),
        old(owner).children_not_locked(*old(guards)),
        old(owner).nodes_locked(*old(guards)),
        old(owner).relate_region(*old(regions)),
        old(owner).in_locked_range(),
        !old(owner).popped_too_high,
        old(cur_entry).wf(old(owner).cur_entry_owner()),
        ChildRef::None.wf(old(owner).cur_entry_owner())
    ensures
        owner.inv(),
        owner.va == old(owner).va,
        self.inner.wf(*owner),
        regions.inv(),
        self.inner.inv(),
        owner.in_locked_range(),
        owner.children_not_locked(*guards),
        owner.nodes_locked(*guards),
        owner.relate_region(*regions),
        !owner.popped_too_high,
        self.inner.level == old(self).inner.level - 1,
        self.inner.guard_level == old(self).inner.guard_level,
    )]
    fn map_branch_none(&mut self, cur_entry: &mut Entry<'rcu, C>, rcu_guard: &'rcu A)
    {
        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let tracked mut child_owner = continuation.take_child();

        proof_decl! {
            let tracked mut guard_perm;
        }

        let child_guard = (
        #[verus_spec(with Tracked(&mut child_owner), Tracked(regions), Tracked(guards), Tracked(&mut continuation.guard_perm) => Tracked(guard_perm))]
        cur_entry.alloc_if_none(rcu_guard)).unwrap();

        proof {
            continuation.put_child(child_owner);
            owner.continuations.tracked_insert(owner.level - 1, continuation);
        }

        assert(owner.only_current_locked(*guards)) by { admit() };
        assert(owner.relate_region(*regions)) by { admit() };
        assert(owner.inv()) by { admit() };

        #[verus_spec(with Tracked(owner), Tracked(guard_perm.tracked_unwrap()), Tracked(regions), Tracked(guards))]
        self.inner.push_level(child_guard);
    }


    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    requires
        old(owner).inv(),
        old(self).inner.wf(*old(owner)),
        old(self).inner.inv(),
        old(regions).inv(),
        old(owner).children_not_locked(*old(guards)),
        old(owner).nodes_locked(*old(guards)),
        old(owner).relate_region(*old(regions)),
        old(owner).in_locked_range(),
        !old(owner).popped_too_high,
        old(cur_entry).wf(old(owner).cur_entry_owner()),
        old(owner).cur_entry_owner().is_frame(),
        old(cur_entry).node.addr() == old(owner).continuations[old(owner).level - 1].guard_perm.addr()
    ensures
        owner.inv(),
        owner.va == old(owner).va,
        self.inner.wf(*owner),
        regions.inv(),
        self.inner.inv(),
        owner.in_locked_range(),
        owner.children_not_locked(*guards),
        owner.nodes_locked(*guards),
        owner.relate_region(*regions),
        !owner.popped_too_high,
        self.inner.level == old(self).inner.level - 1,
        self.inner.guard_level == old(self).inner.guard_level,
    )]
    fn map_branch_frame(&mut self, cur_entry: &mut Entry<'rcu, C>, rcu_guard: &'rcu A)
    {
        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let tracked mut child_owner = continuation.take_child();
        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        let split_child = (
        #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions),
                Tracked(guards), Tracked(&mut continuation.guard_perm))]
        cur_entry.split_if_mapped_huge(rcu_guard)).unwrap();

        proof {
            continuation.put_child(child_owner);
            continuation.entry_own.node = Some(parent_owner);
            assert(continuation.inv()) by { admit() };
            owner.continuations.tracked_insert(owner.level - 1, continuation);
            assert(self.inner.wf(*owner));
            assert(child_owner.value == owner.cur_entry_owner());
        }

        assert(guards.locked(child_owner.value.node.unwrap().meta_perm.addr()));
        assert(guards.guards[child_owner.value.node.unwrap().meta_perm.addr()] is Some);
        let tracked child_guard_perm = guards.take(child_owner.value.node.unwrap().meta_perm.addr());

        assert(child_owner.value.node.unwrap().relate_guard_perm(child_guard_perm));
        assert(child_owner.value.node.unwrap().meta_perm.addr() == split_child.addr());

        assert(owner.children_not_locked(*guards)) by { admit() };
        assert(owner.nodes_locked(*guards)) by { admit() };
        assert(owner.relate_region(*regions)) by { admit() };

        #[verus_spec(with Tracked(owner), Tracked(child_guard_perm), Tracked(regions), Tracked(guards))]
        self.inner.push_level(split_child);
    }

    /// In order for the function to not panic, the current virtual address must be within the barrier range,
    /// the level of the item to be mapped must be within the highest translation level,
    /// the item must be aligned to the page size, at its level,
    /// and the virtual address range to be mapped must not exceed the barrier range.
    /// If the page table config doesn't allow the top level to be unmapped, then the item must also not be at the top level.
    pub open spec fn map_panic_conditions(self, item: C::Item) -> bool {
        &&& self.inner.va < self.inner.barrier_va.end
        &&& C::item_into_raw(item).1 <= C::HIGHEST_TRANSLATION_LEVEL()
        &&& !C::TOP_LEVEL_CAN_UNMAP_spec() ==> C::item_into_raw(item).1 < C::NR_LEVELS()
        &&& self.inner.va % page_size(C::item_into_raw(item).1) == 0
        &&& self.inner.va + page_size(C::item_into_raw(item).1) <= self.inner.barrier_va.end
    }

    pub open spec fn map_cursor_inv(
        self,
        owner: CursorOwner<'rcu, C>,
        guards: Guards<'rcu, C>,
        regions: MetaRegionOwners,
    ) -> bool {
        &&& owner.inv()
        &&& self.inner.wf(owner)
        &&& self.inner.inv()
        &&& owner.children_not_locked(guards)
        &&& owner.nodes_locked(guards)
        &&& !owner.popped_too_high
        &&& regions.inv()
        &&& owner.relate_region(regions)
    }

    pub open spec fn map_cursor_requires(
        self,
        owner: CursorOwner<'rcu, C>,
        guards: Guards<'rcu, C>,
    ) -> bool {
        &&& owner.in_locked_range()
        &&& self.inner.level < self.inner.guard_level
        &&& self.inner.va < self.inner.barrier_va.end
    }

    pub open spec fn map_item_requires(
        self,
        item: C::Item,
        entry_owner: EntryOwner<C>,
    ) -> bool {
        &&& entry_owner.inv()
        &&& self.inner.va % page_size(C::item_into_raw(item).1) == 0
        &&& self.inner.va + page_size(C::item_into_raw(item).1) <= self.inner.barrier_va.end
        &&& C::item_into_raw(item).1 < self.inner.guard_level
        &&& Child::Frame(
            C::item_into_raw(item).0,
            C::item_into_raw(item).1,
            C::item_into_raw(item).2,
        ).wf(entry_owner)
    }

    pub open spec fn map_item_mapping(
        self,
        item: C::Item,
    ) -> Mapping {
        let (pa, level, prop) = C::item_into_raw(item);
        let size = page_size(level);
        Mapping {
            va_range: self.inner.va..(self.inner.va + size) as usize,
            pa_range: pa..(pa + size) as usize,
            page_size: size,
            property: prop,
        }
    }

    pub open spec fn map_item_ensures(
        self,
        item: C::Item,
        old_view: CursorView<C>,
        new_view: CursorView<C>,
    ) -> bool {
        let mapping = self.map_item_mapping(item);
        new_view == old_view.map_spec(mapping.pa_range.start, mapping.page_size, mapping.property)
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
            Tracked(entry_owner): Tracked<EntryOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn map(&mut self, item: C::Item) -> (res: Result<(), PageTableFrag<C>>)
        requires
            old(self).map_cursor_inv(*old(owner), *old(guards), *old(regions)),
            old(self).map_cursor_requires(*old(owner), *old(guards)),
            old(self).map_item_requires(item, entry_owner),
            old(self).map_panic_conditions(item),
        ensures
            self.map_cursor_inv(*owner, *guards, *regions),
            old(self).map_item_ensures(item, old(self).inner.model(*old(owner)), self.inner.model(*owner)),
    {
        let ghost self0 = *self;
        let ghost owner0 = *owner;

        let (pa, level, prop) = C::item_into_raw(item);
        let size = page_size(level);

        let rcu_guard = self.inner.rcu_guard;

        let ghost guard_level = self.inner.guard_level;

        // Adjust ourselves to the level of the item.
        while self.inner.level != level
            invariant
                owner.inv(),
                owner.va == owner0.va,
                self.inner.wf(*owner),
                regions.inv(),
                self.inner.inv(),
                self.inner.guard_level == guard_level,
                level < guard_level,
                owner.in_locked_range(),
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.relate_region(*regions),
                !owner.popped_too_high,
            decreases abs(level - self.inner.level),
        {
            if self.inner.level < level {
                proof {
                    owner.pop_level_owner_preserves_invs(*guards, *regions);
                }

                #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                self.inner.pop_level();
                
                continue ;
            }
            // We are at a higher level, go down.

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let mut cur_entry = self.inner.cur_entry();

            // Capture state before modifications
            let ghost owner_before = *owner;
            let ghost regions_before = *regions;
            let ghost cont0 = owner.continuations[owner.level - 1];
            
            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let tracked child_owner = continuation.take_child();
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner), Tracked(regions), Tracked(&continuation.guard_perm))]
            let cur_child = cur_entry.to_ref();

            proof {
                cont0.take_put_child();
                continuation.put_child(child_owner);
                assert(continuation == cont0);
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                
                assert(*regions =~= regions_before);
                assert(owner.continuations =~= owner_before.continuations);
                assert(owner.level == owner_before.level);
                owner_before.relate_region_preserved(*owner, *regions);
            }

            assert(owner.relate_region(*regions));

            match cur_child {
                ChildRef::PageTable(pt) => {
                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.map_branch_pt(pt, rcu_guard);

                    continue ;
                },
                ChildRef::None => {
                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.map_branch_none(&mut cur_entry, rcu_guard);

                    continue ;
                },
                ChildRef::Frame(_, _, _) => {
                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.map_branch_frame(&mut cur_entry, rcu_guard);

                    continue ;
                },
            }
        }

        assert(owner.va == owner0.va);
        assert(self.inner.level == level);

        let ghost owner1 = *owner;
        // Not actually true because of the possibility of 'split if huge' happening. Need to adjust spec for that.
        assert(owner1@.mappings == owner0@.mappings) by { admit() };

        proof_decl! {
            let tracked new_owner = owner.continuations.tracked_borrow(owner.level - 1).new_child(pa, prop);
        }

        #[verus_spec(with Tracked(owner), Tracked(new_owner), Tracked(regions), Tracked(guards))]
        let frag = self.replace_cur_entry(Child::Frame(pa, level, prop));

        let ghost owner2 = *owner;
        assert(owner2@.mappings == owner1@.mappings - PageTableOwner(owner1.cur_subtree())@.mappings + PageTableOwner(new_owner)@.mappings);

        let ghost mapping = self0.map_item_mapping(item);

        assert(PageTableOwner(owner1.cur_subtree())@.mappings == owner0@.mappings.filter(|m: Mapping|
            owner0@.cur_va <= m.va_range.start < m.va_range.end <= owner0@.cur_va + page_size(level))) by { admit() };
        assert(PageTableOwner(new_owner)@.mappings == set![mapping]) by { admit() };

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.move_forward();

        let ghost target_va = owner0@.map_spec(mapping.pa_range.start, mapping.page_size, mapping.property).cur_va;

        proof {    
            owner.va.reflect_prop(self.inner.va);
            owner2.va.align_up_concrete(level as int);
            owner.va.reflect_prop(nat_align_up(owner1.va.to_vaddr() as nat, page_size(level) as nat) as Vaddr);
        }

        let ghost original = owner0@.mappings.filter(|m: Mapping| owner0@.cur_va <= m.va_range.start < m.va_range.end <= owner0@.cur_va + page_size(level));
        assert(owner@.mappings == owner0@.mappings - original + set![mapping]) by { admit() };
        assert(self0.map_item_ensures(item, owner0@, owner@)) by { admit() };

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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(regions).inv(),
            old(owner).inv(),
            old(self).inner.wf(*old(owner)),
            old(self).inner.inv(),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).inner.va + len <= old(self).inner.barrier_va.end,
            old(self).inner.level < NR_LEVELS(),
//            op.requires((old(self).inner.cur_entry().pte.prop(),)),
    )]
    pub fn protect_next(
        &mut self,
        len: usize,
        op: impl FnOnce(PageProperty) -> PageProperty,
    ) -> Option<Range<Vaddr>>
    {
        (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.find_next_impl(len, false, true))?;

        #[verus_spec(with Tracked(owner), Tracked(regions))]
        let mut entry = self.inner.cur_entry();

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let tracked mut child_owner = continuation.take_child();
        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        assert(op.requires((entry.pte.prop(),))) by { admit() };

        #[verus_spec(with Tracked(&mut child_owner.value), Tracked(&mut parent_owner), Tracked(&mut continuation.guard_perm))]
        entry.protect(op);

        proof {
            assert(child_owner.inv());
            continuation.put_child(child_owner);
            continuation.entry_own.node = Some(parent_owner);
            owner.continuations.tracked_insert(owner.level - 1, continuation);
        }

        #[verus_spec(with Tracked(owner))]
        let protected_va = self.inner.cur_va_range();

        assert(owner.in_locked_range()) by { admit() };
        assert(owner.children_not_locked(*guards)) by { admit() };
        assert(owner.relate_region(*regions)) by { admit() };

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.move_forward();

        Some(protected_va)
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(new_owner): Tracked<OwnerSubtree<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    fn replace_cur_entry(&mut self, new_child: Child<C>) -> (res: Option<PageTableFrag<C>>)
        requires
            old(owner).inv(),
            old(self).inner.inv(),
            new_owner.inv(),
            old(self).inner.wf(*old(owner)),
            old(regions).inv(),
            !C::TOP_LEVEL_CAN_UNMAP_spec() ==> old(owner).level < C::NR_LEVELS(),
            old(owner).in_locked_range(),
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
            !old(owner).popped_too_high,
            new_owner.level == old(owner).continuations[old(owner).level - 1].tree_level + 1,
            new_owner.value.parent_level == old(owner).continuations[old(owner).level - 1].child().value.parent_level,
            new_owner.value.path == old(owner).continuations[old(owner).level - 1].path().push_tail(old(owner).continuations[old(owner).level - 1].idx as usize),
            new_child.wf(new_owner.value),
        ensures
            owner@.mappings == old(owner)@.mappings -
                               PageTableOwner(old(owner).cur_subtree())@.mappings +
                               PageTableOwner(new_owner)@.mappings,
            owner.inv(),
            owner.va == old(owner).va,
            self.inner.inv(),
            self.inner.wf(*owner),
            self.inner.level == old(self).inner.level,
            regions.inv(),
            owner.guard_level == old(owner).guard_level,
            owner.in_locked_range(),
            owner.children_not_locked(*guards),
            owner.nodes_locked(*guards),
            owner.relate_region(*regions),
            !owner.popped_too_high,
    {
        let ghost owner0 = *owner;
        let ghost guard_level = owner.guard_level;
        let rcu_guard = self.inner.rcu_guard;

        let va = self.inner.va;
        let level = self.inner.level;

        #[verus_spec(with Tracked(owner), Tracked(regions))]
        let mut cur_entry = self.inner.cur_entry();

        let tracked mut continuation = owner.continuations.tracked_remove((owner.level - 1) as int);
        let ghost cont0 = continuation;
        let ghost owner1 = *owner;
        let tracked old_child_owner = continuation.take_child();

        let ghost cont1 = continuation;
        assert(cont1.view_mappings() == cont0.view_mappings() - cont0.view_mappings_take_child_spec()) by {
            cont0.view_mappings_take_child();
            assert(cont1 == cont0.take_child_spec().1);
        }
        assert(owner.continuations == owner0.continuations.remove(owner.level - 1));

        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        #[verus_spec(with Tracked(regions),
            Tracked(&old_child_owner.value),
            Tracked(&new_owner.value),
            Tracked(&mut parent_owner),
            Tracked(&mut continuation.guard_perm)
        )]
        let old = cur_entry.replace(new_child);

        proof {
            continuation.entry_own.node = Some(parent_owner);
            continuation.put_child(new_owner);
            cont1.view_mappings_put_child(new_owner);
            owner.continuations.tracked_insert((owner.level - 1) as int, continuation);

            owner0.view_mappings_take_lowest(owner1);
            owner1.view_mappings_put_lowest(*owner, continuation);
            assert(owner@.mappings == owner0@.mappings - PageTableOwner(owner0.cur_subtree())@.mappings + PageTableOwner(new_owner)@.mappings);
        }

        assert(owner.children_not_locked(*guards)) by { admit() };
        assert(owner.relate_region(*regions)) by { admit() };

        let result = match old {
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

                let ghost owner2 = *owner;

                let tracked mut old_node_owner = old_child_owner.value.node.tracked_take();

                #[verus_spec(with Tracked(regions), Tracked(&old_node_owner.meta_perm))]
                let borrow_pt = pt.borrow();

                proof_decl! {
                    let tracked mut guard_perm: Tracked<GuardPerm<'rcu, C>>;
                }

                let ghost guards0 = *guards;

                #[verus_spec(with Tracked(&old_node_owner), Tracked(guards) => Tracked(guard_perm))]
                let locked_pt = borrow_pt.make_guard_unchecked(rcu_guard);

                proof {
                    assert(owner.inv()) by { admit() };
                    owner.map_children_implies(CursorOwner::node_unlocked(guards0),
                        CursorOwner::node_unlocked_except(*guards, old_node_owner.meta_perm.addr()));
                    assert(owner.inv()) by { admit() };
                }

                // SAFETY:
                //  - We checked that we are not unmapping shared kernel page table nodes.
                //  - We must have locked the entire sub-tree since the range is locked.
                #[verus_spec(with Tracked(owner))]
                let num_frames = locking::dfs_mark_stray_and_unlock(rcu_guard, locked_pt);

                assert(owner.children_not_locked(*guards)) by { admit() };
                assert(owner.nodes_locked(*guards)) by { admit() };
                assert(owner.relate_region(*regions)) by { admit() };

                assert(owner@.mappings == owner2@.mappings) by { admit() };

                Some(
                    PageTableFrag::StrayPageTable {
                        pt: pt.into(),
                        va,
                        len: page_size(self.inner.level),
                        num_frames,
                    },
                )
            },
        };

        result
    }
}

} // verus!
