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
use vstd_extra::drop_tracking::ManuallyDrop;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::Frame;
use crate::mm::page_table::*;
use crate::mm::{Paddr, Vaddr, MAX_NR_LEVELS, MAX_PADDR};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::mm::frame::mapping::{frame_to_index, frame_to_index_spec, frame_to_meta, max_meta_slots, meta_addr, meta_to_frame, META_SLOT_SIZE};
use crate::specs::mm::frame::meta_owners::{MetaSlotOwner, REF_COUNT_UNUSED};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::page_size_lemmas::*;

use core::{fmt::Debug, marker::PhantomData, ops::Range};

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
pub struct Cursor<'rcu, C: PageTableConfig, A: InAtomicMode> {
    /// The current path of the cursor.
    ///
    /// The level 1 page table lock guard is at index 0, and the level N page
    /// table lock guard is at index N - 1.
    pub path: [Option<PPtr<PageTableGuard<'rcu, C>>>; NR_LEVELS],
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
    (PAGE_SIZE * pow2(
        (nr_subpage_per_huge::<PagingConsts>().ilog2() * (level - 1)) as nat,
    )) as usize
}

/// The page size at a given level.
#[verifier::when_used_as_spec(page_size_spec)]
#[verifier::external_body]
pub fn page_size(level: PagingLevel) -> (ret: usize)
    requires
        1 <= level <= NR_LEVELS + 1,
    ensures
        ret == page_size_spec(level),
        exists|e| ret == pow2(e),
        ret >= 2,
{
    PAGE_SIZE << (nr_subpage_per_huge::<PagingConsts>().ilog2() as usize * (level as usize - 1))
}


/// Borrows a live `PageTableNode` as a `PageTableNodeRef` without requiring
/// `raw_count == 1`.
///
/// ## Justification
/// `Child::from_pte` (called inside `Entry::replace`) invokes `PageTableNode::from_raw`,
/// which sets `regions.slot_owners[idx].raw_count = 0` and marks the entry owner
/// `in_scope = true`.  Consequently `relate_region` reports `raw_count == 0`, but
/// `Frame::borrow` / `FrameRef::borrow_paddr` require `raw_count == 1`.
///
/// This function bridges that gap: we have unique ownership of the live frame `pt`
/// (just returned from `Entry::replace`), so borrowing it as a `PageTableNodeRef`
/// is semantically sound.  The `raw_count == 1` requirement in `borrow_paddr` is an
/// accounting invariant designed for *forgotten* frames stored in PTEs; it does not
/// apply to live frames held directly.
///
/// ## Fix path
/// The proper fix is:
///   1. Add `ensures old(owner).is_node() ==> regions.slots.contains_key(...)` to
///      `Entry::replace` (derivable from `Child::from_pte`'s `from_pte_regions_spec`).
///   2. Replace this call with `pt.into_raw()` + `PageTableNodeRef::borrow_paddr()`.

/// A fragment of a page table that can be taken out of the page table.
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

    #[verus_spec(
        with Tracked(slot_perm): Tracked<&PointsTo<MetaSlot>>,
        Tracked(rc_perm): Tracked<&mut PermissionU64>)]
    pub fn clone_item(item: &C::Item) -> (res: C::Item)
        requires
            item.clone_requires(*slot_perm, *old(rc_perm)),
            old(rc_perm).is_for(slot_perm.value().ref_count),
            old(rc_perm).value() < u64::MAX,
        ensures
            res == *item,
            rc_perm.value() == old(rc_perm).value() + 1,
    {
        item.clone(Tracked(slot_perm), Tracked(rc_perm))
    }

    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[verus_spec(r =>
        with Tracked(pt_own): Tracked<PageTableOwner<C>>,
            Tracked(guard_perm): Tracked<PointsTo<PageTableGuard<'rcu, C>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            pt_own.inv(),
        ensures
            Self::cursor_new_success_conditions(va) ==> {
                &&& r is Ok
                &&& r.unwrap().0.invariants(*r.unwrap().1, *regions, *guards)
                &&& r.unwrap().1.in_locked_range()
                &&& r.unwrap().0.level < r.unwrap().0.guard_level
                &&& r.unwrap().0.va < r.unwrap().0.barrier_va.end
                &&& r.unwrap().0.va == va.start
                &&& r.unwrap().0.barrier_va == *va
            },
            !Self::cursor_new_success_conditions(va) ==> r is Err,
            forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
            forall|item: C::Item| #![trigger CursorMut::<C, A>::item_not_mapped(item, *old(regions))]
                CursorMut::<C, A>::item_not_mapped(item, *old(regions)) ==>
                CursorMut::<C, A>::item_not_mapped(item, *regions),
    )]
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>)
    -> Result<(Self, Tracked<CursorOwner<'rcu, C>>), PageTableError>
    {
        let valid = is_valid_range::<C>(va);
        if !valid || va.start >= va.end {
            return Err(PageTableError::InvalidVaddrRange(va.start, va.end));
        }
        if va.start % C::BASE_PAGE_SIZE() != 0 || va.end % C::BASE_PAGE_SIZE() != 0 {
            return Err(PageTableError::UnalignedVaddr);
        }
        //        const { assert!(C::NR_LEVELS() as usize <= MAX_NR_LEVELS) };

        proof {
            assert(pt_own.0.value.is_node());
            assert(pt_own.0.inv_children());
            assert forall|i: int| 0 <= i < NR_ENTRIES implies pt_own.0.children[i] is Some by {
                if pt_own.0.children[i] is None {
                    assert(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::rel_children(pt_own.0.value, i, None));
                }
            };
        }

        Ok(
            #[verus_spec(with Tracked(pt_own), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
            locking::lock_range(pt, guard, va),
        )
    }

    /// Gets the current virtual address.
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
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([Self::invariants])
    /// must hold before the call.
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call
    /// - **Correctness**: if the cursor is within the locked range, the result will be `Ok`;
    /// otherwise it will be an error.
    /// - **Correctness**: if there is a mapping present ([Self::query_some_condition]),
    /// then the second field of the result will `Some(item)`, where `item` is the mapping,
    /// and the first field will give its range.
    /// - **Correctness**: if there is no mapping present, then the second field of the result will be
    /// 'None'>
    /// ## Safety
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
        ensures
            self.invariants(*owner, *regions, *guards),
            old(owner)@.mappings == owner@.mappings,
            old(owner).in_locked_range() ==> res is Ok,
            res matches Ok(state) ==>
                self.query_some_condition(*owner) ==>
                self.query_some_ensures(*owner, state),
            res matches Ok(state) ==>
                !self.query_some_condition(*owner) ==>
                self.query_none_ensures(*owner, state),
    )]
    pub fn query(&mut self) -> Result<PagesState<C>, PageTableError> {
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
                self.invariants(*owner, *regions, *guards),
                self.va == initial_va,
                old(owner)@.mappings == owner@.mappings,
            decreases self.level,
        {
            proof { reveal(CursorContinuation::inv_children); }

            let cur_va = self.va;
            let level = self.level;

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let entry = self.cur_entry();

            let ghost continuations0 = owner.continuations;
            let ghost owner_snap = *owner;
            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let ghost cont0 = continuation;
            let tracked child_owner = continuation.take_child();
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();

            assert(!child_owner.value.in_scope) by {
                owner_snap.continuations_not_in_scope();
                assert(owner_snap.continuations[(owner_snap.level - 1) as int].children[cont0.idx as int] is Some);
            };

            let ghost regions_before_ref = *regions;

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner), Tracked(regions), Tracked(&continuation.guard_perm) )]
            let cur_child = entry.to_ref();

            proof {
                continuation.put_child(child_owner);
                cont0.take_put_child();
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                assert(owner.continuations == continuations0);
                owner.relate_region_slot_owners_preserved(regions_before_ref, *regions);
            }

            let item = match cur_child {
                ChildRef::PageTable(pt) => {
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

                        owner.map_children_implies(
                            CursorOwner::node_unlocked(guards0),
                            CursorOwner::node_unlocked_except(*guards, child_node.meta_perm.addr()),
                        );
                        owner.cur_entry_node_implies_level_gt_1();
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
                    proof {
                        owner.cur_entry_frame_present();
                    }
                    assert(owner@.query(pa, page_size(level), prop));

                    // debug_assert_eq!(ch_level, level);
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

                    proof {
                        C::item_roundtrip(item, pa, level, prop);
                    }

                    assert(pa == owner.cur_entry_owner().frame.unwrap().mapped_pa);

                    let idx = frame_to_index(pa);
                    let ghost old_regions = *regions;
                    let tracked slot_perm = owner.borrow_cur_frame_slot_perm();
                    let tracked mut slot_own = regions.slot_owners.tracked_remove(idx);

                    assert(item.clone_requires(*slot_perm, slot_own.inner_perms.ref_count)) by {
                        owner.cur_frame_clone_requires(item, pa, level, prop, old_regions);
                    };

                    #[verus_spec(with Tracked(slot_perm), Tracked(&mut slot_own.inner_perms.ref_count))]
                    let cloned = Self::clone_item(&item);

                    proof {
                        regions.slot_owners.tracked_insert(idx, slot_own);
                        owner.clone_item_preserves_invariants(old_regions, *regions, idx);
                        assert(regions.inv());
                        assert(owner.relate_region(*regions));
                    }

                    Some(cloned)
                },
            };

            let size = page_size(level);

            proof {
                owner.cur_va_range_reflects_view();
            }

            assert(old(owner)@.mappings == owner@.mappings);

            return Ok(
                (#[verus_spec(with Tracked(owner))]
                self.cur_va_range(), item),
            );
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
            old(self).level < old(self).guard_level,
            old(owner).in_locked_range(),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).va + len <= old(self).barrier_va.end,
        ensures
            self.invariants(*owner, *regions, *guards),
            res is Some ==> {
                &&& res.unwrap() == self.va
                &&& owner.level < owner.guard_level
                &&& owner.in_locked_range()
            },
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    fn find_next_impl(&mut self, len: usize, find_unmap_subtree: bool, split_huge: bool) -> (res:
        Option<Vaddr>)
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            old(owner).level < NR_LEVELS,
            // Panic conditions as preconditions
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).va + len <= old(self).barrier_va.end,
        ensures
            self.invariants(*owner, *regions, *guards),
            res is Some ==> {
                &&& res.unwrap() == self.va
                &&& owner.level < owner.guard_level
                &&& !find_unmap_subtree ==> owner.cur_entry_owner().is_frame()
                &&& owner.in_locked_range()
            },
            res is Some && !find_unmap_subtree && old(owner).cur_entry_owner().is_frame() ==>
                owner.cur_entry_owner().frame.unwrap().prop
                == old(owner).cur_entry_owner().frame.unwrap().prop,
            res is None ==> {
                &&& self.va >= old(self).va + len
            },
    {
        let end = self.va + len;

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
                owner.level < NR_LEVELS,
            decreases owner.max_steps(),
        {
            proof { reveal(CursorContinuation::inv_children); }

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

            assert(!child_owner.value.in_scope) by {
                owner0.continuations_not_in_scope();
                assert(owner0.continuations[(owner0.level - 1) as int].children[cont0.idx as int] is Some);
            };

            let ghost regions_before_ref = *regions;

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&node_owner), Tracked(regions), Tracked(&continuation.guard_perm))]
            let cur_child = cur_entry.to_ref();

            proof {
                continuation.put_child(child_owner);
                assert(continuation.children == cont0.children);
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                assert(owner.continuations == owner0.continuations);
                owner.relate_region_slot_owners_preserved(regions_before_ref, *regions);
            }

            match cur_child {
                ChildRef::PageTable(pt) => {
                    if find_unmap_subtree && cur_entry_fits_range && (C::TOP_LEVEL_CAN_UNMAP()
                        || self.level != C::NR_LEVELS()) {
                        return Some(cur_va);
                    }
                    assert(owner.children_not_locked(*guards));

                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
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

                        owner.map_children_implies(
                            CursorOwner::node_unlocked(guards0),
                            CursorOwner::node_unlocked_except(
                                *guards,
                                child_node_owner.meta_perm.addr(),
                            ),
                        );
                    }

                    assert(owner.only_current_locked(*guards));

                    // If there's no mapped PTEs in the next level, we can
                    // skip to save time.
                    if (nr_children != 0) {
                        proof { assert(owner.level > 1) by {
                            owner.cur_entry_node_implies_level_gt_1();
                        }; }
                        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
                        self.push_level(pt_guard);
                    } else {
                        let ghost guards_before_drop = *guards;
                        let ghost locked_addr = child_node_owner.meta_perm.addr();

                        let _ = ManuallyDrop::new(
                            pt_guard.take(Tracked(&mut guard_perm)),
                            Tracked(guards),
                        );
                        proof {
                            assert(OwnerSubtree::implies(
                                CursorOwner::node_unlocked_except(guards_before_drop, locked_addr),
                                CursorOwner::node_unlocked(*guards),
                            ));
                            owner.map_children_implies(
                                CursorOwner::node_unlocked_except(guards_before_drop, locked_addr),
                                CursorOwner::node_unlocked(*guards),
                            );
                            assert(owner.children_not_locked(*guards));

                            owner.move_forward_increases_va();
                            owner.move_forward_not_popped_too_high();
                        }

                        let ghost owner_before_move = *owner;
                        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                        self.move_forward();

                        proof {
                            owner.va.reflect_prop(self.va);
                            assert(*owner == owner_before_move.move_forward_owner_spec());
                            owner.in_locked_range_level_lt_nr_levels();
                        }
                    }

                    proof {
                        assert(owner.in_locked_range());
                        owner.in_locked_range_level_lt_nr_levels();
                    }
                    continue ;
                },
                ChildRef::None => {
                    proof {
                        owner.move_forward_increases_va();
                        owner.move_forward_not_popped_too_high();
                    }

                    // These predicates are established by the loop invariants

                    let ghost owner_before_move = *owner;
                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.move_forward();

                    proof {
                        owner.va.reflect_prop(self.va);
                        assert(*owner == owner_before_move.move_forward_owner_spec());
                        // move_forward ensures owner.in_locked_range()
                        owner.in_locked_range_level_lt_nr_levels();
                    }
                    continue ;
                },
                ChildRef::Frame(_, _, _) => {
                    assert(owner.max_steps() == owner0.max_steps());
                    if cur_entry_fits_range || !split_huge {
                        assert(!find_unmap_subtree && old(owner).cur_entry_owner().is_frame() ==>
                            owner.cur_entry_owner().frame.unwrap().prop
                            == old(owner).cur_entry_owner().frame.unwrap().prop) by {
                            if !find_unmap_subtree && old(owner).cur_entry_owner().is_frame() {
                                // Both owner and old(owner) are at frames in the same locked region.
                                // find_next_impl does not modify frame props; any found frame is
                                // either the same frame or a sub-frame after split (same prop).
                                owner.find_next_frame_prop_preserved(*old(owner));
                            }
                        };
                        return Some(cur_va);
                    }
                    let tracked mut continuation = owner.continuations.tracked_remove(
                        owner.level - 1,
                    );
                    let ghost orig_cont_level = continuation.level();
                    proof {
                        assert(continuation.tree_level == INC_LEVELS - orig_cont_level - 1);
                    }
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

                    proof {
                        assert(child_owner.value.is_frame());
                        assert(parent_owner.level > 1) by {
                            assert(child_owner.value.parent_level == owner0.level) by {
                                reveal(CursorContinuation::inv_children);
                            };
                            owner0.frame_not_fits_implies_level_gt_1(cur_entry_fits_range, cur_va, end);
                        };
                    }

                    let split_child = (
                    #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions),
                        Tracked(guards), Tracked(&mut continuation.guard_perm))]
                    cur_entry.split_if_mapped_huge(rcu_guard)).expect(
                        "The entry must be a huge page",
                    );

                    proof {
                        assert(guards.guards.contains_key(split_child.addr()));
                        assert(guards.locked(split_child.addr()));
                        assert(child_owner.value.node.unwrap().meta_perm.addr()
                            == split_child.addr());
                    }

                    let tracked guard_perm = guards.take(
                        child_owner.value.node.unwrap().meta_perm.addr(),
                    );

                    proof {
                        continuation.put_child(child_owner);
                        continuation.entry_own.node = Some(parent_owner);
                        continuation.continuation_inv_holds_after_split_restore();
                        owner.continuations.tracked_insert(owner.level - 1, continuation);

                        owner0.max_steps_partial_inv(*owner, owner.level as usize);
                        owner.cur_entry_node_implies_level_gt_1();
                    }

                    #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
                    self.push_level(split_child);

                    continue ;
                },
            }
        }

        assert(self.va >= end);

        None
    }

    /// Jumps to the given virtual address.
    /// If the target address is out of the range, this method will return `Err`.
    ///
    /// # Panics
    ///
    /// This method panics if the address has bad alignment.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn jump(&mut self, va: Vaddr) -> (res: Result<(), PageTableError>)
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
            old(self).level < old(self).guard_level,
            old(owner).in_locked_range(),
            old(self).jump_panic_condition(va),
        ensures
            self.invariants(*owner, *regions, *guards),
            self.barrier_va.start <= va < self.barrier_va.end ==> {
                &&& res is Ok
                &&& self.va == va
            },
            !(self.barrier_va.start <= va < self.barrier_va.end) ==> res is Err,
    {
        if !self.barrier_va.contains(&va) {
            return Err(PageTableError::InvalidVaddr(va));
        }
        loop
            invariant
                self.invariants(*owner, *regions, *guards),
                self.level <= self.guard_level,
                self.barrier_va.start <= va < self.barrier_va.end,
                owner.in_locked_range(),
            decreases self.guard_level - self.level,
        {
            let node_size = page_size(self.level + 1);
            let node_start = self.va.align_down(node_size);

            proof {
                AbstractVaddr::reflect_prop(owner.va, self.va);

                if self.level < self.guard_level {
                    owner.node_within_locked_range(self.level);
                }
            }

            // If the address is within the current node, we can jump directly.
            if node_start <= va && va < node_start + node_size {
                let ghost owner0 = *owner;
                let ghost new_va = AbstractVaddr::from_vaddr(va);
                let ghost old_va = self.va;
                self.va = va;
                proof {
                    AbstractVaddr::from_vaddr_wf(va);

                    lemma_nat_align_down_sound(old_va as nat, node_size as nat);

                    AbstractVaddr::same_node_indices_match(va, old_va, node_start, self.level);
                    AbstractVaddr::from_vaddr_to_vaddr_roundtrip(va);

                    owner.set_va_in_node(new_va);
                }

                return Ok(());
            }

            proof {
                owner.in_locked_range_level_lt_guard_level();
                owner.jump_not_in_node_level_lt_guard_minus_one(self.level, va, node_start);
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
            owner.inv(),
            self.wf(*owner),
            self.inv(),
            regions.inv(),
            *owner == old(owner).move_forward_owner_spec(),
            owner.max_steps() < old(owner).max_steps(),
            self.barrier_va == old(self).barrier_va,
            self.guard_level == old(self).guard_level,
            !owner.popped_too_high,
            owner.in_locked_range(),
            owner.children_not_locked(*guards),
            owner.nodes_locked(*guards),
            owner.relate_region(*regions),
            owner.va == old(owner).va.align_up(old(self).level as int),
            // move_forward only calls pop_level, which does not touch regions.
            forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
    {
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;
        proof {
            owner.move_forward_owner_decreases_steps();
            old(owner).move_forward_not_popped_too_high();
            old(owner).move_forward_owner_preserves_in_locked_range();
        }

        let ghost start_level = self.level;
        let ghost guard_level = self.guard_level;
        let ghost barrier_va = self.barrier_va;
        let ghost va = self.va;

        let next_va = (#[verus_spec(with Tracked(owner))]
            self.cur_va_range()).end;

        let ghost abs_va_down = owner0.va.align_down((start_level - 1) as int);
        let ghost abs_next_va = AbstractVaddr::from_vaddr(next_va);

        proof {
            AbstractVaddr::reflect_from_vaddr(next_va);
            owner0.va.reflect_prop(va);
            if start_level > 1 {
                owner0.va.align_down_inv((start_level - 1) as int);
                owner0.va.align_down_concrete(start_level - 1);
                owner0.va.align_down(start_level - 1).reflect_prop(
                    nat_align_down(va as nat, page_size((start_level - 1) as PagingLevel) as nat) as Vaddr);
            } else {
                owner0.va.align_down_zero_properties();
            }
            abs_next_va.reflect_prop(next_va);

            AbstractVaddr::reflect_eq(abs_next_va, owner0.va.align_up(start_level as int), next_va);

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
                1 <= start_level <= self.level <= self.guard_level <= NR_LEVELS,
                forall|i: int|
                    start_level <= i < NR_LEVELS ==> #[trigger] owner0.va.index[i - 1]
                        == abs_va_down.index[i - 1],
                forall|i: int|
                    self.level <= i < NR_LEVELS ==> #[trigger] owner0.va.index[i - 1]
                        == owner.continuations[i - 1].idx,
                owner.in_locked_range(),
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.relate_region(*regions),
                // pop_level does not touch regions, so path_if_in_pt is preserved.
                *regions == regions0,
            decreases self.guard_level - self.level,
        {
            proof {
                assert(abs_next_va.index[self.level - 1] == 0);
                abs_va_down.wrapped_unwrap(start_level as int, self.level as int);
                abs_va_down.use_wrapped(start_level as int, self.level as int);
                assert(owner0.va.index[self.level - 1] + 1 == NR_ENTRIES);
                assert(owner.move_forward_owner_spec()
                    == owner.pop_level_owner_spec().0.move_forward_owner_spec());
                owner.pop_level_owner_preserves_invs(*guards, *regions);
            }

            #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
            self.pop_level();
        }

        let ghost index = abs_next_va.index[self.level - 1];
        assert(self.level >= self.guard_level || index != 0);
        assert(self.level < self.guard_level) by {
            owner.move_forward_pop_loop_level_lt_guard(owner0);
        };

        assert(owner0.va.index[self.level - 1] + 1 < NR_ENTRIES);
        assert(owner.move_forward_owner_spec() == owner0.move_forward_owner_spec());
        assert(owner.move_forward_owner_spec() == owner.inc_index().zero_below_level());

        self.va = next_va;

        proof {
            owner.do_inc_index();
            owner.zero_preserves_all_but_va();
            owner.do_zero_below_level();
            owner0.move_forward_va_is_align_up();
        }
    }

    /// Goes up a level.
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
            self.inv(),
            self.wf(*owner),
            regions.inv(),
            owner.inv(),
            owner.in_locked_range(),
            owner.children_not_locked(*guards),
            owner.nodes_locked(*guards),
            owner.relate_region(*regions),
            self.guard_level == old(self).guard_level,
            *owner == old(owner).pop_level_owner_spec().0,
            // pop_level does not touch regions at all (only owner and guards are modified).
            *regions == *old(regions),
    {
        proof {
            let ghost child_cont = owner.continuations[owner.level - 1];
            assert(child_cont.all_some());
            assert(child_cont.inv());
            assert(self.path[self.level as usize - 1] is Some);
            assert(self.path[self.level as usize - 1].unwrap().addr()
                == owner.continuations[owner.level - 1].guard_perm.addr());
            assert(guards.lock_held(
                owner.continuations[owner.level - 1].guard_perm.value().inner.inner@.ptr.addr(),
            ));
            owner.pop_level_owner_preserves_invs(*guards, *regions);
        }
        let tracked guard_perm = owner.pop_level_owner();

        let ghost owner0 = *owner;
        let ghost guards0 = *guards;
        let ghost guard = guard_perm.value();

        let taken: Option<PPtr<PageTableGuard<'rcu, C>>> = *self.path.get(
            self.level as usize - 1,
        ).unwrap();
        let _ = ManuallyDrop::new(taken.unwrap().take(Tracked(&mut guard_perm)), Tracked(guards));

        proof {
            owner.never_drop_restores_children_not_locked(guard, guards0, *guards);
            owner.never_drop_restores_nodes_locked(guard, guards0, *guards);
        }

        self.level = self.level + 1;

        assert(self.wf(*owner));
    }

    /// Goes down a level to a child page table.
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
            old(owner).level > 1,
            //old(owner).in_locked_range(),
            old(owner).only_current_locked(*guards),
            old(owner).nodes_locked(*guards),
            old(owner).relate_region(*regions),
            !old(owner).popped_too_high,
            guards.lock_held(guard_perm.value().inner.inner@.ptr.addr()),
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
            *owner == old(owner).push_level_owner_spec(guard_perm),
            owner.max_steps() < old(owner).max_steps(),
            old(owner)@.mappings == owner@.mappings,
    {
        assert(owner.va.index.contains_key(owner.level - 2)) by {
            // old(owner).level > 1 (precondition), so owner.level - 2 is in [0, NR_LEVELS)
            assert(owner.level >= 2);
            assert(owner.va.inv());
        };

        self.level = self.level - 1;
        // debug_assert_eq!(self.level, child_pt.level());

        // let old = self.path.get(self.level as usize - 1);
        self.path.set(self.level as usize - 1, Some(child_pt));

        proof {
            owner.push_level_owner_preserves_invs(guard_perm, *regions, *guards);
            owner.push_level_owner_decreases_steps(guard_perm);
            owner.push_level_owner_preserves_va(guard_perm);
            owner.push_level_owner_preserves_mappings(guard_perm);
            owner.push_level_owner(Tracked(guard_perm));
        }
        // debug_assert!(old.is_none());
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
            *self == *old(self),
            *owner == *old(owner),
            owner.continuations[owner.level - 1].guard_perm.addr() == res.node.addr(),
            owner.relate_region(*regions),
            res.idx == owner.continuations[owner.level - 1].idx,
    {
        proof { reveal(CursorContinuation::inv_children); }

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
        }

        assert(ptei == parent_continuation.idx) by {
            owner0.va.reflect_prop(self.va);
            if owner0.level == 1 {
            } else if owner0.level == 2 {
            } else if owner0.level == 3 {
            } else {
            }
        };
        assert(!child.value.in_scope) by {
            owner0.continuations_not_in_scope();
            assert(owner0.continuations[(owner0.level - 1) as int].children[cont0.idx as int] is Some);
        };

        #[verus_spec(with Tracked(&parent_own),
            Tracked(&child.value),
            Tracked(&parent_continuation.guard_perm))]
        let res = PageTableGuard::entry(node, pte_index::<C>(self.va, self.level));

        // res.idx == ptei: entry ensures res.idx == idx (pte_index result),
        // pte_index spec gives pte_index result == AbstractVaddr::from_vaddr(va).index[level-1] == ptei.

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
    #[verus_spec(
        with Tracked(owner): Tracked<&CursorOwner<C>>
    )]
    fn cur_va_range(&self) -> (res: Range<Vaddr>)
        requires
            owner.inv(),
            self.wf(*owner),
        ensures
            owner.cur_va_range().start.reflect(res.start),
            owner.cur_va_range().end.reflect(res.end),
    {
        let page_size = page_size(self.level);
        let start = self.va.align_down(page_size);

        proof {
            owner.va.reflect_prop(self.va);
            owner.va.align_down_concrete(self.level as int);
            owner.va.align_up_concrete(self.level as int);
            owner.va.align_diff(self.level as int);
            assert(owner.cur_va_range().start.reflect(start));
            assert(owner.cur_va_range().end.reflect((start + page_size) as Vaddr));
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
    #[verus_spec(r =>
        with Tracked(pt_own): Tracked<PageTableOwner<C>>,
            Tracked(guard_perm): Tracked<GuardPerm<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            pt_own.inv(),
        ensures
            Cursor::<C, A>::cursor_new_success_conditions(va) ==> {
                &&& r is Ok
                &&& r.unwrap().0.inner.invariants(*r.unwrap().1, *regions, *guards)
                &&& r.unwrap().1.in_locked_range()
                &&& r.unwrap().0.inner.level < r.unwrap().0.inner.guard_level
                &&& r.unwrap().0.inner.va < r.unwrap().0.inner.barrier_va.end
                &&& r.unwrap().0.inner.va == va.start
                &&& r.unwrap().0.inner.barrier_va == *va
            },
            !Cursor::<C, A>::cursor_new_success_conditions(va) ==> r is Err,
            // cursor_mut only acquires locks on page-table node slots; it does not
            // set path_if_in_pt for data-frame slots. Any frame that was item_not_mapped
            // before the call remains item_not_mapped after.
            forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                Self::item_not_mapped(item, *old(regions)) ==>
                Self::item_not_mapped(item, *regions),
            // cursor_mut only locks page-table node slots; it does not modify path_if_in_pt
            // for any slot (neither node slots nor data-frame slots).
            forall |idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
    )]
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>)
    -> Result<(Self, Tracked<CursorOwner<'rcu, C>>), PageTableError> {
        let res = #[verus_spec(with Tracked(pt_own), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
        Cursor::new(pt, guard, va);
        match res {
            Ok((inner_cursor, tracked_owner)) => {
                proof {
                    // In the Ok branch, cursor_new_success_conditions(va) holds
                    // (from !conditions ==> Err, contrapositive gives Ok ==> conditions).
                    // Therefore the success-case ensures apply, giving us invariants.
                    assert(inner_cursor.invariants(*tracked_owner, *regions, *guards));
                    assert(CursorMut::<C, A> { inner: inner_cursor }.inner.invariants(*tracked_owner, *regions, *guards));
                }
                Ok((Self { inner: inner_cursor }, tracked_owner))
            }
            Err(e) => Err(e),
        }
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// This is the same as [`Cursor::find_next`].
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(self).inner.level < old(self).inner.guard_level,
            old(owner).in_locked_range(),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).inner.va + len <= old(self).inner.barrier_va.end,
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            res is Some ==> {
                &&& res.unwrap() == self.inner.va
                &&& owner.level < owner.guard_level
                &&& owner.in_locked_range()
            },
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn jump(&mut self, va: Vaddr) -> (res: Result<(), PageTableError>)
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(self).inner.level < old(self).inner.guard_level,
            old(owner).in_locked_range(),
            old(self).inner.jump_panic_condition(va),
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            self.inner.barrier_va.start <= va < self.inner.barrier_va.end ==> {
                &&& res is Ok
                &&& self.inner.va == va
            },
            !(self.inner.barrier_va.start <= va < self.inner.barrier_va.end) ==> res is Err,
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.jump(va)
    }

    /// Gets the current virtual address.
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
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            old(owner).in_locked_range() ==> res is Ok,
            res matches Ok(state) ==>
                self.inner.query_some_condition(*owner) ==>
                self.inner.query_some_ensures(*owner, state),
            res matches Ok(state) ==>
                !self.inner.query_some_condition(*owner) ==>
                self.inner.query_none_ensures(*owner, state),
//            owner.in_locked_range(),
    )]
    pub fn query(&mut self) -> (res: Result<PagesState<C>, PageTableError>) {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.query()
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            ChildRef::PageTable(pt).wf(old(owner).cur_entry_owner())
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            owner.in_locked_range(),
            owner.va == old(owner).va,
            self.inner.level == old(self).inner.level - 1,
            self.inner.guard_level == old(self).inner.guard_level,
            // push_level preserves the abstract view: mappings are unchanged and cur_va is unchanged.
            owner@ == old(owner)@,
            // map_branch_pt only locks an existing node (push_level takes regions by shared ref);
            // regions is not modified.
            *regions == *old(regions),
    )]
    fn map_branch_pt(&mut self, pt: PageTableNodeRef<'rcu, C>, rcu_guard: &'rcu A) {
        proof { reveal(CursorContinuation::inv_children); }

        let ghost guards0 = *guards;

        // Ghost snapshots for proving owner restoration after the manipulations below.
        let ghost level_key = owner.level as int - 1;
        let ghost cont_orig = owner.continuations[level_key];

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let tracked mut child_owner = continuation.take_child();
        let ghost orig_child_owner = child_owner;
        let tracked mut child_node = child_owner.value.node.tracked_take();

        proof_decl! {
            let tracked mut guard_perm: Tracked<GuardPerm<'rcu, C>>;
        }

        // SAFETY: The `pt` must be locked and no other guards exist.
        #[verus_spec(with Tracked(&child_node), Tracked(guards) => Tracked(guard_perm))]
        let pt_guard = pt.make_guard_unchecked(rcu_guard);

        proof {
            child_owner.value.node = Some(child_node);
            assert(child_owner == orig_child_owner);
            continuation.put_child(child_owner);
            cont_orig.take_put_child();
            assert(continuation == cont_orig);
            owner.continuations.tracked_insert(owner.level - 1, continuation);
            assert(owner.continuations =~= old(owner).continuations);
            assert(*owner == *old(owner));

            owner.map_children_implies(
                CursorOwner::node_unlocked(guards0),
                CursorOwner::node_unlocked_except(*guards, child_node.meta_perm.addr()),
            );

            owner.cur_entry_node_implies_level_gt_1();
        }
        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
        self.inner.push_level(pt_guard);

        proof { assert(owner@ == old(owner)@); }
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(cur_entry).wf(old(owner).cur_entry_owner()),
            old(owner).cur_entry_owner().is_absent(),
            old(owner).in_locked_range(),
            old(owner).level >= 2,
            old(cur_entry).node.addr() == old(owner).continuations[old(owner).level - 1].guard_perm.addr(),
            old(owner).cur_entry_owner().match_pte(
                old(owner).continuations[old(owner).level - 1].entry_own.node.unwrap().children_perm.value()
                    [old(cur_entry).idx as int],
                old(owner).cur_entry_owner().parent_level,
            ),
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            owner.in_locked_range(),
            owner.va == old(owner).va,
            self.inner.level == old(self).inner.level - 1,
            self.inner.guard_level == old(self).inner.guard_level,
            // alloc_if_none creates an empty PT; push_level preserves all existing mappings.
            owner@ == old(owner)@,
            // The slot for item remains in regions.
            forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                Self::item_slot_in_regions(item, *old(regions)) ==>
                Self::item_slot_in_regions(item, *regions),
            // The newly allocated PT is empty, so the current entry at the new level is absent.
            owner.cur_entry_owner().is_absent(),
            // Slot owners for non-UNUSED indices are entirely preserved (alloc_if_none only
            // modifies slot_owners at the newly allocated PT node's index, which was UNUSED).
            forall|idx: usize|
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED ==>
                (#[trigger] regions.slot_owners[idx]) == old(regions).slot_owners[idx],
    )]
    fn map_branch_none(&mut self, cur_entry: &mut Entry<'rcu, C>, rcu_guard: &'rcu A) {
        proof { reveal(CursorContinuation::inv_children); }

        let ghost owner0 = *owner;
        let ghost guards0 = *guards;

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let ghost cont0 = continuation;
        let tracked mut child_owner = continuation.take_child();
        let ghost old_child_value = child_owner.value; // absent entry before alloc_if_none
        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        proof {
            assert(continuation.guard_perm.addr() == cur_entry.node.addr());
            assert(cur_entry.node_matching(
                child_owner.value,
                parent_owner,
                continuation.guard_perm,
            ));
        }

        proof_decl! {
            let tracked mut guard_perm;
        }

        let child_guard = (
        #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions), Tracked(guards), Tracked(&mut continuation.guard_perm)
            => Tracked(guard_perm))]
        cur_entry.alloc_if_none(rcu_guard)).unwrap();

        let ghost new_node_addr = child_owner.value.node.unwrap().meta_perm.addr();
        let ghost new_child_value = child_owner.value; // newly allocated node after alloc_if_none
        let ghost new_pt_idx = frame_to_index(new_child_value.meta_slot_paddr().unwrap());
        // From alloc_if_none: all children of the newly allocated node are absent.
        let ghost child_owner_children = child_owner.children;

        proof {
            assert(forall|i: int| 0 <= i < NR_ENTRIES ==>
                (#[trigger] child_owner_children[i]) is Some
                && child_owner_children[i].unwrap().value.is_absent());

            cont0.take_put_child();
            continuation.entry_own.node = Some(parent_owner);
            continuation.put_child(child_owner);
            owner.continuations.tracked_insert(owner.level - 1, continuation);

            assert(owner.cur_entry_owner().node.unwrap().meta_perm.addr() == new_node_addr);

            assert forall|i: int|
                owner0.level <= i < NR_LEVELS implies #[trigger] owner.continuations[i]
                == owner0.continuations[i] by {};

            let f_unlocked = CursorOwner::<'rcu, C>::node_unlocked(guards0);
            let g_unlocked = CursorOwner::<'rcu, C>::node_unlocked_except(*guards, new_node_addr);
            let f_region = PageTableOwner::<C>::relate_region_pred(*old(regions));
            let g_region = PageTableOwner::<C>::relate_region_pred(*regions);

            Entry::<C>::alloc_if_none_relate_region_preserved(old_child_value, new_child_value, *old(regions), *regions);

            let idx = cont0.idx as int;
            let cont_final = owner.continuations[owner.level - 1];

            assert forall|i: int|
                #![auto]
                owner.level <= i < NR_LEVELS implies
                    owner.continuations[i].map_children(g_unlocked)
                    && owner.continuations[i].map_children(g_region)
            by {
                owner0.continuations[i].map_children_lift(f_unlocked, g_unlocked);
                owner0.continuations[i].map_children_lift(f_region, g_region);
            };

            cont_final.map_children_lift_skip_idx(cont0, idx, f_unlocked, g_unlocked);
            cont_final.map_children_lift_skip_idx(cont0, idx, f_region, g_region);

            owner.map_branch_none_inv_holds(owner0);

            assert(Entry::<C>::path_tracked_pred_preserved(*old(regions), *regions));
            owner.map_branch_none_path_tracked_holds(owner0, *regions, *old(regions));
        }

        let ghost owner_pre_push = *owner;
        let ghost cont_before_push = owner_pre_push.continuations[owner_pre_push.level - 1];
        proof { assert(owner.level > 1); } // follows from old(owner).level >= 2
        #[verus_spec(with Tracked(owner), Tracked(guard_perm.tracked_unwrap()), Tracked(regions), Tracked(guards))]
        self.inner.push_level(child_guard);

        proof {
            owner_pre_push.map_branch_none_no_new_mappings(owner0);
            assert(owner@ == old(owner)@);

            assert(forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                Self::item_slot_in_regions(item, *old(regions)) ==>
                Self::item_slot_in_regions(item, *regions)) by {};
            assert forall|idx: usize|
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            implies
                (#[trigger] regions.slot_owners[idx]) == old(regions).slot_owners[idx]
            by {};

            // cur_entry_owner().is_absent(): push_level enters the empty node created by alloc_if_none.
            assert(cont_before_push.children[cont_before_push.idx as int].unwrap().children
                == child_owner_children);
            assert(owner.continuations[owner.level - 1].children == child_owner_children);
            assert(forall|i: int| 0 <= i < NR_ENTRIES ==>
                (#[trigger] owner.continuations[owner.level - 1].children[i]) is Some &&
                owner.continuations[owner.level - 1].children[i].unwrap().value.is_absent());
            owner.map_branch_none_cur_entry_absent();
        }
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(cur_entry).wf(old(owner).cur_entry_owner()),
            old(owner).cur_entry_owner().is_frame(),
            old(cur_entry).node.addr() == old(owner).continuations[old(owner).level - 1].guard_perm.addr(),
            old(owner).in_locked_range(),
            old(owner).level > 1,
            old(owner).level < NR_LEVELS,
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            owner@ == old(owner)@.split_if_mapped_huge_spec(page_size((old(owner).level - 1) as PagingLevel)),
            owner.in_locked_range(),
            owner.va == old(owner).va,
            self.inner.level == old(self).inner.level - 1,
            self.inner.guard_level == old(self).inner.guard_level,
            // The slot for item remains in regions.
            forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                Self::item_slot_in_regions(item, *old(regions)) ==>
                Self::item_slot_in_regions(item, *regions),
            // Slot owners for non-UNUSED indices are entirely preserved.
            forall|idx: usize|
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED ==>
                (#[trigger] regions.slot_owners[idx]) == old(regions).slot_owners[idx],
    )]
    fn map_branch_frame(&mut self, cur_entry: &mut Entry<'rcu, C>, rcu_guard: &'rcu A) {
        proof { reveal(CursorContinuation::inv_children); }

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let tracked mut child_owner = continuation.take_child();
        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        let split_child = (
        #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions),
                Tracked(guards), Tracked(&mut continuation.guard_perm))]
        cur_entry.split_if_mapped_huge(rcu_guard)).unwrap();

        proof {
            assert(guards.guards.contains_key(split_child.addr()));
            assert(guards.locked(split_child.addr()));
            assert(child_owner.value.node.unwrap().meta_perm.addr() == split_child.addr());

            continuation.put_child(child_owner);
            continuation.entry_own.node = Some(parent_owner);
            owner.continuations.tracked_insert(owner.level - 1, continuation);
        }

        let tracked child_guard_perm = guards.take(
            child_owner.value.node.unwrap().meta_perm.addr(),
        );

        proof { assert(owner.level > 1); } // from old(owner).level > 1 precondition
        #[verus_spec(with Tracked(owner), Tracked(child_guard_perm), Tracked(regions), Tracked(guards))]
        self.inner.push_level(split_child);

        proof {
            // item_slot_in_regions preserved: split_if_mapped_huge preserves all slot keys
            // and either leaves slot_owners unchanged (i != pt_idx) or sets ref_count != UNUSED.
            assert(forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                Self::item_slot_in_regions(item, *old(regions)) ==>
                Self::item_slot_in_regions(item, *regions)) by {
                // split_if_mapped_huge postconditions:
                // 1. forall i: old.slots.contains_key(i) ==> regions.slots.contains_key(i)
                // 2. forall i != pt_idx: regions.slot_owners[i] == old.slot_owners[i]
                // 3. regions.slot_owners[pt_idx].ref_count != REF_COUNT_UNUSED
            };
            // Non-UNUSED slot_owners preservation: split_if_mapped_huge only modifies
            // slot_owners at the new PT node's index, which had ref_count == UNUSED.
            assert forall|idx: usize|
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            implies
                (#[trigger] regions.slot_owners[idx]) == old(regions).slot_owners[idx]
            by {};
        }
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            level < old(self).inner.guard_level,
            level >= 1,
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            owner.va == old(owner).va,
            self.inner.guard_level == old(self).inner.guard_level,
            self.inner.level == level,
            owner.in_locked_range(),
            owner@ == old(owner)@.split_while_huge(page_size(level)),
            // map_loop only creates page-table nodes along the path; the data-frame slot for item
            // stays in regions.slots with its ref_count intact.
            forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                Self::item_slot_in_regions(item, *old(regions)) ==>
                Self::item_slot_in_regions(item, *regions),
            // If the current entry was absent before map_loop (no mapping at that VA), it remains
            // absent at the target level after descending.
            old(owner).cur_entry_owner().is_absent() ==> owner.cur_entry_owner().is_absent(),
            // Slot owners for non-UNUSED indices are entirely preserved through map_loop.
            // map_loop only allocates PT nodes from UNUSED slots, so non-UNUSED entries are untouched.
            forall|idx: usize|
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED ==>
                (#[trigger] regions.slot_owners[idx]) == old(regions).slot_owners[idx],
    )]
    pub fn map_loop(&mut self, level: PagingLevel, rcu_guard: &'rcu A) {
        let ghost guard_level = self.inner.guard_level;
        let ghost owner0 = *owner;
        proof { assert(owner0.inv()); }

        // The split_while_huge invariant holds initially: the cursor starts above the target level,
        // so the mapping at cur_va (if any) has page_size <= page_size(initial_level), meaning
        // split_while_huge(page_size(initial_level)) does not split it and returns owner0@.
        assert(owner@ == owner0@.split_while_huge(page_size(self.inner.level))) by {
            owner0.split_while_huge_at_level_noop();
        };

        // Adjust ourselves to the level of the item.
        while self.inner.level != level
            invariant
                owner.inv(),
                owner0.inv(),
                owner.va == owner0.va,
                self.inner.wf(*owner),
                regions.inv(),
                self.inner.inv(),
                self.inner.guard_level == guard_level,
                level < self.inner.guard_level,
                level >= 1,
                owner.in_locked_range(),
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.relate_region(*regions),
                !owner.popped_too_high,
                // Partial split_while_huge progress: the current view equals the result of
                // splitting the initial view down to the current cursor level's page size.
                owner@ == owner0@.split_while_huge(page_size(self.inner.level)),
                forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                    Self::item_slot_in_regions(item, *old(regions)) ==>
                    Self::item_slot_in_regions(item, *regions),
                // If the initial entry (at map_loop start) was absent, it remains absent
                // as the cursor descends: None branches create empty nodes (absent entries),
                // PT/Frame branches are vacuously true since those entries are not absent.
                owner0.cur_entry_owner().is_absent() ==> owner.cur_entry_owner().is_absent(),
                // Non-UNUSED slot_owners are preserved from map_loop entry.
                forall|idx: usize|
                    old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED ==>
                    (#[trigger] regions.slot_owners[idx]) == old(regions).slot_owners[idx],
            decreases abs(level - self.inner.level),
        {
            proof { reveal(CursorContinuation::inv_children); }

            if self.inner.level < level {
                let ghost owner_pre_pop = *owner;
                let ghost level_pre_pop = self.inner.level;

                proof {
                    owner.pop_level_owner_preserves_invs(*guards, *regions);
                }

                #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                self.inner.pop_level();

                proof {
                    owner_pre_pop.pop_level_owner_preserves_mappings();
                    let ghost level_before_pop = level_pre_pop as int;
                    owner.map_loop_pop_level_invariant(owner0, owner_pre_pop@, level_before_pop);
                    owner.map_loop_pop_level_absent_preserved(owner0);
                }
                continue ;
            }
            // We are at a higher level, go down.

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let mut cur_entry = self.inner.cur_entry();

            let ghost owner1 = *owner;
            let ghost regions0 = *regions;
            let ghost cont0 = owner.continuations[owner.level - 1];

            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let tracked child_owner = continuation.take_child();
            // Ghost snapshot of child_owner.value for use in match arms after child_owner is consumed.
            let ghost child_entry_val = child_owner.value;
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();

            assert(!child_owner.value.in_scope) by {
                owner1.continuations_not_in_scope();
            };

            let ghost regions_before_ref = *regions;

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner),
                Tracked(regions), Tracked(&continuation.guard_perm))]
            let cur_child = cur_entry.to_ref();

            proof {
                cont0.take_put_child();
                continuation.put_child(child_owner);
                assert(continuation == cont0);
                owner.continuations.tracked_insert(owner.level - 1, continuation);

                assert(owner.continuations =~= owner1.continuations);
                owner1.relate_region_slot_owners_preserved(regions_before_ref, *regions);
            }

            let ghost regions_after_ref = *regions;

            match cur_child {
                ChildRef::PageTable(pt) => {
                    let ghost owner_pre_pt = *owner;
                    let ghost level_pre_pt = self.inner.level;

                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.map_branch_pt(pt, rcu_guard);

                    proof {
                        axiom_page_size_monotone(self.inner.level, level_pre_pt);

                        owner0@.split_while_huge_compose(page_size(level_pre_pt), page_size(self.inner.level));

                        owner_pre_pt.split_while_huge_node_noop();
                    }
                    
                    continue ;
                },
                ChildRef::None => {
                    let ghost owner_pre_none = *owner;
                    let ghost level_pre_none = self.inner.level;

                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.map_branch_none(&mut cur_entry, rcu_guard);

                    proof {
                        axiom_page_size_monotone(self.inner.level, level_pre_none);
                        owner0@.split_while_huge_compose(page_size(level_pre_none), page_size(self.inner.level));
                        owner_pre_none.split_while_huge_absent_noop(page_size(self.inner.level));
                        assert(owner@ == owner0@.split_while_huge(page_size(self.inner.level)));
                    }

                    assert forall |item: C::Item|
                        Self::item_slot_in_regions(item, *old(regions))
                        implies #[trigger] Self::item_slot_in_regions(item, *regions)
                    by {
                        assert(Self::item_slot_in_regions(item, regions0));
                        let idx = frame_to_index(C::item_into_raw(item).0);
                        assert(regions_after_ref.slots.contains_key(idx));
                        assert(Self::item_slot_in_regions(item, regions_after_ref));
                    };

                    continue ;
                },
                ChildRef::Frame(_, _, _) => {
                    let ghost owner_before_frame = *owner;
                    let ghost level_before_frame = self.inner.level;

                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.map_branch_frame(&mut cur_entry, rcu_guard);


                    // Chain: owner@ = owner_before_frame@.split_if_mapped_huge_spec(page_size(level_before_frame - 1))
                    //   and loop invariant: owner_before_frame@ = owner0@.split_while_huge(page_size(level_before_frame))
                    //   => owner@ = owner0@.split_while_huge(page_size(self.inner.level))
                    //   via the map_branch_frame_split_while_huge axiom.
                    proof {
                        owner.map_branch_frame_split_while_huge(owner0, owner_before_frame, level_before_frame as int);
                        assert(owner@ == owner0@.split_while_huge(page_size(self.inner.level)));
                    }
                    
                    assert forall |item: C::Item|
                        Self::item_slot_in_regions(item, *old(regions))
                        implies #[trigger] Self::item_slot_in_regions(item, *regions)
                    by {
                        // Chain: loop_inv gives old(regions) ==> regions0.
                        // to_ref: regions0.slots ⊆ regions_after_ref.slots, slot_owners =~=.
                        // map_branch_frame postcond: regions_after_ref ==> *regions.
                        assert(Self::item_slot_in_regions(item, regions0));
                        let idx = frame_to_index(C::item_into_raw(item).0);
                        assert(regions_after_ref.slots.contains_key(idx));
                        assert(Self::item_slot_in_regions(item, regions_after_ref));
                    };
                    // Non-UNUSED slot_owners preserved: chain through to_ref + map_branch_frame.
                    assert forall|idx: usize|
                        old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    implies
                        (#[trigger] regions.slot_owners[idx]) == old(regions).slot_owners[idx]
                    by {
                        assert(regions0.slot_owners[idx] == old(regions).slot_owners[idx]);
                        assert(regions_after_ref.slot_owners[idx] == regions0.slot_owners[idx]);
                    };
                    assert(owner0.cur_entry_owner().is_absent() ==> owner.cur_entry_owner().is_absent()) by {
                        assert(child_entry_val == owner1.cur_entry_owner());
                    };
                    continue ;
                },
            }
        }
        assert(old(owner).cur_entry_owner().is_absent() ==> owner.cur_entry_owner().is_absent()) by {};
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
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(entry_owner): Tracked<EntryOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(self).map_cursor_requires(*old(owner), *old(guards)),
            old(self).map_item_requires(item, entry_owner),
            old(self).map_panic_conditions(item),
            Self::item_not_mapped(item, *old(regions)),
            Self::item_slot_in_regions(item, *old(regions)),
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            old(self).map_item_ensures(
                item,
                old(self).inner.model(*old(owner)),
                self.inner.model(*owner),
            ),
            self.inner.va < self.inner.barrier_va.end ==>
                self.map_cursor_requires(*owner, *guards),
            old(owner).cur_entry_owner().is_absent() ==> res.is_ok(),
            // For non-UNUSED indices other than the mapped frame, path_if_in_pt is preserved.
            forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                idx != frame_to_index(C::item_into_raw(item).0) &&
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED ==>
                regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
            self.inner.guard_level == old(self).inner.guard_level,
    )]
    pub fn map(&mut self, item: C::Item) -> (res: Result<(), PageTableFrag<C>>) {
        proof { reveal(CursorContinuation::inv_children); }

        let ghost self0 = *self;
        let ghost owner0 = *owner;

        let (pa, level, prop) = C::item_into_raw(item);
        let size = page_size(level);

        let ghost target = Mapping {
            va_range: owner@.cur_slot_range(size),
            pa_range: pa..(pa + size) as usize,
            page_size: size,
            property: prop,
        };

        let rcu_guard = self.inner.rcu_guard;

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.map_loop(level, rcu_guard);

        let ghost owner1 = *owner;
        let ghost regions_before_new_child = *regions;

        proof_decl! {
            // item_slot_in_regions precondition + map_loop preservation => slot in regions.slots.
            assert(regions.slots.contains_key(frame_to_index(pa))) by {
                assert(Self::item_slot_in_regions(item, regions_before_new_child));
            };
            let tracked new_owner = owner.continuations.tracked_borrow(owner.level - 1).new_child(pa, prop, regions);
        }

        let ghost regions_after_new_child = *regions;

        proof {
            // Hoist common facts about new_owner from new_child postcondition.
            let cont = owner1.continuations[owner1.level as int - 1];
            assert(new_owner.value == EntryOwner::<C>::new_frame_spec(
                pa,
                cont.path().push_tail(cont.idx as usize),
                cont.level(),
                prop,
                regions_before_new_child.slots[frame_to_index(pa)],
            ));
            assert(new_owner.value.is_frame());
            assert(new_owner.value.frame.unwrap().mapped_pa == pa);

            assert(PageTableOwner(new_owner)@.mappings == set![target]) by {
                assert(owner1.level == level);
                owner1.new_child_mappings_eq_target(new_owner, pa, level, prop);
                assert(owner@.cur_slot_range(size) == owner1@.cur_slot_range(page_size(level)));
            };

            assert(pa % PAGE_SIZE == 0) by {
                assert(new_owner.inv());
            };

            // From map_loop's item_not_mapped preservation and map precondition:
            // item_not_mapped(item, regions_before_new_child) holds.
            // Therefore slot_owners[frame_to_index(pa)].path_if_in_pt is None.
            let ghost pa_idx = frame_to_index(pa);
            // Size is positive so pa is strictly below pa+size.
            axiom_page_size_ge_page_size(level);
            assert(regions_before_new_child.slot_owners[pa_idx].path_if_in_pt is None) by {
                assert(Self::item_slot_in_regions(item, *old(regions)));
                assert(regions_before_new_child.slot_owners[pa_idx] == old(regions).slot_owners[pa_idx]);
                assert(Self::item_not_mapped(item, *old(regions)));
                axiom_pa_plus_page_size_no_overflow(pa, level);
                let ghost range = pa..(pa + size) as usize;
                old(regions).paddr_not_mapped_at(range, pa);
            };

            assert(new_owner.tree_predicate_map(
                new_owner.value.path,
                CursorOwner::<'rcu, C>::node_unlocked(*guards),
            ));

            // All entries in the tree have a different paddr than the new frame.
            // new_owner.value.meta_slot_paddr() == Some(pa), and pa has path_if_in_pt is None.
            assert(new_owner.value.meta_slot_paddr() == Some(pa));
            owner1.not_in_tree_from_not_mapped(regions_before_new_child, new_owner.value);
            assert(*owner == owner1);
            assert(owner.not_in_tree(new_owner.value));
            assert(owner.map_full_tree(
                |entry_owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry_owner.meta_slot_paddr_neq(new_owner.value),
            ));

            // new_owner.value.relate_region(*regions): prove each conjunct for the frame case.
            assert(regions.slot_owners =~= regions_before_new_child.slot_owners);

            assert(new_owner.value.relate_region(*regions)) by {
                assert(Self::item_slot_in_regions(item, regions_before_new_child));
            };

            assert(owner.relate_region(*regions)) by {
                assert(OwnerSubtree::implies(
                    PageTableOwner::<C>::relate_region_pred(regions_before_new_child),
                    PageTableOwner::<C>::relate_region_pred(*regions),
                ));
                assert(OwnerSubtree::implies(
                    PageTableOwner::<C>::path_tracked_pred(regions_before_new_child),
                    PageTableOwner::<C>::path_tracked_pred(*regions),
                ));
                owner1.relate_region_preserved(owner1, regions_before_new_child, *regions);
            };

            // new_child removed one key from regions.slots; the remaining keys and all
            // slot_owners are unchanged, so the forall-based inv is preserved.
            assert(regions.inv()) by {
                let idx = frame_to_index(pa);
                assert(regions.slots =~= regions_before_new_child.slots.remove(idx));
                assert(regions.slot_owners =~= regions_before_new_child.slot_owners);
                assert forall |i: usize| #[trigger] regions.slots.contains_key(i) implies {
                    &&& regions.slot_owners.contains_key(i)
                    &&& regions.slot_owners[i].inv()
                    &&& regions.slots[i].is_init()
                    &&& regions.slots[i].addr() == meta_addr(i)
                    &&& regions.slots[i].value().wf(regions.slot_owners[i])
                    &&& regions.slot_owners[i].self_addr == regions.slots[i].addr()
                } by {
                    assert(regions_before_new_child.slots.contains_key(i));
                };
                assert forall |i: usize| #[trigger] regions.slot_owners.contains_key(i) implies
                    regions.slot_owners[i].inv() by {};
                assert forall |i: usize| i < max_meta_slots() <==> #[trigger] regions.slot_owners.contains_key(i) by {};
                assert forall |i: usize| #[trigger] regions.slots.contains_key(i) implies i < max_meta_slots() by {
                    assert(regions_before_new_child.slots.contains_key(i));
                };
            };
        }

        #[verus_spec(with Tracked(owner), Tracked(new_owner), Tracked(regions), Tracked(guards))]
        let frag = self.replace_cur_entry(Child::Frame(pa, level, prop));

        let ghost owner2 = *owner;
        let ghost regions_after_replace = *regions;
        assert(owner2@.mappings == owner1@.mappings - PageTableOwner(owner1.cur_subtree())@.mappings
            + PageTableOwner(new_owner)@.mappings);

        proof {
            // At this point, level == owner1.level
            owner1.cur_subtree_eq_filtered_mappings();
            owner.move_forward_owner_preserves_mappings();
        }
        assert(owner1@.remove_subtree(page_size(level)) == owner1@.mappings - PageTableOwner(
            owner1.cur_subtree(),
        )@.mappings);
        assert(owner2@.mappings == owner1@.remove_subtree(page_size(level)) + PageTableOwner(
            new_owner,
        )@.mappings);

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.move_forward();

        proof {
            owner.va.reflect_prop(self.inner.va);
            owner2.va.align_up_concrete(level as int);
            owner.va.reflect_prop(
                nat_align_up(owner1.va.to_vaddr() as nat, page_size(level) as nat) as Vaddr,
            );
        }

        assert(owner@.cur_va == owner2@.align_up_spec(page_size(level)));
        assert(owner@ == owner0@.map_spec(pa, page_size(level), prop));
        assert(self0.map_item_ensures(item, owner0@, owner@));

        proof {
            assert(self.inner.va >= self.inner.barrier_va.end
                || self.map_cursor_requires(*owner, *guards)) by {
                if !owner.above_locked_range() {
                    owner2.move_forward_increases_va();
                }
            };
            let ghost pa_idx2 = frame_to_index(C::item_into_raw(item).0);
            assert forall|idx: usize|
                idx != pa_idx2 &&
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            implies
                #[trigger] regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt
            by {
                assert(regions_after_new_child.slot_owners =~= regions_before_new_child.slot_owners);
            };
            assert(old(owner).cur_entry_owner().is_absent() ==> frag.is_none()) by {
                assert(old(owner).cur_entry_owner().is_absent() ==> owner1.cur_entry_owner().is_absent());
            };
        }

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
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).inner.va + len <= old(self).inner.barrier_va.end,
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            self.inner.va > old(self).inner.va,
            self.inner.va <= old(self).inner.va + len,
            self.inner.va % C::BASE_PAGE_SIZE() == 0,
            self.inner.barrier_va == old(self).inner.barrier_va,
            owner.in_locked_range(),
            res is None ==> {
                &&& owner@.cur_va >= (old(owner)@.cur_va + len) as Vaddr
                &&& owner@.mappings =~= old(owner)@.mappings
                &&& old(owner)@.mappings.filter(|m: Mapping|
                    old(owner)@.cur_va <= m.va_range.start < (old(owner)@.cur_va + len) as Vaddr) =~= Set::<Mapping>::empty()
            },
            res is Some ==> {
                &&& owner@.mappings =~= old(owner)@.mappings.difference(
                    old(owner)@.mappings.filter(|m: Mapping| old(owner)@.cur_va <= m.va_range.start < owner@.cur_va))
            },
            res is Some ==> res.unwrap() is Mapped ==> {
                old(owner)@.mappings.filter(|m: Mapping| old(owner)@.cur_va <= m.va_range.start < owner@.cur_va).len() == 1
            },
            res is Some ==> res.unwrap() is StrayPageTable ==> {
                old(owner)@.mappings.filter(|m: Mapping| old(owner)@.cur_va <= m.va_range.start < owner@.cur_va).len()
                    == (res.unwrap()->StrayPageTable_num_frames) as nat
            },
    )]
    #[verifier::external_body]
    pub fn take_next(&mut self, len: usize) -> (r: Option<PageTableFrag<C>>) {
        (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.find_next_impl(len, true, true))?;

        let tracked absent_entry_owner = EntryOwner::new_absent(
            owner.cur_entry_owner().path,
            owner.level,
        );
        let tracked subtree = OwnerSubtree::new_val_tracked(
            absent_entry_owner,
            (owner.continuations.tracked_borrow(owner.level - 1).tree_level + 1) as nat,
        );

        assert(subtree.value.meta_slot_paddr() is None);
        proof {
            owner.absent_not_in_tree(subtree.value);
        }

        #[verus_spec(with Tracked(owner), Tracked(subtree), Tracked(regions), Tracked(guards))]
        let frag = self.replace_cur_entry(Child::None);

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
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
            old(self).inner.level < NR_LEVELS,
            old(owner).cur_entry_owner().is_frame(),
            op.requires((old(owner).cur_entry_owner().frame.unwrap().prop,)),
        )]
    pub fn protect_next(
        &mut self,
        len: usize,
        op: impl FnOnce(PageProperty) -> PageProperty,
    ) -> Option<Range<Vaddr>> {
        (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.find_next_impl(len, false, true))?;

        // find_next_impl ensures: res is Some && !find_unmap_subtree ==> is_frame()
        // find_unmap_subtree=false was passed and we're on the Some path after ?
        assert(owner.cur_entry_owner().is_frame());

        // The prop is preserved from old(owner) to the found entry
        assert(owner.cur_entry_owner().frame.unwrap().prop == old(
            owner,
        ).cur_entry_owner().frame.unwrap().prop);

        #[verus_spec(with Tracked(owner), Tracked(regions))]
        let mut entry = self.inner.cur_entry();

        proof { reveal(CursorContinuation::inv_children); }
        assert(entry.pte.prop() == owner.cur_entry_owner().frame.unwrap().prop) by {
            assert(owner.cur_entry_owner().match_pte(
                entry.pte,
                owner.cur_entry_owner().parent_level,
            ));
        };

        let ghost owner0 = *owner;

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let ghost cont0 = continuation;
        let tracked mut child_owner = continuation.take_child();
        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        #[verus_spec(with Tracked(&mut child_owner.value), Tracked(&mut parent_owner), Tracked(&mut continuation.guard_perm))]
        entry.protect(op);

        let ghost child_owner_path = child_owner.value.path;
        let ghost child_owner_mapped_pa = child_owner.value.frame.unwrap().mapped_pa;
        let ghost child_owner_slot_perm = child_owner.value.frame.unwrap().slot_perm;
        let ghost child_owner_parent_level = child_owner.value.parent_level;

        proof {
            continuation.put_child(child_owner);
            continuation.entry_own.node = Some(parent_owner);
            cont0.take_put_child();
            owner.continuations.tracked_insert(owner.level - 1, continuation);
            owner0.protect_preserves_cursor_inv_relate(*owner, *regions);
        }

        #[verus_spec(with Tracked(owner))]
        let protected_va = self.inner.cur_va_range();

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.move_forward();

        Some(protected_va)
    }

    #[verifier::rlimit(200)]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(new_owner): Tracked<OwnerSubtree<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    fn replace_cur_entry(&mut self, new_child: Child<C>) -> (res: Option<PageTableFrag<C>>)
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
            new_owner.inv(),
            new_owner.value.is_node() ==> new_owner.value.node.unwrap().level + 1 == new_owner.value.parent_level,
            new_owner.level == old(owner).continuations[old(owner).level - 1].tree_level + 1,
            new_owner.value.parent_level == old(owner).continuations[old(owner).level - 1].child().value.parent_level,
            new_owner.value.path == old(owner).continuations[old(owner).level - 1].path().push_tail(
                old(owner).continuations[old(owner).level - 1].idx as usize,
            ),
            new_child.wf(new_owner.value),
            new_owner.value.is_node() ==> old(regions).slot_owners[
                frame_to_index(new_owner.value.meta_slot_paddr().unwrap())
            ].inner_perms.ref_count.value() != REF_COUNT_UNUSED,
            new_owner.value.is_node() ==> old(regions).slots.contains_key(
                frame_to_index(new_owner.value.meta_slot_paddr().unwrap())
            ),
            new_owner.value.in_scope,
            new_owner == OwnerSubtree::new_val(new_owner.value, new_owner.level as nat),
            new_owner.value.relate_region(*old(regions)),
            new_owner.tree_predicate_map(
                new_owner.value.path,
                CursorOwner::<'rcu, C>::node_unlocked(*old(guards)),
            ),
            old(owner).map_full_tree(
                |entry_owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry_owner.meta_slot_paddr_neq(new_owner.value),
            ),
            // panic
            !C::TOP_LEVEL_CAN_UNMAP_spec() ==> old(owner).level < NR_LEVELS,
        ensures
            owner@.mappings == old(owner)@.mappings - PageTableOwner(
                old(owner).cur_subtree(),
            )@.mappings + PageTableOwner(new_owner)@.mappings,
            self.inner.invariants(*owner, *regions, *guards),
            owner.va == old(owner).va,
            self.inner.level == old(self).inner.level,
            owner.guard_level == old(owner).guard_level,
            owner.in_locked_range(),
            // If the current entry was absent before the replace, no old fragment is returned.
            old(owner).cur_entry_owner().is_absent() ==> res is None,
            // path_if_in_pt is changed only for new_owner's slot; all others are preserved.
            // (new_owner.value here is the post-into_pte state; meta_slot_paddr() is unchanged.)
            forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                (new_owner.value.is_absent() || idx != frame_to_index(new_owner.value.meta_slot_paddr().unwrap()))
                    ==> regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
    {
        proof { reveal(CursorContinuation::inv_children); }

        let ghost owner0 = *owner;
        let ghost regions0 = *regions;
        let ghost guard_level = owner.guard_level;
        let rcu_guard = self.inner.rcu_guard;

        let tracked mut new_owner = new_owner;

        let va = self.inner.va;
        let level = self.inner.level;

        #[verus_spec(with Tracked(owner), Tracked(regions))]
        let mut cur_entry = self.inner.cur_entry();

        let tracked mut continuation = owner.continuations.tracked_remove((owner.level - 1) as int);
        let ghost cont0 = continuation;
        let ghost owner1 = *owner;
        let tracked old_child_owner = continuation.take_child();

        let ghost cont1 = continuation;
        assert(cont1.view_mappings() == cont0.view_mappings()
            - cont0.view_mappings_take_child_spec()) by {
            cont0.view_mappings_take_child();
            assert(cont1 == cont0.take_child_spec().1);
        }
        assert(owner.continuations == owner0.continuations.remove(owner.level - 1));

        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        let ghost pre_new_owner_value = new_owner.value;
        // Capture the old child value before Entry::replace mutates it (from_pte_owner_spec
        // only changes in_scope, so meta_slot_paddr() is unchanged, but we need the pre-replace
        // value to match Entry::relate_region_neq_preserved's old(owner) parameter).
        let ghost old_child_pre_replace = old_child_owner.value;

        assert(!old_child_owner.value.in_scope) by {
            owner0.continuations_not_in_scope();
            assert(owner0.continuations[(owner0.level - 1) as int].children[cont0.idx as int] is Some);
        };

        #[verus_spec(with Tracked(regions),
            Tracked(&mut old_child_owner.value),
            Tracked(&mut new_owner.value),
            Tracked(&mut parent_owner),
            Tracked(&mut continuation.guard_perm)
        )]
        let old = cur_entry.replace(new_child);
        let ghost old_child_snap = old; // ghost alias to avoid `old(...)` keyword ambiguity in proofs

        // Pin relate_region_neq_preserved: for entries with paddr ≠ old_child and ≠ new_child,
        // relate_region is preserved from regions0 to post-replace *regions.
        // This is Entry::replace's postcondition (line 278 in entry.rs).
        assert(Entry::<C>::relate_region_neq_preserved(
            old_child_pre_replace,
            pre_new_owner_value,
            regions0,
            *regions,
        ));

        // Pin the path_if_in_pt preservation fact to a static snapshot so Z3 doesn't re-trigger
        // on later modifications to `regions`. The postcondition of `replace` gives us this with
        // old(regions) == regions0 (since cur_entry() takes only an immutable ref to regions).
        let ghost regions_after_replace = *regions;
        assert(cur_entry.idx == continuation.idx) by {
            assert(cur_entry.idx == owner0.continuations[(owner0.level - 1) as int].idx);
        };

        proof {
            continuation.entry_own.node = Some(parent_owner);
            continuation.put_child(new_owner);
            cont1.view_mappings_put_child(new_owner);

            let ghost final_cont = continuation;
            owner.continuations.tracked_insert((owner.level - 1) as int, continuation);

            owner0.view_mappings_take_lowest(owner1);
            owner1.view_mappings_put_lowest(*owner, continuation);

            let level = owner0.level;
            let idx = cont0.idx as int;

            assert forall|j: int|
                #![trigger final_cont.children[j]]
                0 <= j < NR_ENTRIES && j != idx implies final_cont.children[j]
                == cont0.children[j] by {
                assert(cont1.children[j] == cont0.children[j]);
            };

            assert(new_owner.value.meta_slot_paddr() == pre_new_owner_value.meta_slot_paddr());
            // f_neq uses pre-replace old_child value so it matches relate_region_neq_preserved.
            // (from_pte_owner_spec only changes in_scope, so meta_slot_paddr() is unchanged.)
            let f_neq_new = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.meta_slot_paddr_neq(pre_new_owner_value);
            let f_neq_old = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.meta_slot_paddr_neq(old_child_pre_replace);
            let f_neq = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.meta_slot_paddr_neq(pre_new_owner_value)
                    && entry.meta_slot_paddr_neq(old_child_pre_replace);
            let f_region = PageTableOwner::<C>::relate_region_pred(regions0);
            let g_region = PageTableOwner::<C>::relate_region_pred(*regions);
            let f_path = PageTableOwner::<C>::path_tracked_pred(regions0);
            let g_path = PageTableOwner::<C>::path_tracked_pred(*regions);

            assert forall|i: int| #![auto] owner0.level <= i < NR_LEVELS implies {
                &&& owner.continuations[i].map_children(g_region)
                &&& owner.continuations[i].map_children(g_path)
            } by {
                assert(owner.continuations[i] == owner0.continuations[i]);
                let cont = owner0.continuations[i];
                assert forall|j: int|
                    #![auto]
                    0 <= j < NR_ENTRIES
                        && cont.children[j] is Some implies cont.children[j].unwrap().tree_predicate_map(
                cont.path().push_tail(j as usize), g_region) by {
                    let subtree = cont.children[j].unwrap();
                    let path_j = cont.path().push_tail(j as usize);
                    if old_child_pre_replace.meta_slot_paddr() is Some {
                        owner0.cursor_path_nesting(i, owner0.level as int - 1);
                        cont0.path().push_tail_property_index(idx as usize);
                        cont.path().push_tail_property_index(j as usize);
                        PageTableOwner::<C>::neq_old_from_path_disjoint(subtree, path_j, old_child_pre_replace, regions0);
                    } else {
                        OwnerSubtree::map_implies(subtree, path_j, f_region, f_neq_old);
                    }
                    OwnerSubtree::map_implies_and(subtree, path_j, f_neq_new, f_neq_old, f_neq);
                    OwnerSubtree::map_implies_and(subtree, path_j, f_region, f_neq, g_region);
                };
                cont.map_children_lift(f_path, g_path);
            };

            assert(new_owner.value.relate_region(*regions));
            assert(!new_owner.value.is_absent() ==>
                PageTableOwner::<C>::path_tracked_pred(*regions)(new_owner.value, new_owner.value.path));
            let child_path = final_cont.path().push_tail(idx as usize);
            assert(new_owner.tree_predicate_map(child_path, g_region)) by {
                assert forall|lv: nat, p: TreePath<NR_ENTRIES>| lv < INC_LEVELS implies
                    #[trigger] g_region(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::default(lv), p) by {}; // default is absent
                OwnerSubtree::new_val_tree_predicate_map(new_owner, child_path, g_region);
            };
            assert(new_owner.tree_predicate_map(child_path, g_path)) by {
                assert forall|lv: nat, p: TreePath<NR_ENTRIES>| lv < INC_LEVELS implies
                    #[trigger] g_path(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::default(lv), p) by {}; // default.meta_slot_paddr() is None
                OwnerSubtree::new_val_tree_predicate_map(new_owner, child_path, g_path);
            };

            assert(final_cont.map_children(g_region)) by {
                assert forall|j: int|
                    #![auto]
                    0 <= j < NR_ENTRIES
                        && final_cont.children[j] is Some implies final_cont.children[j].unwrap().tree_predicate_map(
                final_cont.path().push_tail(j as usize), g_region) by {
                    if j != idx as int {
                        let subtree = cont0.children[j].unwrap();
                        let path_j = final_cont.path().push_tail(j as usize);
                        if old_child_pre_replace.meta_slot_paddr() is Some {
                            cont0.path().push_tail_property_index(j as usize);
                            cont0.path().push_tail_property_index(idx as usize);
                            cont0.path().push_tail_property_len(j as usize);
                            PageTableOwner::<C>::neq_old_from_path_disjoint(
                                subtree, path_j, old_child_pre_replace, regions0,
                            );
                        } else {
                            OwnerSubtree::map_implies(subtree, path_j, f_region, f_neq_old);
                        }
                        OwnerSubtree::map_implies_and(subtree, path_j, f_neq_new, f_neq_old, f_neq);
                        OwnerSubtree::map_implies_and(subtree, path_j, f_region, f_neq, g_region);
                    }
                };
            };

            final_cont.map_children_lift_skip_idx(cont0, idx as int, f_path, g_path);

            assert(owner.relate_region(*regions));

            assert forall|j: int|
                #![trigger final_cont.children[j]]
                0 <= j < NR_ENTRIES && final_cont.children[j] is Some implies {
                &&& final_cont.children[j].unwrap().value.path == final_cont.path().push_tail(
                    j as usize,
                )
                &&& final_cont.children[j].unwrap().value.parent_level == final_cont.level()
                &&& final_cont.children[j].unwrap().inv()
                &&& final_cont.children[j].unwrap().level == final_cont.tree_level + 1
            } by {
                if j != idx {
                    assert(final_cont.children[j] == cont0.children[j]);
                }
            };
        }

        let ghost owner_after_replace = *owner;
        let ghost regions_after_replace = *regions;

        let result = match old {
            Child::None => None,
            Child::Frame(pa, ch_level, prop) => {
                proof {
                    let ghost entry_owner_snap = old_child_owner.value;
                    assert(old_child_snap.invariants(entry_owner_snap, regions_after_replace));
                    assert(entry_owner_snap.is_frame());
                    assert(entry_owner_snap.relate_region(regions_after_replace));

                    let tracked frame_own = old_child_owner.value.frame.tracked_take();
                    let idx = frame_to_index(pa);
                    regions.slots.tracked_insert(idx, frame_own.slot_perm);
                    regions_after_replace.frame_slot_perm_insert_preserves_inv(idx, frame_own.slot_perm, *regions);

                    assert forall |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                        PageTableOwner::<C>::relate_region_pred(regions_after_replace)(e, p)
                        implies #[trigger] PageTableOwner::<C>::relate_region_pred(*regions)(e, p) by {
                        e.relate_region_slot_owners_only(regions_after_replace, *regions);
                    };
                    assert(regions.slot_owners == regions_after_replace.slot_owners);

                    owner_after_replace.relate_region_preserved(*owner, regions_after_replace, *regions);
                }
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
                // debug_assert_eq!(pt.level(), level - 1);
                if !C::TOP_LEVEL_CAN_UNMAP() {
                    assert(!C::TOP_LEVEL_CAN_UNMAP_spec());
                    if level as usize == NR_LEVELS {
                        assert(owner.level == NR_LEVELS);

                        let _ = ManuallyDrop::new(pt, Tracked(regions));  // leak it to make shared PTs stay `'static`.
                        assert(false);
                        return None;
                        // panic!("Unmapping shared kernel page table nodes");
                    }
                }
                // SAFETY: We must have locked this node.

                let ghost owner2 = *owner;
                let ghost child_entry = old_child_owner.value;

                let tracked mut old_node_owner = old_child_owner.value.node.tracked_take();

                let ghost regions_before_borrow = *regions;

                #[verus_spec(with Tracked(regions), Tracked(& old_node_owner.meta_perm))]
                let borrow_pt = pt.borrow();

                let ghost regions_after_borrow = *regions;

                proof_decl! {
                    let tracked mut guard_perm: Tracked<GuardPerm<'rcu, C>>;
                }

                let ghost guards0 = *guards;

                #[verus_spec(with Tracked(&old_node_owner), Tracked(guards) => Tracked(guard_perm))]
                let locked_pt = borrow_pt.make_guard_unchecked(rcu_guard);

                proof {
                    owner.map_children_implies(
                        CursorOwner::node_unlocked(guards0),
                        CursorOwner::node_unlocked_except(*guards, old_node_owner.meta_perm.addr()),
                    );
                }

                let ghost guards1 = *guards;
                let ghost locked_addr = old_node_owner.meta_perm.addr();
                let ghost owner_before_dfs = *owner;

                // SAFETY:
                //  - We checked that we are not unmapping shared kernel page table nodes.
                //  - We must have locked the entire sub-tree since the range is locked.
                #[verus_spec(with Tracked(owner), Tracked(guards), Ghost(locked_addr))]
                let num_frames = locking::dfs_mark_stray_and_unlock(rcu_guard, locked_pt);

                proof {
                    owner.map_children_implies(
                        CursorOwner::node_unlocked_except(guards1, locked_addr),
                        CursorOwner::node_unlocked(*guards),
                    );

                    // Pre-establish cont_entries_relate_region for all continuations.
                    owner0.cont_entries_relate_region(regions0);

                    reveal(CursorContinuation::inv_children);

                    assert forall|i: int|
                        owner.level - 1 <= i < NR_LEVELS implies
                        #[trigger] owner.continuations[i].node_locked(*guards) by {
                        let cont_low = owner0.continuations[(owner0.level - 1) as int];
                        cont_low.path().push_tail_property_len(cont_low.idx as usize);
                        owner0.continuations[i].entry_own.nodes_different_paths_different_addrs(old_child_pre_replace, regions0);
                    };

                    let ghost pt_idx = pt.index();
                    assert(regions_before_borrow =~= regions_after_replace);
                    owner_after_replace.relate_region_borrow_slot(
                        regions_after_replace,
                        regions_after_borrow,
                        pt_idx,
                    );
                    assert(owner_before_dfs.relate_region(*regions));

                    let f = PageTableOwner::<C>::relate_region_pred(*regions);

                    owner_before_dfs.cont_entries_relate_region(*regions);
                    assert forall|i: int| #![auto] owner.level - 1 <= i < NR_LEVELS implies {
                        &&& f(owner.continuations[i].entry_own, owner.continuations[i].path())
                        &&& owner.continuations[i].map_children(f)
                    } by {
                        if i >= owner.level as int {
                            assert(owner.continuations[i] == owner_before_dfs.continuations[i]);
                        } else {
                            assert(owner.continuations[i].entry_own
                                == owner_before_dfs.continuations[i].entry_own);
                            assert(forall|j: int|
                                0 <= j < NR_ENTRIES ==>
                                #[trigger] owner.continuations[owner.level - 1].children[j] ==
                                owner_before_dfs.continuations[owner.level - 1].children[j]);
                        }
                    };

                    assert forall|i: int|
                        #![auto]
                        owner.level - 1 <= i < NR_LEVELS
                            implies owner.continuations[i].view_mappings()
                        == owner_before_dfs.continuations[i].view_mappings() by {
                            assert(owner.continuations[i].children
                                =~= owner_before_dfs.continuations[i].children);
                    };

                    assert(forall|m: Mapping|
                        owner.view_mappings().contains(m) <==> owner_before_dfs.view_mappings().contains(m));
                }

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

        assert(forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
            (new_owner.value.is_absent() || idx != frame_to_index(new_owner.value.meta_slot_paddr().unwrap()))
                ==> regions.slot_owners[idx].path_if_in_pt == regions0.slot_owners[idx].path_if_in_pt
        ) by {
            assert(forall|i: usize| #![trigger regions.slot_owners[i].path_if_in_pt]
                regions.slot_owners[i].path_if_in_pt == regions_after_replace.slot_owners[i].path_if_in_pt);
        };

        result
    }
}

} // verus!
