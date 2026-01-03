// SPDX-License-Identifier: MPL-2.0
//! Implementation of the locking protocol.
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Range, sync::atomic::Ordering};

use vstd::prelude::*;

use vstd::simple_pptr::*;

use crate::mm::{
    nr_subpage_per_huge, paddr_to_vaddr,
    page_table::*,
    Vaddr, Paddr, PagingLevel, PagingConstsTrait, PagingConsts,
    PAGE_SIZE, NR_ENTRIES, NR_LEVELS
};

use vstd_extra::array_ptr::*;

use crate::mm::page_table::*;
use crate::specs::task::InAtomicMode;

use core::ops::IndexMut;

verus! {

pub assume_specification<Idx: Clone>[ Range::<Idx>::clone ](range: &Range<Idx>) -> (res: Range<Idx>)
    ensures
        res == *range,
;

#[verus_spec(
    with Tracked(pt_own): Tracked<&mut PageTableOwner<C>>,
        Tracked(guard_perm): Tracked<& vstd::simple_pptr::PointsTo<PageTableGuard<'rcu, C>>>
)]
#[verifier::external_body]
pub fn lock_range<'rcu, C: PageTableConfig, A: InAtomicMode>(
    pt: &'rcu PageTable<C>,
    guard: &'rcu A,
    va: &Range<Vaddr>,
) -> (Cursor<'rcu, C, A>, Tracked<CursorOwner<'rcu, C>>) {
    unimplemented!()
    // The re-try loop of finding the sub-tree root.
    //
    // If we locked a stray node, we need to re-try. Otherwise, although
    // there are no safety concerns, the operations of a cursor on an stray
    // sub-tree will not see the current state and will not change the current
    // state, breaking serializability.
    /*
    let mut subtree_root = loop {
        if let Some(subtree_root) = try_traverse_and_lock_subtree_root(pt, guard, va) {
            break subtree_root;
        }
    };
    *//*
    #[verus_spec(with Tracked(pt_own), Tracked(guard_perm))]
    let subtree_root = try_traverse_and_lock_subtree_root(pt, guard, va);

    assert(subtree_root is Some) by { admit() };
    let subtree_root = subtree_root.unwrap();
    let tracked entry_own = pt_own.tree.value;
    //    let tracked child_node = owner_node.tracked_child()

    // Once we have locked the sub-tree that is not stray, we won't read any
    // stray nodes in the following traversal since we must lock before reading.
    let subtree_guard = subtree_root.borrow(Tracked(guard_perm));
    let guard_level = subtree_guard.level();
    let cur_node_va = align_down(va.start, page_size(guard_level + 1));
    dfs_acquire_lock(guard, subtree_root, cur_node_va, va.clone());

    let mut path = [None, None, None, None];
    path[guard_level as usize - 1] = Some(subtree_root);

    Cursor::<'rcu, C, A> {
        path,
        rcu_guard: guard,
        level: guard_level,
        guard_level,
        va: va.start,
        barrier_va: va.clone(),
        _phantom: PhantomData,
    }*/
}

#[verifier::external_body]
pub fn unlock_range<C: PageTableConfig, A: InAtomicMode>(cursor: &mut Cursor<'_, C, A>) {
    unimplemented!()/*    let end = cursor.guard_level as usize - 1;
    for i in (0..end) {
        if let Some(guard) = cursor.path[end - i].take() {
            let _ = ManuallyDrop::new(guard);
        }
    }
    let guard_node = cursor.path[cursor.guard_level as usize - 1].take().unwrap();
    let cur_node_va = align_down(cursor.barrier_va.start, page_size(cursor.guard_level + 1));

    // SAFETY: A cursor maintains that its corresponding sub-tree is locked.
    dfs_release_lock(
        cursor.rcu_guard,
        guard_node,
        cur_node_va,
        cursor.barrier_va.clone(),
    );*/

}

/// Finds and locks an intermediate page table node that covers the range.
///
/// If that node (or any of its ancestors) does not exist, we need to lock
/// the parent and create it. After the creation the lock of the parent will
/// be released and the new node will be locked.
///
/// If this function founds that a locked node is stray (because of racing with
/// page table recycling), it will return `None`. The caller should retry in
/// this case to lock the proper node.
#[verus_spec(
    with Tracked(pt_own): Tracked<&mut PageTableOwner<C>>,
        Tracked(guard_perm): Tracked<&mut vstd::simple_pptr::PointsTo<PageTableGuard<'rcu, C>>>
)]
#[verifier::external_body]
fn try_traverse_and_lock_subtree_root<'rcu, C: PageTableConfig, A: InAtomicMode>(
    pt: &PageTable<C>,
    guard: &'rcu A,
    va: &Range<Vaddr>,
) -> Option<PPtr<PageTableGuard<'rcu, C>>> {
    let mut cur_node_guard: Option<PPtr<PageTableGuard<C>>> = None;
    let mut cur_pt_addr = pt.root.start_paddr();

    let end = C::NR_LEVELS();
    for cur_level in 0..end {
        let start_idx = pte_index::<C>(va.start, end - cur_level + 1);
        let level_too_high = {
            let end_idx = pte_index::<C>(va.end - 1, end - cur_level + 1);
            (end - cur_level + 1) > 1 && start_idx == end_idx
        };
        if !level_too_high {
            break ;
        }
        let cur_pt_ptr = ArrayPtr::<C::E, CONST_NR_ENTRIES>::from_addr(paddr_to_vaddr(cur_pt_addr));
        // SAFETY:
        //  - The page table node is alive because (1) the root node is alive and
        //    (2) all child nodes cannot be recycled because we're in the RCU critical section.
        //  - The index is inside the bound, so the page table entry is valid.
        //  - All page table entries are aligned and accessed with atomic operations only.
        let cur_pte = load_pte(cur_pt_ptr.add(start_idx), Ordering::Acquire);

        if cur_pte.is_present() {
            if cur_pte.is_last(end - cur_level + 1) {
                break ;
            }
            cur_pt_addr = cur_pte.paddr();
            cur_node_guard = None;
            continue ;
        }
        // In case the child is absent, we should lock and allocate a new page table node.

        let mut pt_guard = if let Some(pt_guard) = cur_node_guard.take() {
            pt_guard
        } else {
            // SAFETY: The node must be alive for at least `'rcu` since the
            // address is read from the page table node.
            let node_ref = PageTableNodeRef::<'rcu, C>::borrow_paddr(cur_pt_addr);
            node_ref.lock(guard)
        };

        let mut guard_val = pt_guard.take(Tracked(guard_perm));
        let tracked node_owner = pt_own.tree.value.node.tracked_take();
        let stray_mut = guard_val.stray_mut(); //.borrow(Tracked(&node_owner.as_node.meta_own.stray));

        proof {
            pt_guard.put(Tracked(guard_perm), guard_val);
            pt_own.tree.value.node = Some(node_owner);
        }

        if *(stray_mut.borrow(Tracked(&node_owner.as_node.meta_own.stray))) {
            return None;
        }
        let mut cur_entry = PageTableGuard::<'rcu, C>::entry(pt_guard, start_idx);
        if cur_entry.is_none() {
            let allocated_guard = cur_entry.alloc_if_none(guard).unwrap();
            let guard_val = allocated_guard.borrow(Tracked(guard_perm));
            cur_pt_addr = guard_val.start_paddr();
            cur_node_guard = Some(allocated_guard);
        } else if cur_entry.is_node() {
            let opt_pt = match cur_entry.to_ref() {
                ChildRef::PageTable(pt) => Some(pt),
                _ => None,
            };
            let pt = opt_pt.unwrap();

            cur_pt_addr = pt.start_paddr();
            cur_node_guard = None;
        } else {
            break ;
        }
    }

    let mut pt_guard = if let Some(pt_guard) = cur_node_guard {
        pt_guard
    } else {
        // SAFETY: The node must be alive for at least `'rcu` since the
        // address is read from the page table node.
        let node_ref = PageTableNodeRef::<'rcu, C>::borrow_paddr(cur_pt_addr);
        node_ref.lock(guard)
    };

    let mut guard_val = pt_guard.take(Tracked(guard_perm));
    let tracked node_owner = pt_own.tree.value.node.tracked_take();
    let stray_mut = guard_val.stray_mut();

    proof {
        pt_guard.put(Tracked(guard_perm), guard_val);
        pt_own.tree.value.node = Some(node_owner);
    }

    if *(stray_mut.borrow(Tracked(&node_owner.as_node.meta_own.stray))) {
        return None;
    }
    Some(pt_guard)
}

/// Acquires the locks for the given range in the sub-tree rooted at the node.
///
/// `cur_node_va` must be the virtual address of the `cur_node`. The `va_range`
/// must be within the range of the `cur_node`. The range must not be empty.
///
/// The function will forget all the [`PageTableGuard`] objects in the sub-tree.
#[verus_spec(
    with Tracked(entry_own): Tracked<EntryOwner<C>>,
        Tracked(guard_perm): Tracked<&vstd::simple_pptr::PointsTo<PageTableGuard<'rcu, C>>>
)]
#[verifier::external_body]
fn dfs_acquire_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &A,
    cur_node: PPtr<PageTableGuard<'rcu, C>>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
) {
    //    debug_assert!(!*cur_node.stray_mut());
    let cur_guard = cur_node.borrow(Tracked(guard_perm));
    let cur_level = cur_guard.level();
    if cur_level == 1 {
        return ;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    for i in idx_range {
        let child = PageTableGuard::<'rcu, C>::entry(cur_node, i);
        match child.to_ref() {
            ChildRef::PageTable(pt) => {
                let mut pt_guard = pt.lock(guard);
                let child_node_va = cur_node_va + i * page_size(cur_level);
                let child_node_va_end = child_node_va + page_size(cur_level);
                let va_start = va_range.start.max(child_node_va);
                let va_end = va_range.end.min(child_node_va_end);
                dfs_acquire_lock(guard, pt_guard, child_node_va, va_start..va_end);
                let _ = ManuallyDrop::new(pt_guard);
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {},
        }
    }
}

/// Releases the locks for the given range in the sub-tree rooted at the node.
///
/// # Safety
///
/// The caller must ensure that the nodes in the specified sub-tree are locked
/// and all guards are forgotten.
#[verus_spec(
    with Tracked(entry_own): Tracked<EntryOwner<C>>,
        Tracked(guard_perm): Tracked<&vstd::simple_pptr::PointsTo<PageTableGuard<'rcu, C>>>
)]
#[verifier::external_body]
unsafe fn dfs_release_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &'rcu A,
    cur_node: PPtr<PageTableGuard<'rcu, C>>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
) {
    let cur_guard = cur_node.borrow(Tracked(guard_perm));
    let cur_level = cur_guard.level();
    if cur_level == 1 {
        return ;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let end = idx_range.end;
    for i in idx_range {
        let child = PageTableGuard::<'rcu, C>::entry(cur_node, end - i);
        match child.to_ref() {
            ChildRef::PageTable(pt) => {
                // SAFETY: The caller ensures that the node is locked and the new guard is unique.
                let child_node = pt.make_guard_unchecked(guard);
                let child_node_va = cur_node_va + (end - i) * page_size(cur_level);
                let child_node_va_end = child_node_va + page_size(cur_level);
                let va_start = va_range.start.max(child_node_va);
                let va_end = va_range.end.min(child_node_va_end);
                // SAFETY: The caller ensures that all the nodes in the sub-tree are locked and all
                // guards are forgotten.
                dfs_release_lock(guard, child_node, child_node_va, va_start..va_end);
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {},
        }
    }
}

/// Marks all the nodes in the sub-tree rooted at the node as stray, and
/// returns the num of pages mapped within the sub-tree.
///
/// It must be called upon the node after the node is removed from the parent
/// page table. It also unlocks the nodes in the sub-tree.
///
/// This function returns the number of physical frames mapped in the sub-tree.
///
/// # Safety
///
/// The caller must ensure that all the nodes in the sub-tree are locked
/// and all guards are forgotten.
///
/// This function must not be called upon a shared node, e.g., the second-
/// top level nodes that the kernel space and user space share.
#[verus_spec(
    with Tracked(owner): Tracked<&mut CursorOwner<'a, C>>
)]
#[verifier::external_body]
pub fn dfs_mark_stray_and_unlock<'a, C: PageTableConfig, A: InAtomicMode>(
    rcu_guard: &A,
    sub_tree: PPtr<PageTableGuard<'a, C>>,
) -> usize {
    unimplemented!();
    /*
    let mut sub_tree_val = sub_tree.take(Tracked(guard_perm));
    let stray_mut = sub_tree_val.stray_mut();
    let tracked node_owner = entry_own.node.tracked_take();
    let stray = stray_mut.take(Tracked(&mut node_owner.as_node.meta_own.stray));

    stray_mut.put(Tracked(&mut node_owner.as_node.meta_own.stray), true);

    proof {
        entry_own.node = Some(node_owner);
    }

    if sub_tree_val.level() == 1 {
        return sub_tree_val.nr_children() as usize;
    }
    sub_tree.put(Tracked(guard_perm), sub_tree_val);

    let mut num_frames = 0;

    let end = nr_subpage_per_huge::<C>();
    for i in 0..end {
        let child = PageTableGuard::entry(sub_tree, i);
        match child.to_ref() {
            ChildRef::PageTable(pt) => {
                // SAFETY: The caller ensures that the node is locked and the new guard is unique.
                let locked_pt = pt.make_guard_unchecked(rcu_guard);
                // SAFETY: The caller ensures that all the nodes in the sub-tree are locked and all
                // guards are forgotten.
                num_frames += dfs_mark_stray_and_unlock(rcu_guard, locked_pt);
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {},
        }
    }

    num_frames*/
}

#[verifier::external_body]
fn dfs_get_idx_range<C: PagingConstsTrait>(
    cur_node_level: PagingLevel,
    cur_node_va: Vaddr,
    va_range: &Range<Vaddr>,
) -> Range<usize> {
    //    debug_assert!(va_range.start >= cur_node_va);
    //    debug_assert!(va_range.end <= cur_node_va.saturating_add(page_size(cur_node_level + 1)));
    let start_idx = (va_range.start - cur_node_va) / page_size(cur_node_level);
    let end_idx = (va_range.end - cur_node_va).div_ceil(page_size(cur_node_level));

    //    debug_assert!(start_idx < end_idx);
    //    debug_assert!(end_idx <= nr_subpage_per_huge::<C>());

    start_idx..end_idx
}

} // verus!
