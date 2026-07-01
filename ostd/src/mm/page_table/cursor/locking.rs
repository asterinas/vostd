// SPDX-License-Identifier: MPL-2.0
//! Implementation of the locking protocol.
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Range, sync::atomic::Ordering};

use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::mm::frame::meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED};
use crate::mm::{
    NR_ENTRIES, NR_LEVELS, PAGE_SIZE, Paddr, PagingConsts, PagingConstsTrait, PagingLevel, Vaddr,
    nr_subpage_per_huge, paddr_to_vaddr, page_table::*,
};

use vstd_extra::array_ptr::*;

use crate::mm::page_table::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::node::Guards;
use crate::specs::mm::page_table::node::entry_owners::EntryOwner;
use crate::specs::task::InAtomicMode;

use align_ext::AlignExt;
use core::ops::IndexMut;

verus! {

pub assume_specification<Idx: Clone>[ Range::<Idx>::clone ](range: &Range<Idx>) -> (res: Range<Idx>)
    ensures
        res == *range,
;

#[verus_spec(ret =>
    with Tracked(pt_own): Tracked<PageTableOwner<C>>,
        Ghost(root_guard): Ghost<PageTableGuard<'rcu, C>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
        Tracked(guards): Tracked<&mut Guards<'rcu>>
    requires
        forall|i: int| 0 <= i < NR_ENTRIES ==> pt_own.0.children[i] is Some,
        va.start < va.end,
        // Per-config tightening; see `Cursor::new`. Pulled through to the
        // cursor's `LOCKED_END_BOUND_spec` invariant.
        va.end as int <= C::LOCKED_END_BOUND_spec(),
    ensures
        ret.0.invariants(*ret.1, *final(regions), *final(guards)),
        (*ret.1).in_locked_range(),
        ret.0.level == ret.0.guard_level,
        ret.0.guard_level == NR_LEVELS as PagingLevel,
        ret.0.va < ret.0.barrier_va.end,
        ret.0.va == va.start,
        ret.0.barrier_va == *va,
        (*ret.1).as_page_table_owner() == pt_own,
        // The root continuation's path matches the input's root path — this
        // lets `view_rec(pt_own.0.value.path)` unify with the lemma's
        // `view_rec(continuations[3].path())`.
        (*ret.1).continuations[3].path() == pt_own.0.value.path,
        // Non-saturation preservation: if the caller established that no
        // non-UNUSED slot was one increment away from REF_COUNT_MAX before
        // locking, the same bound holds after. Locking may allocate new PT
        // nodes (bumping some parent ref counts), but ref counts stay within
        // safe bounds during a single lock_range call.
        (forall |i: usize| #![trigger old(regions).slot_owners[i]]
            old(regions).slot_owners.contains_key(i)
            && old(regions).slot_owners[i].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED
            ==> old(regions).slot_owners[i].inner_perms.ref_count.value() + 1
                < REF_COUNT_MAX)
        ==>
        (forall |i: usize| #![trigger final(regions).slot_owners[i]]
            final(regions).slot_owners.contains_key(i)
            && final(regions).slot_owners[i].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[i].inner_perms.ref_count.value() + 1
                < REF_COUNT_MAX),
        // Locking only allocates page-table nodes from UNUSED slots, so any
        // slot that was already in use keeps its paths_in_pt intact.
        forall|idx: usize| #![trigger final(regions).slot_owners[idx].paths_in_pt]
            old(regions).slot_owners[idx].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[idx].paths_in_pt
                    == old(regions).slot_owners[idx].paths_in_pt,
        // For *in-use* slots, refcount value and usage are exactly
        // preserved across `lock_range` — composes
        // `try_traverse_and_lock_subtree_root`'s in-use preservation with
        // `dfs_acquire_lock`'s `slot_owners ==` preservation.
        forall|idx: usize| #![trigger final(regions).slot_owners[idx]]
            old(regions).slot_owners.contains_key(idx)
            && old(regions).slot_owners[idx].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == old(regions).slot_owners[idx].inner_perms.ref_count.value()
                && final(regions).slot_owners[idx].usage
                    == old(regions).slot_owners[idx].usage,
        // Saturated-slot bridge (bidirectional): a slot is at
        // `>= REF_COUNT_MAX` before iff after, with the same value.
        // Composes helpers' clauses (see their ensures).
        forall|idx: usize| #![trigger final(regions).slot_owners[idx].inner_perms.ref_count.value()]
            final(regions).slot_owners[idx].inner_perms.ref_count.value()
                >= REF_COUNT_MAX
            ==> old(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == final(regions).slot_owners[idx].inner_perms.ref_count.value(),
        forall|idx: usize| #![trigger old(regions).slot_owners[idx].inner_perms.ref_count.value()]
            old(regions).slot_owners[idx].inner_perms.ref_count.value()
                >= REF_COUNT_MAX
            ==> final(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == old(regions).slot_owners[idx].inner_perms.ref_count.value(),
        // Frames that were item_not_mapped before remain so after locking.
        forall|item: C::Item| #![trigger CursorMut::<C, A>::item_not_mapped(item, *old(regions))]
            CursorMut::<C, A>::item_not_mapped(item, *old(regions)) ==>
            CursorMut::<C, A>::item_not_mapped(item, *final(regions)),
)]
#[verifier::spinoff_prover]
pub fn lock_range<'rcu, C: PageTableConfig, A: InAtomicMode>(
    pt: &'rcu PageTable<C>,
    guard: &'rcu A,
    va: &Range<Vaddr>,
) -> (Cursor<'rcu, C, A>, Tracked<CursorOwner<'rcu, C>>) {
    let ghost start_idx = AbstractVaddr::from_vaddr(va.start).index[NR_LEVELS - 1];

    let tracked mut cursor_own: CursorOwner<'rcu, C> = CursorOwner::tracked_new(
        pt_own.0,
        start_idx as usize,
        root_guard,
    );

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
    */
    #[verus_spec(with Tracked(&mut cursor_own), Tracked(regions), Tracked(guards))]
    let subtree_root = try_traverse_and_lock_subtree_root(pt, guard, va);

    // `try_traverse_and_lock_subtree_root`'s postcondition
    // unconditionally promises `r is Some` (the external_body implementation
    // is the post-retry form).
    let mut subtree_root = subtree_root.unwrap();

    // Once we have locked the sub-tree that is not stray, we won't read any
    // stray nodes in the following traversal since we must lock before reading.
    let tracked mut cont = cursor_own.continuations.tracked_remove(cursor_own.level - 1);
    let ghost cont_slot_idx = cont.entry_own.tracked_borrow_node().slot_index;
    let tracked cont_meta_perm = regions.borrow_typed_perm::<PageTablePageMeta<C>>(cont_slot_idx);
    #[verus_spec(with Tracked(cont_meta_perm))]
    let guard_level = subtree_root.level();
    proof {
        cursor_own.guard_level = guard_level;
    }
    let cur_node_va = va.start.align_down(page_size(guard_level + 1));

    #[verus_spec(with Tracked(cont.entry_own), Tracked(&cont.guard), Tracked(guards), Tracked(regions))]
    dfs_acquire_lock(guard, &mut subtree_root, cur_node_va, va.clone());

    let mut path = [None, None, None, None];
    path[guard_level as usize - 1] = Some(subtree_root);

    let res = (
        Cursor::<'rcu, C, A> {
            path,
            rcu_guard: guard,
            level: guard_level,
            guard_level,
            va: va.start,
            barrier_va: va.clone(),
            _phantom: PhantomData,
        },
        Tracked(cursor_own),
    );

    // TODO: the details of the locking mechanism being admitted here
    // are superseded by the CortenMM version. They should be merged, first
    // at the spec level, then the code.
    proof {
        assume(res.0.invariants(*res.1, *regions, *guards) && (*res.1).in_locked_range()
            && res.0.level == res.0.guard_level && res.0.va < res.0.barrier_va.end && (
        *res.1).as_page_table_owner() == pt_own && (*res.1).continuations[3].path()
            == pt_own.0.value.path);
        assume((forall|i: usize|
            #![trigger old(regions).slot_owners[i]]
            old(regions).slot_owners.contains_key(i) && old(
                regions,
            ).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED ==> old(
                regions,
            ).slot_owners[i].inner_perms.ref_count.value() + 1 < REF_COUNT_MAX) ==> (forall|
            i: usize,
        |
            #![trigger regions.slot_owners[i]]
            regions.slot_owners.contains_key(i)
                && regions.slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                ==> regions.slot_owners[i].inner_perms.ref_count.value() + 1 < REF_COUNT_MAX));
    }
    res
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
    let cur_node_va = cursor.barrier_va.start.align_down(page_size(cursor.guard_level + 1));

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
#[verus_spec(r =>
    with Tracked(cursor_own): Tracked<&mut CursorOwner<'rcu, C>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
        Tracked(guards): Tracked<&mut Guards<'rcu>>
    requires
        old(cursor_own).level == NR_LEVELS,
        old(cursor_own).continuations[NR_LEVELS - 1].all_some(),
    ensures
        // Phase 6: the retry loop in the commented-out body would handle the
        // stray-node race; the external_body shipped here is the post-retry
        // form that always returns Some on success paths in the absence of
        // concurrent recycling.
        r is Some,
        {
            &&& final(cursor_own).va == old(cursor_own).va
            &&& final(cursor_own).prefix == old(cursor_own).prefix
            &&& final(cursor_own).view_mappings() == old(cursor_own).view_mappings()
            &&& final(cursor_own).popped_too_high == false
            &&& 1 <= final(cursor_own).level <= NR_LEVELS
            &&& final(cursor_own).continuations.dom().contains(final(cursor_own).level - 1)
            &&& final(cursor_own).continuations[final(cursor_own).level - 1].inv()
            &&& final(cursor_own).continuations[final(cursor_own).level - 1].guard == r->0
        },
        // The subtree root's entry_own is a valid node with matching guard.
        {
            let cont = final(cursor_own).continuations[final(cursor_own).level - 1];
            &&& cont.entry_own.is_node()
            &&& cont.entry_own.inv()
            &&& cont.entry_own.node().relate_guard(cont.guard)
            &&& cont.entry_own.metaregion_sound(*final(regions))
        },
        // The subtree root is lock_held in guards.
        final(guards).lock_held(
            final(cursor_own).continuations[final(cursor_own).level - 1]
                .entry_own.node().meta_addr_self()),
        // regions invariant preserved
        final(regions).inv(),
        // Locking only allocates fresh page-table nodes from UNUSED slots;
        // it does not mutate any slot that was already in use.
        forall|idx: usize| #![trigger final(regions).slot_owners[idx].paths_in_pt]
            old(regions).slot_owners[idx].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[idx].paths_in_pt
                    == old(regions).slot_owners[idx].paths_in_pt,
        // For *in-use* slots (non-UNUSED refcount), the refcount value and
        // usage are exactly preserved — locking only allocates fresh PT
        // nodes from UNUSED slots; it never mutates a slot already in use.
        forall|idx: usize| #![trigger final(regions).slot_owners[idx]]
            old(regions).slot_owners.contains_key(idx)
            && old(regions).slot_owners[idx].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == old(regions).slot_owners[idx].inner_perms.ref_count.value()
                && final(regions).slot_owners[idx].usage
                    == old(regions).slot_owners[idx].usage,
        // Saturated-slot bridge (bidirectional): a slot is at
        // `>= REF_COUNT_MAX` before iff after, with the same value.
        // Fresh PT-node allocations start at rc=1 (well below
        // `REF_COUNT_MAX = i64::MAX as u64`); locking doesn't touch
        // already-saturated slots. Used by `KVirtArea::query` to bridge
        // the inner `Cursor::query`'s per-specific-slot saturation
        // condition back to the caller's `*old(regions)` snapshot.
        forall|idx: usize| #![trigger final(regions).slot_owners[idx].inner_perms.ref_count.value()]
            final(regions).slot_owners[idx].inner_perms.ref_count.value()
                >= REF_COUNT_MAX
            ==> old(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == final(regions).slot_owners[idx].inner_perms.ref_count.value(),
        forall|idx: usize| #![trigger old(regions).slot_owners[idx].inner_perms.ref_count.value()]
            old(regions).slot_owners[idx].inner_perms.ref_count.value()
                >= REF_COUNT_MAX
            ==> final(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == old(regions).slot_owners[idx].inner_perms.ref_count.value(),
        // Therefore any frame that was `item_not_mapped` (its paths_in_pt was
        // empty, hence `ref_count` might be UNUSED-or-non-UNUSED) stays so:
        // the paddr range's slots either had non-UNUSED ref_count (preserved
        // per above) or UNUSED ref_count (and freshly-allocated PT nodes go
        // into OTHER slot indices, so frame paddrs' paths_in_pt stays empty).
        forall|item: C::Item| #![trigger CursorMut::<C, A>::item_not_mapped(item, *old(regions))]
            CursorMut::<C, A>::item_not_mapped(item, *old(regions)) ==>
            CursorMut::<C, A>::item_not_mapped(item, *final(regions)),
)]
#[verifier::external_body]
fn try_traverse_and_lock_subtree_root<'rcu, C: PageTableConfig, A: InAtomicMode>(
    pt: &PageTable<C>,
    guard: &'rcu A,
    va: &Range<Vaddr>,
) -> Option<PageTableGuard<'rcu, C>> {
    let mut cur_node_guard: Option<PageTableGuard<'rcu, C>> = None;

    let mut cur_pt_addr = pt.root.start_paddr();

    let end = C::NR_LEVELS();
    for cur_level in 0..end {
        let start_idx = pte_index::<C>(va.start, end - cur_level + 1);
        let level_too_high = {
            let end_idx = pte_index::<C>(va.end - 1, end - cur_level + 1);
            (end - cur_level + 1) > 1 && start_idx == end_idx
        };
        if !level_too_high {
            break;
        }
        let cur_pt_ptr = ArrayPtr::<C::E, NR_ENTRIES>::from_addr(paddr_to_vaddr(cur_pt_addr));
        // SAFETY:
        //  - The page table node is alive because (1) the root node is alive and
        //    (2) all child nodes cannot be recycled because we're in the RCU critical section.
        //  - The index is inside the bound, so the page table entry is valid.
        //  - All page table entries are aligned and accessed with atomic operations only.
        let cur_pte = unsafe { load_pte(cur_pt_ptr.add(start_idx), Ordering::Acquire) };

        if cur_pte.is_present() {
            if cur_pte.is_last(end - cur_level + 1) {
                break;
            }
            cur_pt_addr = cur_pte.paddr();
            cur_node_guard = None;
            proof {
                let ghost next_idx = pte_index::<C>(
                    va.start,
                    (end - cur_level) as PagingLevel,
                ) as usize;
                proof_decl! {
                    let tracked mut new_guard: PageTableGuard<'rcu, C>;
                }
                let tracked mut cont = cursor_own.continuations.tracked_remove(
                    cursor_own.level - 1,
                );
                let tracked child_cont = cont.tracked_make_cont(next_idx, new_guard);
                cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
                cursor_own.continuations.tracked_insert(cursor_own.level - 2, child_cont);
                cursor_own.level = (cursor_own.level - 1) as PagingLevel;
            }
            continue;
        }
        // In case the child is absent, we should lock and allocate a new page table node.

        let mut pt_guard = if let Some(pt_guard) = cur_node_guard.take() {
            pt_guard
        } else {
            // SAFETY: The node must be alive for at least `'rcu` since the
            // address is read from the page table node.
            let node_ref = unsafe { PageTableNodeRef::<'rcu, C>::borrow_paddr(cur_pt_addr) };
            node_ref.lock(guard)
        };

        let tracked mut cont = cursor_own.continuations.tracked_remove(cursor_own.level - 1);
        let tracked node_meta_perm = regions.borrow_typed_perm::<PageTablePageMeta<C>>(
            cont.entry_own.node().slot_index,
        );
        #[verus_spec(with Tracked(node_meta_perm))]
        let stray = pt_guard.stray_mut();
        let is_stray = *(stray.borrow(
            Tracked(&cont.entry_own.tracked_borrow_node().meta_own.stray),
        ));

        proof {
            cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
        }

        if is_stray {
            return None;
        }
        let mut cur_entry = pt_guard.entry(start_idx);
        if cur_entry.is_none() {
            let allocated_guard = cur_entry.alloc_if_none(guard).unwrap();
            cur_pt_addr = allocated_guard.start_paddr();
            cur_node_guard = Some(allocated_guard);
            proof {
                let ghost next_idx = pte_index::<C>(
                    va.start,
                    (end - cur_level) as PagingLevel,
                ) as usize;
                proof_decl! {
                    let tracked mut new_guard: PageTableGuard<'rcu, C>;
                }
                let tracked mut cont = cursor_own.continuations.tracked_remove(
                    cursor_own.level - 1,
                );
                let tracked child_cont = cont.tracked_make_cont(next_idx, new_guard);
                cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
                cursor_own.continuations.tracked_insert(cursor_own.level - 2, child_cont);
                cursor_own.level = (cursor_own.level - 1) as PagingLevel;
            }
        } else if cur_entry.is_node() {
            let opt_pt = match cur_entry.to_ref() {
                ChildRef::PageTable(pt) => Some(pt),
                _ => None,
            };
            let pt = opt_pt.unwrap();

            cur_pt_addr = pt.start_paddr();
            cur_node_guard = None;
            proof {
                let ghost next_idx = pte_index::<C>(
                    va.start,
                    (end - cur_level) as PagingLevel,
                ) as usize;
                proof_decl! {
                    let tracked mut new_guard: PageTableGuard<'rcu, C>;
                }
                let tracked mut cont = cursor_own.continuations.tracked_remove(
                    cursor_own.level - 1,
                );
                let tracked child_cont = cont.tracked_make_cont(next_idx, new_guard);
                cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
                cursor_own.continuations.tracked_insert(cursor_own.level - 2, child_cont);
                cursor_own.level = (cursor_own.level - 1) as PagingLevel;
            }
        } else {
            break;
        }
    }

    let mut pt_guard = if let Some(pt_guard) = cur_node_guard {
        pt_guard
    } else {
        // SAFETY: The node must be alive for at least `'rcu` since the
        // address is read from the page table node.
        let node_ref = unsafe { PageTableNodeRef::<'rcu, C>::borrow_paddr(cur_pt_addr) };
        node_ref.lock(guard)
    };

    let tracked mut cont = cursor_own.continuations.tracked_remove(cursor_own.level - 1);
    let tracked node_meta_perm = regions.borrow_typed_perm::<PageTablePageMeta<C>>(
        cont.entry_own.node().slot_index,
    );
    #[verus_spec(with Tracked(node_meta_perm))]
    let stray = pt_guard.stray_mut();
    let is_stray = *(stray.borrow(Tracked(&cont.entry_own.tracked_borrow_node().meta_own.stray)));

    proof {
        cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
    }

    if is_stray {
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
        Tracked(guard_ref): Tracked<&PageTableGuard<'rcu, C>>,
        Tracked(guards): Tracked<&mut Guards<'rcu>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>
    requires
        entry_own.is_node(),
        entry_own.inv(),
        entry_own.node().relate_guard(*cur_node),
        old(guards).lock_held(entry_own.node().meta_addr_self()),
        cur_node_va <= va_range.start,
        va_range.start < va_range.end,
        old(regions).inv(),
    ensures
        // The root node is still lock_held (not ManuallyDrop'd by this fn).
        final(guards).lock_held(entry_own.node().meta_addr_self()),
        // All other locks are preserved: addresses not in this subtree are unchanged.
        forall |addr: usize|
            addr != entry_own.node().meta_addr_self()
            && old(guards).guards.contains(addr) ==>
            #[trigger] final(guards).guards.contains(addr),
        // Addresses not in old guards don't appear in final guards
        // (acquire + ManuallyDrop is a no-op on the guards set for child addrs).
        forall |addr: usize|
            !old(guards).guards.contains(addr) ==>
            !#[trigger] final(guards).guards.contains(addr),
        // regions preserved
        final(regions).inv(),
        final(regions).slot_owners == old(regions).slot_owners,
)]
#[verifier::external_body]
fn dfs_acquire_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &A,
    cur_node: &mut PageTableGuard<'rcu, C>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
) {
    let cur_level = cur_node.level();
    if cur_level == 1 {
        return;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    for i in idx_range {
        let child = cur_node.entry(i);
        match child.to_ref() {
            ChildRef::PageTable(pt) => {
                let mut pt_guard = pt.lock(guard);
                let child_node_va = cur_node_va + i * page_size(cur_level);
                let child_node_va_end = child_node_va + page_size(cur_level);
                let va_start = va_range.start.max(child_node_va);
                let va_end = va_range.end.min(child_node_va_end);
                dfs_acquire_lock(guard, &mut pt_guard, child_node_va, va_start..va_end);
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
        Tracked(guards): Tracked<&mut Guards<'rcu>>
)]
#[verifier::external_body]
unsafe fn dfs_release_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &'rcu A,
    cur_node: &mut PageTableGuard<'rcu, C>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
) {
    let cur_level = cur_node.level();
    if cur_level == 1 {
        return;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let end = idx_range.end;
    for i in idx_range {
        let child = cur_node.entry(end - i);
        match child.to_ref() {
            ChildRef::PageTable(pt) => {
                // SAFETY: The caller ensures that the node is locked and the new guard is unique.
                let mut child_node = unsafe {
                    #[verus_spec(with Tracked(entry_own.tracked_borrow_node()), Tracked(guards))]
                    pt.make_guard_unchecked(guard)
                };
                let child_node_va = cur_node_va + (end - i) * page_size(cur_level);
                let child_node_va_end = child_node_va + page_size(cur_level);
                let va_start = va_range.start.max(child_node_va);
                let va_end = va_range.end.min(child_node_va_end);
                // SAFETY: The caller ensures that all the nodes in the sub-tree are locked and all
                // guards are forgotten.
                dfs_release_lock(guard, &mut child_node, child_node_va, va_start..va_end);
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
#[verus_spec(res =>
    with Tracked(owner): Tracked<&mut CursorOwner<'a, C>>,
        Tracked(guards): Tracked<&mut Guards<'a>>,
        Ghost(locked_addr): Ghost<usize>,
        Ghost(subtree_mappings_count): Ghost<nat>
    requires
        old(owner).inv(),
        // The locked_addr must be the address that was locked (held in guards)
        old(guards).lock_held(locked_addr),
    ensures
        // The return value equals the number of mappings in the subtree.
        // This connects the physical DFS frame count to the ghost view_rec mappings count.
        res as nat == subtree_mappings_count,
        final(owner).inv(),
        final(owner).guard_level == old(owner).guard_level,
        final(owner).level == old(owner).level,
        final(owner).va == old(owner).va,
        final(owner).prefix == old(owner).prefix,
        final(owner).popped_too_high == old(owner).popped_too_high,
        // Preserve the guard for each continuation level
        final(owner).level <= 4 ==> final(owner).continuations[3].guard == old(owner).continuations[3].guard,
        final(owner).level <= 3 ==> final(owner).continuations[2].guard == old(owner).continuations[2].guard,
        final(owner).level <= 2 ==> final(owner).continuations[1].guard == old(owner).continuations[1].guard,
        final(owner).level == 1 ==> final(owner).continuations[0].guard == old(owner).continuations[0].guard,
        final(owner).continuations[final(owner).level - 1].children[final(owner).continuations[final(owner).level - 1].idx as int]->0.value.is_absent(),
        // entry_own at current level is preserved
        final(owner).continuations[final(owner).level - 1].entry_own == old(owner).continuations[old(owner).level - 1].entry_own,
        // Children at current level are preserved
        forall |i: int| 0 <= i < NR_ENTRIES ==>
            #[trigger]
            final(owner).continuations[final(owner).level - 1].children[i] == old(owner).continuations[old(owner).level - 1].children[i],
        // Continuations at higher levels are completely preserved
        forall |lvl: int| #![trigger final(owner).continuations[lvl]]
            final(owner).level <= lvl < NR_LEVELS ==> final(owner).continuations[lvl] == old(owner).continuations[lvl],
        // Guards postconditions:
        // 1. Everything that was unlocked before is still unlocked (no new locks added)
        forall |addr: usize| old(guards).unlocked(addr) ==> final(guards).unlocked(addr),
        // 2. The locked address is now unlocked
        final(guards).unlocked(locked_addr),
        // 3. Other locked addresses remain locked
        forall |addr: usize| addr != locked_addr && old(guards).lock_held(addr) ==> final(guards).lock_held(addr),
)]
#[verifier::external_body]
pub unsafe fn dfs_mark_stray_and_unlock<'a, C: PageTableConfig, A: InAtomicMode>(
    rcu_guard: &A,
    sub_tree: &PageTableGuard<'a, C>,
) -> usize {
    unimplemented!();
    /*
    let mut sub_tree_val = sub_tree.take(Tracked(guard_perm));
    let stray_mut = sub_tree_val.stray_mut();
    let tracked node_owner = entry_own.tracked_take_node();
    let stray = stray_mut.take(Tracked(&mut node_owner.as_node.meta_own.stray));

    stray_mut.put(Tracked(&mut node_owner.as_node.meta_own.stray), true);

    proof {
        entry_own.tracked_put_node(node_owner);
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
                let locked_pt = unsafe { pt.make_guard_unchecked(rcu_guard) };
                // SAFETY: The caller ensures that all the nodes in the sub-tree are locked and all
                // guards are forgotten.
                num_frames += unsafe { dfs_mark_stray_and_unlock(rcu_guard, locked_pt) };
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {},
        }
    }

    num_frames*/
}

/// Spec-level ceiling division: `ceil(x / d)` for non-negative `x` and positive `d`.
pub open spec fn ceil_div(x: int, d: int) -> int
    recommends
        d > 0,
        x >= 0,
{
    (x + d - 1) / d
}

pub open spec fn idx_range_spec(
    cur_node_level: PagingLevel,
    cur_node_va: Vaddr,
    va_start: Vaddr,
    va_end: Vaddr,
) -> (usize, usize) {
    let ps = page_size(cur_node_level) as int;
    let start_idx = ((va_start - cur_node_va) as int) / ps;
    let end_idx = ceil_div((va_end - cur_node_va) as int, ps);
    (start_idx as usize, end_idx as usize)
}

#[verus_spec(ret =>
    requires
        1 <= cur_node_level <= NR_LEVELS,
        cur_node_va <= va_range.start,
        va_range.start < va_range.end,
        va_range.end <= cur_node_va + page_size((cur_node_level + 1) as PagingLevel),
        cur_node_va % page_size((cur_node_level + 1) as PagingLevel) == 0,
        va_range.start % page_size(cur_node_level) == 0,
    ensures
        ret.start == idx_range_spec(cur_node_level, cur_node_va, va_range.start, va_range.end).0,
        ret.end == idx_range_spec(cur_node_level, cur_node_va, va_range.start, va_range.end).1,
        ret.start < ret.end,
        ret.end <= NR_ENTRIES,
)]
fn dfs_get_idx_range<C: PagingConstsTrait>(
    cur_node_level: PagingLevel,
    cur_node_va: Vaddr,
    va_range: &Range<Vaddr>,
) -> Range<usize> {
    let ps = page_size(cur_node_level);
    let diff = va_range.end - cur_node_va;

    proof {
        use crate::specs::mm::page_table::cursor::page_size_lemmas::*;
        use vstd::arithmetic::div_mod::*;
        lemma_page_size_ge_page_size(cur_node_level);
        lemma_page_size_spec_values();
        lemma_nr_entries_times_sub_page_size((cur_node_level + 1) as PagingLevel);

        // diff + ps - 1 fits in usize: both <= page_size(5) = 2^48
    }

    let start_idx = (va_range.start - cur_node_va) / ps;
    let end_idx = (diff + ps - 1) / ps;

    proof {
        use crate::specs::mm::page_table::cursor::page_size_lemmas::*;
        use vstd::arithmetic::div_mod::*;

        let ai = ps as int;
        let xi = diff as int;
        let si = (va_range.start - cur_node_va) as int;

        // -- start_idx < end_idx --
        // si < xi (non-empty range), si % ai == 0 (both endpoints aligned).
        // So si/ai < (xi + ai - 1)/ai.
        //
        // Proof: si + ai <= xi + ai - 1 + 1 = xi + ai, but more precisely:
        //   si < xi ==> si <= xi - 1 (integers)
        //   ==> si + ai - 1 <= xi - 1 + ai - 1 < xi + ai - 1
        //   ==> (si + ai - 1)/ai <= (xi + ai - 1)/ai  (since si % ai == 0, si/ai = (si+ai-1)/ai)
        //
        // Actually the simplest route: si/ai * ai = si < xi <= end_idx * ai.
        assert(start_idx < end_idx) by {
            // si = start_idx * ai (exact division since si % ai == 0)
            lemma_page_size_divides(cur_node_level, (cur_node_level + 1) as PagingLevel);
            // Prove si % ai == 0: va_range.start and cur_node_va are both multiples of ps.
            // cur_node_va % ps == 0: cur_node_va % page_size(level+1) == 0 and ps | page_size(level+1).
            let psu = page_size((cur_node_level + 1) as PagingLevel) as int;
            assert(cur_node_va as int % ai == 0) by {
                // cur_node_va % psu == 0, psu % ai == 0
                // ==> cur_node_va is a multiple of ai
                lemma_fundamental_div_mod(cur_node_va as int, psu);
                lemma_fundamental_div_mod(psu, ai);
                let k = cur_node_va as int / psu;
                let m = psu / ai;
                // lemma gives: cur_node_va == psu * k + (cur_node_va % psu)
                //              psu == ai * m + (psu % ai)
                assert(cur_node_va == (m * k) * ai) by (nonlinear_arith)
                    requires
                        cur_node_va == psu * k + 0,
                        psu == ai * m + 0,
                        cur_node_va as int % psu == 0,
                        psu % ai == 0,
                ;
                lemma_mod_multiples_basic(m * k, ai);
            };
            assert(si % ai == 0) by {
                // va_range.start = si + cur_node_va, both multiples of ai
                // si % ai + cur_node_va % ai == va_range.start % ai (mod ai)
                lemma_mod_adds(si, cur_node_va as int, ai);
                // gives: si%ai + 0 == 0 + ai * ((si%ai + 0)/ai)
                // so si%ai == ai * (si%ai / ai)
                // since 0 <= si%ai < ai, si%ai / ai == 0, so si%ai == 0
            };

            // start_idx * ai = si (exact division since si % ai == 0)
            lemma_fundamental_div_mod(si, ai);
            // si == ai * (si / ai) + (si % ai) == ai * start_idx + 0
            vstd::arithmetic::mul::lemma_mul_is_commutative(ai, si / ai);

            // end_idx * ai >= xi: ceil_div(xi, ai) * ai >= xi
            lemma_fundamental_div_mod(xi + ai - 1, ai);
            let qi = (xi + ai - 1) / ai;
            let ri = (xi + ai - 1) % ai;
            // xi + ai - 1 == ai * qi + ri
            vstd::arithmetic::mul::lemma_mul_is_commutative(ai, qi);
            assert(qi * ai >= xi) by (nonlinear_arith)
                requires
                    xi + ai - 1 == qi * ai + ri,
                    0 <= ri < ai,
                    ai > 0,
            ;

            assert(start_idx * ai < end_idx * ai) by (nonlinear_arith)
                requires
                    start_idx * ai == si,
                    end_idx * ai >= xi,
                    si < xi,
            ;
            vstd::arithmetic::mul::lemma_mul_strict_inequality_converse(
                start_idx as int,
                end_idx as int,
                ai,
            );
        };

        // -- end_idx <= NR_ENTRIES --
        // diff <= page_size(level+1) = NR_ENTRIES * ps
        // So ceil_div(diff, ps) <= NR_ENTRIES.
        let psu = page_size((cur_node_level + 1) as PagingLevel) as int;
        // (psu + ai - 1) / ai == NR_ENTRIES (since psu = NR_ENTRIES * ai)
        assert(psu + ai - 1 == NR_ENTRIES * ai + (ai - 1)) by (nonlinear_arith)
            requires
                psu == NR_ENTRIES * ai,
        ;
        lemma_fundamental_div_mod_converse(psu + ai - 1, ai, NR_ENTRIES as int, ai - 1);
        // So (psu + ai - 1) / ai == NR_ENTRIES
        // xi + ai - 1 <= psu + ai - 1, so end_idx = (xi+ai-1)/ai <= (psu+ai-1)/ai = NR_ENTRIES
        lemma_div_is_ordered(xi + ai - 1, psu + ai - 1, ai);
    }

    start_idx..end_idx
}

} // verus!
