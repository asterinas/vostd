use vstd::prelude::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::arch::mm::PagingConsts;
use crate::mm::frame::meta::mapping::meta_to_frame;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr, page_size};
use crate::specs::arch::{NR_ENTRIES, NR_LEVELS};
use crate::specs::mm::Guards;
use crate::specs::mm::Mapping;
use crate::specs::mm::MetaRegionOwners;
use crate::specs::mm::page_table::AbstractVaddr;
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::node::EntryOwner;
use crate::specs::mm::page_table::owners::{INC_LEVELS, OwnerSubtree, PageTableOwner};

use crate::specs::mm::frame::mapping::frame_to_index;
use crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size;
use vstd_extra::arithmetic::{lemma_nat_align_down_sound, nat_align_down};

use core::ops::Range;

verus! {

broadcast use group_ghost_tree_lemmas;

/// Paths obtained by push_tail with different indices are different
pub proof fn push_tail_different_indices_different_paths(path: TreePath<NR_ENTRIES>, i: int, j: int)
    requires
        path.inv(),
        0 <= i < NR_ENTRIES,
        0 <= j < NR_ENTRIES,
        i != j,
    ensures
        path.push_tail(i) != path.push_tail(j),
{
}

/// Paths with different lengths are different
pub proof fn different_length_different_paths(
    path1: TreePath<NR_ENTRIES>,
    path2: TreePath<NR_ENTRIES>,
)
    requires
        path1.len() != path2.len(),
    ensures
        path1 != path2,
{
}

/// A path obtained by push_tail has greater length than the original
pub proof fn push_tail_increases_length(path: TreePath<NR_ENTRIES>, i: int)
    requires
        path.inv(),
        0 <= i < NR_ENTRIES,
    ensures
        path.push_tail(i).len() > path.len(),
{
}

/// Upgrade `node_unlocked_except` to `node_unlocked` on a subtree where the excepted
/// entry cannot appear. The precondition `path == subtree.value.path` ties structural
/// positions to entry paths. `excepted_path` must differ from all descendant paths,
/// which is guaranteed when `excepted_path != path` and `excepted_path` is not an
/// extension of `path` (all descendants have paths extending `path`).
pub proof fn subtree_unlock_upgrade<'rcu, C: PageTableConfig>(
    subtree: OwnerSubtree<C>,
    path: TreePath<NR_ENTRIES>,
    guards: Guards<'rcu>,
    regions: MetaRegionOwners,
    excepted_addr: usize,
    excepted_path: TreePath<NR_ENTRIES>,
)
    requires
        subtree.inv(),
        PageTableOwner::<C>(subtree).pt_inv(),
        subtree.subtree_satisfies(path, PageTableOwner::<C>::metaregion_sound_pred(regions)),
        subtree.subtree_satisfies(
            path,
            CursorOwner::<'rcu, C>::node_unlocked_except(guards, excepted_addr),
        ),
        regions.slot_owners[frame_to_index(meta_to_frame(excepted_addr))].paths_in_pt
            == set![excepted_path],
        // Structural path == value path
        path == subtree.value().path,
        path.inv(),
        // excepted_path does not match this subtree root
        path != excepted_path,
        // excepted_path is not a descendant (all descendants extend path, so if
        // excepted_path.len() <= path.len() it can't be a descendant; otherwise
        // it must diverge at some index below path.len())
        excepted_path.len() <= path.len() || (exists|k: int|
            0 <= k < path.len() && #[trigger] excepted_path[k] != path[k]),
    ensures
        subtree.subtree_satisfies(path, CursorOwner::<'rcu, C>::node_unlocked(guards)),
    decreases INC_LEVELS - subtree.level(),
{
    let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
    let g = CursorOwner::<'rcu, C>::node_unlocked_except(guards, excepted_addr);
    let h = CursorOwner::<'rcu, C>::node_unlocked(guards);

    if subtree.value().is_node() {
        if subtree.value().node().meta_addr_self() == excepted_addr {
            // addr == excepted_addr contradicts path != excepted_path
            // via metaregion_sound's singleton paths_in_pt.
            let idx = frame_to_index(meta_to_frame(excepted_addr));

            assert(set![subtree.value().path].contains(excepted_path));
            assert(false);
        }
    }
    if subtree.level() < INC_LEVELS - 1 && subtree.value().is_node() {
        assert forall|i: int|
            #![trigger subtree.children()[i]]
            0 <= i < subtree.children().len() && subtree.has_child(i) implies subtree.child(
            i,
        ).subtree_satisfies(path.push_tail(i), h) by {
            let child = subtree.child(i);

            let child_path = path.push_tail(i);

            subtree_unlock_upgrade(
                child,
                child_path,
                guards,
                regions,
                excepted_addr,
                excepted_path,
            );
        };
    } else if subtree.level() < INC_LEVELS - 1 && !subtree.value().is_node() {
        // Non-node: pt_inv gives children[i] is None, so subtree_satisfies
        // has no children to recurse into.
    }
}

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    /// The number of steps it will take to walk through every node of a full
    /// page table at level `level`
    pub open spec fn max_steps_subtree(level: usize) -> nat
        decreases level,
    {
        if level <= 1 {
            NR_ENTRIES as nat
        } else {
            (NR_ENTRIES as nat) * (Self::max_steps_subtree((level - 1) as usize) + 1)
        }
    }

    /// Per-level "above-current" contribution: count `NR_ENTRIES - cont.idx - 1`
    /// at every level (the entry at `cont.idx` is being descended into; its
    /// work is captured at lower levels in the recursion). `max_steps()`
    /// adds back one `subtree(self.level)` to count the current level's
    /// in-progress entry.
    ///
    /// The base case is `level > NR_LEVELS` (not `== NR_LEVELS`) so that
    /// `level == NR_LEVELS` itself contributes a non-zero term. This avoids
    /// degenerate behavior at the root: without it, `max_steps` collapses
    /// to 0 at the root and `push_level` from the root cannot decrease
    /// (and the popped_too_high `q` at NR_LEVELS would dominate `self`).
    pub open spec fn max_steps_partial(self, level: usize) -> nat
        decreases NR_LEVELS + 1 - level,
        when level <= NR_LEVELS + 1
    {
        if level > NR_LEVELS {
            0
        } else {
            let cont = self.continuations[(level - 1) as int];
            let count: nat = (NR_ENTRIES - cont.idx - 1) as nat;
            let steps = Self::max_steps_subtree(level) * count;
            let remaining_steps = self.max_steps_partial((level + 1) as usize);
            steps + remaining_steps
        }
    }

    pub open spec fn max_steps(self) -> nat {
        (self.max_steps_partial(self.level as usize) + Self::max_steps_subtree(
            self.level as usize,
        )) as nat
    }

    pub proof fn max_steps_subtree_positive(level: usize)
        ensures
            Self::max_steps_subtree(level) > 0,
        decreases level,
    {
    }

    /// Two owners with the same idx values from `start` upward have the same max_steps_partial.
    pub proof fn max_steps_partial_eq(self, other: Self, start: usize)
        requires
            1 <= start <= NR_LEVELS + 1,
            forall|k: int|
                start - 1 <= k < NR_LEVELS ==> #[trigger] self.continuations[k].idx
                    == other.continuations[k].idx,
        ensures
            self.max_steps_partial(start) == other.max_steps_partial(start),
        decreases NR_LEVELS + 1 - start,
    {
        if start <= NR_LEVELS {
            self.max_steps_partial_eq(other, (start + 1) as usize);
        }
    }

    pub proof fn max_steps_partial_inv(self, other: Self, level: usize)
        requires
            self.inv(),
            other.inv(),
            self.level == other.level,
            self.level <= level <= NR_LEVELS + 1,
            forall|i: int|
                #![trigger self.continuations[i].idx]
                #![trigger other.continuations[i].idx]
                self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].idx
                    == other.continuations[i].idx,
        ensures
            self.max_steps_partial(level) == other.max_steps_partial(level),
        decreases NR_LEVELS + 1 - level,
    {
        if level <= NR_LEVELS {
            self.max_steps_partial_inv(other, (level + 1) as usize);
        }
    }

    pub open spec fn push_level_owner(self, guard: PageTableGuard<'rcu, C>) -> Self {
        let cont = self.continuations[self.level - 1];
        let (child, cont) = cont.make_cont(self.va.index[self.level - 2] as usize, guard);
        let new_continuations = self.continuations.insert(self.level - 1, cont).insert(
            self.level - 2,
            child,
        );

        let new_level = (self.level - 1) as u8;
        Self { continuations: new_continuations, level: new_level, popped_too_high: false, ..self }
    }

    pub proof fn push_level_owner_decreases_steps(self, guard: PageTableGuard<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
        ensures
            self.push_level_owner(guard).max_steps() < self.max_steps(),
    {
        let new_self = self.push_level_owner(guard);
        let l = self.level as usize;
        let lm1 = (self.level - 1) as usize;
        // Continuations agree at indices [l-1, NR_LEVELS): only [l-2] changed.
        new_self.max_steps_partial_eq(self, l);
        // va.index[l-2] < NR_ENTRIES (from va.inv()).
        assert(self.va.index.contains_key(self.level - 2));
        let new_child = new_self.continuations[lm1 - 1];

        // subtree(l) == NR * (subtree(lm1) + 1) (from def of max_steps_subtree, l > 1).
        // subtree(lm1) * (NR - new_child.idx) <= subtree(lm1) * NR < subtree(l).
        vstd::arithmetic::mul::lemma_mul_inequality(
            (NR_ENTRIES - new_child.idx) as int,
            NR_ENTRIES as int,
            Self::max_steps_subtree(lm1) as int,
        );
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            Self::max_steps_subtree(lm1) as int,
            (NR_ENTRIES - new_child.idx - 1) as int,
            1,
        );
        vstd::arithmetic::mul::lemma_mul_is_commutative(
            (NR_ENTRIES - new_child.idx) as int,
            Self::max_steps_subtree(lm1) as int,
        );

    }

    pub proof fn push_level_owner_preserves_va(self, guard: PageTableGuard<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
        ensures
            self.push_level_owner(guard).va == self.va,
            self.push_level_owner(guard).continuations[self.level - 2].idx
                == self.va.index[self.level - 2],
    {
        assert(self.va.index.contains_key(self.level - 2));
    }

    pub proof fn push_level_owner_preserves_mappings(self, guard: PageTableGuard<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
            self.cur_entry_owner().is_node(),
        ensures
            self.push_level_owner(guard)@.mappings == self@.mappings,
    {
        broadcast use {
            CursorContinuation::group_lemmas,
            CursorOwner::group_lemmas,
            PageTableOwner::group_lemmas,
        };

        let new_owner = self.push_level_owner(guard);
        let old_cont = self.continuations[self.level - 1];
        let (_, modified_cont) = old_cont.make_cont(self.va.index[self.level - 2] as usize, guard);

        old_cont.view_mappings_take_child();

        let taken = old_cont.take_child().1;

        assert(modified_cont.children == taken.children) by {};

        assert forall|m: Mapping|
            self.view_mappings().contains(m) implies new_owner.view_mappings().contains(m) by {
            let i = choose|i: int|
                self.level - 1 <= i < NR_LEVELS && (
                #[trigger] self.continuations[i]).view_mappings().contains(m);
            if i == self.level - 1 {
                if old_cont.view_mappings_take_child_spec().contains(m) {
                    assert(new_owner.continuations[self.level - 2].view_mappings().contains(m));
                } else {
                    assert(new_owner.continuations[self.level - 1].view_mappings().contains(m));
                }
            } else {
                assert(new_owner.continuations[i] == self.continuations[i]);
            }
        };

    }

    pub proof fn push_level_owner_preserves_inv(self, guard: PageTableGuard<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
            !self.popped_too_high,
            self.level <= self.guard_level,
            self.in_locked_range(),
            // The current entry is a node (we're descending into it)
            self.cur_entry_owner().is_node(),
            // The child node's guard relates to the new guard
            self.cur_entry_owner().node().relate_guard(guard),
            // Guard distinctness: the new guard points to a different node than all existing continuations
            forall|i: int|
                #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS
                    ==> self.continuations[i].guard.inner.inner@.ptr.addr()
                    != guard.inner.inner@.ptr.addr(),
        ensures
            self.push_level_owner(guard).inv(),
    {
        // locking-work: when self.level == self.guard_level, self.inv() does
        // not supply va.index[guard_level-1] == prefix.index[guard_level-1]
        // (the conjunct at owners.rs:481-482 requires strict level < guard_level).
        // After push_level, the new level < guard_level triggers that conjunct.
        // Derive it from in_locked_range() for all cases.
        self.in_locked_range_guard_index_eq_prefix();

        let new_owner = self.push_level_owner(guard);

        let old_cont = self.continuations[self.level - 1];

        let child_node = old_cont.children[old_cont.idx as int].unwrap();
        let (child, _) = old_cont.make_cont(self.va.index[self.level - 2] as usize, guard);

        assert(self.va.index.contains_key(self.level - 2));

        assert(child.inv_children_rel()) by {
            assert forall|j: int|
                0 <= j < NR_ENTRIES && #[trigger] child.children[j] is Some implies {
                &&& child.children[j].unwrap().value().parent_level == child.level()
                &&& child.children[j].unwrap().level() == child.tree_level + 1
                &&& child.children[j].unwrap().value().path.len()
                    == child.entry_own.node().tree_level + 1
                &&& child.children[j].unwrap().value().match_pte(
                    child.entry_own.node().children_perm.value()[j],
                    child.entry_own.node().level,
                )
                &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    child.entry_own,
                    j,
                    Some(child.children[j].unwrap().value()),
                )
                &&& child.children[j].unwrap().value().path == child.path().push_tail(j)
            } by {
                let gc = child.children[j].unwrap();
                PageTableOwner(child_node).pt_inv_unroll(j);

            };
        };
        assert(child.pt_inv_children()) by {
            assert forall|j: int|
                0 <= j < child.children.len()
                    && #[trigger] child.children[j] is Some implies PageTableOwner(
                child.children[j].unwrap(),
            ).pt_inv() by {
                PageTableOwner(child_node).pt_inv_unroll(j);

            };
        };

        assert(new_owner.continuations[new_owner.level - 1].all_some()) by {
            assert forall|j: int| 0 <= j < NR_ENTRIES implies child.children[j] is Some by {
                PageTableOwner(child_node).pt_inv_unroll(j);

            };
        };

    }

    pub proof fn push_level_owner_preserves_invs(
        self,
        guard: PageTableGuard<'rcu, C>,
        regions: MetaRegionOwners,
        guards: Guards<'rcu>,
    )
        requires
            self.inv(),
            self.level > 1,
            !self.popped_too_high,
            self.level <= self.guard_level,
            self.in_locked_range(),
            self.only_current_locked(guards),
            self.nodes_locked(guards),
            self.metaregion_sound(regions),
            // The current entry is a node (we're descending into it)
            self.cur_entry_owner().is_node(),
            // The child node's guard relates to the new guard
            self.cur_entry_owner().node().relate_guard(guard),
            // The new guard must be locked in guards
            guards.lock_held(guard.inner.inner@.ptr.addr()),
        ensures
            self.push_level_owner(guard).inv(),
            self.push_level_owner(guard).children_not_locked(guards),
            self.push_level_owner(guard).nodes_locked(guards),
            self.push_level_owner(guard).metaregion_sound(regions),
    {
        let new_owner = self.push_level_owner(guard);
        let old_cont = self.continuations[self.level - 1];

        let (child_cont, modified_cont) = old_cont.make_cont(
            self.va.index[self.level - 2] as usize,
            guard,
        );

        let cur_entry = self.cur_entry_owner();
        let cur_entry_addr = cur_entry.node().meta_addr_self();
        let cur_entry_path = old_cont.path().push_tail(old_cont.idx as int);

        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i
                < NR_LEVELS implies self.continuations[i].guard.inner.inner@.ptr.addr()
            != guard.inner.inner@.ptr.addr() by {
            let cont_i = self.continuations[i];

            if cont_i.guard.inner.inner@.ptr.addr() == guard.inner.inner@.ptr.addr() {
                let addr = cont_i.entry_own.node().meta_addr_self();
                assert(addr == cur_entry.node().meta_addr_self());
                let idx = frame_to_index(meta_to_frame(addr));
                assert(regions.slot_owners[idx].paths_in_pt == set![cont_i.path()]);
                assert(regions.slot_owners[idx].paths_in_pt == set![cur_entry_path]);
                assert(set![cont_i.path()].contains(cur_entry_path));

                assert(cur_entry_path.len() == old_cont.tree_level + 1) by {
                    old_cont.inv_children_rel_unroll(old_cont.idx as int);
                };
                assert(false);
            }
        };

        self.push_level_owner_preserves_inv(guard);

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let g_except = CursorOwner::<'rcu, C>::node_unlocked_except(guards, cur_entry_addr);
        let h = CursorOwner::<'rcu, C>::node_unlocked(guards);

        assert forall|i: int|
            #![trigger new_owner.continuations[i]]
            new_owner.level - 1 <= i < NR_LEVELS implies new_owner.continuations[i].map_children(
            h,
        ) by {
            if i == self.level - 2 {
                assert forall|j: int|
                    #![trigger child_cont.children[j]]
                    0 <= j < child_cont.children.len()
                        && child_cont.children[j] is Some implies child_cont.children[j].unwrap().subtree_satisfies(
                child_cont.path().push_tail(j), h) by {
                    let gc = child_cont.children[j].unwrap();
                    let gc_path = child_cont.path().push_tail(j);

                    let child_subtree = old_cont.children[old_cont.idx as int].unwrap();
                    child_subtree.lemma_subtree_satisfies_unroll_once(cur_entry_path, f, j);
                    child_subtree.lemma_subtree_satisfies_unroll_once(cur_entry_path, g_except, j);

                    subtree_unlock_upgrade(
                        gc,
                        gc_path,
                        guards,
                        regions,
                        cur_entry_addr,
                        cur_entry_path,
                    );
                };
            } else if i == self.level - 1 {
                assert forall|j: int|
                    #![trigger modified_cont.children[j]]
                    0 <= j < modified_cont.children.len()
                        && modified_cont.children[j] is Some implies modified_cont.children[j].unwrap().subtree_satisfies(
                modified_cont.path().push_tail(j), h) by {
                    let sibling = old_cont.children[j].unwrap();
                    let sibling_path = old_cont.path().push_tail(j);

                    subtree_unlock_upgrade(
                        sibling,
                        sibling_path,
                        guards,
                        regions,
                        cur_entry_addr,
                        cur_entry_path,
                    );
                };
            } else {
                let cont_i = self.continuations[i];

                assert(cur_entry_path[cont_i.tree_level as int] == cont_i.idx as int);

                assert forall|j: int|
                    #![trigger cont_i.children[j]]
                    0 <= j < cont_i.children.len()
                        && cont_i.children[j] is Some implies cont_i.children[j].unwrap().subtree_satisfies(
                cont_i.path().push_tail(j), h) by {
                    let child_sub = cont_i.children[j].unwrap();
                    let child_path = cont_i.path().push_tail(j);

                    subtree_unlock_upgrade(
                        child_sub,
                        child_path,
                        guards,
                        regions,
                        cur_entry_addr,
                        cur_entry_path,
                    );
                };
            }
        };

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let child_subtree = child_cont.as_subtree();

        assert(child_cont.map_children(f)) by {
            assert forall|j: int|
                0 <= j < child_cont.children.len()
                    && #[trigger] child_cont.children[j] is Some implies child_cont.children[j].unwrap().subtree_satisfies(
            child_cont.path().push_tail(j), f) by {
                child_subtree.lemma_subtree_satisfies_unroll_once(child_cont.path(), f, j);

            };
        };

    }

    pub proof fn tracked_push_level_owner(tracked &mut self, guard: PageTableGuard<'rcu, C>)
        requires
            old(self).inv(),
            old(self).level > 1,
        ensures
            *final(self) == old(self).push_level_owner(guard),
    {
        assert(self.va.index.contains_key(self.level - 2));

        let ghost self0 = *self;
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);
        let tracked child = cont.tracked_make_cont(self.va.index[self.level - 2] as usize, guard);

        self.continuations.tracked_insert(self.level - 1, cont);
        self.continuations.tracked_insert(self.level - 2, child);

        assert(self.continuations == self0.continuations.insert(self.level - 1, cont).insert(
            self.level - 2,
            child,
        ));

        self.popped_too_high = false;

        self.level = (self.level - 1) as u8;
    }

    pub open spec fn pop_level_owner(self) -> (Self, PageTableGuard<'rcu, C>) {
        let child = self.continuations[self.level - 1];
        let cont = self.continuations[self.level as int];
        let (new_cont, guard) = cont.restore(child);
        let new_continuations = self.continuations.insert(self.level as int, new_cont).remove(
            self.level - 1,
        );
        let new_level = (self.level + 1) as u8;
        let popped_too_high = if new_level >= self.guard_level {
            true
        } else {
            false
        };
        (
            Self {
                continuations: new_continuations,
                level: new_level,
                popped_too_high: popped_too_high,
                ..self
            },
            guard,
        )
    }

    pub proof fn pop_level_owner_preserves_inv(self)
        requires
            self.inv(),
            self.level < NR_LEVELS,
        ensures
            self.pop_level_owner().0.inv(),
    {
    }

    pub proof fn pop_level_owner_preserves_invs(
        self,
        guards: Guards<'rcu>,
        regions: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.level < NR_LEVELS,
            self.children_not_locked(guards),
            self.nodes_locked(guards),
            self.metaregion_sound(regions),
        ensures
            self.pop_level_owner().0.inv(),
            self.pop_level_owner().0.only_current_locked(guards),
            self.pop_level_owner().0.nodes_locked(guards),
            self.pop_level_owner().0.metaregion_sound(regions),
    {
        let child = self.continuations[self.level - 1];
        let child_addr = child.entry_own.node().meta_addr_self();

        self.map_children_implies(
            CursorOwner::<'rcu, C>::node_unlocked(guards),
            CursorOwner::<'rcu, C>::node_unlocked_except(guards, child_addr),
        );

    }

    /// Update va to a new value that shares the same indices at levels >= self.level.
    /// This preserves invariants because:
    /// 1. The new va satisfies va.inv()
    /// 2. The indices at levels >= level match the continuation indices
    /// 3. in_locked_range/above_locked_range depend on va but the preconditions ensure consistency
    pub proof fn set_va_preserves_inv(self, new_va: AbstractVaddr)
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
            self.level <= self.guard_level,
            new_va.inv(),
            new_va.offset == 0,
            new_va.leading_bits == self.prefix.leading_bits,
            forall|i: int|
                #![auto]
                self.level - 1 <= i < NR_LEVELS ==> new_va.index[i] == self.va.index[i],
            forall|i: int|
                #![auto]
                self.guard_level - 1 <= i < NR_LEVELS ==> new_va.index[i] == self.prefix.index[i],
        ensures
            self.set_va(new_va).inv(),
    {
        let r = self.set_va(new_va);

        assert(r.in_locked_range()) by {
            let gl = self.guard_level;
            if gl >= 1 && gl <= NR_LEVELS {
                r.va.align_down_to_vaddr_eq_if_upper_indices_eq(r.prefix, gl as int);
                r.va.align_down_concrete(gl as int);
                r.prefix.align_down_concrete(gl as int);
                // Use cursor inv helpers on self (r.prefix == self.prefix).
                self.prefix_aligned_to_guard_level();
                self.prefix_plus_ps_no_overflow();
                r.prefix.aligned_align_up_advances(gl as int);
                AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                    nat_align_down(
                        r.va.to_vaddr() as nat,
                        page_size(gl as PagingLevel) as nat,
                    ) as Vaddr,
                );
                AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                    nat_align_down(
                        r.prefix.to_vaddr() as nat,
                        page_size(gl as PagingLevel) as nat,
                    ) as Vaddr,
                );

                lemma_nat_align_down_sound(
                    r.va.to_vaddr() as nat,
                    page_size(gl as PagingLevel) as nat,
                );

            }
        };

    }

    pub proof fn tracked_pop_level_owner(tracked &mut self) -> (guard: PageTableGuard<'rcu, C>)
        requires
            old(self).inv(),
            old(self).level < NR_LEVELS,
        ensures
            *final(self) == old(self).pop_level_owner().0,
            guard == old(self).pop_level_owner().1,
    {
        let ghost self0 = *self;
        let tracked mut parent = self.continuations.tracked_remove(self.level as int);
        let tracked child = self.continuations.tracked_remove(self.level - 1);

        let ghost guard = parent.tracked_restore(child);

        self.continuations.tracked_insert(self.level as int, parent);

        assert(self.continuations == self0.continuations.insert(self.level as int, parent).remove(
            self.level - 1,
        ));

        self.level = (self.level + 1) as u8;

        if self.level >= self.guard_level {
            self.popped_too_high = true;
        }
        guard
    }

    pub open spec fn move_forward_owner_spec(self) -> Self
        recommends
            self.inv(),
            self.level < NR_LEVELS,
            self.in_locked_range(),
        decreases NR_LEVELS - self.level,
        when self.level <= NR_LEVELS
    {
        if self.index() + 1 < NR_ENTRIES {
            // Standard advance. At the very last in-range top-level slot, this
            // produces a "one-past-end" cursor with idx == TOP_LEVEL_INDEX_RANGE.end,
            // which the cursor inv allows (relaxed `<= top_end`). Such a cursor is
            // `above_locked_range`.
            self.inc_index().zero_below_level()
        } else if self.level < NR_LEVELS {
            self.pop_level_owner().0.move_forward_owner_spec()
        } else {
            // self.level == NR_LEVELS && self.index() + 1 == NR_ENTRIES.
            // Advance to the next leading_bits-chunk via `next_index(NR_LEVELS)`.
            Self { va: self.va.next_index(NR_LEVELS as int), popped_too_high: false, ..self }
        }
    }

    pub proof fn move_forward_increases_va(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_locked_range(),
            !self.popped_too_high,
        ensures
            self.move_forward_owner_spec().va.to_vaddr() > self.va.to_vaddr(),
        decreases NR_LEVELS - self.level,
    {
        if self.index() + 1 < NR_ENTRIES {
            self.inc_and_zero_increases_va();
        } else if self.level == self.guard_level {
            // level == guard_level, index + 1 >= NR_ENTRIES.
            // move_forward_owner_spec pops if level < NR_LEVELS, else returns self.
            self.in_locked_range_guard_index_eq_prefix();
            let k = self.prefix.index[self.guard_level - 1];

            if self.guard_level < NR_LEVELS {
                // Pop to parent. Parent is at guard_level + 1 with popped_too_high.
            } else {
                // `level == guard_level == NR_LEVELS && index+1 == NR_ENTRIES`
                // is unreachable: `cursor_top_idx_strict_lt_nr_entries` derives
                // `self.index() + 1 < NR_ENTRIES` from cursor inv +
                // LOCKED_END_BOUND, contradicting the outer `else` guard.
                assert(false);
            }
        } else if self.level + 1 < self.guard_level {
            self.pop_level_owner().0.move_forward_increases_va();
        } else {
            let k = self.prefix.index[self.guard_level - 1];

            let popped = self.pop_level_owner().0;

            if k + 1 < NR_ENTRIES {
                assert(popped.move_forward_owner_spec() == popped.inc_index().zero_below_level());
                popped.inc_and_zero_increases_va();
            }
        }
    }

    pub proof fn move_forward_not_popped_too_high(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_locked_range(),
        ensures
            !self.move_forward_owner_spec().popped_too_high,
        decreases NR_LEVELS - self.level,
    {
        if self.index() + 1 >= NR_ENTRIES && self.level < NR_LEVELS {
            self.pop_level_owner().0.move_forward_not_popped_too_high();
        }
    }

    /// Variant of `move_forward_owner_decreases_steps` for the popped_too_high
    /// case. Same postcondition, but precondition allows `popped_too_high`.
    /// Used by the main lemma's case 2b to handle the chain of pops that
    /// `move_forward_owner_spec` does internally when popped_too_high.
    pub proof fn move_forward_owner_popped_too_high_decreases(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_locked_range(),
            self.popped_too_high,
            self.continuations[NR_LEVELS - 1].idx + 1 < NR_ENTRIES,
        ensures
            self.move_forward_owner_spec().max_steps() + Self::max_steps_subtree(
                self.level as usize,
            ) <= self.max_steps(),
        decreases NR_LEVELS - self.level,
    {
        let l = self.level as usize;
        let st_l = Self::max_steps_subtree(l) as int;

        if self.index() + 1 < NR_ENTRIES {
            // Case A: advance via inc_index().zero_below_level().
            // (Mirror of subcase A in the main lemma's case 2b.)
            let inc = self.inc_index();

            let new_state = inc.zero_below_level();

            new_state.max_steps_partial_eq(self, (self.level + 1) as usize);
            let self_idx = self.continuations[self.level - 1].idx as int;
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(
                st_l,
                NR_ENTRIES - self_idx - 2,
                1,
            );

        } else if self.level < NR_LEVELS {
            // Case B1: pop again (popped2.popped_too_high also true) and recurse.
            let popped2 = self.pop_level_owner().0;
            let lp1 = (self.level + 1) as usize;
            popped2.max_steps_partial_eq(self, lp1);

            assert(Self::max_steps_subtree(l) * 0nat == 0) by (nonlinear_arith);

            // popped2.popped_too_high holds: popped2.level == self.level + 1
            // > self.guard_level (since self.popped_too_high gives
            // self.level >= self.guard_level), so popped2 satisfies the
            // popped_too_high arm of pop_level_owner.

            // Recurse on popped2.
            popped2.move_forward_owner_popped_too_high_decreases();

        } else {
            // Case C: self.level == NR_LEVELS && self.index() + 1 == NR_ENTRIES.
            // Excluded by the lemma's precondition.
            assert(false);
        }
    }

    pub proof fn move_forward_owner_decreases_steps(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_locked_range(),
            !self.popped_too_high,
            // See `move_forward_owner_popped_too_high_decreases` for the
            // rationale: rules out the unreachable third-branch corner.
            self.continuations[NR_LEVELS - 1].idx + 1 < NR_ENTRIES,
        ensures
    // "Decrease by ≥ subtree(self.level)" form: needed by `push_level`
    // and by the pop+recursion case to compensate for pop_level's
    // `+(subtree(L+1) - subtree(L))` increase.

            self.move_forward_owner_spec().max_steps() + Self::max_steps_subtree(
                self.level as usize,
            ) <= self.max_steps(),
            self.move_forward_owner_spec().max_steps() < self.max_steps(),
        decreases NR_LEVELS - self.level,
    {
        let l = self.level as usize;
        let st_l = Self::max_steps_subtree(l) as int;

        if self.index() + 1 < NR_ENTRIES {
            // Case 1: increment idx at the current level.
            //   new_state.max_steps_partial(L) = old.max_steps_partial(L) - subtree(L)
            //   max_steps adds +subtree(L) on both sides → diff = -subtree(L).
            let inc = self.inc_index();

            let new_state = inc.zero_below_level();

            new_state.max_steps_partial_eq(self, (self.level + 1) as usize);
            let self_idx = self.continuations[self.level - 1].idx as int;
            let tail = self.max_steps_partial((self.level + 1) as usize) as int;
            // st_l * (NR - idx - 1) == st_l * (NR - idx - 2) + st_l * 1.
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(
                st_l,
                NR_ENTRIES - self_idx - 2,
                1,
            );
            // Tie new_state to move_forward_owner_spec and stitch the arithmetic:
            //   new_state.max_steps_partial(l) = (NR - self_idx - 2) * st_l + tail
            //   new_state.max_steps()          = new_state.max_steps_partial(l) + st_l
            //   self.max_steps()               = (NR - self_idx - 1) * st_l + tail + st_l
            // Hence new_state.max_steps() + st_l == self.max_steps() (equality, so ≤).

        } else if self.level < NR_LEVELS {
            let popped = self.pop_level_owner().0;
            let lp1 = (self.level + 1) as usize;
            popped.max_steps_partial_eq(self, lp1);

            assert(Self::max_steps_subtree(l) * 0nat == 0) by (nonlinear_arith);

            if !popped.popped_too_high {
                popped.move_forward_owner_decreases_steps();

            } else {
                // popped.popped_too_high — delegate to the popped_too_high
                // variant, which handles all subcases (advance, recursive pop,
                // and the NR_LEVELS leaf) in one call.
                popped.move_forward_owner_popped_too_high_decreases();
            }
        } else {
            assert(false);
        }
    }

    /// Trivial: zero_below_level is defined as Self { va: self.va.align_down(level), ..self }.
    pub proof fn zero_below_level_eq_align_down(self)
        requires
            self.va.inv(),
            self.va.offset == 0,
            1 <= self.level <= NR_LEVELS,
        ensures
            self.zero_below_level().va == self.va.align_down(self.level as int),
        decreases self.level,
    {
    }

    #[verifier::spinoff_prover]
    pub proof fn move_forward_va_is_align_up(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_locked_range(),
            !self.popped_too_high,
            // At level == guard_level, the wrap case (index+1 == NR_ENTRIES)
            // produces a result whose VA does not equal `va.align_up(level)`
            // when guard_level == NR_LEVELS (the spec returns self unchanged).
            // Callers (e.g. `do_inc_index_or_pop`) already have this from their
            // own bounds assume — see [mod.rs:1549].
            self.level == self.guard_level ==> self.index() + 1 < NR_ENTRIES,
        ensures
            self.move_forward_owner_spec().va == self.va.align_up(self.level as int),
        decreases NR_LEVELS - self.level,
    {
        if self.level == self.guard_level {
            if self.index() + 1 < NR_ENTRIES {
                // Same as the no-carry branch below: use align_up_advances_general.
                let inc = self.inc_index();

                assert(inc.va.inv()) by {
                    assert forall|i: int| 0 <= i < NR_LEVELS implies inc.va.index.contains_key(i)
                        && 0 <= #[trigger] inc.va.index[i] && inc.va.index[i] < NR_ENTRIES by {
                        if i != self.level - 1 {
                        }
                    };
                };
                inc.va.align_down_concrete(self.level as int);
                let ps = page_size(self.level as PagingLevel) as nat;
                let self_va = self.va.to_vaddr() as nat;
                lemma_page_size_ge_page_size(self.level as PagingLevel);

                self.va.index_increment_adds_page_size(self.level as int);

                let inc_va = inc.va.to_vaddr() as nat;
                assert(inc_va == self_va + ps);
                vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(
                    self_va as int,
                    ps as int,
                );
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(self_va as int, ps as int);

                self.va.align_up_advances_general(self.level as int);

                AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.va.align_up(self.level as int));
            }
            // The wrap (`index+1 == NR_ENTRIES`) at `level == guard_level` is
            // precluded by the strengthened precondition.

            return;
        }
        if self.index() + 1 < NR_ENTRIES {
            let inc = self.inc_index();

            inc.va.align_down_concrete(self.level as int);
            let ps = page_size(self.level as PagingLevel) as nat;
            let self_va = self.va.to_vaddr() as nat;
            lemma_page_size_ge_page_size(self.level as PagingLevel);

            self.va.index_increment_adds_page_size(self.level as int);

            let inc_va = inc.va.to_vaddr() as nat;
            assert(inc_va == self_va + ps);
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(self_va as int, ps as int);

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(self_va as int, ps as int);

            self.va.align_up_advances_general(self.level as int);

            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.va.align_up(self.level as int));
        } else if self.level < NR_LEVELS {
            let popped = self.pop_level_owner().0;
            if !popped.popped_too_high {
                popped.move_forward_va_is_align_up();
            } else {
                let inc_p = popped.inc_index();

                assert(inc_p.va.inv()) by {
                    assert forall|i: int| 0 <= i < NR_LEVELS implies inc_p.va.index.contains_key(i)
                        && 0 <= #[trigger] inc_p.va.index[i] && inc_p.va.index[i] < NR_ENTRIES by {
                        if i != popped.level - 1 {
                        }
                    };
                };
                inc_p.va.align_down_concrete(popped.level as int);
                let ps_p = page_size(popped.level as PagingLevel) as nat;
                let popped_va = popped.va.to_vaddr() as nat;
                lemma_page_size_ge_page_size(popped.level as PagingLevel);

                popped.va.index_increment_adds_page_size(popped.level as int);

                vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(
                    popped_va as int,
                    ps_p as int,
                );
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(popped_va as int, ps_p as int);

                // Sound align_up: align_up.to_vaddr() == nat_align_down(popped_va, ps) + ps.

                popped.va.align_up_advances_general(popped.level as int);

                AbstractVaddr::to_vaddr_from_vaddr_roundtrip(
                    popped.va.align_up(popped.level as int),
                );

                assert(popped.move_forward_owner_spec().va == inc_p.zero_below_level().va);
            }

            self.va.align_up_carry(self.level as int);
        }
    }

    /// After popping a level, the total view_mappings is preserved.
    /// The restored parent at index self.level absorbs the child's mappings,
    /// and both are within the view_mappings range [self.level, NR_LEVELS).
    pub proof fn pop_level_owner_preserves_mappings(self)
        requires
            self.inv(),
            self.level < NR_LEVELS,
            self.in_locked_range(),
        ensures
            self.pop_level_owner().0@.mappings == self@.mappings,
    {
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        let child = self.continuations[self.level - 1];
        let parent = self.continuations[self.level as int];
        let (restored_parent, _) = parent.restore(child);
        let popped = self.pop_level_owner().0;
        let child_subtree = child.as_subtree();

        let r = restored_parent;
        let p = parent.put_child(child_subtree);
        assert forall|j: int| 0 <= j < r.children.len() implies r.children[j]
            == p.children[j] by {};

        assert(restored_parent.view_mappings() == parent.put_child(child_subtree).view_mappings())
            by {};

        parent.view_mappings_put_child(child_subtree);
        child.as_page_table_owner_preserves_view_mappings();

        assert(popped.view_mappings() == self.view_mappings()) by {
            assert forall|m: Mapping|
                self.view_mappings().contains(m) implies popped.view_mappings().contains(m) by {
                let i = choose|i: int|
                    self.level - 1 <= i < NR_LEVELS && (
                    #[trigger] self.continuations[i]).view_mappings().contains(m);
                if i == self.level - 1 {
                    assert(popped.continuations[self.level as int].view_mappings().contains(m));
                } else if i == self.level {
                    assert(popped.continuations[self.level as int].view_mappings().contains(m));
                } else {
                    assert(popped.continuations[i] == self.continuations[i]);
                }
            };

        };
    }

    pub proof fn move_forward_owner_preserves_mappings(self)
        requires
            self.inv(),
            self.in_locked_range(),
        ensures
            self.move_forward_owner_spec()@.mappings == self@.mappings,
        decreases NR_LEVELS - self.level,
    {
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        if self.index() + 1 < NR_ENTRIES {
            let inc = self.inc_index();
            let result = inc.zero_below_level();

            let old_cont = self.continuations[self.level - 1];
            let new_cont = old_cont.inc_index();

            assert(result.view_mappings() == self.view_mappings()) by {
                assert forall|m: Mapping|
                    self.view_mappings().contains(m) implies result.view_mappings().contains(m) by {
                    let i = choose|i: int|
                        self.level - 1 <= i < NR_LEVELS && (
                        #[trigger] self.continuations[i]).view_mappings().contains(m);
                    if i == self.level - 1 {
                        assert(result.continuations[i].view_mappings().contains(m));
                    } else {
                        assert(result.continuations[i] == self.continuations[i]);
                    }
                };

            };

        } else if self.level < NR_LEVELS {
            let popped = self.pop_level_owner().0;

            self.pop_level_owner_preserves_mappings();
            popped.move_forward_owner_preserves_mappings();
        }
    }
}

} // verus!
