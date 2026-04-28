use vstd::prelude::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::node::EntryOwner;
use crate::specs::mm::page_table::owners::{OwnerSubtree, PageTableOwner, INC_LEVELS};
use crate::specs::mm::page_table::AbstractVaddr;
use crate::specs::mm::Guards;
use crate::specs::mm::Mapping;
use crate::specs::mm::MetaRegionOwners;

use crate::specs::mm::frame::mapping::{frame_to_index, meta_to_frame};
use crate::specs::mm::page_table::cursor::page_size_lemmas::{
    lemma_page_size_ge_page_size,
    lemma_page_size_divides,
};
use vstd_extra::arithmetic::{
    lemma_nat_align_down_sound,
    lemma_nat_align_down_within_block,
    nat_align_down,
    nat_align_up,
};
use crate::mm::page_table::page_size_spec as page_size;

use core::ops::Range;

verus! {

/// Paths obtained by push_tail with different indices are different
pub proof fn push_tail_different_indices_different_paths(
    path: TreePath<NR_ENTRIES>,
    i: usize,
    j: usize,
)
    requires
        path.inv(),
        0 <= i < NR_ENTRIES,
        0 <= j < NR_ENTRIES,
        i != j,
    ensures
        path.push_tail(i) != path.push_tail(j),
{
    path.push_tail_property(i);
    path.push_tail_property(j);
    assert(path.push_tail(i).index(path.len() as int) == i as usize);
    assert(path.push_tail(j).index(path.len() as int) == j as usize);
    if path.push_tail(i) == path.push_tail(j) {
        assert(i == j); // Contradiction
    }
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
    // Trivial: if path1 == path2, then their lengths are equal
    if path1 == path2 {
        assert(path1.len() == path2.len());
    }
}

/// A path obtained by push_tail has greater length than the original
pub proof fn push_tail_increases_length(
    path: TreePath<NR_ENTRIES>,
    i: usize,
)
    requires
        path.inv(),
        0 <= i < NR_ENTRIES,
    ensures
        path.push_tail(i).len() > path.len(),
{
    path.push_tail_property(i);
}

/// Upgrade `node_unlocked_except` to `node_unlocked` on a subtree where the excepted
/// entry cannot appear. The precondition `path == subtree.value.path` ties structural
/// positions to entry paths. `excepted_path` must differ from all descendant paths,
/// which is guaranteed when `excepted_path != path` and `excepted_path` is not an
/// extension of `path` (all descendants have paths extending `path`).
pub proof fn subtree_unlock_upgrade<'rcu, C: PageTableConfig>(
    subtree: OwnerSubtree<C>,
    path: TreePath<NR_ENTRIES>,
    guards: Guards<'rcu, C>,
    regions: MetaRegionOwners,
    excepted_addr: usize,
    excepted_path: TreePath<NR_ENTRIES>,
)
    requires
        subtree.inv(),
        PageTableOwner::<C>(subtree).pt_inv(),
        subtree.tree_predicate_map(path, PageTableOwner::<C>::metaregion_sound_pred(regions)),
        subtree.tree_predicate_map(path, CursorOwner::<'rcu, C>::node_unlocked_except(guards, excepted_addr)),
        regions.slot_owners[frame_to_index(meta_to_frame(excepted_addr))].paths_in_pt
            == set![excepted_path],
        // Structural path == value path
        path == subtree.value.path,
        path.inv(),
        // excepted_path does not match this subtree root
        path != excepted_path,
        // excepted_path is not a descendant (all descendants extend path, so if
        // excepted_path.len() <= path.len() it can't be a descendant; otherwise
        // it must diverge at some index below path.len())
        excepted_path.len() <= path.len() ||
            (exists|k: int| 0 <= k < path.len() && #[trigger] excepted_path.index(k) != path.index(k)),
    ensures
        subtree.tree_predicate_map(path, CursorOwner::<'rcu, C>::node_unlocked(guards)),
    decreases INC_LEVELS - subtree.level,
{
    let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
    let g = CursorOwner::<'rcu, C>::node_unlocked_except(guards, excepted_addr);
    let h = CursorOwner::<'rcu, C>::node_unlocked(guards);

    assert(f(subtree.value, path));
    assert(g(subtree.value, path));
    if subtree.value.is_node() {
        if subtree.value.node.unwrap().meta_perm.addr() == excepted_addr {
            // addr == excepted_addr contradicts path != excepted_path
            // via metaregion_sound's singleton paths_in_pt.
            let idx = frame_to_index(meta_to_frame(excepted_addr));
            assert(subtree.value.metaregion_sound(regions));
            assert(regions.slot_owners[idx].paths_in_pt == set![subtree.value.path]);
            assert(set![subtree.value.path].contains(excepted_path));
            assert(false);
        }
    }
    assert(h(subtree.value, path));

    if subtree.level < INC_LEVELS - 1 && subtree.value.is_node() {
        assert forall |i: int|
            #![trigger subtree.children[i]]
            0 <= i < subtree.children.len() && subtree.children[i] is Some implies
            subtree.children[i].unwrap().tree_predicate_map(path.push_tail(i as usize), h) by {
            let child = subtree.children[i].unwrap();
            subtree.map_unroll_once(path, f, i);
            subtree.map_unroll_once(path, g, i);

            PageTableOwner::<C>(subtree).pt_inv_unroll(i);
            let child_path = path.push_tail(i as usize);
            path.push_tail_property(i as usize);

            assert(child_path != excepted_path) by {
                if excepted_path.len() <= path.len() {
                } else {
                    let k = choose|k: int| 0 <= k < path.len() && #[trigger] excepted_path.index(k) != path.index(k);
                    assert(child_path.index(k) == path.index(k));
                }
            };

            assert(excepted_path.len() <= child_path.len() ||
                (exists|k: int| 0 <= k < child_path.len() && #[trigger] excepted_path.index(k) != child_path.index(k))) by {
                if excepted_path.len() <= path.len() {
                } else {
                    let k = choose|k: int| 0 <= k < path.len() && #[trigger] excepted_path.index(k) != path.index(k);
                    assert(child_path.index(k) == path.index(k));
                }
            };

            subtree_unlock_upgrade(child, child_path, guards, regions, excepted_addr, excepted_path);
        };
    } else if subtree.level < INC_LEVELS - 1 && !subtree.value.is_node() {
        // Non-node: pt_inv gives children[i] is None, so tree_predicate_map
        // has no children to recurse into.
        assert forall |i: int|
            #![trigger subtree.children[i]]
            0 <= i < subtree.children.len() && subtree.children[i] is Some implies
            subtree.children[i].unwrap().tree_predicate_map(path.push_tail(i as usize), h) by {
            PageTableOwner::<C>(subtree).pt_inv_non_node(i);
        };
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
        (self.max_steps_partial(self.level as usize) + Self::max_steps_subtree(self.level as usize)) as nat
    }

    pub proof fn max_steps_subtree_positive(level: usize)
        ensures
            Self::max_steps_subtree(level) > 0,
        decreases level,
    {
        if level > 1 {
            Self::max_steps_subtree_positive((level - 1) as usize);
        }
    }

    /// Two owners with the same idx values from `start` upward have the same max_steps_partial.
    pub proof fn max_steps_partial_eq(self, other: Self, start: usize)
        requires
            1 <= start <= NR_LEVELS + 1,
            forall |k: int|
                start - 1 <= k < NR_LEVELS ==> #[trigger] self.continuations[k].idx == other.continuations[k].idx,
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
            forall |i: int|
                #![trigger self.continuations[i].idx]
                #![trigger other.continuations[i].idx]
            self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].idx == other.continuations[i].idx,
        ensures
            self.max_steps_partial(level) == other.max_steps_partial(level),
        decreases NR_LEVELS + 1 - level,
    {
        if level <= NR_LEVELS {
            self.max_steps_partial_inv(other, (level + 1) as usize);
        }
    }

    pub open spec fn push_level_owner_spec(self, guard: PageTableGuard<'rcu, C>) -> Self
    {
        let cont = self.continuations[self.level - 1];
        let (child, cont) = cont.make_cont_spec(self.va.index[self.level - 2] as usize, guard);
        let new_continuations = self.continuations.insert(self.level - 1, cont);
        let new_continuations = new_continuations.insert(self.level - 2, child);

        let new_level = (self.level - 1) as u8;
        Self {
            continuations: new_continuations,
            level: new_level,
            popped_too_high: false,
            ..self
        }
    }

    pub proof fn push_level_owner_decreases_steps(self, guard: PageTableGuard<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
        ensures
            self.push_level_owner_spec(guard).max_steps() < self.max_steps()
    {
        let new_self = self.push_level_owner_spec(guard);
        let l = self.level as usize;
        let lm1 = (self.level - 1) as usize;
        // Continuations agree at indices [l-1, NR_LEVELS): only [l-2] changed.
        new_self.max_steps_partial_eq(self, l);
        // va.index[l-2] < NR_ENTRIES (from va.inv()).
        assert(self.va.index.contains_key(self.level - 2));
        let new_child = new_self.continuations[lm1 - 1];
        assert(new_child.idx < NR_ENTRIES);
        Self::max_steps_subtree_positive(lm1);
        Self::max_steps_subtree_positive(l);
        // subtree(l) == NR * (subtree(lm1) + 1) (from def of max_steps_subtree, l > 1).
        assert(Self::max_steps_subtree(l)
            == (NR_ENTRIES as nat) * (Self::max_steps_subtree(lm1) + 1));
        // subtree(lm1) * (NR - new_child.idx) <= subtree(lm1) * NR < subtree(l).
        vstd::arithmetic::mul::lemma_mul_inequality(
            (NR_ENTRIES - new_child.idx) as int,
            NR_ENTRIES as int,
            Self::max_steps_subtree(lm1) as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            Self::max_steps_subtree(lm1) as int,
            (NR_ENTRIES - new_child.idx - 1) as int,
            1);
        vstd::arithmetic::mul::lemma_mul_is_commutative(
            (NR_ENTRIES - new_child.idx) as int,
            Self::max_steps_subtree(lm1) as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(
            NR_ENTRIES as int,
            Self::max_steps_subtree(lm1) as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            NR_ENTRIES as int,
            Self::max_steps_subtree(lm1) as int,
            1);
    }

    pub proof fn push_level_owner_preserves_va(self, guard: PageTableGuard<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
        ensures
            self.push_level_owner_spec(guard).va == self.va,
            self.push_level_owner_spec(guard).continuations[self.level - 2].idx == self.va.index[self.level - 2],
    {
        assert(self.va.index.contains_key(self.level - 2));
    }

    pub proof fn push_level_owner_preserves_mappings(self, guard: PageTableGuard<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
            self.cur_entry_owner().is_node(),
        ensures
            self.push_level_owner_spec(guard)@.mappings == self@.mappings,
    {
        let new_owner = self.push_level_owner_spec(guard);
        let old_cont = self.continuations[self.level - 1];
        let (child_cont, modified_cont) = old_cont.make_cont_spec(self.va.index[self.level - 2] as usize, guard);

        assert(old_cont.all_some());
        old_cont.view_mappings_take_child();

        let taken = old_cont.take_child_spec().1;

        assert(modified_cont.children =~= taken.children) by {
            assert forall |j: int| 0 <= j < modified_cont.children.len()
                implies modified_cont.children[j] == taken.children[j] by {
                if j == old_cont.idx as int {
                    assert(modified_cont.children[j] is None);
                    assert(taken.children[j] is None);
                } else {
                    assert(modified_cont.children[j] == old_cont.children[j]);
                }
            };
        };
        assert(modified_cont.view_mappings() =~= taken.view_mappings()) by {
            assert(modified_cont.path() == taken.path());
        };

        old_cont.inv_children_rel_unroll(old_cont.idx as int);
        let child_subtree = old_cont.children[old_cont.idx as int].unwrap();
        let child_path = old_cont.path().push_tail(old_cont.idx as usize);
        assert(child_cont.children == child_subtree.children);
        assert(child_cont.path() == child_path);
        assert(child_subtree.value.is_node());
        assert(child_path.len() < INC_LEVELS - 1) by {
            assert(old_cont.tree_level < INC_LEVELS - 1);
            assert(old_cont.entry_own.inv_base());
            old_cont.path().push_tail_property(old_cont.idx as usize);
        };
        old_cont.inv_children_unroll(old_cont.idx as int);
        assert(child_subtree.inv());
        let pto = PageTableOwner(child_subtree);
        assert(pto.view_rec(child_path) =~= child_cont.view_mappings()) by {
            assert forall |m: Mapping| #[trigger] child_cont.view_mappings().contains(m) implies
                pto.view_rec(child_path).contains(m) by {
                let j = choose |j: int| #![auto]
                    0 <= j < child_cont.children.len()
                    && child_cont.children[j] is Some
                    && PageTableOwner(child_cont.children[j].unwrap()).view_rec(
                        child_cont.path().push_tail(j as usize)).contains(m);
                assert(pto.0.children[j] is Some);
                assert(pto.0.children[j] == child_cont.children[j]);
            };
            assert forall |m: Mapping| pto.view_rec(child_path).contains(m) implies
                #[trigger] child_cont.view_mappings().contains(m) by {
                let j = choose |j: int|
                    #![trigger pto.0.children[j]]
                    0 <= j < pto.0.children.len()
                    && pto.0.children[j] is Some
                    && PageTableOwner(pto.0.children[j].unwrap()).view_rec(
                        child_path.push_tail(j as usize)).contains(m);
                assert(child_cont.children[j] == pto.0.children[j]);
                assert(child_cont.children[j] is Some);
            };
        };
        assert(child_cont.view_mappings() =~= old_cont.view_mappings_take_child_spec());

        assert forall |m: Mapping| self.view_mappings().contains(m)
            implies new_owner.view_mappings().contains(m) by {
            let i = choose |i: int|
                self.level - 1 <= i < NR_LEVELS
                && (#[trigger] self.continuations[i]).view_mappings().contains(m);
            if i == self.level - 1 {
                if old_cont.view_mappings_take_child_spec().contains(m) {
                    assert(new_owner.continuations[self.level - 2].view_mappings().contains(m));
                } else {
                    assert(taken.view_mappings().contains(m));
                    assert(modified_cont.view_mappings().contains(m));
                    assert(new_owner.continuations[self.level - 1].view_mappings().contains(m));
                }
            } else {
                assert(new_owner.continuations[i] == self.continuations[i]);
            }
        };
        assert forall |m: Mapping| new_owner.view_mappings().contains(m)
            implies self.view_mappings().contains(m) by {
            let i = choose |i: int|
                new_owner.level - 1 <= i < NR_LEVELS
                && (#[trigger] new_owner.continuations[i]).view_mappings().contains(m);
            if i == self.level - 2 {
                assert(child_cont.view_mappings().contains(m));
                assert(old_cont.view_mappings_take_child_spec().contains(m));
                // view_mappings_take_child_spec() = PTO(children[idx]).view_rec(...)
                // The containment in view_mappings follows directly for i == idx.
                let child_subtree = old_cont.children[old_cont.idx as int].unwrap();
                assert(PageTableOwner(child_subtree).view_rec(
                    old_cont.path().push_tail(old_cont.idx as usize)).contains(m));
                assert(old_cont.view_mappings().contains(m));
                assert(self.continuations[self.level - 1].view_mappings().contains(m));
            } else if i == self.level - 1 {
                assert(modified_cont.view_mappings().contains(m));
                assert(taken.view_mappings().contains(m));
                // taken.view_mappings() == old_cont.view_mappings() - child_spec ⊆ view_mappings.
                assert(old_cont.view_mappings().contains(m));
                assert(self.continuations[self.level - 1].view_mappings().contains(m));
            } else {
                assert(self.continuations[i] == new_owner.continuations[i]);
            }
        };
        assert(new_owner.view_mappings() =~= self.view_mappings());
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
            self.cur_entry_owner().node.unwrap().relate_guard(guard),
            // Guard distinctness: the new guard points to a different node than all existing continuations
            forall |i: int|
                #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS ==>
                    self.continuations[i].guard.inner.inner@.ptr.addr()
                        != guard.inner.inner@.ptr.addr(),
        ensures
            self.push_level_owner_spec(guard).inv(),
    {
        // locking-work: when self.level == self.guard_level, self.inv() does
        // not supply va.index[guard_level-1] == prefix.index[guard_level-1]
        // (the conjunct at owners.rs:481-482 requires strict level < guard_level).
        // After push_level, the new level < guard_level triggers that conjunct.
        // Derive it from in_locked_range() for all cases.
        self.in_locked_range_guard_index_eq_prefix();

        let new_owner = self.push_level_owner_spec(guard);
        let new_level = (self.level - 1) as u8;

        let old_cont = self.continuations[self.level - 1];
        old_cont.inv_children_unroll(old_cont.idx as int);
        let child_node = old_cont.children[old_cont.idx as int].unwrap();
        let (child, modified_cont) = old_cont.make_cont_spec(self.va.index[self.level - 2] as usize, guard);

        old_cont.inv_children_rel_unroll(old_cont.idx as int);
        assert(child.entry_own == child_node.value);
        assert(child.entry_own == self.cur_entry_owner());
        assert(child.children == child_node.children);
        assert(child.tree_level == old_cont.tree_level + 1);

        assert(self.va.inv());
        assert(self.va.index.contains_key(self.level - 2));
        assert(0 <= self.va.index[self.level - 2] < NR_ENTRIES);
        assert(child.idx == self.va.index[self.level - 2] as usize);

        assert(child.entry_own.inv()) by {
            old_cont.inv_children_unroll(old_cont.idx as int);
        };

        assert(child.entry_own.path.len() == old_cont.entry_own.node.unwrap().tree_level + 1);
        assert(old_cont.entry_own.node.unwrap().tree_level == old_cont.tree_level) by {
            assert(old_cont.tree_level == INC_LEVELS - old_cont.level() - 1);
        };
        assert(child.entry_own.path.len() == child.tree_level) by {
            assert(child.tree_level == old_cont.tree_level + 1);
        };

        assert(child.entry_own.node.unwrap().tree_level == child.entry_own.path.len()) by {
            assert(child.children[0] is Some);
            let gc = child.children[0].unwrap();
            assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                child.entry_own, 0, Some(gc.value)));
            assert(gc.value.path.len() == child.entry_own.node.unwrap().tree_level + 1);
            assert(gc.value.path == child.entry_own.path.push_tail(0usize));
            assert(child.entry_own.inv_base());
            assert(child.entry_own.path.inv());
            child.entry_own.path.push_tail_property(0usize);
            assert(child.entry_own.path.push_tail(0usize).len() == child.entry_own.path.len() + 1);
        };

        assert(child.tree_level == child.entry_own.node.unwrap().tree_level);
        assert(child.tree_level == INC_LEVELS - child.level() - 1);

        assert(child.inv_children()) by {
            assert forall |j: int| 0 <= j < child.children.len() && #[trigger] child.children[j] is Some
                implies child.children[j].unwrap().inv() by {
                assert(child.children[j] == child_node.children[j]);
                old_cont.inv_children_unroll(old_cont.idx as int);
            };
        };
        assert(child.inv_children_rel()) by {
            assert forall |j: int| 0 <= j < NR_ENTRIES && #[trigger] child.children[j] is Some
                implies {
                    &&& child.children[j].unwrap().value.parent_level == child.level()
                    &&& child.children[j].unwrap().level == child.tree_level + 1
                    &&& !child.children[j].unwrap().value.in_scope
                    &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                        child.entry_own, j, Some(child.children[j].unwrap().value))
                    &&& child.children[j].unwrap().value.path == child.path().push_tail(j as usize)
                } by {
                let gc = child.children[j].unwrap();
                assert(child.children[j] == child_node.children[j]);
                assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    child.entry_own, j, Some(gc.value)));
                child.inv_children_unroll(j);
                assert(gc.inv());
            };
        };
        assert(child.inv());

        assert(new_owner.continuations[new_owner.level - 1].all_some()) by {
            assert(new_owner.continuations[new_owner.level - 1] == child);
            assert forall |j: int| 0 <= j < NR_ENTRIES implies child.children[j] is Some by {
                if child.children[j] is None {
                    assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                        child.entry_own, j, None));
                }
            };
        };

        assert(modified_cont.all_but_index_some()) by {
            assert(modified_cont.children[modified_cont.idx as int] is None);
            assert forall |i: int| 0 <= i < modified_cont.idx implies
                modified_cont.children[i] is Some by {
                assert(modified_cont.children[i] == old_cont.children[i]);
            };
            assert forall |i: int| modified_cont.idx < i < NR_ENTRIES implies
                modified_cont.children[i] is Some by {
                assert(modified_cont.children[i] == old_cont.children[i]);
            };
        };

        assert(forall|i: int| new_owner.level <= i < NR_LEVELS ==> {
            (#[trigger] new_owner.continuations[i]).all_but_index_some()
        }) by {
            assert forall |i: int| new_owner.level <= i < NR_LEVELS implies
                (#[trigger] new_owner.continuations[i]).all_but_index_some() by {
                if i == self.level - 1 {
                    assert(new_owner.continuations[i] == modified_cont);
                } else {
                    // i >= self.level, unchanged from old state
                    assert(new_owner.continuations[i] == self.continuations[i]);
                }
            };
        };

        // Flattened: hoist inv_children and inv_children_rel proofs so the
        // inner `assert forall` blocks live at depth 2.
        assert(modified_cont.children.len() == NR_ENTRIES);
        assert(0 <= modified_cont.idx < NR_ENTRIES);
        assert(modified_cont.inv_children()) by {
            assert forall |i: int| 0 <= i < modified_cont.children.len() && #[trigger] modified_cont.children[i] is Some
                implies modified_cont.children[i].unwrap().inv() by {
                assert(i != modified_cont.idx);
                assert(modified_cont.children[i] == old_cont.children[i]);
                old_cont.inv_children_unroll(i);
            };
        };
        assert(modified_cont.inv_children_rel()) by {
            assert forall |i: int| 0 <= i < NR_ENTRIES && #[trigger] modified_cont.children[i] is Some
                implies {
                    &&& modified_cont.children[i].unwrap().value.parent_level == modified_cont.level()
                    &&& modified_cont.children[i].unwrap().level == modified_cont.tree_level + 1
                    &&& !modified_cont.children[i].unwrap().value.in_scope
                    &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                        modified_cont.entry_own, i, Some(modified_cont.children[i].unwrap().value))
                    &&& modified_cont.children[i].unwrap().value.path == modified_cont.path().push_tail(i as usize)
                } by {
                assert(i != modified_cont.idx);
                assert(modified_cont.children[i] == old_cont.children[i]);
                assert(old_cont.inv_children_rel());
            };
        };
        assert(modified_cont.entry_own.is_node());
        assert(modified_cont.entry_own.inv());
        assert(modified_cont.entry_own.node.unwrap().relate_guard(modified_cont.guard));
        assert(modified_cont.tree_level == INC_LEVELS - modified_cont.level() - 1);
        assert(modified_cont.tree_level < INC_LEVELS - 1);
        assert(modified_cont.path().len() == modified_cont.tree_level);
        assert(modified_cont.inv());

        assert(new_owner.level <= 4 ==> {
            &&& new_owner.continuations.contains_key(3)
            &&& new_owner.continuations[3].inv()
            &&& new_owner.continuations[3].level() == 4
            &&& new_owner.continuations[3].entry_own.parent_level == 5
            &&& new_owner.va.index[3] == new_owner.continuations[3].idx
        }) by {
            if new_owner.level <= 4 {
                if self.level == 4 {
                    assert(new_owner.continuations[3] == modified_cont);
                } else {
                    assert(new_owner.continuations[3] == self.continuations[3]);
                }
            }
        };

        // Level 3 condition: new_level <= 3 ==> continuations[2] ...
        assert(new_owner.level <= 3 ==> {
            &&& new_owner.continuations.contains_key(2)
            &&& new_owner.continuations[2].inv()
            &&& new_owner.continuations[2].level() == 3
            &&& new_owner.continuations[2].entry_own.parent_level == 4
            &&& new_owner.va.index[2] == new_owner.continuations[2].idx
            &&& new_owner.continuations[2].guard.inner.inner@.ptr.addr() !=
                new_owner.continuations[3].guard.inner.inner@.ptr.addr()
            &&& new_owner.continuations[2].path() == new_owner.continuations[3].path().push_tail(new_owner.continuations[3].idx as usize)
            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    new_owner.continuations[3].entry_own, new_owner.continuations[3].idx as int,
                    Some(new_owner.continuations[2].entry_own))
        }) by {
            if new_owner.level <= 3 {
                if self.level == 4 {
                    assert(self.va.index.contains_key(2));
                    assert(new_owner.continuations[2].guard == guard);
                    assert(new_owner.continuations[3] == modified_cont);
                    assert(modified_cont.guard == old_cont.guard);
                    // guard distinctness
                    assert(new_owner.continuations[2].guard.inner.inner@.ptr.addr() !=
                           new_owner.continuations[3].guard.inner.inner@.ptr.addr()) by {
                        assert(self.continuations[self.level - 1].guard.inner.inner@.ptr.addr()
                            != guard.inner.inner@.ptr.addr());
                    };
                    // path consistency: child.path() == modified_cont.path().push_tail(modified_cont.idx)
                    assert(new_owner.continuations[2].path() == new_owner.continuations[3].path().push_tail(new_owner.continuations[3].idx as usize)) by {
                        assert(modified_cont.path() == old_cont.path());
                        assert(modified_cont.idx == old_cont.idx);
                        old_cont.inv_children_rel_unroll(old_cont.idx as int);
                    };
                    // PTE consistency: from old_cont.inv_children_rel at idx
                    assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                        new_owner.continuations[3].entry_own, new_owner.continuations[3].idx as int,
                        Some(new_owner.continuations[2].entry_own))) by {
                        old_cont.inv_children_rel_unroll(old_cont.idx as int);
                    };
                } else {
                    // self.level <= 3: from self.inv()
                }
            }
        };

        // Level 2 condition: new_level <= 2 ==> continuations[1] ...
        assert(new_owner.level <= 2 ==> {
            &&& new_owner.continuations.contains_key(1)
            &&& new_owner.continuations[1].inv()
            &&& new_owner.continuations[1].level() == 2
            &&& new_owner.continuations[1].entry_own.parent_level == 3
            &&& new_owner.va.index[1] == new_owner.continuations[1].idx
            &&& new_owner.continuations[1].guard.inner.inner@.ptr.addr() !=
                new_owner.continuations[2].guard.inner.inner@.ptr.addr()
            &&& new_owner.continuations[1].guard.inner.inner@.ptr.addr() !=
                new_owner.continuations[3].guard.inner.inner@.ptr.addr()
            &&& new_owner.continuations[1].path() == new_owner.continuations[2].path().push_tail(new_owner.continuations[2].idx as usize)
            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    new_owner.continuations[2].entry_own, new_owner.continuations[2].idx as int,
                    Some(new_owner.continuations[1].entry_own))
        }) by {
            if new_owner.level <= 2 {
                if self.level == 3 {
                    assert(self.va.index.contains_key(1));
                    assert(new_owner.continuations[1].guard == guard);
                    assert(new_owner.continuations[2] == modified_cont);
                    assert(modified_cont.guard == old_cont.guard);

                    assert(new_owner.continuations[1].guard.inner.inner@.ptr.addr() !=
                           new_owner.continuations[2].guard.inner.inner@.ptr.addr()) by {
                        assert(self.continuations[2].guard.inner.inner@.ptr.addr()
                            != guard.inner.inner@.ptr.addr());
                    };
                    assert(new_owner.continuations[1].guard.inner.inner@.ptr.addr() !=
                           new_owner.continuations[3].guard.inner.inner@.ptr.addr()) by {
                        assert(self.continuations[3].guard.inner.inner@.ptr.addr()
                            != guard.inner.inner@.ptr.addr());
                    };
                    // path: child.path() == modified_cont.path().push_tail(modified_cont.idx)
                    assert(new_owner.continuations[1].path() == new_owner.continuations[2].path().push_tail(new_owner.continuations[2].idx as usize)) by {
                        assert(modified_cont.path() == old_cont.path());
                        assert(modified_cont.idx == old_cont.idx);
                        old_cont.inv_children_rel_unroll(old_cont.idx as int);
                    };
                    // child properties: level, parent_level from tree_level
                    assert(old_cont.level() == 3);
                    assert(child.entry_own.parent_level == 3) by {
                        old_cont.inv_children_rel_unroll(old_cont.idx as int);
                    };
                    // PTE consistency: from old_cont.inv_children_rel at idx
                    assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                        new_owner.continuations[2].entry_own, new_owner.continuations[2].idx as int,
                        Some(new_owner.continuations[1].entry_own))) by {
                        old_cont.inv_children_rel_unroll(old_cont.idx as int);
                    };
                } else {
                    // self.level == 2: both continuations unchanged
                }
            }
        };

        // Level 1 condition: new_level == 1 ==> continuations[0] exists and is valid
        assert(new_owner.level == 1 ==> {
            &&& new_owner.continuations.contains_key(0)
            &&& new_owner.continuations[0].inv()
            &&& new_owner.continuations[0].level() == 1
            &&& new_owner.continuations[0].entry_own.parent_level == 2
            &&& new_owner.va.index[0] == new_owner.continuations[0].idx
            &&& new_owner.continuations[0].guard.inner.inner@.ptr.addr() !=
                new_owner.continuations[1].guard.inner.inner@.ptr.addr()
            &&& new_owner.continuations[0].guard.inner.inner@.ptr.addr() !=
                new_owner.continuations[2].guard.inner.inner@.ptr.addr()
            &&& new_owner.continuations[0].guard.inner.inner@.ptr.addr() !=
                new_owner.continuations[3].guard.inner.inner@.ptr.addr()
            &&& new_owner.continuations[0].path() == new_owner.continuations[1].path().push_tail(new_owner.continuations[1].idx as usize)
            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    new_owner.continuations[1].entry_own, new_owner.continuations[1].idx as int,
                    Some(new_owner.continuations[0].entry_own))
        }) by {
            if new_owner.level == 1 {
                // self.level == 2, new_level == 1
                assert(new_owner.continuations[0].guard == guard);
                assert(new_owner.continuations[1] == modified_cont);
                assert(modified_cont.guard == old_cont.guard);

                // Guard distinctness from precondition
                assert(self.continuations[1].guard.inner.inner@.ptr.addr()
                    != guard.inner.inner@.ptr.addr());
                assert(self.continuations[2].guard.inner.inner@.ptr.addr()
                    != guard.inner.inner@.ptr.addr());
                assert(self.continuations[3].guard.inner.inner@.ptr.addr()
                    != guard.inner.inner@.ptr.addr());

                // child.level() == 1: from tree_level arithmetic
                // old_cont = continuations[1], old_cont.level() == 2 (from self.inv() level <= 2)
                assert(old_cont.level() == 2);
                // child.tree_level == old_cont.tree_level + 1
                // old_cont.tree_level == INC_LEVELS - 2 - 1 == 2
                // child.tree_level == 3
                // child.level() == INC_LEVELS - child.tree_level - 1 == 5 - 3 - 1 == 1
                assert(child.tree_level == INC_LEVELS - child.level() - 1);

                // parent_level == 2: from inv_children_rel on old_cont
                assert(child.entry_own.parent_level == 2) by {
                    old_cont.inv_children_rel_unroll(old_cont.idx as int);
                    assert(child.entry_own.parent_level == old_cont.level());
                };

                // idx match
                assert(new_owner.va.index[0] == child.idx);

                // path consistency: child.path() == modified_cont.path().push_tail(modified_cont.idx)
                assert(child.path() == modified_cont.path().push_tail(modified_cont.idx as usize)) by {
                    assert(modified_cont.path() == old_cont.path());
                    assert(modified_cont.idx == old_cont.idx);
                    old_cont.inv_children_rel_unroll(old_cont.idx as int);
                    assert(child.entry_own.path == old_cont.path().push_tail(old_cont.idx as usize));
                };

                // PTE consistency: from old_cont.inv_children_rel at idx
                assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    new_owner.continuations[1].entry_own, new_owner.continuations[1].idx as int,
                    Some(new_owner.continuations[0].entry_own))) by {
                    old_cont.inv_children_rel_unroll(old_cont.idx as int);
                };
            }
        };

    }

    pub proof fn push_level_owner_preserves_invs(self, guard: PageTableGuard<'rcu, C>, regions: MetaRegionOwners, guards: Guards<'rcu, C>)
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
            self.cur_entry_owner().node.unwrap().relate_guard(guard),
            // The new guard must be locked in guards
            guards.lock_held(guard.inner.inner@.ptr.addr()),
        ensures
            self.push_level_owner_spec(guard).inv(),
            self.push_level_owner_spec(guard).children_not_locked(guards),
            self.push_level_owner_spec(guard).nodes_locked(guards),
            self.push_level_owner_spec(guard).metaregion_sound(regions),
    {
        if self.level == self.guard_level {
            self.in_locked_range_guard_index_eq_prefix();
        }
        reveal(CursorContinuation::inv_children);
        let new_owner = self.push_level_owner_spec(guard);
        let old_cont = self.continuations[self.level - 1];
        old_cont.inv_children_unroll_all();
        let (child_cont, modified_cont) = old_cont.make_cont_spec(self.va.index[self.level - 2] as usize, guard);

        let cur_entry = self.cur_entry_owner();
        let cur_entry_addr = cur_entry.node.unwrap().meta_perm.addr();
        let cur_entry_path = old_cont.path().push_tail(old_cont.idx as usize);
        self.cont_entries_metaregion(regions);

        assert forall |i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies
                self.continuations[i].guard.inner.inner@.ptr.addr()
                    != guard.inner.inner@.ptr.addr() by {
            let cont_i = self.continuations[i];

            if cont_i.guard.inner.inner@.ptr.addr()
                == guard.inner.inner@.ptr.addr()
            {
                let addr = cont_i.entry_own.node.unwrap().meta_perm.addr();
                assert(addr == cur_entry.node.unwrap().meta_perm.addr());
                let idx = frame_to_index(meta_to_frame(addr));
                assert(regions.slot_owners[idx].paths_in_pt == set![cont_i.path()]);
                assert(regions.slot_owners[idx].paths_in_pt == set![cur_entry_path]);
                assert(set![cont_i.path()].contains(cur_entry_path));

                assert(cur_entry_path.len() == old_cont.tree_level + 1) by {
                    old_cont.inv_children_rel_unroll(old_cont.idx as int);
                    old_cont.entry_own.path.push_tail_property(old_cont.idx as usize);
                };
                assert(cont_i.tree_level <= old_cont.tree_level) by {
                    if self.level as int == 1 {
                        assert(old_cont.level() == 1);
                    } else if self.level as int == 2 {
                        assert(old_cont.level() == 2);
                    } else if self.level as int == 3 {
                        assert(old_cont.level() == 3);
                    } else {
                        assert(old_cont.level() == 4);
                    }
                };
                assert(false);
            }
        };
        self.push_level_owner_preserves_inv(guard);

        let excepted_idx = frame_to_index(meta_to_frame(cur_entry_addr));
        assert(regions.slot_owners[excepted_idx].paths_in_pt == set![cur_entry_path]) by {
            old_cont.inv_children_rel_unroll(old_cont.idx as int);
        };

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let g_except = CursorOwner::<'rcu, C>::node_unlocked_except(guards, cur_entry_addr);
        let h = CursorOwner::<'rcu, C>::node_unlocked(guards);

        assert forall |i: int|
            #![trigger new_owner.continuations[i]]
            new_owner.level - 1 <= i < NR_LEVELS implies
            new_owner.continuations[i].map_children(h) by {

            if i == self.level - 2 {
                assert(new_owner.continuations[i] == child_cont);
                assert forall |j: int|
                    #![trigger child_cont.children[j]]
                    0 <= j < child_cont.children.len() && child_cont.children[j] is Some implies
                    child_cont.children[j].unwrap().tree_predicate_map(
                        child_cont.path().push_tail(j as usize), h) by {
                    let gc = child_cont.children[j].unwrap();
                    let gc_path = child_cont.path().push_tail(j as usize);
                    child_cont.inv_children_unroll(j);
                    child_cont.inv_children_rel_unroll(j);
                    child_cont.path().push_tail_property(j as usize);

                    let child_subtree = old_cont.children[old_cont.idx as int].unwrap();
                    child_subtree.map_unroll_once(cur_entry_path, f, j);
                    child_subtree.map_unroll_once(cur_entry_path, g_except, j);

                    assert(child_cont.path() == cur_entry_path);
                    assert(gc_path == cur_entry_path.push_tail(j as usize));
                    assert(cur_entry_path.len() < gc_path.len());
                    child_cont.pt_inv_children_unroll(j);
                    subtree_unlock_upgrade(gc, gc_path, guards, regions,
                        cur_entry_addr, cur_entry_path);
                };
            } else if i == self.level - 1 {
                assert(new_owner.continuations[i] == modified_cont);
                assert(modified_cont.path() == old_cont.path());
                assert forall |j: int|
                    #![trigger modified_cont.children[j]]
                    0 <= j < modified_cont.children.len() && modified_cont.children[j] is Some implies
                    modified_cont.children[j].unwrap().tree_predicate_map(
                        modified_cont.path().push_tail(j as usize), h) by {
                    assert(j != old_cont.idx as int);
                    assert(modified_cont.children[j] == old_cont.children[j]);
                    let sibling = old_cont.children[j].unwrap();
                    let sibling_path = old_cont.path().push_tail(j as usize);
                    old_cont.inv_children_unroll(j);
                    old_cont.inv_children_rel_unroll(j);
                    old_cont.path().push_tail_property(j as usize);

                    push_tail_different_indices_different_paths(old_cont.path(), j as usize, old_cont.idx);
                    // `cur_entry_path.len() <= sibling_path.len()` previously had its own
                    // `by { ... }` block at depth 3; inline its facts instead.
                    old_cont.inv_children_rel_unroll(old_cont.idx as int);
                    old_cont.path().push_tail_property(old_cont.idx as usize);
                    assert(cur_entry_path.len() <= sibling_path.len());
                    old_cont.pt_inv_children_unroll(j);
                    subtree_unlock_upgrade(sibling, sibling_path, guards, regions,
                        cur_entry_addr, cur_entry_path);
                };
            } else {
                assert(new_owner.continuations[i] == self.continuations[i]);
                let cont_i = self.continuations[i];

                old_cont.entry_own.path.push_tail_property(old_cont.idx as usize);
                if i == self.level as int {
                    assert(old_cont.path() == cont_i.path().push_tail(cont_i.idx as usize));
                    cont_i.entry_own.path.push_tail_property(cont_i.idx as usize);
                } else if i == self.level as int + 1 {
                    let cont_sl = self.continuations[self.level as int];
                    assert(old_cont.path() == cont_sl.path().push_tail(cont_sl.idx as usize));
                    assert(cont_sl.path() == cont_i.path().push_tail(cont_i.idx as usize));
                    cont_i.entry_own.path.push_tail_property(cont_i.idx as usize);
                    cont_i.path().push_tail(cont_i.idx as usize).push_tail_property(cont_sl.idx as usize);
                } else {
                    let cont_sl = self.continuations[self.level as int];
                    let cont_sl1 = self.continuations[self.level as int + 1];
                    assert(old_cont.path() == cont_sl.path().push_tail(cont_sl.idx as usize));
                    assert(cont_sl.path() == cont_sl1.path().push_tail(cont_sl1.idx as usize));
                    assert(cont_sl1.path() == cont_i.path().push_tail(cont_i.idx as usize));
                    cont_i.entry_own.path.push_tail_property(cont_i.idx as usize);
                    cont_i.path().push_tail(cont_i.idx as usize).push_tail_property(cont_sl1.idx as usize);
                    cont_sl1.path().push_tail(cont_sl1.idx as usize).push_tail_property(cont_sl.idx as usize);
                }
                assert(cur_entry_path.index(cont_i.tree_level as int) == cont_i.idx as usize);

                assert forall |j: int|
                    #![trigger cont_i.children[j]]
                    0 <= j < cont_i.children.len() && cont_i.children[j] is Some implies
                    cont_i.children[j].unwrap().tree_predicate_map(
                        cont_i.path().push_tail(j as usize), h) by {
                    let child_sub = cont_i.children[j].unwrap();
                    let child_path = cont_i.path().push_tail(j as usize);
                    cont_i.inv_children_unroll(j);
                    cont_i.inv_children_rel_unroll(j);
                    cont_i.path().push_tail_property(j as usize);

                    assert(child_path.index(cont_i.tree_level as int) == j as usize);
                    assert(j != cont_i.idx as int);
                    assert(child_path.index(cont_i.tree_level as int)
                        != cur_entry_path.index(cont_i.tree_level as int));
                    assert(cont_i.tree_level < child_path.len());
                    cont_i.pt_inv_children_unroll(j);
                    subtree_unlock_upgrade(child_sub, child_path, guards, regions,
                        cur_entry_addr, cur_entry_path);
                };
            }
        };
        assert(new_owner.children_not_locked(guards));
        assert forall |i: int|
            #![trigger new_owner.continuations[i]]
            new_owner.level - 1 <= i < NR_LEVELS implies
            new_owner.continuations[i].node_locked(guards) by {

            if i == self.level - 2 {
                assert(new_owner.continuations[i] == child_cont);
                assert(child_cont.guard == guard);
            } else if i == self.level - 1 {
                assert(new_owner.continuations[i] == modified_cont);
                assert(modified_cont.guard == old_cont.guard);
            } else {
                assert(new_owner.continuations[i] == self.continuations[i]);
            }
        };
        assert(new_owner.nodes_locked(guards));

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let child_subtree = child_cont.as_subtree();

        assert(child_subtree.inv_children()) by {
            assert forall |j: int| 0 <= j < NR_ENTRIES implies
                match #[trigger] child_subtree.children[j] {
                    Some(ch) => {
                        &&& ch.level == child_subtree.level + 1
                        &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(child_subtree.value, j, Some(ch.value))
                    },
                    None => <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(child_subtree.value, j, None),
                }
            by {
                assert(child_cont.children[j] is Some);
                let ch = child_cont.children[j].unwrap();
                assert(ch.level == child_cont.tree_level + 1);
                assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    child_cont.entry_own, j, Some(ch.value)));
            };
        };
        assert forall |j: int| 0 <= j < NR_ENTRIES implies
            match #[trigger] child_subtree.children[j] {
                Some(ch) => ch.inv(),
                None => true,
            }
        by {
            child_cont.inv_children_unroll(j);
        };
        assert(child_subtree.inv()) by {
            assert(child_subtree.inv_node());
        };

        // Pre-prove tree_predicate_map for child_subtree (f)
        assert(child_subtree.tree_predicate_map(child_cont.path(), f)) by {
            assert(f(child_subtree.value, child_cont.path()));
            assert forall |j: int| 0 <= j < child_subtree.children.len() implies
                match #[trigger] child_subtree.children[j] {
                    Some(ch) => ch.tree_predicate_map(child_cont.path().push_tail(j as usize), f),
                    None => true,
                }
            by { child_subtree.map_unroll_once(child_cont.path(), f, j); };
        };

        // Pre-prove map_children for modified_cont (f)
        assert(modified_cont.map_children(f)) by {
            assert forall |j: int|
                0 <= j < modified_cont.children.len() && #[trigger] modified_cont.children[j] is Some implies
                modified_cont.children[j].unwrap().tree_predicate_map(modified_cont.path().push_tail(j as usize), f) by {
                assert(j != old_cont.idx as int);
                assert(modified_cont.children[j] == old_cont.children[j]);
            };
        };

        assert(new_owner.metaregion_sound(regions)) by {
            assert forall |i: int| #![auto]
                new_owner.level - 1 <= i < NR_LEVELS implies {
                    &&& f(new_owner.continuations[i].entry_own, new_owner.continuations[i].path())
                    &&& new_owner.continuations[i].map_children(f)
                } by {
                if i == self.level - 2 {
                    assert(new_owner.continuations[i] == child_cont);
                } else if i == self.level - 1 {
                    assert(new_owner.continuations[i] == modified_cont);
                    assert(modified_cont.entry_own == old_cont.entry_own);
                    assert(modified_cont.path() == old_cont.path());
                } else {
                    assert(new_owner.continuations[i] == self.continuations[i]);
                }
            };
        };
    }

    #[verifier::returns(proof)]
    pub proof fn push_level_owner(tracked &mut self, guard: PageTableGuard<'rcu, C>)
        requires
            old(self).inv(),
            old(self).level > 1,
        ensures
            *final(self) == old(self).push_level_owner_spec(guard),
    {
        assert(self.va.index.contains_key(self.level - 2));

        let ghost self0 = *self;
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);
        let ghost cont0 = cont;
        let tracked child = cont.make_cont(self.va.index[self.level - 2] as usize, guard);

        assert((child, cont) == cont0.make_cont_spec(self.va.index[self.level - 2] as usize, guard));

        self.continuations.tracked_insert(self.level - 1, cont);
        self.continuations.tracked_insert(self.level - 2, child);

        assert(self.continuations == self0.continuations.insert(self.level - 1, cont).insert(self.level - 2, child));

        self.popped_too_high = false;

        self.level = (self.level - 1) as u8;
    }

    pub open spec fn pop_level_owner_spec(self) -> (Self, PageTableGuard<'rcu, C>)
    {
        let child = self.continuations[self.level - 1];
        let cont = self.continuations[self.level as int];
        let (new_cont, guard) = cont.restore_spec(child);
        let new_continuations = self.continuations.insert(self.level as int, new_cont);
        let new_continuations = new_continuations.remove(self.level - 1);
        let new_level = (self.level + 1) as u8;
        let popped_too_high = if new_level >= self.guard_level { true } else { false };
        (Self {
            continuations: new_continuations,
            level: new_level,
            popped_too_high: popped_too_high,
            ..self
        }, guard)
    }

    pub proof fn pop_level_owner_preserves_inv(self)
        requires
            self.inv(),
            self.level < NR_LEVELS,
            self.in_locked_range(),
        ensures
            self.pop_level_owner_spec().0.inv(),
    {
        let child = self.continuations[self.level - 1];
        assert(child.inv());
        assert(child.all_some());
        let cont = self.continuations[self.level as int];
        assert(cont.inv());
        let (new_cont, _) = cont.restore_spec(child);
        let new_owner = self.pop_level_owner_spec().0;

        let child_node = OwnerSubtree {
            value: child.entry_own,
            level: child.tree_level,
            children: child.children,
        };

        let nc = self.continuations.insert(self.level as int, new_cont).remove(self.level - 1);
        assert(new_owner.continuations == nc);
        if self.level < 3 {
            assert(nc[3] == self.continuations[3]);
        }
        if self.level < 2 {
            assert(nc[2] == self.continuations[2]);
        }
        assert(new_cont.all_some()) by {
            assert forall |i: int| 0 <= i < NR_ENTRIES implies new_cont.children[i] is Some by {
                if i == cont.idx as int {
                    assert(new_cont.children[i] == Some(child_node));
                } else {
                    assert(new_cont.children[i] == cont.children[i]);
                }
            };
        };

        assert forall |i: int| new_owner.level <= i < NR_LEVELS implies
            (#[trigger] new_owner.continuations[i]).all_but_index_some() by {
            if i == self.level as int {
                assert(new_owner.continuations[i] == new_cont);
                assert(new_cont.all_some());
            } else {
                assert(new_owner.continuations[i] == self.continuations[i]);
            }
        };

        assert(child.path() == cont.path().push_tail(cont.idx as usize));
        assert(child.entry_own.path == new_cont.path().push_tail(cont.idx as usize));
        assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                new_cont.entry_own, cont.idx as int, Some(child.entry_own)));

        assert(child_node.inv_children()) by {
            assert forall |j: int| 0 <= j < NR_ENTRIES implies
                match #[trigger] child_node.children[j] {
                    Some(ch) => {
                        &&& ch.level == child_node.level + 1
                        &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(child_node.value, j, Some(ch.value))
                    },
                    None => <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(child_node.value, j, None),
                }
            by {
                assert(child.children[j] is Some);
                let ch = child.children[j].unwrap();
                assert(ch.level == child.tree_level + 1);
                assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    child.entry_own, j, Some(ch.value)));
            };
        };
        assert forall |j: int| 0 <= j < NR_ENTRIES implies
            match #[trigger] child_node.children[j] {
                Some(ch) => ch.inv(),
                None => true,
            }
        by {
            child.inv_children_unroll(j);
        };
        assert(child_node.inv()) by {
            assert(child_node.inv_node());
        };

        assert(new_cont.inv_children()) by {
            assert forall |i: int| 0 <= i < new_cont.children.len() && #[trigger] new_cont.children[i] is Some
                implies new_cont.children[i].unwrap().inv() by {
                if i == cont.idx as int {
                    assert(new_cont.children[i].unwrap() == child_node);
                } else {
                    assert(new_cont.children[i] == cont.children[i]);
                    cont.inv_children_unroll(i);
                }
            };
        };

        assert(new_cont.inv_children_rel()) by {
            assert forall |i: int| 0 <= i < NR_ENTRIES && #[trigger] new_cont.children[i] is Some
                implies {
                    &&& new_cont.children[i].unwrap().value.parent_level == new_cont.level()
                    &&& new_cont.children[i].unwrap().level == new_cont.tree_level + 1
                    &&& !new_cont.children[i].unwrap().value.in_scope
                    &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                        new_cont.entry_own, i, Some(new_cont.children[i].unwrap().value))
                    &&& new_cont.children[i].unwrap().value.path == new_cont.path().push_tail(i as usize)
                } by {
                if i == cont.idx as int {
                    assert(new_cont.children[i].unwrap() == child_node);
                    assert(!child.entry_own.in_scope);
                } else {
                    assert(new_cont.children[i] == cont.children[i]);
                    cont.inv_children_rel_unroll(i);
                }
            };
        };

        assert(new_cont.inv()) by {
            assert(new_cont.tree_level == INC_LEVELS - new_cont.level() - 1);
            assert(new_cont.path().len() == new_cont.tree_level);
        };

        assert(new_owner.level <= 4 ==> {
            &&& new_owner.continuations.contains_key(3)
            &&& new_owner.continuations[3].inv()
            &&& new_owner.continuations[3].level() == 4
            &&& new_owner.continuations[3].entry_own.parent_level == 5
            &&& new_owner.va.index[3] == new_owner.continuations[3].idx
        }) by {
            if self.level as int == 3 {
                assert(new_owner.continuations[3] == new_cont);
            } else {
                assert(new_owner.continuations[3] == self.continuations[3]);
            }
        };

        // Level 3 condition
        assert(new_owner.level <= 3 ==> {
            &&& new_owner.continuations.contains_key(2)
            &&& new_owner.continuations[2].inv()
            &&& new_owner.continuations[2].level() == 3
            &&& new_owner.continuations[2].entry_own.parent_level == 4
            &&& new_owner.va.index[2] == new_owner.continuations[2].idx
            &&& new_owner.continuations[2].guard.inner.inner@.ptr.addr() !=
                new_owner.continuations[3].guard.inner.inner@.ptr.addr()
            &&& new_owner.continuations[2].path() == new_owner.continuations[3].path().push_tail(new_owner.continuations[3].idx as usize)
            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    new_owner.continuations[3].entry_own, new_owner.continuations[3].idx as int,
                    Some(new_owner.continuations[2].entry_own))
        }) by {
            if new_owner.level <= 3 {
                if self.level as int == 2 {
                    assert(new_owner.continuations[2] == new_cont);
                } else {
                    assert(new_owner.continuations[2] == self.continuations[2]);
                }
            }
        };

        // Level 2 condition
        assert(new_owner.level <= 2 ==> {
            &&& new_owner.continuations.contains_key(1)
            &&& new_owner.continuations[1].inv()
            &&& new_owner.continuations[1].level() == 2
            &&& new_owner.continuations[1].entry_own.parent_level == 3
            &&& new_owner.va.index[1] == new_owner.continuations[1].idx
            &&& new_owner.continuations[1].guard.inner.inner@.ptr.addr() !=
                new_owner.continuations[2].guard.inner.inner@.ptr.addr()
            &&& new_owner.continuations[1].guard.inner.inner@.ptr.addr() !=
                new_owner.continuations[3].guard.inner.inner@.ptr.addr()
            &&& new_owner.continuations[1].path() == new_owner.continuations[2].path().push_tail(new_owner.continuations[2].idx as usize)
            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    new_owner.continuations[2].entry_own, new_owner.continuations[2].idx as int,
                    Some(new_owner.continuations[1].entry_own))
        }) by {
            if new_owner.level <= 2 {
                assert(new_owner.continuations[1] == new_cont);
            }
        };
    }

    pub proof fn pop_level_owner_preserves_invs(self, guards: Guards<'rcu, C>, regions: MetaRegionOwners)
        requires
            self.inv(),
            self.level < NR_LEVELS,
            self.in_locked_range(),
            self.children_not_locked(guards),
            self.nodes_locked(guards),
            self.metaregion_sound(regions),
        ensures
            self.pop_level_owner_spec().0.inv(),
            self.pop_level_owner_spec().0.only_current_locked(guards),
            self.pop_level_owner_spec().0.nodes_locked(guards),
            self.pop_level_owner_spec().0.metaregion_sound(regions),
    {
        let new_owner = self.pop_level_owner_spec().0;
        let child = self.continuations[self.level - 1];
        let cont = self.continuations[self.level as int];
        let (new_cont, _guard) = cont.restore_spec(child);
        let child_node = OwnerSubtree {
            value: child.entry_own,
            level: child.tree_level,
            children: child.children,
        };

        self.pop_level_owner_preserves_inv();

        assert(new_owner.va == self.va);

        assert(new_owner.nodes_locked(guards)) by {
            assert forall |i: int|
                #![trigger new_owner.continuations[i]]
                new_owner.level - 1 <= i < NR_LEVELS implies
                new_owner.continuations[i].node_locked(guards) by {
                    if i == self.level as int {
                        assert(new_owner.continuations[i] == new_cont);
                        assert(new_cont.guard == cont.guard);
                    } else {
                        assert(new_owner.continuations[i] == self.continuations[i]);
                    }
                };
        };

        let child_addr = child.entry_own.node.unwrap().meta_perm.addr();
        let child_subtree = child.as_subtree();

        assert forall |j: int| 0 <= j < NR_ENTRIES implies
            match #[trigger] child_subtree.children[j] {
                Some(ch) => ch.inv(),
                None => true,
            }
        by { child.inv_children_unroll(j); };
        assert(child_subtree.inv());

        assert(OwnerSubtree::<C>::implies(
            CursorOwner::<'rcu, C>::node_unlocked(guards),
            CursorOwner::<'rcu, C>::node_unlocked_except(guards, child_addr),
        ));
        self.map_children_implies(
            CursorOwner::<'rcu, C>::node_unlocked(guards),
            CursorOwner::<'rcu, C>::node_unlocked_except(guards, child_addr),
        );

        assert(new_owner.only_current_locked(guards)) by {
            assert forall |i: int|
                #![trigger new_owner.continuations[i]]
                new_owner.level - 1 <= i < NR_LEVELS implies
                new_owner.continuations[i].map_children(
                    CursorOwner::<'rcu, C>::node_unlocked_except(guards, child_addr)) by {
                if i > self.level as int {
                    assert(new_owner.continuations[i] == self.continuations[i]);
                } else {
                    assert(new_owner.continuations[i] == new_cont);
                    new_cont.map_children_lift_skip_idx(
                        cont,
                        cont.idx as int,
                        CursorOwner::<'rcu, C>::node_unlocked(guards),
                        CursorOwner::<'rcu, C>::node_unlocked_except(guards, child_addr),
                    );
                }
            };
        };

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        self.cont_entries_metaregion(regions);

        assert(new_owner.metaregion_sound(regions)) by {
            assert forall |i: int| #![auto]
                new_owner.level - 1 <= i < NR_LEVELS implies
                    new_owner.continuations[i].map_children(f)
            by {
                if i > self.level as int {
                } else {
                    new_cont.map_children_lift_skip_idx(cont, cont.idx as int, f, f);
                }
            };
        };
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
            forall |i: int| #![auto] self.level - 1 <= i < NR_LEVELS ==> new_va.index[i] == self.va.index[i],
            forall |i: int| #![auto] self.guard_level - 1 <= i < NR_LEVELS ==> new_va.index[i] == self.prefix.index[i],
        ensures
            self.set_va_spec(new_va).inv(),
    {
        let r = self.set_va_spec(new_va);

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
                    nat_align_down(r.va.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
                AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                    nat_align_down(r.prefix.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
                lemma_page_size_ge_page_size(gl as PagingLevel);
                lemma_nat_align_down_sound(r.va.to_vaddr() as nat, page_size(gl as PagingLevel) as nat);
                r.prefix.align_down_shape(gl as int);
                r.prefix.align_down(gl as int).reflect_prop(
                    nat_align_down(r.prefix.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
            }
        };

        assert(r.continuations[r.level - 1].all_some());
        assert(r.level <= 4 ==> {
            &&& r.continuations.contains_key(3)
            &&& r.continuations[3].inv()
            &&& r.continuations[3].level() == 4
            &&& r.continuations[3].entry_own.parent_level == 5
            &&& r.in_locked_range() ==> r.va.index[3] == r.continuations[3].idx
        });

        assert(r.level <= 3 ==> {
            &&& r.continuations.contains_key(2)
            &&& r.continuations[2].inv()
            &&& r.continuations[2].level() == 3
            &&& r.continuations[2].entry_own.parent_level == 4
            &&& r.in_locked_range() ==> r.va.index[2] == r.continuations[2].idx
            &&& r.continuations[2].guard.inner.inner@.ptr.addr() !=
                r.continuations[3].guard.inner.inner@.ptr.addr()
            &&& r.continuations[2].path() == r.continuations[3].path().push_tail(r.continuations[3].idx as usize)
        });

        assert(r.level <= 2 ==> {
            &&& r.continuations.contains_key(1)
            &&& r.continuations[1].inv()
            &&& r.continuations[1].level() == 2
            &&& r.continuations[1].entry_own.parent_level == 3
            &&& r.in_locked_range() ==> r.va.index[1] == r.continuations[1].idx
            &&& r.continuations[1].guard.inner.inner@.ptr.addr() !=
                r.continuations[2].guard.inner.inner@.ptr.addr()
            &&& r.continuations[1].guard.inner.inner@.ptr.addr() !=
                r.continuations[3].guard.inner.inner@.ptr.addr()
            &&& r.continuations[1].path() == r.continuations[2].path().push_tail(r.continuations[2].idx as usize)
        });

        assert(r.level == 1 ==> {
            &&& r.continuations.contains_key(0)
            &&& r.continuations[0].inv()
            &&& r.continuations[0].level() == 1
            &&& r.continuations[0].entry_own.parent_level == 2
            &&& r.in_locked_range() ==> r.va.index[0] == r.continuations[0].idx
            &&& r.continuations[0].guard.inner.inner@.ptr.addr() !=
                r.continuations[1].guard.inner.inner@.ptr.addr()
            &&& r.continuations[0].guard.inner.inner@.ptr.addr() !=
                r.continuations[2].guard.inner.inner@.ptr.addr()
            &&& r.continuations[0].guard.inner.inner@.ptr.addr() !=
                r.continuations[3].guard.inner.inner@.ptr.addr()
            &&& r.continuations[0].path() == r.continuations[1].path().push_tail(r.continuations[1].idx as usize)
        });
    }

    #[verifier::returns(proof)]
    pub proof fn pop_level_owner(tracked &mut self) -> (tracked guard: PageTableGuard<'rcu, C>)
        requires
            old(self).inv(),
            old(self).level < NR_LEVELS,
        ensures
            *final(self) == old(self).pop_level_owner_spec().0,
            guard == old(self).pop_level_owner_spec().1,
    {
        let ghost self0 = *self;
        let tracked mut parent = self.continuations.tracked_remove(self.level as int);
        let tracked child = self.continuations.tracked_remove(self.level - 1);

        let tracked guard = parent.restore(child);

        self.continuations.tracked_insert(self.level as int, parent);

        assert(self.continuations == self0.continuations.insert(self.level as int, parent).remove(self.level - 1));

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
        decreases NR_LEVELS - self.level when self.level <= NR_LEVELS
    {
        if self.index() + 1 < NR_ENTRIES {
            // Standard advance. At the very last in-range top-level slot, this
            // produces a "one-past-end" cursor with idx == TOP_LEVEL_INDEX_RANGE.end,
            // which the cursor inv allows (relaxed `<= top_end`). Such a cursor is
            // `above_locked_range`.
            self.inc_index().zero_below_level()
        } else if self.level < NR_LEVELS {
            self.pop_level_owner_spec().0.move_forward_owner_spec()
        } else {
            // self.level == NR_LEVELS && self.index() + 1 == NR_ENTRIES.
            // Advance to the next leading_bits-chunk via `next_index(NR_LEVELS)`.
            Self {
                va: self.va.next_index(NR_LEVELS as int),
                popped_too_high: false,
                ..self
            }
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
        decreases NR_LEVELS - self.level
    {
        self.in_locked_range_level_le_guard_level();
        if self.index() + 1 < NR_ENTRIES {
            self.inc_and_zero_increases_va();
        } else if self.level == self.guard_level {
            // level == guard_level, index + 1 >= NR_ENTRIES.
            // move_forward_owner_spec pops if level < NR_LEVELS, else returns self.
            self.in_locked_range_guard_index_eq_prefix();
            let k = self.prefix.index[self.guard_level - 1];
            assert(self.index() == k);
            if self.guard_level < NR_LEVELS {
                // Pop to parent. Parent is at guard_level + 1 with popped_too_high.
                assert(self.level < NR_LEVELS);
                self.pop_level_owner_preserves_inv();
                let popped = self.pop_level_owner_spec().0;
                // popped.popped_too_high == true, so move_forward on popped
                // does inc_index().zero_below_level(). VA increases.
                // k == NR_ENTRIES - 1 here, so the parent idx advances.
            } else {
                // `level == guard_level == NR_LEVELS && index+1 == NR_ENTRIES`
                // is unreachable: `cursor_top_idx_strict_lt_nr_entries` derives
                // `self.index() + 1 < NR_ENTRIES` from cursor inv +
                // LOCKED_END_BOUND, contradicting the outer `else` guard.
                self.cursor_top_idx_strict_lt_nr_entries();
                assert(false);
            }
        } else if self.level + 1 < self.guard_level {
            assert(self.level < NR_LEVELS);
            self.pop_level_owner_preserves_inv();
            self.pop_level_owner_spec().0.move_forward_increases_va();
        } else {
            assert(self.level < NR_LEVELS);
            assert(self.guard_level == self.level + 1);
            self.in_locked_range_guard_index_eq_prefix();
            let k = self.prefix.index[self.guard_level - 1];
            assert(self.va.index[self.level as int] == k);
            self.pop_level_owner_preserves_inv();
            let popped = self.pop_level_owner_spec().0;
            assert(self.move_forward_owner_spec() == popped.move_forward_owner_spec());
            if k + 1 < NR_ENTRIES {
                assert(popped.move_forward_owner_spec() == popped.inc_index().zero_below_level());
                popped.inc_and_zero_increases_va();
            } else {
                // k == NR_ENTRIES - 1: popped state at guard_level wraps. move_forward
                // pops further (if guard_level < NR_LEVELS). VA still increases
                // because the parent entry advances.
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
        if self.index() + 1 < NR_ENTRIES {
            self.inc_index().zero_preserves_all_but_va();
        } else if self.level < NR_LEVELS {
            self.pop_level_owner_preserves_inv();
            self.pop_level_owner_spec().0.move_forward_not_popped_too_high();
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
            self.move_forward_owner_spec().max_steps()
                + Self::max_steps_subtree(self.level as usize) <= self.max_steps(),
        decreases NR_LEVELS - self.level,
    {
        let l = self.level as usize;
        let st_l = Self::max_steps_subtree(l) as int;
        Self::max_steps_subtree_positive(l);
        if self.index() + 1 < NR_ENTRIES {
            // Case A: advance via inc_index().zero_below_level().
            // (Mirror of subcase A in the main lemma's case 2b.)
            let inc = self.inc_index();
            inc.zero_preserves_all_but_va();
            let new_state = inc.zero_below_level();
            assert(new_state.level == self.level);
            assert(new_state.continuations[self.level - 1].idx
                == self.continuations[self.level - 1].idx + 1);
            new_state.max_steps_partial_eq(self, (self.level + 1) as usize);
            let self_idx = self.continuations[self.level - 1].idx as int;
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(
                st_l, NR_ENTRIES - self_idx - 2, 1);
            assert(self.move_forward_owner_spec() == new_state);
            assert(new_state.max_steps() + st_l == self.max_steps());
        } else if self.level < NR_LEVELS {
            // Case B1: pop again (popped2.popped_too_high also true) and recurse.
            self.pop_level_owner_preserves_inv();
            let popped2 = self.pop_level_owner_spec().0;
            let lp1 = (self.level + 1) as usize;
            popped2.max_steps_partial_eq(self, lp1);
            Self::max_steps_subtree_positive(lp1);

            // Bookkeeping (mirrors the main lemma at lines 1683-1695):
            assert(self.continuations[self.level - 1].idx + 1 == NR_ENTRIES);
            assert((NR_ENTRIES - self.continuations[self.level - 1].idx - 1) as nat == 0nat);
            assert(Self::max_steps_subtree(l) * 0nat == 0) by (nonlinear_arith);
            assert(self.max_steps_partial(l) == self.max_steps_partial(lp1));
            assert(popped2.level == lp1 as u8);
            assert(popped2.max_steps()
                == self.max_steps_partial(lp1) + Self::max_steps_subtree(lp1));
            assert(self.max_steps()
                == self.max_steps_partial(lp1) + Self::max_steps_subtree(l));

            // popped2.popped_too_high holds: popped2.level == self.level + 1
            // > self.guard_level (since self.popped_too_high gives
            // self.level >= self.guard_level), so popped2 satisfies the
            // popped_too_high arm of pop_level_owner_spec.

            // Recurse on popped2.
            popped2.move_forward_owner_popped_too_high_decreases();
            assert(popped2.move_forward_owner_spec().max_steps()
                + Self::max_steps_subtree(lp1) <= popped2.max_steps());
            // Spec unfolding: in the else-if branch, self.move_forward unfolds
            // to popped2.move_forward.
            assert(self.move_forward_owner_spec() == popped2.move_forward_owner_spec());
            // Stitch: popped2.move_forward.max_steps + subtree(lp1) ≤ popped2.max_steps
            //                                          == self.max_steps_partial(lp1) + subtree(lp1)
            //   ⟹ popped2.move_forward.max_steps ≤ self.max_steps_partial(lp1)
            //   ⟹ popped2.move_forward.max_steps + st_l ≤ self.max_steps()
            assert(popped2.move_forward_owner_spec().max_steps()
                <= self.max_steps_partial(lp1));
            assert(self.move_forward_owner_spec().max_steps() + st_l
                <= self.max_steps());
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
            self.move_forward_owner_spec().max_steps()
                + Self::max_steps_subtree(self.level as usize) <= self.max_steps(),
            self.move_forward_owner_spec().max_steps() < self.max_steps(),
        decreases NR_LEVELS - self.level,
    {
        let l = self.level as usize;
        let st_l = Self::max_steps_subtree(l) as int;
        Self::max_steps_subtree_positive(l);
        if self.index() + 1 < NR_ENTRIES {
            // Case 1: increment idx at the current level.
            //   new_state.max_steps_partial(L) = old.max_steps_partial(L) - subtree(L)
            //   max_steps adds +subtree(L) on both sides → diff = -subtree(L).
            let inc = self.inc_index();
            inc.zero_preserves_all_but_va();
            let new_state = inc.zero_below_level();
            assert(new_state.level == self.level);
            assert(new_state.continuations[self.level - 1].idx == self.continuations[self.level - 1].idx + 1);
            new_state.max_steps_partial_eq(self, (self.level + 1) as usize);
            let self_idx = self.continuations[self.level - 1].idx as int;
            let tail = self.max_steps_partial((self.level + 1) as usize) as int;
            // st_l * (NR - idx - 1) == st_l * (NR - idx - 2) + st_l * 1.
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(
                st_l, NR_ENTRIES - self_idx - 2, 1);
            // Tie new_state to move_forward_owner_spec and stitch the arithmetic:
            //   new_state.max_steps_partial(l) = (NR - self_idx - 2) * st_l + tail
            //   new_state.max_steps()          = new_state.max_steps_partial(l) + st_l
            //   self.max_steps()               = (NR - self_idx - 1) * st_l + tail + st_l
            // Hence new_state.max_steps() + st_l == self.max_steps() (equality, so ≤).
            assert(self.move_forward_owner_spec() == new_state);
            assert(new_state.max_steps() + st_l == self.max_steps());
        } else if self.level < NR_LEVELS {
            self.in_locked_range_level_le_guard_level();
            self.pop_level_owner_preserves_inv();
            let popped = self.pop_level_owner_spec().0;
            let lp1 = (self.level + 1) as usize;
            popped.max_steps_partial_eq(self, lp1);
            Self::max_steps_subtree_positive(lp1);

            assert(self.continuations[self.level - 1].idx + 1 == NR_ENTRIES);
            assert((NR_ENTRIES - self.continuations[self.level - 1].idx - 1) as nat == 0nat);
            assert(Self::max_steps_subtree(l) * 0nat == 0) by (nonlinear_arith);
            assert(self.max_steps_partial(l) == self.max_steps_partial(lp1));
            assert(popped.level == (self.level + 1) as u8);
            assert(popped.max_steps()
                == self.max_steps_partial(lp1) + Self::max_steps_subtree(lp1));
            assert(self.max_steps()
                == self.max_steps_partial(lp1) + Self::max_steps_subtree(l));
            if !popped.popped_too_high {
                popped.move_forward_owner_decreases_steps();
                assert(popped.move_forward_owner_spec().max_steps()
                    + Self::max_steps_subtree(lp1) <= popped.max_steps());
                assert(self.move_forward_owner_spec() == popped.move_forward_owner_spec());
                // Stitch: popped.move_forward.max_steps + subtree(lp1) ≤ popped.max_steps
                //                                          == self.max_steps_partial(lp1) + subtree(lp1)
                //   ⟹ popped.move_forward.max_steps ≤ self.max_steps_partial(lp1)
                //   ⟹ popped.move_forward.max_steps + st_l ≤ self.max_steps_partial(lp1) + st_l
                //                                          == self.max_steps()
                assert(popped.move_forward_owner_spec().max_steps()
                    <= self.max_steps_partial(lp1));
                assert(self.move_forward_owner_spec().max_steps() + st_l
                    <= self.max_steps());
            } else {
                // popped.popped_too_high — delegate to the popped_too_high
                // variant, which handles all subcases (advance, recursive pop,
                // and the NR_LEVELS leaf) in one call.
                popped.move_forward_owner_popped_too_high_decreases();
                assert(popped.move_forward_owner_spec().max_steps()
                    + Self::max_steps_subtree(lp1) <= popped.max_steps());
                assert(self.move_forward_owner_spec() == popped.move_forward_owner_spec());
                // Same stitching as the !popped_too_high case:
                //   popped.move_forward.max_steps + subtree(lp1) ≤ popped.max_steps
                //                                          == self.max_steps_partial(lp1) + subtree(lp1)
                //   ⟹ popped.move_forward.max_steps ≤ self.max_steps_partial(lp1)
                //   ⟹ popped.move_forward.max_steps + st_l ≤ self.max_steps()
                assert(popped.move_forward_owner_spec().max_steps()
                    <= self.max_steps_partial(lp1));
                assert(self.move_forward_owner_spec().max_steps() + st_l
                    <= self.max_steps());
            }
        } else {
            self.in_locked_range_level_le_nr_levels();
            self.in_locked_range_level_le_guard_level();
            self.cursor_top_idx_strict_lt_nr_entries();
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
    {}

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
        decreases NR_LEVELS - self.level
    {
        if self.level == self.guard_level {
            if self.index() + 1 < NR_ENTRIES {
                // Same as the no-carry branch below: use align_up_advances_general.
                let inc = self.inc_index();
                inc.zero_preserves_all_but_va();
                inc.zero_below_level_va();
                assert(inc.va.inv()) by {
                    assert forall |i: int| 0 <= i < NR_LEVELS implies
                        inc.va.index.contains_key(i) && 0 <= #[trigger] inc.va.index[i] && inc.va.index[i] < NR_ENTRIES
                    by { if i != self.level - 1 { assert(inc.va.index[i] == self.va.index[i]); } };
                };
                inc.va.align_down_concrete(self.level as int);
                let ps = page_size(self.level as PagingLevel) as nat;
                let self_va = self.va.to_vaddr() as nat;
                lemma_page_size_ge_page_size(self.level as PagingLevel);
                assert(self.va.index[self.level - 1] == self.continuations[self.level - 1].idx);
                self.va.index_increment_adds_page_size(self.level as int);
                let inc_va = inc.va.to_vaddr() as nat;
                assert(inc_va == self_va + ps);
                assert(self_va + ps == ps * 1 + self_va) by (nonlinear_arith);
                vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(1int, self_va as int, ps as int);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(self_va as int, ps as int);
                vstd::arithmetic::div_mod::lemma_mod_bound(self_va as int, ps as int);
                vstd::arithmetic::div_mod::lemma_div_pos_is_pos(self_va as int, ps as int);
                assert(nat_align_down(inc_va, ps) == nat_align_down(self_va, ps) + ps);
                vstd_extra::arithmetic::lemma_nat_align_down_sound(self_va, ps);
                assert(vstd_extra::arithmetic::nat_align_down(self_va, ps) + ps <= usize::MAX as nat);
                self.va.align_up_advances_general(self.level as int);
                inc.va.align_down_shape(self.level as int);
                self.va.align_down_shape(self.level as int);
                AbstractVaddr::to_vaddr_from_vaddr_roundtrip(inc.va.align_down(self.level as int));
                AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.va.align_up(self.level as int));
            }
            // The wrap (`index+1 == NR_ENTRIES`) at `level == guard_level` is
            // precluded by the strengthened precondition.
            return;
        }
        if self.index() + 1 < NR_ENTRIES {
            let inc = self.inc_index();
            inc.zero_preserves_all_but_va();
            inc.zero_below_level_va();
            assert(inc.va.inv()) by {
                assert forall |i: int| 0 <= i < NR_LEVELS implies
                    inc.va.index.contains_key(i) && 0 <= #[trigger] inc.va.index[i] && inc.va.index[i] < NR_ENTRIES
                by { if i != self.level - 1 { assert(inc.va.index[i] == self.va.index[i]); } };
            };
            inc.va.align_down_concrete(self.level as int);
            let ps = page_size(self.level as PagingLevel) as nat;
            let self_va = self.va.to_vaddr() as nat;
            lemma_page_size_ge_page_size(self.level as PagingLevel);
            assert(self.va.index[self.level - 1] == self.continuations[self.level - 1].idx);
            self.va.index_increment_adds_page_size(self.level as int);
            let inc_va = inc.va.to_vaddr() as nat;
            assert(inc_va == self_va + ps);
            assert(self_va + ps == ps * 1 + self_va) by (nonlinear_arith);
            vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(1int, self_va as int, ps as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(self_va as int, ps as int);
            vstd::arithmetic::div_mod::lemma_mod_bound(self_va as int, ps as int);
            vstd::arithmetic::div_mod::lemma_div_pos_is_pos(self_va as int, ps as int);
            // nat_align_down(inc_va, ps) == nat_align_down(self_va, ps) + ps
            // (adding a multiple of ps preserves the aligned base).
            assert(nat_align_down(inc_va, ps) == nat_align_down(self_va, ps) + ps);
            // Sound align_up: self.va.align_up(level).to_vaddr() == nat_align_down(self_va, ps) + ps.
            // Overflow bound: nat_align_down(self_va, ps) <= self_va, and self_va + ps == inc_va
            // is a valid usize (inc.va.to_vaddr() didn't overflow), so nat_align_down + ps <= inc_va <= usize::MAX.
            vstd_extra::arithmetic::lemma_nat_align_down_sound(self_va, ps);
            assert(vstd_extra::arithmetic::nat_align_down(self_va, ps) + ps <= usize::MAX as nat);
            self.va.align_up_advances_general(self.level as int);
            // Now inc.va.align_down(level).to_vaddr() == nat_align_down(inc_va, ps)
            //    == nat_align_down(self_va, ps) + ps == self.va.align_up(level).to_vaddr().
            // Equal to_vaddr + both satisfy inv ⇒ both equal via from_vaddr uniqueness.
            inc.va.align_down_shape(self.level as int);
            self.va.align_down_shape(self.level as int);
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(inc.va.align_down(self.level as int));
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.va.align_up(self.level as int));
        } else if self.level < NR_LEVELS {
            self.in_locked_range_level_le_guard_level();
            self.pop_level_owner_preserves_inv();
            let popped = self.pop_level_owner_spec().0;
            if !popped.popped_too_high {
                popped.move_forward_va_is_align_up();
            } else {
                let inc_p = popped.inc_index();
                inc_p.zero_preserves_all_but_va();
                inc_p.zero_below_level_va();
                assert(inc_p.va.inv()) by {
                    assert forall |i: int| 0 <= i < NR_LEVELS implies
                        inc_p.va.index.contains_key(i) && 0 <= #[trigger] inc_p.va.index[i] && inc_p.va.index[i] < NR_ENTRIES
                    by { if i != popped.level - 1 { assert(inc_p.va.index[i] == popped.va.index[i]); } };
                };
                inc_p.va.align_down_concrete(popped.level as int);
                let ps_p = page_size(popped.level as PagingLevel) as nat;
                let popped_va = popped.va.to_vaddr() as nat;
                let inc_p_va = inc_p.va.to_vaddr() as nat;
                lemma_page_size_ge_page_size(popped.level as PagingLevel);
                assert(popped.va.index[popped.level as int - 1] == popped.continuations[popped.level as int - 1].idx);
                popped.va.index_increment_adds_page_size(popped.level as int);
                assert(inc_p_va == popped_va + ps_p);
                assert(popped_va + ps_p == ps_p * 1 + popped_va) by (nonlinear_arith);
                vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(1int, popped_va as int, ps_p as int);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(popped_va as int, ps_p as int);
                vstd::arithmetic::div_mod::lemma_mod_bound(popped_va as int, ps_p as int);
                vstd::arithmetic::div_mod::lemma_div_pos_is_pos(popped_va as int, ps_p as int);
                // Sound align_up: align_up.to_vaddr() == nat_align_down(popped_va, ps) + ps.
                vstd_extra::arithmetic::lemma_nat_align_down_sound(popped_va, ps_p);
                assert(vstd_extra::arithmetic::nat_align_down(popped_va, ps_p) + ps_p <= usize::MAX as nat);
                popped.va.align_up_advances_general(popped.level as int);
                assert(nat_align_down(inc_p_va, ps_p)
                    == vstd_extra::arithmetic::nat_align_down(popped_va, ps_p) + ps_p);
                inc_p.va.align_down_shape(popped.level as int);
                popped.va.align_down_shape(popped.level as int);
                AbstractVaddr::to_vaddr_from_vaddr_roundtrip(inc_p.va.align_down(popped.level as int));
                AbstractVaddr::to_vaddr_from_vaddr_roundtrip(popped.va.align_up(popped.level as int));
                assert(inc_p.va.align_down(popped.level as int) == popped.va.align_up(popped.level as int));
                assert(popped.index() + 1 < NR_ENTRIES);
                assert(popped.move_forward_owner_spec().va == inc_p.zero_below_level().va);
            }
            assert(self.va.index[self.level as int - 1] == self.continuations[self.level as int - 1].idx);
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
            self.pop_level_owner_spec().0@.mappings == self@.mappings,
    {
        let child = self.continuations[self.level - 1];
        let parent = self.continuations[self.level as int];
        let (restored_parent, _) = parent.restore_spec(child);
        let popped = self.pop_level_owner_spec().0;
        let child_subtree = child.as_subtree();

        assert(child.inv());
        assert(child.all_some());
        assert(parent.inv());
        assert(parent.all_but_index_some());
        assert(child.path() == parent.path().push_tail(parent.idx as usize));

        assert(child_subtree.inv()) by {
            assert(child_subtree.inv_node());
            assert forall |i: int| 0 <= i < NR_ENTRIES implies
                match #[trigger] child_subtree.children[i] {
                    Some(ch) => {
                        &&& ch.level == child_subtree.level + 1
                        &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(child_subtree.value, i, Some(ch.value))
                    },
                    None => <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(child_subtree.value, i, None),
                }
            by {
                let ch = child.children[i].unwrap();
                assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    child.entry_own, i, Some(ch.value)));
            };
            assert(child_subtree.inv_children());

            assert forall |i: int| 0 <= i < NR_ENTRIES implies
                match #[trigger] child_subtree.children[i] {
                    Some(ch) => ch.inv(),
                    None => true,
                }
            by {
                child.inv_children_unroll(i);
            };
        };

        parent.as_subtree_restore(child);

        let r = restored_parent;
        let p = parent.put_child_spec(child_subtree);
        assert forall |j: int| 0 <= j < r.children.len()
            implies r.children[j] == p.children[j] by {
            if j == parent.idx as int {
                assert(r.children[j] == Some(child_subtree));
            } else {
                assert(r.children[j] == parent.children[j]);
            }
        };
        assert(r.children =~= p.children);
        assert(restored_parent.view_mappings() =~=
            parent.put_child_spec(child_subtree).view_mappings()) by {
            assert(r.path() == p.path());
            assert forall |m: Mapping| r.view_mappings().contains(m)
                implies p.view_mappings().contains(m) by {
                let j = choose |j: int| #![auto]
                    0 <= j < r.children.len()
                    && r.children[j] is Some
                    && PageTableOwner(r.children[j].unwrap()).view_rec(
                        r.path().push_tail(j as usize)).contains(m);
                assert(p.children[j] is Some);
                assert(PageTableOwner(p.children[j].unwrap()).view_rec(
                    p.path().push_tail(j as usize)).contains(m));
            };
            assert forall |m: Mapping| p.view_mappings().contains(m)
                implies r.view_mappings().contains(m) by {
                let j = choose |j: int| #![auto]
                    0 <= j < p.children.len()
                    && p.children[j] is Some
                    && PageTableOwner(p.children[j].unwrap()).view_rec(
                        p.path().push_tail(j as usize)).contains(m);
                assert(r.children[j] is Some);
                assert(PageTableOwner(r.children[j].unwrap()).view_rec(
                    r.path().push_tail(j as usize)).contains(m));
            };
        };

        parent.view_mappings_put_child(child_subtree);
        child.as_page_table_owner_preserves_view_mappings();

        assert(popped.level == (self.level + 1) as u8);
        assert(popped.continuations[self.level as int] == restored_parent);

        assert(popped.view_mappings() =~= self.view_mappings()) by {
            assert forall |m: Mapping| self.view_mappings().contains(m)
                implies popped.view_mappings().contains(m) by {
                let i = choose |i: int|
                    self.level - 1 <= i < NR_LEVELS
                    && (#[trigger] self.continuations[i]).view_mappings().contains(m);
                if i == self.level - 1 {
                    assert(child.view_mappings().contains(m));
                    assert(restored_parent.view_mappings().contains(m));
                    assert(popped.continuations[self.level as int].view_mappings().contains(m));
                } else if i == self.level as int {
                    assert(parent.view_mappings().contains(m));
                    assert(restored_parent.view_mappings().contains(m));
                    assert(popped.continuations[self.level as int].view_mappings().contains(m));
                } else {
                    assert(popped.continuations[i] == self.continuations[i]);
                }
            };
            assert forall |m: Mapping| popped.view_mappings().contains(m)
                implies self.view_mappings().contains(m) by {
                let i = choose |i: int|
                    popped.level - 1 <= i < NR_LEVELS
                    && (#[trigger] popped.continuations[i]).view_mappings().contains(m);
                if i == self.level as int {
                    assert(restored_parent.view_mappings().contains(m));
                    if child.view_mappings().contains(m) {
                        assert(self.continuations[self.level - 1].view_mappings().contains(m));
                    } else {
                        assert(parent.view_mappings().contains(m));
                        assert(self.continuations[self.level as int].view_mappings().contains(m));
                    }
                } else {
                    assert(self.continuations[i] == popped.continuations[i]);
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
        if self.index() + 1 < NR_ENTRIES {
            let inc = self.inc_index();
            let result = inc.zero_below_level();

            inc.zero_preserves_all_but_va();
            assert(result.continuations =~= inc.continuations);
            assert(result.level == inc.level);

            let old_cont = self.continuations[self.level - 1];
            let new_cont = old_cont.inc_index();
            assert(new_cont.children =~= old_cont.children);
            assert(new_cont.entry_own == old_cont.entry_own);
            assert(new_cont.path() == old_cont.path());

            assert(new_cont.view_mappings() =~= old_cont.view_mappings()) by {
                assert forall |m: Mapping| old_cont.view_mappings().contains(m)
                    implies new_cont.view_mappings().contains(m) by {
                    let i = choose |i: int| #![auto]
                        0 <= i < old_cont.children.len()
                        && old_cont.children[i] is Some
                        && PageTableOwner(old_cont.children[i].unwrap()).view_rec(
                            old_cont.path().push_tail(i as usize)).contains(m);
                    assert(new_cont.children[i] is Some);
                    assert(PageTableOwner(new_cont.children[i].unwrap()).view_rec(
                        new_cont.path().push_tail(i as usize)).contains(m));
                };
                assert forall |m: Mapping| new_cont.view_mappings().contains(m)
                    implies old_cont.view_mappings().contains(m) by {
                    let i = choose |i: int| #![auto]
                        0 <= i < new_cont.children.len()
                        && new_cont.children[i] is Some
                        && PageTableOwner(new_cont.children[i].unwrap()).view_rec(
                            new_cont.path().push_tail(i as usize)).contains(m);
                    assert(old_cont.children[i] is Some);
                    assert(PageTableOwner(old_cont.children[i].unwrap()).view_rec(
                        old_cont.path().push_tail(i as usize)).contains(m));
                };
            };

            assert(result.view_mappings() =~= self.view_mappings()) by {
                assert forall |m: Mapping| self.view_mappings().contains(m)
                    implies result.view_mappings().contains(m) by {
                    let i = choose |i: int|
                        self.level - 1 <= i < NR_LEVELS
                        && (#[trigger] self.continuations[i]).view_mappings().contains(m);
                    if i == self.level - 1 {
                        assert(result.continuations[i].view_mappings().contains(m));
                    } else {
                        assert(result.continuations[i] == self.continuations[i]);
                    }
                };
                assert forall |m: Mapping| result.view_mappings().contains(m)
                    implies self.view_mappings().contains(m) by {
                    let i = choose |i: int|
                        result.level - 1 <= i < NR_LEVELS
                        && (#[trigger] result.continuations[i]).view_mappings().contains(m);
                    if i == self.level - 1 {
                        assert(self.continuations[i].view_mappings().contains(m));
                    } else {
                        assert(self.continuations[i] == result.continuations[i]);
                    }
                };
            };
        } else if self.level < NR_LEVELS {
            let popped = self.pop_level_owner_spec().0;

            self.pop_level_owner_preserves_inv();
            assert(popped.in_locked_range()) by {
                assert(popped.va == self.va);
                assert(popped.prefix == self.prefix);
                assert(popped.guard_level == self.guard_level);
            };

            self.pop_level_owner_preserves_mappings();
            popped.move_forward_owner_preserves_mappings();
        }
    }
}

}

 
 
 
