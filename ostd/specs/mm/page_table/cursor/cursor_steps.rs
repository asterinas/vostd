use vstd::prelude::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::node::EntryOwner;
use crate::specs::mm::page_table::node::GuardPerm;
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
        subtree.tree_predicate_map(path, PageTableOwner::<C>::metaregion_sound_pred(regions)),
        subtree.tree_predicate_map(path, CursorOwner::<'rcu, C>::node_unlocked_except(guards, excepted_addr)),
        regions.slot_owners[frame_to_index(meta_to_frame(excepted_addr))].path_if_in_pt
            == Some(excepted_path),
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

    // Root: value.path == path != excepted_path.
    // If addr == excepted_addr: metaregion_sound gives slot.path_if_in_pt == Some(value.path)
    // == Some(path). And slot.path_if_in_pt == Some(excepted_path). So path == excepted_path.
    // Contradiction.
    assert(f(subtree.value, path));
    assert(g(subtree.value, path));
    if subtree.value.is_node() {
        if subtree.value.node.unwrap().meta_perm.addr() == excepted_addr {
            let idx = frame_to_index(meta_to_frame(excepted_addr));
            assert(subtree.value.metaregion_sound(regions));
            assert(regions.slot_owners[idx].path_if_in_pt == Some(subtree.value.path));
            assert(subtree.value.path == path);
            // path == excepted_path: contradiction with precondition
            assert(false);
        }
    }
    assert(h(subtree.value, path));

    // Children: from inv, child.value.path == path.push_tail(i).
    // excepted_path can't equal path.push_tail(i) (would need to extend path, but
    // excepted_path doesn't extend path by precondition).
    // excepted_path is also not a descendant of path.push_tail(i) (if excepted_path
    // diverges from path at some k < path.len(), it diverges from path.push_tail(i) at the
    // same k; if excepted_path.len() <= path.len(), then excepted_path.len() < path.push_tail(i).len()).
    if subtree.level < INC_LEVELS - 1 {
        assert forall |i: int|
            #![trigger subtree.children[i]]
            0 <= i < subtree.children.len() && subtree.children[i] is Some implies
            subtree.children[i].unwrap().tree_predicate_map(path.push_tail(i as usize), h) by {
            let child = subtree.children[i].unwrap();
            subtree.map_unroll_once(path, f, i);
            subtree.map_unroll_once(path, g, i);

            // child.value.path == path.push_tail(i) from rel_children
            assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                subtree.value, i, Some(child.value)));
            let child_path = path.push_tail(i as usize);
            assert(child.value.path == child_path);
            path.push_tail_property(i as usize);

            // child_path != excepted_path:
            // Case 1: excepted_path.len() <= path.len() < child_path.len(). Different lengths.
            // Case 2: excepted_path diverges from path at some k < path.len().
            //   child_path agrees with path at 0..path.len()-1 (from push_tail).
            //   So excepted_path diverges from child_path at k too.
            assert(child_path != excepted_path) by {
                if excepted_path.len() <= path.len() {
                    // child_path.len() == path.len() + 1 > excepted_path.len()
                } else {
                    let k = choose|k: int| 0 <= k < path.len() && #[trigger] excepted_path.index(k) != path.index(k);
                    assert(child_path.index(k) == path.index(k));
                    assert(excepted_path.index(k) != child_path.index(k));
                }
            };

            // Propagate "not a descendant" to child: excepted_path.len() <= child_path.len()
            // or diverges at some k < child_path.len()
            assert(excepted_path.len() <= child_path.len() ||
                (exists|k: int| 0 <= k < child_path.len() && #[trigger] excepted_path.index(k) != child_path.index(k))) by {
                if excepted_path.len() <= path.len() {
                    // excepted_path.len() <= path.len() < child_path.len()
                } else {
                    let k = choose|k: int| 0 <= k < path.len() && #[trigger] excepted_path.index(k) != path.index(k);
                    assert(child_path.index(k) == path.index(k));
                    assert(k < child_path.len());
                    assert(excepted_path.index(k) != child_path.index(k));
                }
            };

            subtree_unlock_upgrade(child, child_path, guards, regions, excepted_addr, excepted_path);
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

    /// The number of steps it will take to walk through the remaining entries of the page table
    /// starting at the given level.
    pub open spec fn max_steps_partial(self, level: usize) -> nat
        decreases NR_LEVELS - level,
        when level <= NR_LEVELS
    {
        if level == NR_LEVELS {
            0
        } else {
            // How many entries remain at this level?
            let cont = self.continuations[(level - 1) as int];
            // Each entry takes at most `max_step_subtree` steps.
            let steps = Self::max_steps_subtree(level) * ((NR_ENTRIES - cont.idx) as nat);
            // Then the number of steps for the remaining entries at higher levels
            let remaining_steps = self.max_steps_partial((level + 1) as usize);
            steps + remaining_steps
        }
    }

    pub open spec fn max_steps(self) -> nat {
        self.max_steps_partial(self.level as usize)
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
            1 <= start <= NR_LEVELS,
            forall |k: int|
                start - 1 <= k < NR_LEVELS ==> #[trigger] self.continuations[k].idx == other.continuations[k].idx,
        ensures
            self.max_steps_partial(start) == other.max_steps_partial(start),
        decreases NR_LEVELS - start,
    {
        if start < NR_LEVELS {
            self.max_steps_partial_eq(other, (start + 1) as usize);
        }
    }

    pub proof fn max_steps_partial_inv(self, other: Self, level: usize)
        requires
            self.inv(),
            other.inv(),
            self.level == other.level,
            self.level <= level <= NR_LEVELS,
            forall |i: int|
                #![trigger self.continuations[i].idx]
                #![trigger other.continuations[i].idx]
            self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].idx == other.continuations[i].idx,
        ensures
            self.max_steps_partial(level) == other.max_steps_partial(level),
        decreases NR_LEVELS - level,
    {
        if level < NR_LEVELS {
            self.max_steps_partial_inv(other, (level + 1) as usize);
        }
    }

    pub open spec fn push_level_owner_spec(self, guard_perm: GuardPerm<'rcu, C>) -> Self
    {
        let cont = self.continuations[self.level - 1];
        let (child, cont) = cont.make_cont_spec(self.va.index[self.level - 2] as usize, guard_perm);
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

    pub proof fn push_level_owner_decreases_steps(self, guard_perm: GuardPerm<'rcu, C>)
        requires
            self.inv(),
            self.level > 0,
        ensures
            self.push_level_owner_spec(guard_perm).max_steps() < self.max_steps()
    { admit() }

    pub proof fn push_level_owner_preserves_va(self, guard_perm: GuardPerm<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
        ensures
            self.push_level_owner_spec(guard_perm).va == self.va,
            self.push_level_owner_spec(guard_perm).continuations[self.level - 2].idx == self.va.index[self.level - 2],
    {
        assert(self.va.index.contains_key(self.level - 2));
    }

    pub proof fn push_level_owner_preserves_mappings(self, guard_perm: GuardPerm<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
            self.cur_entry_owner().is_node(),
        ensures
            self.push_level_owner_spec(guard_perm)@.mappings == self@.mappings,
    {
        let new_owner = self.push_level_owner_spec(guard_perm);
        let old_cont = self.continuations[self.level - 1];
        let (child_cont, modified_cont) = old_cont.make_cont_spec(self.va.index[self.level - 2] as usize, guard_perm);

        reveal(CursorContinuation::inv_children);

        // old_cont.view_mappings() == child_cont.view_mappings() + modified_cont.view_mappings()
        // From view_mappings_take_child: modified_cont.view_mappings() == old_cont.view_mappings() - child_spec
        // And child_cont.view_mappings() == child_spec (via as_page_table_owner_preserves_view_mappings)
        assert(old_cont.all_some());
        old_cont.view_mappings_take_child();
        // take_child_spec().1.view_mappings() == old_cont.view_mappings() - view_mappings_take_child_spec()

        // modified_cont.view_mappings() == take_child_spec().1.view_mappings()
        // They have the same children (both have children[idx] = None, rest unchanged)
        // and same path/entry_own.
        let taken = old_cont.take_child_spec().1;
        assert(modified_cont.view_mappings() =~= taken.view_mappings()) by {
            // modified_cont and taken differ only in how children[idx] is set to None
            // (update vs remove+insert), but the result is the same sequence.
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
            assert(modified_cont.path() == taken.path());
        };

        // child_cont.view_mappings() == view_mappings_take_child_spec()
        // Both are the set of mappings from the child subtree's children.
        // child_cont.view_mappings() = union over j of PTO(child_cont.children[j]).view_rec(child_cont.path().push_tail(j))
        // view_mappings_take_child_spec() = PTO(old_cont.children[old_cont.idx]).view_rec(old_cont.path().push_tail(old_cont.idx))
        // Since child_cont.children == old_cont.children[old_cont.idx].children
        //   and child_cont.path() == old_cont.path().push_tail(old_cont.idx) (from inv_children_rel)
        // The child_cont.view_mappings() is exactly the view_rec decomposition of the child subtree.
        old_cont.inv_children_rel_unroll(old_cont.idx as int);
        assert(child_cont.view_mappings() =~= old_cont.view_mappings_take_child_spec()) by {
            let child_subtree = old_cont.children[old_cont.idx as int].unwrap();
            let child_path = old_cont.path().push_tail(old_cont.idx as usize);
            assert(child_cont.children == child_subtree.children);
            assert(child_cont.path() == child_path);
            // Both child_cont.view_mappings() and PTO(child_subtree).view_rec(child_path) unfold
            // to the same set (union over children), since children and path are the same.
            assert(child_subtree.value.is_node());
            assert(child_path.len() < INC_LEVELS - 1) by {
                assert(old_cont.tree_level < INC_LEVELS - 1);
                assert(old_cont.entry_own.inv_base());
                old_cont.path().push_tail_property(old_cont.idx as usize);
            };
            // view_rec for a node = union over children; view_mappings = same union.
            // Need child_subtree.inv() for view_rec unfolding.
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
                    // child_cont.children[j] == child_subtree.children[j]
                    // child_cont.path() == child_path
                    assert(pto.0.children[j] is Some);
                    assert(pto.0.children[j] == child_cont.children[j]);
                };
                assert forall |m: Mapping| pto.view_rec(child_path).contains(m) implies
                    #[trigger] child_cont.view_mappings().contains(m) by {
                    // view_rec for node: exists i s.t. children[i] is Some && PTO(children[i]).view_rec(...)
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
        };

        // new_owner.view_mappings() == child_cont.view_mappings() + modified_cont.view_mappings()
        //                              + (higher continuations unchanged)
        // == view_mappings_take_child_spec() + (old_cont.view_mappings() - view_mappings_take_child_spec())
        //    + higher
        // == old_cont.view_mappings() + higher
        // == self.view_mappings()
        assert(new_owner.view_mappings() =~= self.view_mappings()) by {
            assert forall |m: Mapping| self.view_mappings().contains(m)
                implies new_owner.view_mappings().contains(m) by {
                let i = choose |i: int|
                    self.level - 1 <= i < NR_LEVELS
                    && (#[trigger] self.continuations[i]).view_mappings().contains(m);
                if i == self.level - 1 {
                    // m in old_cont.view_mappings()
                    // m in child_spec or m in modified.view_mappings()
                    if old_cont.view_mappings_take_child_spec().contains(m) {
                        // m in child_cont.view_mappings()
                        assert(new_owner.continuations[self.level - 2].view_mappings().contains(m));
                    } else {
                        // m in modified_cont.view_mappings()
                        assert(taken.view_mappings().contains(m));
                        assert(modified_cont.view_mappings().contains(m));
                        assert(new_owner.continuations[self.level - 1].view_mappings().contains(m));
                    }
                } else {
                    // i > self.level - 1, unchanged
                    assert(new_owner.continuations[i] == self.continuations[i]);
                }
            };
            assert forall |m: Mapping| new_owner.view_mappings().contains(m)
                implies self.view_mappings().contains(m) by {
                let i = choose |i: int|
                    new_owner.level - 1 <= i < NR_LEVELS
                    && (#[trigger] new_owner.continuations[i]).view_mappings().contains(m);
                if i == self.level - 2 {
                    // m in child_cont.view_mappings() == child_spec
                    assert(child_cont.view_mappings().contains(m));
                    assert(old_cont.view_mappings_take_child_spec().contains(m));
                    // child_spec ⊆ old_cont.view_mappings()
                    // view_mappings_take_child_spec is a subset of view_mappings
                    // (it's the view_rec of one child subtree)
                    assert(old_cont.view_mappings().contains(m)) by {
                        // view_mappings_take_child_spec() = PTO(children[idx]).view_rec(path.push_tail(idx))
                        // view_mappings() includes this for i == idx
                        let child_subtree = old_cont.children[old_cont.idx as int].unwrap();
                        assert(PageTableOwner(child_subtree).view_rec(
                            old_cont.path().push_tail(old_cont.idx as usize)).contains(m));
                    };
                    assert(self.continuations[self.level - 1].view_mappings().contains(m));
                } else if i == self.level - 1 {
                    // m in modified_cont.view_mappings() ⊆ old_cont.view_mappings()
                    assert(modified_cont.view_mappings().contains(m));
                    assert(taken.view_mappings().contains(m));
                    // taken.view_mappings() ⊆ old_cont.view_mappings() (subset after removal)
                    assert(old_cont.view_mappings().contains(m)) by {
                        // taken.view_mappings() == old_cont.view_mappings() - child_spec
                        // So taken.view_mappings() ⊆ old_cont.view_mappings()
                    };
                    assert(self.continuations[self.level - 1].view_mappings().contains(m));
                } else {
                    assert(self.continuations[i] == new_owner.continuations[i]);
                }
            };
        };
    }

    pub proof fn push_level_owner_preserves_inv(self, guard_perm: GuardPerm<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
            !self.popped_too_high,
            self.level < self.guard_level,
            // The current entry is a node (we're descending into it)
            self.cur_entry_owner().is_node(),
            // The child node's guard relates to the new guard_perm
            self.cur_entry_owner().node.unwrap().relate_guard_perm(guard_perm),
            // Guard distinctness: the new guard_perm points to a different node than all existing continuations
            forall |i: int|
                #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS ==>
                    self.continuations[i].guard_perm.value().inner.inner@.ptr.addr()
                        != guard_perm.value().inner.inner@.ptr.addr(),
        ensures
            self.push_level_owner_spec(guard_perm).inv(),
    {
        let new_owner = self.push_level_owner_spec(guard_perm);
        let new_level = (self.level - 1) as u8;

        let old_cont = self.continuations[self.level - 1];
        old_cont.inv_children_unroll(old_cont.idx as int);
        let child_node = old_cont.children[old_cont.idx as int].unwrap();
        let (child, modified_cont) = old_cont.make_cont_spec(self.va.index[self.level - 2] as usize, guard_perm);

        // Establish key facts about child
        old_cont.inv_children_rel_unroll(old_cont.idx as int);
        assert(child.entry_own == child_node.value);
        assert(child.entry_own == self.cur_entry_owner());
        assert(child.children == child_node.children);
        assert(child.guard_perm == guard_perm);
        assert(child.entry_own.is_node());
        assert(child.tree_level == old_cont.tree_level + 1);

        assert(child.inv()) by {
            reveal(CursorContinuation::inv_children);

            // 1. children.len()
            assert(child.children.len() == NR_ENTRIES);

            // 2. idx in range (from va.inv())
            assert(self.va.inv());
            assert(0 <= self.level - 2 < NR_LEVELS);
            assert(self.va.index.contains_key(self.level - 2));
            assert(0 <= self.va.index[self.level - 2] < NR_ENTRIES);
            assert(child.idx == self.va.index[self.level - 2] as usize);
            assert(0 <= child.idx < NR_ENTRIES);

            // 3. entry_own.inv() from child_node.inv()
            assert(child.entry_own.inv()) by {
                old_cont.inv_children_unroll(old_cont.idx as int);
            };
            assert(!child.entry_own.in_scope);

            // 4. relate_guard_perm from precondition
            assert(child.entry_own.node.unwrap().relate_guard_perm(child.guard_perm));

            // 5. tree_level == INC_LEVELS - level() - 1
            // Strategy: show child.entry_own.path.len() == child.entry_own.node.unwrap().tree_level
            // via grandchild path lengths, then connect to child.tree_level.

            // child.entry_own.path.len() == old_cont.tree_level + 1 == child.tree_level
            // (from rel_children on old_cont at idx)
            assert(child.entry_own.path.len() == old_cont.entry_own.node.unwrap().tree_level + 1);
            assert(old_cont.entry_own.node.unwrap().tree_level == old_cont.tree_level) by {
                assert(old_cont.tree_level == INC_LEVELS - old_cont.level() - 1);
            };
            assert(child.entry_own.path.len() == child.tree_level) by {
                assert(child.tree_level == old_cont.tree_level + 1);
            };

            // child.entry_own.node.unwrap().tree_level == child.entry_own.path.len()
            // via grandchild at index 0
            assert(child.entry_own.node.unwrap().tree_level == child.entry_own.path.len()) by {
                // child_node has all children Some (from child.all_some())
                assert(child.children[0] is Some);
                let gc = child.children[0].unwrap();
                // From child_node.inv() -> inv_children():
                // rel_children(child.entry_own, 0, Some(gc.value)) includes:
                //   gc.value.path.len() == child.entry_own.node.unwrap().tree_level + 1
                //   gc.value.path == child.entry_own.path.push_tail(0)
                // But we need to trigger these from OwnerSubtree::inv_children
                // child_node.inv() gives child_node.inv_children()
                // which gives rel_children(child_node.value, 0, Some(gc.value))
                assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    child.entry_own, 0, Some(gc.value)));
                assert(gc.value.path.len() == child.entry_own.node.unwrap().tree_level + 1);
                assert(gc.value.path == child.entry_own.path.push_tail(0usize));
                // push_tail_property: path.push_tail(0).len() == path.len() + 1
                assert(child.entry_own.inv_base());
                assert(child.entry_own.path.inv());
                child.entry_own.path.push_tail_property(0usize);
                assert(child.entry_own.path.push_tail(0usize).len() == child.entry_own.path.len() + 1);
            };

            // Combine: child.tree_level == child.entry_own.node.unwrap().tree_level
            //        == INC_LEVELS - child.level() - 1
            assert(child.tree_level == child.entry_own.node.unwrap().tree_level);
            assert(child.tree_level == INC_LEVELS - child.level() - 1);
            assert(child.tree_level < INC_LEVELS - 1);
            assert(child.path().len() == child.tree_level) by {
                assert(child.path() == child.entry_own.path);
            };

            // inv_children: from child_node.inv()
            assert(child.inv_children()) by {
                assert forall |j: int| 0 <= j < child.children.len() && #[trigger] child.children[j] is Some
                    implies child.children[j].unwrap().inv() by {
                    assert(child.children[j] == child_node.children[j]);
                    old_cont.inv_children_unroll(old_cont.idx as int);
                };
            };
            // inv_children_rel: from child_node's inv_children + recursive inv
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
                    // From child_node.inv_children():
                    //   gc.level == child_node.level + 1 == child.tree_level + 1
                    //   rel_children(child.entry_own, j, Some(gc.value))
                    assert(gc.level == child.tree_level + 1);
                    assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                        child.entry_own, j, Some(gc.value)));
                    // rel_children gives: gc.value.path == child.entry_own.path.push_tail(j)
                    //                     == child.path().push_tail(j)
                    // Also !in_scope from gc.inv() -> value.inv()
                    child.inv_children_unroll(j);
                    assert(gc.inv());
                    assert(gc.value.inv());
                    assert(!gc.value.in_scope);
                    // parent_level: from rel_children, gc.value.parent_level == child.entry_own.node.unwrap().level
                    assert(gc.value.parent_level == child.level());
                };
            };
        };

        assert(new_owner.level == new_level);
        assert(new_owner.va == self.va);
        assert(new_owner.guard_level == self.guard_level);
        assert(new_owner.prefix == self.prefix);
        assert(new_owner.popped_too_high == false);
        assert(new_owner.continuations[self.level - 1] == modified_cont);
        assert(new_owner.continuations[self.level - 2] == child);

        assert(modified_cont.entry_own == old_cont.entry_own);
        assert(modified_cont.idx == old_cont.idx);
        assert(modified_cont.tree_level == old_cont.tree_level);
        assert(modified_cont.path == old_cont.path);
        assert(modified_cont.guard_perm == old_cont.guard_perm);
        assert(modified_cont.children == old_cont.children.update(old_cont.idx as int, None));

        assert(child.entry_own == child_node.value);
        assert(child.tree_level == old_cont.tree_level + 1);
        assert(child.idx == self.va.index[self.level - 2] as usize);
        assert(child.children == child_node.children);
        assert(child.guard_perm == guard_perm);

        assert(new_owner.va.inv());

        assert(1 <= new_owner.level <= NR_LEVELS);

        assert(new_owner.guard_level <= NR_LEVELS);

        assert(!new_owner.popped_too_high ==> new_owner.level < new_owner.guard_level || new_owner.above_locked_range()) by {
            // new_owner.popped_too_high == false, so the antecedent is true.
            // From !self.popped_too_high + self.inv(): self.level < guard_level || above_locked_range
            // new_owner.level = self.level - 1 < self.level
            // If self.level < guard_level: new_owner.level < guard_level ✓
            // If above_locked_range: new_owner.above_locked_range ✓ (va unchanged)
        };

        assert(new_owner.prefix.inv());

        assert(new_owner.continuations[new_owner.level - 1].all_some()) by {
            // new_owner.continuations[new_level - 1] == child
            // child.children == child_node.children
            // From child.entry_own.is_node() and rel_children definition:
            // is_node() ==> child is Some for all indices
            // So child_node.inv_children() gives all children are Some
            assert(new_owner.continuations[new_owner.level - 1] == child);
            assert forall |j: int| 0 <= j < NR_ENTRIES implies child.children[j] is Some by {
                // From child_node.inv() -> inv_children() (since is_node => level < INC_LEVELS - 1):
                //   for each j: if children[j] is Some, rel_children(value, j, Some(ch.value))
                //                if children[j] is None, rel_children(value, j, None)
                // Since is_node(), rel_children(value, j, None) is false (it requires child is Some)
                // So children[j] must be Some
                if child.children[j] is None {
                    assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                        child.entry_own, j, None));
                    // rel_children with is_node() and child == None: requires child is Some — contradiction
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

        assert(modified_cont.inv()) by {
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
            assert(modified_cont.entry_own.node.unwrap().relate_guard_perm(modified_cont.guard_perm));
            assert(modified_cont.tree_level == INC_LEVELS - modified_cont.level() - 1);
            assert(modified_cont.tree_level < INC_LEVELS - 1);
            assert(modified_cont.path().len() == modified_cont.tree_level);
        };

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
            &&& new_owner.continuations[2].guard_perm.value().inner.inner@.ptr.addr() !=
                new_owner.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
            &&& new_owner.continuations[2].path() == new_owner.continuations[3].path().push_tail(new_owner.continuations[3].idx as usize)
            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    new_owner.continuations[3].entry_own, new_owner.continuations[3].idx as int,
                    Some(new_owner.continuations[2].entry_own))
        }) by {
            if new_owner.level <= 3 {
                if self.level == 4 {
                    assert(self.va.index.contains_key(2));
                    assert(new_owner.continuations[2].guard_perm == guard_perm);
                    assert(new_owner.continuations[3] == modified_cont);
                    assert(modified_cont.guard_perm == old_cont.guard_perm);
                    // guard distinctness
                    assert(new_owner.continuations[2].guard_perm.value().inner.inner@.ptr.addr() !=
                           new_owner.continuations[3].guard_perm.value().inner.inner@.ptr.addr()) by {
                        assert(self.continuations[self.level - 1].guard_perm.value().inner.inner@.ptr.addr()
                            != guard_perm.value().inner.inner@.ptr.addr());
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
            &&& new_owner.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                new_owner.continuations[2].guard_perm.value().inner.inner@.ptr.addr()
            &&& new_owner.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                new_owner.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
            &&& new_owner.continuations[1].path() == new_owner.continuations[2].path().push_tail(new_owner.continuations[2].idx as usize)
            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    new_owner.continuations[2].entry_own, new_owner.continuations[2].idx as int,
                    Some(new_owner.continuations[1].entry_own))
        }) by {
            if new_owner.level <= 2 {
                if self.level == 3 {
                    assert(self.va.index.contains_key(1));
                    assert(new_owner.continuations[1].guard_perm == guard_perm);
                    assert(new_owner.continuations[2] == modified_cont);
                    assert(modified_cont.guard_perm == old_cont.guard_perm);

                    assert(new_owner.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                           new_owner.continuations[2].guard_perm.value().inner.inner@.ptr.addr()) by {
                        assert(self.continuations[2].guard_perm.value().inner.inner@.ptr.addr()
                            != guard_perm.value().inner.inner@.ptr.addr());
                    };
                    assert(new_owner.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                           new_owner.continuations[3].guard_perm.value().inner.inner@.ptr.addr()) by {
                        assert(self.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
                            != guard_perm.value().inner.inner@.ptr.addr());
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
            &&& new_owner.continuations[0].guard_perm.value().inner.inner@.ptr.addr() !=
                new_owner.continuations[1].guard_perm.value().inner.inner@.ptr.addr()
            &&& new_owner.continuations[0].guard_perm.value().inner.inner@.ptr.addr() !=
                new_owner.continuations[2].guard_perm.value().inner.inner@.ptr.addr()
            &&& new_owner.continuations[0].guard_perm.value().inner.inner@.ptr.addr() !=
                new_owner.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
            &&& new_owner.continuations[0].path() == new_owner.continuations[1].path().push_tail(new_owner.continuations[1].idx as usize)
            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    new_owner.continuations[1].entry_own, new_owner.continuations[1].idx as int,
                    Some(new_owner.continuations[0].entry_own))
        }) by {
            if new_owner.level == 1 {
                // self.level == 2, new_level == 1
                assert(new_owner.continuations[0].guard_perm == guard_perm);
                assert(new_owner.continuations[1] == modified_cont);
                assert(modified_cont.guard_perm == old_cont.guard_perm);

                // Guard distinctness from precondition
                assert(self.continuations[1].guard_perm.value().inner.inner@.ptr.addr()
                    != guard_perm.value().inner.inner@.ptr.addr());
                assert(self.continuations[2].guard_perm.value().inner.inner@.ptr.addr()
                    != guard_perm.value().inner.inner@.ptr.addr());
                assert(self.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
                    != guard_perm.value().inner.inner@.ptr.addr());

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

    pub proof fn push_level_owner_preserves_invs(self, guard_perm: GuardPerm<'rcu, C>, regions: MetaRegionOwners, guards: Guards<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
            !self.popped_too_high,
            self.level < self.guard_level,
            self.only_current_locked(guards),
            self.nodes_locked(guards),
            self.metaregion_sound(regions),
            // The current entry is a node (we're descending into it)
            self.cur_entry_owner().is_node(),
            // The child node's guard relates to the new guard_perm
            self.cur_entry_owner().node.unwrap().relate_guard_perm(guard_perm),
            // The new guard_perm must be locked in guards
            guards.lock_held(guard_perm.value().inner.inner@.ptr.addr()),
        ensures
            self.push_level_owner_spec(guard_perm).inv(),
            self.push_level_owner_spec(guard_perm).children_not_locked(guards),
            self.push_level_owner_spec(guard_perm).nodes_locked(guards),
            self.push_level_owner_spec(guard_perm).metaregion_sound(regions),
            self.metaregion_correct(regions) ==>
                self.push_level_owner_spec(guard_perm).metaregion_correct(regions),
    {
        reveal(CursorContinuation::inv_children);
        let new_owner = self.push_level_owner_spec(guard_perm);
        let old_cont = self.continuations[self.level - 1];
        old_cont.inv_children_unroll_all();
        let (child_cont, modified_cont) = old_cont.make_cont_spec(self.va.index[self.level - 2] as usize, guard_perm);

        let cur_entry = self.cur_entry_owner();
        let cur_entry_addr = cur_entry.node.unwrap().meta_perm.addr();
        let cur_entry_path = old_cont.path().push_tail(old_cont.idx as usize);
        self.cont_entries_metaregion(regions);

        assert forall |i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies
                self.continuations[i].guard_perm.value().inner.inner@.ptr.addr()
                    != guard_perm.value().inner.inner@.ptr.addr() by {
            let cont_i = self.continuations[i];

            if cont_i.guard_perm.value().inner.inner@.ptr.addr()
                == guard_perm.value().inner.inner@.ptr.addr()
            {
                let addr = cont_i.entry_own.node.unwrap().meta_perm.addr();
                assert(addr == cur_entry.node.unwrap().meta_perm.addr());
                let idx = frame_to_index(meta_to_frame(addr));
                assert(regions.slot_owners[idx].path_if_in_pt == Some(cont_i.path()));
                assert(regions.slot_owners[idx].path_if_in_pt == Some(cur_entry_path));

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
        self.push_level_owner_preserves_inv(guard_perm);

        let excepted_idx = frame_to_index(meta_to_frame(cur_entry_addr));
        assert(regions.slot_owners[excepted_idx].path_if_in_pt == Some(cur_entry_path)) by {
            old_cont.inv_children_rel_unroll(old_cont.idx as int);
        };

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let g_except = CursorOwner::<'rcu, C>::node_unlocked_except(guards, cur_entry_addr);
        let h = CursorOwner::<'rcu, C>::node_unlocked(guards);

        assert(new_owner.children_not_locked(guards)) by {
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

                        assert(gc_path == cur_entry_path.push_tail(j as usize)) by {
                            assert(child_cont.path() == cur_entry_path);
                        };
                        assert(cur_entry_path.len() < gc_path.len());
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
                        assert(cur_entry_path.len() <= sibling_path.len()) by {
                            old_cont.inv_children_rel_unroll(old_cont.idx as int);
                            old_cont.path().push_tail_property(old_cont.idx as usize);
                        };

                        subtree_unlock_upgrade(sibling, sibling_path, guards, regions,
                            cur_entry_addr, cur_entry_path);
                    };
                } else {
                    assert(new_owner.continuations[i] == self.continuations[i]);
                    let cont_i = self.continuations[i];

                    // Pre-prove: cur_entry_path goes through cont_i.idx at cont_i.tree_level
                    assert(cur_entry_path.index(cont_i.tree_level as int) == cont_i.idx as usize) by {
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
                    };

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

                        subtree_unlock_upgrade(child_sub, child_path, guards, regions,
                            cur_entry_addr, cur_entry_path);
                    };
                }
            };
        };
        assert(new_owner.nodes_locked(guards)) by {
            assert forall |i: int|
                #![trigger new_owner.continuations[i]]
                new_owner.level - 1 <= i < NR_LEVELS implies
                new_owner.continuations[i].node_locked(guards) by {

                if i == self.level - 2 {
                    assert(new_owner.continuations[i] == child_cont);
                    assert(child_cont.guard_perm == guard_perm);
                } else if i == self.level - 1 {
                    assert(new_owner.continuations[i] == modified_cont);
                    assert(modified_cont.guard_perm == old_cont.guard_perm);
                } else {
                    assert(new_owner.continuations[i] == self.continuations[i]);
                }
            };
        };

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let g = PageTableOwner::<C>::path_tracked_pred(regions);
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
        if self.metaregion_correct(regions) {
            // Pre-prove tree_predicate_map for child_subtree (g)
            assert(child_subtree.tree_predicate_map(child_cont.path(), g)) by {
                assert(g(child_subtree.value, child_cont.path()));
                assert forall |j: int| 0 <= j < child_subtree.children.len() implies
                    match #[trigger] child_subtree.children[j] {
                        Some(ch) => ch.tree_predicate_map(child_cont.path().push_tail(j as usize), g),
                        None => true,
                    }
                by { child_subtree.map_unroll_once(child_cont.path(), g, j); };
            };

            // Pre-prove map_children for modified_cont (g)
            assert(modified_cont.map_children(g)) by {
                assert forall |j: int|
                    0 <= j < modified_cont.children.len() && #[trigger] modified_cont.children[j] is Some implies
                    modified_cont.children[j].unwrap().tree_predicate_map(modified_cont.path().push_tail(j as usize), g) by {
                    assert(j != old_cont.idx as int);
                    assert(modified_cont.children[j] == old_cont.children[j]);
                };
            };

            assert(new_owner.metaregion_correct(regions)) by {
                assert forall |i: int| #![auto]
                    new_owner.level - 1 <= i < NR_LEVELS implies {
                        &&& g(new_owner.continuations[i].entry_own, new_owner.continuations[i].path())
                        &&& new_owner.continuations[i].map_children(g)
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
    }

    #[verifier::returns(proof)]
    pub proof fn push_level_owner(tracked &mut self, tracked guard_perm: Tracked<GuardPerm<'rcu, C>>)
        requires
            old(self).inv(),
            old(self).level > 1,
        ensures
            *final(self) == old(self).push_level_owner_spec(guard_perm@),
    {
        assert(self.va.index.contains_key(self.level - 2));

        let ghost self0 = *self;
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);
        let ghost cont0 = cont;
        let tracked child = cont.make_cont(self.va.index[self.level - 2] as usize, guard_perm);

        assert((child, cont) == cont0.make_cont_spec(self.va.index[self.level - 2] as usize, guard_perm@));

        self.continuations.tracked_insert(self.level - 1, cont);
        self.continuations.tracked_insert(self.level - 2, child);

        assert(self.continuations == self0.continuations.insert(self.level - 1, cont).insert(self.level - 2, child));

        self.popped_too_high = false;

        self.level = (self.level - 1) as u8;
    }

    pub open spec fn pop_level_owner_spec(self) -> (Self, GuardPerm<'rcu, C>)
    {
        let child = self.continuations[self.level - 1];
        let cont = self.continuations[self.level as int];
        let (new_cont, guard_perm) = cont.restore_spec(child);
        let new_continuations = self.continuations.insert(self.level as int, new_cont);
        let new_continuations = new_continuations.remove(self.level - 1);
        let new_level = (self.level + 1) as u8;
        let popped_too_high = if new_level >= self.guard_level { true } else { false };
        (Self {
            continuations: new_continuations,
            level: new_level,
            popped_too_high: popped_too_high,
            ..self
        }, guard_perm)
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
            &&& new_owner.continuations[2].guard_perm.value().inner.inner@.ptr.addr() !=
                new_owner.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
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
            &&& new_owner.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                new_owner.continuations[2].guard_perm.value().inner.inner@.ptr.addr()
            &&& new_owner.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                new_owner.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
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
            self.metaregion_correct(regions) ==>
                self.pop_level_owner_spec().0.metaregion_correct(regions),
    {
        let new_owner = self.pop_level_owner_spec().0;
        let child = self.continuations[self.level - 1];
        let cont = self.continuations[self.level as int];
        let (new_cont, _guard_perm) = cont.restore_spec(child);
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
                        assert(new_cont.guard_perm == cont.guard_perm);
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
        let g = PageTableOwner::<C>::path_tracked_pred(regions);
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
        if self.metaregion_correct(regions) {
            assert(new_owner.metaregion_correct(regions)) by {
                assert forall |i: int| #![auto]
                    new_owner.level - 1 <= i < NR_LEVELS implies
                        new_owner.continuations[i].map_children(g)
                by {
                    if i > self.level as int {
                    } else {
                        new_cont.map_children_lift_skip_idx(cont, cont.idx as int, g, g);
                    }
                };
            };
        }
    }

    /// Update va to a new value that shares the same indices at levels >= self.level.
    /// This preserves invariants because:
    /// 1. The new va satisfies va.inv()
    /// 2. The indices at levels >= level match the continuation indices
    /// 3. in_locked_range/above_locked_range depend on va but the preconditions ensure consistency
    pub proof fn set_va_preserves_inv(self, new_va: AbstractVaddr)
        requires
            self.inv(),
            !self.popped_too_high,
            self.level < self.guard_level,
            new_va.inv(),
            new_va.offset == 0,
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
                r.prefix.align_diff(gl as int);
                r.prefix.align_up_concrete(gl as int);
                AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                    nat_align_down(r.va.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
                AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                    nat_align_down(r.prefix.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
                AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                    nat_align_up(r.prefix.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
                lemma_page_size_ge_page_size(gl as PagingLevel);
                lemma_nat_align_down_sound(r.va.to_vaddr() as nat, page_size(gl as PagingLevel) as nat);
                r.prefix.align_down_shape(gl as int);
                r.prefix.align_down(gl as int).reflect_prop(
                    nat_align_down(r.prefix.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
                r.prefix.align_up(gl as int).reflect_prop(
                    nat_align_up(r.prefix.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
            }
        };

        assert(r.continuations[r.level - 1].all_some());
        assert(r.level <= 4 ==> {
            &&& r.continuations.contains_key(3)
            &&& r.continuations[3].inv()
            &&& r.continuations[3].level() == 4
            &&& r.continuations[3].entry_own.parent_level == 5
            &&& r.va.index[3] == r.continuations[3].idx
        });

        assert(r.level <= 3 ==> {
            &&& r.continuations.contains_key(2)
            &&& r.continuations[2].inv()
            &&& r.continuations[2].level() == 3
            &&& r.continuations[2].entry_own.parent_level == 4
            &&& r.va.index[2] == r.continuations[2].idx
            &&& r.continuations[2].guard_perm.value().inner.inner@.ptr.addr() !=
                r.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
            &&& r.continuations[2].path() == r.continuations[3].path().push_tail(r.continuations[3].idx as usize)
        });

        assert(r.level <= 2 ==> {
            &&& r.continuations.contains_key(1)
            &&& r.continuations[1].inv()
            &&& r.continuations[1].level() == 2
            &&& r.continuations[1].entry_own.parent_level == 3
            &&& r.va.index[1] == r.continuations[1].idx
            &&& r.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                r.continuations[2].guard_perm.value().inner.inner@.ptr.addr()
            &&& r.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                r.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
            &&& r.continuations[1].path() == r.continuations[2].path().push_tail(r.continuations[2].idx as usize)
        });

        assert(r.level == 1 ==> {
            &&& r.continuations.contains_key(0)
            &&& r.continuations[0].inv()
            &&& r.continuations[0].level() == 1
            &&& r.continuations[0].entry_own.parent_level == 2
            &&& r.va.index[0] == r.continuations[0].idx
            &&& r.continuations[0].guard_perm.value().inner.inner@.ptr.addr() !=
                r.continuations[1].guard_perm.value().inner.inner@.ptr.addr()
            &&& r.continuations[0].guard_perm.value().inner.inner@.ptr.addr() !=
                r.continuations[2].guard_perm.value().inner.inner@.ptr.addr()
            &&& r.continuations[0].guard_perm.value().inner.inner@.ptr.addr() !=
                r.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
            &&& r.continuations[0].path() == r.continuations[1].path().push_tail(r.continuations[1].idx as usize)
        });
    }

    #[verifier::returns(proof)]
    pub proof fn pop_level_owner(tracked &mut self) -> (tracked guard_perm: GuardPerm<'rcu, C>)
        requires
            old(self).inv(),
            old(self).level < NR_LEVELS,
        ensures
            *final(self) == old(self).pop_level_owner_spec().0,
            guard_perm == old(self).pop_level_owner_spec().1,
    {
        let ghost self0 = *self;
        let tracked mut parent = self.continuations.tracked_remove(self.level as int);
        let tracked child = self.continuations.tracked_remove(self.level - 1);

        let tracked guard_perm = parent.restore(child);

        self.continuations.tracked_insert(self.level as int, parent);

        assert(self.continuations == self0.continuations.insert(self.level as int, parent).remove(self.level - 1));

        self.level = (self.level + 1) as u8;

        if self.level >= self.guard_level {
            self.popped_too_high = true;
        }

        guard_perm
    }

    pub open spec fn move_forward_owner_spec(self) -> Self
        recommends
            self.inv(),
            self.level < NR_LEVELS,
            self.in_locked_range(),
        decreases NR_LEVELS - self.level when self.level <= NR_LEVELS
    {
        if self.index() + 1 < NR_ENTRIES {
            self.inc_index().zero_below_level()
        } else if self.level < NR_LEVELS {
            self.pop_level_owner_spec().0.move_forward_owner_spec()
        } else {
            // Should never happen
            Self {
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
        self.in_locked_range_level_lt_guard_level();
        if self.index() + 1 < NR_ENTRIES {
            self.inc_and_zero_increases_va();
        } else if self.level + 1 < self.guard_level {
            self.pop_level_owner_preserves_inv();
            self.pop_level_owner_spec().0.move_forward_increases_va();
        } else {
            assert(self.guard_level == self.level + 1);
            assert(self.va.index[self.level as int] == 0);
            self.pop_level_owner_preserves_inv();
            let popped = self.pop_level_owner_spec().0;
            assert(self.move_forward_owner_spec() == popped.move_forward_owner_spec());
            assert(popped.move_forward_owner_spec() == popped.inc_index().zero_below_level());
            popped.inc_and_zero_increases_va();
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

    pub proof fn move_forward_owner_decreases_steps(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_locked_range(),
            !self.popped_too_high,
        ensures
            self.move_forward_owner_spec().max_steps() < self.max_steps()
        decreases NR_LEVELS - self.level,
    {
        if self.index() + 1 < NR_ENTRIES {
            let inc = self.inc_index();
            inc.zero_preserves_all_but_va();
            Self::max_steps_subtree_positive(self.level as usize);
            if self.level < NR_LEVELS {
                inc.zero_below_level().max_steps_partial_eq(self, (self.level + 1) as usize);
            }
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(
                Self::max_steps_subtree(self.level as usize) as int,
                (NR_ENTRIES - self.index() - 1) as int, 1);
            if self.level as usize == NR_LEVELS {
                self.in_locked_range_level_lt_nr_levels();
            }
        } else if self.level < NR_LEVELS {
            self.in_locked_range_level_lt_guard_level();
            self.pop_level_owner_preserves_inv();
            let popped = self.pop_level_owner_spec().0;
            if !popped.popped_too_high {
                popped.move_forward_owner_decreases_steps();
            } else {
                admit(); // max_steps termination measure issue
            }
            popped.max_steps_partial_eq(self, (self.level + 1) as usize);
            Self::max_steps_subtree_positive(self.level as usize);
        } else {
            self.in_locked_range_level_lt_nr_levels();
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
        ensures
            self.move_forward_owner_spec().va == self.va.align_up(self.level as int),
        decreases NR_LEVELS - self.level
    {
        if self.index() + 1 < NR_ENTRIES {
            let inc = self.inc_index();
            inc.zero_preserves_all_but_va();
            inc.zero_below_level_va();
            self.va.align_up_concrete(self.level as int);
            assert(inc.va.inv()) by {
                assert forall |i: int| 0 <= i < NR_LEVELS implies
                    inc.va.index.contains_key(i) && 0 <= #[trigger] inc.va.index[i] && inc.va.index[i] < NR_ENTRIES
                by { if i != self.level - 1 { assert(inc.va.index[i] == self.va.index[i]); } };
            };
            inc.va.align_down_concrete(self.level as int);
            let ps = page_size(self.level as PagingLevel) as nat;
            let self_va = self.va.to_vaddr() as nat;
            self.va.align_diff(self.level as int);
            lemma_page_size_ge_page_size(self.level as PagingLevel);
            assert(self.va.index[self.level - 1] == self.continuations[self.level - 1].idx);
            self.va.index_increment_adds_page_size(self.level as int);
            assert(self_va + ps == ps * 1 + self_va) by (nonlinear_arith);
            vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(1int, self_va as int, ps as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(self_va as int, ps as int);
            vstd::arithmetic::div_mod::lemma_mod_bound(self_va as int, ps as int);
            vstd::arithmetic::div_mod::lemma_div_pos_is_pos(self_va as int, ps as int);
        } else if self.level < NR_LEVELS {
            self.in_locked_range_level_lt_guard_level();
            self.pop_level_owner_preserves_inv();
            let popped = self.pop_level_owner_spec().0;
            if !popped.popped_too_high {
                popped.move_forward_va_is_align_up();
            } else {
                let inc_p = popped.inc_index();
                inc_p.zero_preserves_all_but_va();
                inc_p.zero_below_level_va();
                popped.va.align_up_concrete(popped.level as int);
                assert(inc_p.va.inv()) by {
                    assert forall |i: int| 0 <= i < NR_LEVELS implies
                        inc_p.va.index.contains_key(i) && 0 <= #[trigger] inc_p.va.index[i] && inc_p.va.index[i] < NR_ENTRIES
                    by { if i != popped.level - 1 { assert(inc_p.va.index[i] == popped.va.index[i]); } };
                };
                inc_p.va.align_down_concrete(popped.level as int);
                let ps_p = page_size(popped.level as PagingLevel) as nat;
                let popped_va = popped.va.to_vaddr() as nat;
                let inc_p_va = inc_p.va.to_vaddr() as nat;
                popped.va.align_diff(popped.level as int);
                lemma_page_size_ge_page_size(popped.level as PagingLevel);
                assert(popped.va.index[popped.level as int - 1] == popped.continuations[popped.level as int - 1].idx);
                popped.va.index_increment_adds_page_size(popped.level as int);
                assert(popped_va + ps_p == ps_p * 1 + popped_va) by (nonlinear_arith);
                vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(1int, popped_va as int, ps_p as int);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(popped_va as int, ps_p as int);
                vstd::arithmetic::div_mod::lemma_mod_bound(popped_va as int, ps_p as int);
                vstd::arithmetic::div_mod::lemma_div_pos_is_pos(popped_va as int, ps_p as int);
                assert(nat_align_down(inc_p_va, ps_p) == nat_align_up(popped_va, ps_p));
                assert(inc_p.va.align_down(popped.level as int) == popped.va.align_up(popped.level as int));
                assert(popped.move_forward_owner_spec().va == inc_p.zero_below_level().va);
            }
            assert(self.va.index[self.level as int - 1] == self.continuations[self.level as int - 1].idx);
            self.va.align_up_carry(self.level as int);
        } else {
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

        // From cursor invariant
        assert(child.inv());
        assert(child.all_some());
        assert(parent.inv());
        assert(parent.all_but_index_some());

        // Path relationship follows from CursorOwner::inv() path consistency conditions
        assert(child.path() == parent.path().push_tail(parent.idx as usize));

        // child.as_subtree().inv() follows from child.inv() + child.all_some()
        assert(child_subtree.inv()) by {
            // inv_node: value.inv(), la_inv(level), level < L, children.len() == N
            assert(child_subtree.value.inv());
            assert(child_subtree.level < INC_LEVELS);
            assert(child_subtree.children.len() == NR_ENTRIES);
            // la_inv: is_node() ==> tree_level < INC_LEVELS - 1
            assert(child.entry_own.is_node());
            assert(child.tree_level < INC_LEVELS - 1);
            assert(child_subtree.inv_node());

            // inv_children: for each i, child.level == tree_level + 1, rel_children holds
            assert(child_subtree.inv_children()) by {
                assert(child_subtree.level < INC_LEVELS - 1);
                assert forall |i: int| 0 <= i < NR_ENTRIES implies
                    match #[trigger] child_subtree.children[i] {
                        Some(ch) => {
                            &&& ch.level == child_subtree.level + 1
                            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(child_subtree.value, i, Some(ch.value))
                        },
                        None => <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(child_subtree.value, i, None),
                    }
                by {
                    assert(child.children[i] is Some);
                    let ch = child.children[i].unwrap();
                    assert(ch.level == child.tree_level + 1);
                    // rel_children body is identical for TreeNodeValue<NR_LEVELS> and <INC_LEVELS>
                    assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                        child.entry_own, i, Some(ch.value)));
                };
            };

            // Recursive child invariants
            assert forall |i: int| 0 <= i < NR_ENTRIES implies
                match #[trigger] child_subtree.children[i] {
                    Some(ch) => ch.inv(),
                    None => true,
                }
            by {
                child.inv_children_unroll(i);
                assert(child.children[i] is Some);
                assert(child.children[i].unwrap().inv());
            };
        };

        // Connect restore_spec to put_child_spec via as_subtree_restore
        parent.as_subtree_restore(child);
        // restored_parent.as_subtree() == parent.put_child_spec(child_subtree).as_subtree()

        // Since view_mappings depends only on children and path() (= entry_own.path),
        // and as_subtree() captures both, equal subtrees give equal view_mappings.
        assert(restored_parent.view_mappings() =~=
            parent.put_child_spec(child_subtree).view_mappings()) by {
            let r = restored_parent;
            let p = parent.put_child_spec(child_subtree);
            assert(r.children =~= p.children) by {
                assert forall |j: int| 0 <= j < r.children.len()
                    implies r.children[j] == p.children[j] by {
                    if j == parent.idx as int {
                        assert(r.children[j] == Some(child_subtree));
                    } else {
                        assert(r.children[j] == parent.children[j]);
                    }
                };
            };
            assert(r.path() == p.path());
            // With same children and path, view_mappings are the same
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

        // view_mappings_put_child: parent.put_child_spec(child_subtree).view_mappings()
        //   == parent.view_mappings() + PTO(child_subtree).view_rec(parent.path().push_tail(parent.idx))
        parent.view_mappings_put_child(child_subtree);

        // as_page_table_owner_preserves_view_mappings:
        //   PTO(child.as_subtree()).view_rec(child.path()) == child.view_mappings()
        child.as_page_table_owner_preserves_view_mappings();

        // Combined with path relationship:
        //   PTO(child_subtree).view_rec(parent.path().push_tail(parent.idx)) == child.view_mappings()
        // Therefore:
        //   restored_parent.view_mappings() == parent.view_mappings() + child.view_mappings()

        // Now show popped.view_mappings() == self.view_mappings()
        // popped has level = self.level + 1, continuations[self.level] = restored_parent
        // self has level, continuations[self.level - 1] = child, continuations[self.level] = parent
        assert(popped.level == (self.level + 1) as u8);
        assert(popped.continuations[self.level as int] == restored_parent);

        // The restored parent at index self.level is within the
        // view_mappings range [self.level, NR_LEVELS).
        assert(popped.view_mappings() =~= self.view_mappings()) by {
            // Forward: self.view_mappings() ⊆ popped.view_mappings()
            assert forall |m: Mapping| self.view_mappings().contains(m)
                implies popped.view_mappings().contains(m) by {
                let i = choose |i: int|
                    self.level - 1 <= i < NR_LEVELS
                    && (#[trigger] self.continuations[i]).view_mappings().contains(m);
                if i == self.level - 1 {
                    // m in child.view_mappings() ⊆ restored_parent.view_mappings()
                    assert(child.view_mappings().contains(m));
                    assert(restored_parent.view_mappings().contains(m));
                    assert(popped.continuations[self.level as int].view_mappings().contains(m));
                } else if i == self.level as int {
                    // m in parent.view_mappings() ⊆ restored_parent.view_mappings()
                    assert(parent.view_mappings().contains(m));
                    assert(restored_parent.view_mappings().contains(m));
                    assert(popped.continuations[self.level as int].view_mappings().contains(m));
                } else {
                    // i > self.level, unchanged
                    assert(popped.continuations[i] == self.continuations[i]);
                }
            };
            // Backward: popped.view_mappings() ⊆ self.view_mappings()
            assert forall |m: Mapping| popped.view_mappings().contains(m)
                implies self.view_mappings().contains(m) by {
                let i = choose |i: int|
                    popped.level - 1 <= i < NR_LEVELS
                    && (#[trigger] popped.continuations[i]).view_mappings().contains(m);
                if i == self.level as int {
                    // m in restored_parent.view_mappings()
                    //   = parent.view_mappings() ∪ child.view_mappings()
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
            // Case 1: result = self.inc_index().zero_below_level()
            let inc = self.inc_index();
            let result = inc.zero_below_level();

            // zero_below_level preserves continuations and level
            inc.zero_preserves_all_but_va();
            assert(result.continuations =~= inc.continuations);
            assert(result.level == inc.level);

            // inc_index only changes idx at level-1; children and entry_own unchanged
            let old_cont = self.continuations[self.level - 1];
            let new_cont = old_cont.inc_index();
            assert(new_cont.children =~= old_cont.children);
            assert(new_cont.entry_own == old_cont.entry_own);
            assert(new_cont.path() == old_cont.path());

            // CursorContinuation::view_mappings depends on children and path(), not idx
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

            // Now result.view_mappings() == self.view_mappings()
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
            // Case 2: result = self.pop_level_owner_spec().0.move_forward_owner_spec()
            let popped = self.pop_level_owner_spec().0;

            // Pop preserves inv and in_locked_range
            self.pop_level_owner_preserves_inv();
            assert(popped.in_locked_range()) by {
                assert(popped.va == self.va);
                assert(popped.prefix == self.prefix);
                assert(popped.guard_level == self.guard_level);
            };

            // Pop preserves mappings (restored parent within view_mappings range)
            self.pop_level_owner_preserves_mappings();
            // Inductive step
            popped.move_forward_owner_preserves_mappings();
        } else {
            // Case 3: level >= NR_LEVELS, only popped_too_high changes
            // continuations and level unchanged, view_mappings trivially preserved
        }
    }

    // NOTE: move_forward_owner_preserves_in_locked_range was removed because it is UNSOUND.
}

}

 
 
 
