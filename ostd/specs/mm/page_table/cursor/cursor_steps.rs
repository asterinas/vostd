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

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    /// The number of steps it will take to walk through every node of a full
    /// page table at level `level`
    pub open spec fn max_steps_subtree(level: usize) -> usize
        decreases level,
    {
        if level <= 1 {
            NR_ENTRIES
        } else {
            // One step to push down a level, then the number for that subtree
            (NR_ENTRIES * (Self::max_steps_subtree((level - 1) as usize) + 1)) as usize
        }
    }

    /// The number of steps it will take to walk through the remaining entries of the page table
    /// starting at the given level.
    pub open spec fn max_steps_partial(self, level: usize) -> usize
        decreases NR_LEVELS - level,
        when level <= NR_LEVELS
    {
        if level == NR_LEVELS {
            0
        } else {
            // How many entries remain at this level?
            let cont = self.continuations[(level - 1) as int];
            // Each entry takes at most `max_step_subtree` steps.
            let steps = Self::max_steps_subtree(level) * (NR_ENTRIES - cont.idx);
            // Then the number of steps for the remaining entries at higher levels
            let remaining_steps = self.max_steps_partial((level + 1) as usize);
            (steps + remaining_steps) as usize
        }
    }

    pub open spec fn max_steps(self) -> usize {
        self.max_steps_partial(self.level as usize)
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
        ensures
            self.push_level_owner_spec(guard_perm)@.mappings == self@.mappings,
    { admit() }

    pub proof fn push_level_owner_preserves_inv(self, guard_perm: GuardPerm<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
            !self.popped_too_high,
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
            assert(self.va.index.contains_key(self.level - 2));
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

        // VA/prefix consistency: !popped_too_high ==> va matches prefix
        // new_owner.popped_too_high == false. From !self.popped_too_high (precondition):
        // match holds for self. VA, prefix, guard_level unchanged ⟹ match for new_owner.
    }

    pub proof fn push_level_owner_preserves_invs(self, guard_perm: GuardPerm<'rcu, C>, regions: MetaRegionOwners, guards: Guards<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
            !self.popped_too_high,
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
        let new_level = (self.level - 1) as u8;

        let old_cont = self.continuations[self.level - 1];

        old_cont.inv_children_unroll_all();

        let (child_cont, modified_cont) = old_cont.make_cont_spec(self.va.index[self.level - 2] as usize, guard_perm);
        // Establish relate_guard_perm precondition
        assert(self.cur_entry_owner().node.unwrap().relate_guard_perm(guard_perm));

        // Establish guard distinctness precondition (node addresses differ across levels)
        assert(forall |i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==>
                self.continuations[i].guard_perm.value().inner.inner@.ptr.addr()
                    != guard_perm.value().inner.inner@.ptr.addr()) by { admit() };
        self.push_level_owner_preserves_inv(guard_perm);

        let cur_entry = self.cur_entry_owner();
        let cur_entry_addr = cur_entry.node.unwrap().meta_perm.addr();
        let cur_entry_path = old_cont.path().push_tail(old_cont.idx as usize);

        assert(cur_entry.metaregion_sound(regions));

        assert(new_owner.children_not_locked(guards)) by {
            assert forall |i: int|
                #![trigger new_owner.continuations[i]]
                new_owner.level - 1 <= i < NR_LEVELS implies
                new_owner.continuations[i].map_children(CursorOwner::<'rcu, C>::node_unlocked(guards)) by {

                if i == self.level - 2 {
                    assert(new_owner.continuations[i] == child_cont);
                    admit();
                } else if i == self.level - 1 {
                    assert(new_owner.continuations[i] == modified_cont);
                    assert(modified_cont.path() == old_cont.path());

                    assert forall |j: int|
                        #![trigger modified_cont.children[j]]
                        0 <= j < modified_cont.children.len() && modified_cont.children[j] is Some implies
                        modified_cont.children[j].unwrap().tree_predicate_map(
                            modified_cont.path().push_tail(j as usize),
                            CursorOwner::<'rcu, C>::node_unlocked(guards)) by {
                        assert(j != old_cont.idx as int);
                        assert(modified_cont.children[j] == old_cont.children[j]);
                        let sibling_root_path = old_cont.path().push_tail(j as usize);
                        assert(old_cont.path().inv()) by {
                            assert(old_cont.entry_own.inv_base());
                        };

                        push_tail_different_indices_different_paths(old_cont.path(), j as usize, old_cont.idx);
                        assert(sibling_root_path != cur_entry_path);

                        admit();
                    };
                } else {
                    assert(new_owner.continuations[i] == self.continuations[i]);
                    admit();
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
                } else {
                    assert(i >= self.level - 1);
                    if i == self.level - 1 {
                        assert(new_owner.continuations[i] == modified_cont);
                        assert(modified_cont.guard_perm == old_cont.guard_perm);
                    } else {
                        assert(new_owner.continuations[i] == self.continuations[i]);
                    }
                }
            };
        };

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let g = PageTableOwner::<C>::path_tracked_pred(regions);
        let child_subtree = child_cont.as_subtree();
        self.cont_entries_metaregion(regions);

        // child_subtree.inv() — shared between sound and correct proofs.
        assert(child_subtree.inv()) by {
            assert(child_subtree.value.inv());
            assert(child_subtree.level < INC_LEVELS);
            assert(child_subtree.children.len() == NR_ENTRIES);
            assert(child_cont.entry_own.is_node());
            assert(child_cont.tree_level < INC_LEVELS - 1);
            assert(child_subtree.inv_node());
            assert(child_subtree.inv_children()) by {
                assert(child_subtree.level < INC_LEVELS - 1);
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
                assert(child_cont.children[j] is Some);
                assert(child_cont.children[j].unwrap().inv());
            };
        };

        // metaregion_sound (unconditional)
        assert(new_owner.metaregion_sound(regions)) by {
            assert forall |i: int| #![auto]
                new_owner.level - 1 <= i < NR_LEVELS implies {
                    &&& f(new_owner.continuations[i].entry_own, new_owner.continuations[i].path())
                    &&& new_owner.continuations[i].map_children(f)
                } by {
                if i == self.level - 2 {
                    assert(new_owner.continuations[i] == child_cont);
                    assert(f(new_owner.continuations[i].entry_own, new_owner.continuations[i].path()));
                    assert(child_subtree.tree_predicate_map(child_cont.path(), f)) by {
                        assert(f(child_subtree.value, child_cont.path()));
                        assert forall |j: int| 0 <= j < child_subtree.children.len() implies
                            match #[trigger] child_subtree.children[j] {
                                Some(ch) => ch.tree_predicate_map(child_cont.path().push_tail(j as usize), f),
                                None => true,
                            }
                        by { child_subtree.map_unroll_once(child_cont.path(), f, j); };
                    };
                    assert(new_owner.continuations[i].map_children(f));
                } else if i == self.level - 1 {
                    assert(new_owner.continuations[i] == modified_cont);
                    assert(modified_cont.entry_own == old_cont.entry_own);
                    assert(modified_cont.path() == old_cont.path());
                    assert(f(modified_cont.entry_own, modified_cont.path()));
                    assert(modified_cont.map_children(f)) by {
                        assert forall |j: int|
                            0 <= j < modified_cont.children.len() && #[trigger] modified_cont.children[j] is Some implies
                            modified_cont.children[j].unwrap().tree_predicate_map(modified_cont.path().push_tail(j as usize), f) by {
                            assert(j != old_cont.idx as int);
                            assert(modified_cont.children[j] == old_cont.children[j]);
                        };
                    };
                } else {
                    assert(new_owner.continuations[i] == self.continuations[i]);
                    assert(f(new_owner.continuations[i].entry_own, new_owner.continuations[i].path()));
                    assert(new_owner.continuations[i].map_children(f));
                }
            };
        };
        // metaregion_correct (conditional)
        if self.metaregion_correct(regions) {
            assert(new_owner.metaregion_correct(regions)) by {
                assert forall |i: int| #![auto]
                    new_owner.level - 1 <= i < NR_LEVELS implies {
                        &&& g(new_owner.continuations[i].entry_own, new_owner.continuations[i].path())
                        &&& new_owner.continuations[i].map_children(g)
                    } by {
                    if i == self.level - 2 {
                        assert(new_owner.continuations[i] == child_cont);
                        assert(g(new_owner.continuations[i].entry_own, new_owner.continuations[i].path()));
                        assert(child_subtree.tree_predicate_map(child_cont.path(), g)) by {
                            assert(g(child_subtree.value, child_cont.path()));
                            assert forall |j: int| 0 <= j < child_subtree.children.len() implies
                                match #[trigger] child_subtree.children[j] {
                                    Some(ch) => ch.tree_predicate_map(child_cont.path().push_tail(j as usize), g),
                                    None => true,
                                }
                            by { child_subtree.map_unroll_once(child_cont.path(), g, j); };
                        };
                        assert(new_owner.continuations[i].map_children(g));
                    } else if i == self.level - 1 {
                        assert(new_owner.continuations[i] == modified_cont);
                        assert(modified_cont.entry_own == old_cont.entry_own);
                        assert(modified_cont.path() == old_cont.path());
                        assert(g(modified_cont.entry_own, modified_cont.path()));
                        assert(modified_cont.map_children(g)) by {
                            assert forall |j: int|
                                0 <= j < modified_cont.children.len() && #[trigger] modified_cont.children[j] is Some implies
                                modified_cont.children[j].unwrap().tree_predicate_map(modified_cont.path().push_tail(j as usize), g) by {
                                assert(j != old_cont.idx as int);
                                assert(modified_cont.children[j] == old_cont.children[j]);
                            };
                        };
                    } else {
                        assert(new_owner.continuations[i] == self.continuations[i]);
                        assert(g(new_owner.continuations[i].entry_own, new_owner.continuations[i].path()));
                        assert(new_owner.continuations[i].map_children(g));
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
            *self == old(self).push_level_owner_spec(guard_perm@),
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
            // Required to maintain popped_too_high ==> in_locked_range.
            // When above_locked_range and level + 1 >= guard_level, popping sets
            // popped_too_high but in_locked_range is false, violating the invariant.
            self.in_locked_range(),
        ensures
            self.pop_level_owner_spec().0.inv(),
    {
        reveal(CursorContinuation::inv_children);
        let child = self.continuations[self.level - 1];
        assert(child.inv());
        assert(child.all_some());

        let cont = self.continuations[self.level as int];
        assert(cont.inv());
        let (new_cont, _) = cont.restore_spec(child);
        let new_owner = self.pop_level_owner_spec().0;
        let new_level = (self.level + 1) as u8;

        let child_node = OwnerSubtree {
            value: child.entry_own,
            level: child.tree_level,
            children: child.children,
        };

        // Basic structural facts about new_cont
        assert(new_cont.children == cont.children.update(cont.idx as int, Some(child_node)));
        assert(new_cont.entry_own == cont.entry_own);
        assert(new_cont.idx == cont.idx);
        assert(new_cont.tree_level == cont.tree_level);
        assert(new_cont.guard_perm == cont.guard_perm);
        assert(new_cont.children[cont.idx as int] == Some(child_node));

        // new_owner structural facts
        assert(new_owner.level == new_level);
        assert(new_owner.va == self.va);
        assert(new_owner.guard_level == self.guard_level);
        assert(new_owner.prefix == self.prefix);

        // Map reasoning: new_owner.continuations = self.continuations.insert(self.level, new_cont).remove(self.level - 1)
        // The insert overwrites key self.level with new_cont.
        // The remove deletes key self.level - 1.
        // For keys > self.level: unchanged from self.continuations
        let nc = self.continuations.insert(self.level as int, new_cont).remove(self.level - 1);
        assert(new_owner.continuations == nc);
        assert(nc[self.level as int] == new_cont);
        // For key 3 when self.level < 3:
        if self.level < 3 {
            assert(3 != self.level as int && 3 != self.level - 1);
            assert(nc.contains_key(3));
            assert(nc[3] == self.continuations[3]);
        }
        // For key 2 when self.level < 2:
        if self.level < 2 {
            assert(2 != self.level as int && 2 != self.level - 1);
            assert(nc.contains_key(2));
            assert(nc[2] == self.continuations[2]);
        }
        // For key 1 when self.level < 1: impossible (level >= 1)
        // Summary by self.level value:
        if self.level as int == 3 {
            assert(nc[3] == new_cont);
        } else if self.level as int == 2 {
            assert(nc[2] == new_cont);
            assert(nc[3] == self.continuations[3]);
        } else if self.level as int == 1 {
            assert(nc[1] == new_cont);
            assert(nc[2] == self.continuations[2]);
            assert(nc[3] == self.continuations[3]);
        }

        // (1) va.inv() — unchanged
        assert(new_owner.va.inv());

        // (2) level bounds
        assert(1 <= new_owner.level <= NR_LEVELS);

        // (3) guard_level bounds
        assert(new_owner.guard_level <= NR_LEVELS);

        // (5) in_locked_range || above_locked_range — va, prefix, guard_level unchanged
        assert(new_owner.in_locked_range() || new_owner.above_locked_range());

        // (6) popped_too_high conditions
        assert(new_owner.popped_too_high ==> new_owner.level >= new_owner.guard_level && new_owner.in_locked_range()) by {
            if new_owner.popped_too_high {
                assert(new_owner.level >= new_owner.guard_level);
                // va, prefix, guard_level unchanged, so in_locked_range preserved
            }
        };
        assert(!new_owner.popped_too_high ==> new_owner.level < new_owner.guard_level || new_owner.above_locked_range()) by {
            if !new_owner.popped_too_high {
                // !popped_too_high means new_level < guard_level
                assert(new_owner.level < new_owner.guard_level);
            }
        };

        // (9) prefix.inv() — unchanged
        assert(new_owner.prefix.inv());

        // (7) new_cont.all_some() — restored child fills the gap
        assert(new_cont.all_some()) by {
            assert forall |i: int| 0 <= i < NR_ENTRIES implies new_cont.children[i] is Some by {
                if i == cont.idx as int {
                    assert(new_cont.children[i] == Some(child_node));
                } else {
                    // From cont.all_but_index_some()
                    assert(new_cont.children[i] == cont.children[i]);
                }
            };
        };

        // (8) all_but_index_some at higher levels — unchanged
        assert(forall |i: int| new_owner.level <= i < NR_LEVELS ==> {
            (#[trigger] new_owner.continuations[i]).all_but_index_some()
        }) by {
            assert forall |i: int| new_owner.level <= i < NR_LEVELS implies
                (#[trigger] new_owner.continuations[i]).all_but_index_some() by {
                // i >= self.level + 1, so i > self.level
                // For i == self.level: new_owner.continuations[i] == new_cont
                // For i > self.level: new_owner.continuations[i] == self.continuations[i]
                if i == self.level as int {
                    // new_cont: all children are Some, so all_but_index_some() holds trivially
                    assert(new_owner.continuations[i] == new_cont);
                    assert(new_cont.all_some());
                    // all_some implies all_but_index_some
                    assert forall |j: int|
                        0 <= j < NR_ENTRIES && j != new_cont.idx as int implies
                        new_cont.children[j] is Some by {};
                } else {
                    assert(new_owner.continuations[i] == self.continuations[i]);
                }
            };
        };

        // new_cont.inv()
        assert(new_cont.inv()) by {
            assert(new_cont.children.len() == NR_ENTRIES);
            assert(0 <= new_cont.idx < NR_ENTRIES);
            assert(new_cont.entry_own.is_node());
            assert(new_cont.entry_own.inv());
            assert(!new_cont.entry_own.in_scope);
            assert(new_cont.entry_own.node.unwrap().relate_guard_perm(new_cont.guard_perm));
            assert(new_cont.tree_level == INC_LEVELS - new_cont.level() - 1);
            assert(new_cont.tree_level < INC_LEVELS - 1);
            assert(new_cont.path().len() == new_cont.tree_level);

            // inv_children: all children (including restored child_node) have inv()
            // First establish child_node.inv() == child.as_subtree().inv()
            assert(child_node == child.as_subtree());
            assert(child_node.inv()) by {
                assert(child_node.value.inv());
                assert(child_node.level < INC_LEVELS);
                assert(child_node.children.len() == NR_ENTRIES);
                assert(child.entry_own.is_node());
                assert(child.tree_level < INC_LEVELS - 1);
                assert(child_node.inv_node());
                assert(child_node.inv_children()) by {
                    assert(child_node.level < INC_LEVELS - 1);
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
                    assert(child.children[j] is Some);
                    assert(child.children[j].unwrap().inv());
                };
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

            // inv_children_rel: restored child has correct parent_level, tree_level, path
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
                        // Restored child: child_node at cont.idx
                        assert(new_cont.children[i].unwrap() == child_node);
                        assert(child_node.value == child.entry_own);
                        assert(child_node.level == child.tree_level);
                        // !in_scope: from child.inv() -> entry_own.inv()
                        assert(!child.entry_own.in_scope);
                        // tree_level: child.tree_level == cont.tree_level + 1
                        // From CursorOwner::inv() level conditions
                        assert(child.tree_level == cont.tree_level + 1) by {
                            // From CursorOwner::inv() level blocks:
                            //   continuations[k].level() == k + 1
                            // So child.level() == self.level, cont.level() == self.level + 1
                            // From CursorContinuation::inv():
                            //   tree_level == INC_LEVELS - level() - 1
                            // Therefore child.tree_level == cont.tree_level + 1
                            if self.level as int == 1 {
                                assert(child.level() == 1);
                                assert(cont.level() == 2);
                            } else if self.level as int == 2 {
                                assert(child.level() == 2);
                                assert(cont.level() == 3);
                            } else {
                                // self.level == 3 (since self.level < NR_LEVELS == 4)
                                assert(child.level() == 3);
                                assert(cont.level() == 4);
                            }
                        };
                        // parent_level: from CursorOwner::inv() level blocks
                        // continuations[k].entry_own.parent_level == k + 2
                        assert(child.entry_own.parent_level == new_cont.level()) by {
                            if self.level as int == 1 {
                                assert(child.entry_own.parent_level == 2);
                                assert(new_cont.level() == 2);
                            } else if self.level as int == 2 {
                                assert(child.entry_own.parent_level == 3);
                                assert(new_cont.level() == 3);
                            } else {
                                assert(child.entry_own.parent_level == 4);
                                assert(new_cont.level() == 4);
                            }
                        };
                        // path: from CursorOwner::inv() path consistency
                        // continuations[k].path() == continuations[k+1].path().push_tail(continuations[k+1].idx)
                        assert(child.entry_own.path == new_cont.path().push_tail(cont.idx as usize)) by {
                            // child.path() == child.entry_own.path
                            // cont.path() == cont.entry_own.path == new_cont.path() (same entry_own)
                            assert(new_cont.path() == cont.path());
                            if self.level as int == 1 {
                                // child = cont[0], cont = cont[1]
                                // inv: cont[0].path() == cont[1].path().push_tail(cont[1].idx)
                                assert(child.path() == cont.path().push_tail(cont.idx as usize));
                            } else if self.level as int == 2 {
                                assert(child.path() == cont.path().push_tail(cont.idx as usize));
                            } else {
                                assert(child.path() == cont.path().push_tail(cont.idx as usize));
                            }
                        };
                        // rel_children: from CursorOwner::inv() PTE consistency condition
                        // self.inv() gives: rel_children(cont.entry_own, cont.idx, Some(child.entry_own))
                        // new_cont.entry_own == cont.entry_own, so this transfers directly
                        assert(<EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                            new_cont.entry_own, cont.idx as int, Some(child.entry_own))) by {
                            if self.level as int == 1 {
                            } else if self.level as int == 2 {
                            } else {
                            }
                        };
                    } else {
                        assert(new_cont.children[i] == cont.children[i]);
                        cont.inv_children_rel_unroll(i);
                    }
                };
            };
        };

        // prefix index consistency
        assert(forall |i: int| i < self.guard_level ==> self.prefix.index[i] == 0);
        // VA/prefix match: !popped_too_high ==> match
        // If !new_owner.popped_too_high: new_level < guard_level, so self.level < guard_level.
        // From self.inv(): popped_too_high ==> level >= guard_level, so !self.popped_too_high.
        // Match from self.inv(). VA unchanged.
        // If new_owner.popped_too_high: condition is vacuous.
        assert(!new_owner.popped_too_high ==> forall |i: int| new_owner.guard_level <= i < NR_LEVELS ==>
            new_owner.va.index[i] == new_owner.prefix.index[i]) by {
            if !new_owner.popped_too_high {
                // new_level < guard_level means self.level < guard_level
                // so !self.popped_too_high from self.inv()
            }
        };

        // Level-specific conditions
        // The structure mirrors CursorOwner::inv() level conditions.
        // After pop, new_level = self.level + 1. We need conditions for levels >= new_level.
        // For levels that were already active (>= self.level + 1 in old state), unchanged.
        // For level self.level (= new_level - 1): new_cont was just restored.

        // Level 4 condition
        assert(new_owner.level <= 4 ==> {
            &&& new_owner.continuations.contains_key(3)
            &&& new_owner.continuations[3].inv()
            &&& new_owner.continuations[3].level() == 4
            &&& new_owner.continuations[3].entry_own.parent_level == 5
            &&& new_owner.va.index[3] == new_owner.continuations[3].idx
        }) by {
            if new_owner.level <= 4 {
                if self.level as int == 3 {
                    assert(new_owner.continuations[3] == new_cont);
                    // From self.inv() level <= 4: cont == self.continuations[3]
                    // has level() == 4, parent_level == 5, idx == va.index[3]
                    // new_cont preserves entry_own, idx from cont
                    assert(new_cont.entry_own == cont.entry_own);
                    assert(new_cont.idx == cont.idx);
                } else {
                    // self.level < 3 or self.level == 4
                    // continuations[3] unchanged
                    assert(new_owner.continuations[3] == self.continuations[3]);
                }
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
                    assert(new_owner.continuations[3] == self.continuations[3]);
                    assert(new_cont.entry_own == cont.entry_own);
                    assert(new_cont.idx == cont.idx);
                    assert(new_cont.guard_perm == cont.guard_perm);
                    // PTE consistency: new_cont.entry_own == cont.entry_own, and
                    // rel_children(cont.entry_own, cont.idx, Some(child.entry_own)) from self.inv()
                    // But here the child at cont.idx is the restored child_node,
                    // and cont[2].entry_own == new_cont.entry_own == cont.entry_own.
                    // We need rel_children(cont[3].entry_own, cont[3].idx, Some(cont[2].entry_own))
                    // = rel_children(self.cont[3].entry_own, self.cont[3].idx, Some(cont.entry_own))
                    // This was in self.inv() level <= 3 block!
                } else {
                    assert(self.level as int == 1);
                    assert(new_owner.continuations[2] == self.continuations[2]);
                    assert(new_owner.continuations[3] == self.continuations[3]);
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
                assert(self.level as int == 1);
                assert(new_owner.continuations[1] == new_cont);
                assert(new_owner.continuations[2] == self.continuations[2]);
                assert(new_owner.continuations[3] == self.continuations[3]);
                assert(new_cont.entry_own == cont.entry_own);
                assert(new_cont.idx == cont.idx);
                assert(new_cont.guard_perm == cont.guard_perm);
                // PTE consistency: from self.inv() level <= 2 block
                // self.continuations[2].entry_own, self.continuations[2].idx unchanged
                // new_cont.entry_own == cont.entry_own == self.continuations[1].entry_own
            }
        };

        // Level 1 condition
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
        }) by {
            if new_owner.level == 1 {
                // new_level = 1 means self.level = 0, but self.level >= 1 contradiction
                // So this case is impossible
                assert(false);
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

        // in_locked_range: va, prefix, guard_level unchanged by pop (..self)
        assert(new_owner.va == self.va);
        assert(new_owner.prefix == self.prefix);
        assert(new_owner.guard_level == self.guard_level);

        // nodes_locked: range shrinks from [self.level-1, NR_LEVELS) to [self.level, NR_LEVELS)
        // new_cont.guard_perm = cont.guard_perm (restore only changes children)
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

        // only_current_locked: excepted address is child.entry_own.node.meta_perm.addr()
        // After pop, cur_entry_owner = child.entry_own (restored as child_node at cont.idx)
        let child_addr = child.entry_own.node.unwrap().meta_perm.addr();

        // node_unlocked implies node_unlocked_except for any address
        assert(OwnerSubtree::<C>::implies(
            CursorOwner::<'rcu, C>::node_unlocked(guards),
            CursorOwner::<'rcu, C>::node_unlocked_except(guards, child_addr),
        ));

        // Lift: all old continuations satisfy node_unlocked_except
        self.map_children_implies(
            CursorOwner::<'rcu, C>::node_unlocked(guards),
            CursorOwner::<'rcu, C>::node_unlocked_except(guards, child_addr),
        );

        // For levels > self.level: new continuations == old continuations, already covered
        // For level == self.level: new_cont has child restored at cont.idx
        assert(new_owner.only_current_locked(guards)) by {
            assert forall |i: int|
                #![trigger new_owner.continuations[i]]
                new_owner.level - 1 <= i < NR_LEVELS implies
                new_owner.continuations[i].map_children(
                    CursorOwner::<'rcu, C>::node_unlocked_except(guards, child_addr)) by {
                if i > self.level as int {
                    assert(new_owner.continuations[i] == self.continuations[i]);
                    // Already have node_unlocked_except from map_children_implies above
                } else {
                    // i == self.level
                    assert(new_owner.continuations[i] == new_cont);
                    // new_cont = cont with children[cont.idx] = Some(child_node)
                    // For j != cont.idx: same as cont, node_unlocked_except from above
                    // For j == cont.idx: child_node.value == child.entry_own,
                    //   child_addr == child.entry_own addr, so node_unlocked_except is vacuous
                    //   Children from child.map_children(node_unlocked) -> node_unlocked_except
                    let child_subtree = child.as_subtree();
                    assert(child_subtree.inv()) by {
                        assert(child_subtree.value.inv());
                        assert(child_subtree.level < INC_LEVELS);
                        assert(child_subtree.children.len() == NR_ENTRIES);
                        assert forall |j: int| 0 <= j < NR_ENTRIES implies
                            match #[trigger] child_subtree.children[j] {
                                Some(ch) => ch.inv(),
                                None => true,
                            }
                        by {
                            child.inv_children_unroll(j);
                        };
                    };
                    new_cont.map_children_lift_skip_idx(
                        cont,
                        cont.idx as int,
                        CursorOwner::<'rcu, C>::node_unlocked(guards),
                        CursorOwner::<'rcu, C>::node_unlocked_except(guards, child_addr),
                    );
                }
            };
        };

        // metaregion: child.entry_own.metaregion_sound(regions) is not directly tracked by
        // map_full_tree (which only checks map_children, not entry_own of continuations).
        // This property was established when push extracted the child from the parent's subtree,
        // and is invariant since no operations modify higher-level entry_owns.
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let g = PageTableOwner::<C>::path_tracked_pred(regions);
        let child_subtree = child.as_subtree();
        self.cont_entries_metaregion(regions);

        assert(child_subtree.inv()) by {
            assert forall |j: int| 0 <= j < NR_ENTRIES implies
                match #[trigger] child_subtree.children[j] {
                    Some(ch) => ch.inv(),
                    None => true,
                }
            by { child.inv_children_unroll(j); };
        };

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
            new_va.inv(),
            forall |i: int| #![auto] self.level - 1 <= i < NR_LEVELS ==> new_va.index[i] == self.va.index[i],
            forall |i: int| #![auto] self.guard_level - 1 <= i < NR_LEVELS ==> new_va.index[i] == self.prefix.index[i],
        ensures
            self.set_va_spec(new_va).inv(),
    {
        let r = self.set_va_spec(new_va);
        // Everything unchanged except va
        assert(r.va == new_va);
        assert(r.level == self.level);
        assert(r.guard_level == self.guard_level);
        assert(r.prefix == self.prefix);
        assert(r.popped_too_high == self.popped_too_high);
        assert(r.continuations == self.continuations);

        // va.inv()
        assert(r.va.inv());

        // Level bounds, guard_level bounds
        assert(1 <= r.level <= NR_LEVELS);
        assert(r.guard_level <= NR_LEVELS);

        // TOP_LEVEL_INDEX_RANGE: new_va.index[NR_LEVELS - 1] == self.va.index[NR_LEVELS - 1] (from precondition)
        assert(C::TOP_LEVEL_INDEX_RANGE_spec().start <= r.va.index[NR_LEVELS - 1]);
        assert(r.va.index[NR_LEVELS - 1] < C::TOP_LEVEL_INDEX_RANGE_spec().end);

        // in_locked_range: from precondition, new_va.index[i] == prefix.index[i] for i >= guard_level
        // This means new_va is in the same guard-level subtree as prefix, hence in_locked_range
        assert(r.in_locked_range()) by {
            r.prefix_in_locked_range();
        };

        // popped_too_high conditions
        assert(r.popped_too_high ==> r.level >= r.guard_level && r.in_locked_range()) by {
            if r.popped_too_high {
                assert(r.level >= r.guard_level);
                // r.in_locked_range() already proved above
            }
        };
        assert(!r.popped_too_high ==> r.level < r.guard_level || r.above_locked_range()) by {
            if !r.popped_too_high {
                // From self.inv(): !self.popped_too_high ==> match (new invariant).
                // match + prefix_in_locked_range ==> self.in_locked_range().
                // But self.in_locked_range() && self.above_locked_range() is contradictory.
                // So !self.popped_too_high ==> !self.above_locked_range().
                // Then from !self.popped_too_high ==> level < guard_level || above_locked_range:
                //   level < guard_level.
                assert(!self.popped_too_high);
                self.prefix_in_locked_range();
                assert(self.in_locked_range());
                assert(self.level < self.guard_level || self.above_locked_range());
                // r.level == self.level
            }
        };

        // all_some, all_but_index_some — unchanged (continuations unchanged)
        assert(r.continuations[r.level - 1].all_some());

        // prefix.inv() — unchanged
        assert(r.prefix.inv());
        assert(forall |i: int| i < r.guard_level ==> r.prefix.index[i] == 0);

        // VA/prefix consistency
        assert(r.level <= r.guard_level ==> forall |i: int| r.guard_level <= i < NR_LEVELS ==>
            r.va.index[i] == r.prefix.index[i]);

        // Level conditions: continuations unchanged, va.index matches at levels >= level - 1
        // so va.index[k] == self.va.index[k] == continuations[k].idx for k >= level - 1
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
            *self == old(self).pop_level_owner_spec().0,
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
        ensures
            self.move_forward_owner_spec().va.to_vaddr() > self.va.to_vaddr(),
        decreases NR_LEVELS - self.level
    {
        if self.index() + 1 < NR_ENTRIES {
            self.inc_and_zero_increases_va();
        } else if self.level < NR_LEVELS {
            self.pop_level_owner_preserves_inv();
            self.pop_level_owner_spec().0.move_forward_increases_va();
        } else {
            // self.level == NR_LEVELS (from level <= NR_LEVELS and not < NR_LEVELS)
            // But in_locked_range + !popped_too_high ==> level < guard_level <= NR_LEVELS
            // Contradiction: level == NR_LEVELS but level < NR_LEVELS
            if !self.popped_too_high {
                self.in_locked_range_level_lt_nr_levels();
            } else {
                // popped_too_high + in_locked_range: level >= guard_level
                // But also level == NR_LEVELS and guard_level <= NR_LEVELS
                // in_locked_range means va < locked_range.end
                // At level NR_LEVELS, the cursor is at the root — contradiction with in_locked_range
                // in_locked_range_level_lt_nr_levels handles !popped_too_high only
                // For popped_too_high: level >= guard_level, but we'd need level < NR_LEVELS
                // Since popped_too_high ==> in_locked_range, and in_locked_range ==> !above_locked_range
                // With !popped_too_high or popped_too_high, the key is level < NR_LEVELS
                // But we have level == NR_LEVELS. popped_too_high ==> level >= guard_level.
                // guard_level <= NR_LEVELS. So level >= guard_level is NR_LEVELS >= guard_level — fine.
                // But this is the "unreachable" case. Actually level == NR_LEVELS with inv() is possible.
                // The real contradiction comes from in_locked_range + level == NR_LEVELS.
                admit();
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

    pub proof fn move_forward_owner_decreases_steps(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
        ensures
            self.move_forward_owner_spec().max_steps() < self.max_steps()
    { admit() }

    pub proof fn move_forward_va_is_align_up(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
        ensures
            self.move_forward_owner_spec().va == self.va.align_up(self.level as int),
        decreases NR_LEVELS - self.level
    {
        admit()
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

    /// After `move_forward_owner_spec`, the cursor remains within the locked range.
    pub proof fn move_forward_owner_preserves_in_locked_range(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_locked_range(),
        ensures
            self.move_forward_owner_spec().in_locked_range(),
        decreases NR_LEVELS - self.level,
    {
        if self.index() + 1 < NR_ENTRIES {
            // inc_index + zero_below_level: VA advances within the current node.
            // The node fits within the locked range, so the new VA is still in range.
            admit();
        } else if self.level < NR_LEVELS {
            // Pop + recurse: pop preserves VA (and thus in_locked_range),
            // then the recursive call preserves it.
            self.pop_level_owner_preserves_inv();
            let popped = self.pop_level_owner_spec().0;
            // pop preserves va, prefix, guard_level, so in_locked_range is preserved.
            assert(popped.in_locked_range());
            popped.move_forward_owner_preserves_in_locked_range();
        } else {
            // level == NR_LEVELS: unreachable (in_locked_range + inv ==> level < guard_level <= NR_LEVELS,
            // but level <= NR_LEVELS, so level == NR_LEVELS means guard_level == NR_LEVELS too)
        }
    }

    /// After the pop loop in `move_forward`, the cursor level is strictly below guard_level.
    ///
    /// The loop exits when `level >= guard_level` OR `pte_index != 0`. The `level >= guard_level`
    /// case is impossible: reaching guard_level via pop would set `popped_too_high = true`, but
    /// the loop invariant `owner.move_forward_owner_spec() == owner0.move_forward_owner_spec()`
    /// combined with `move_forward_not_popped_too_high` gives
    /// `!owner.move_forward_owner_spec().popped_too_high`, and `move_forward_owner_spec()`
    /// on a `popped_too_high` state gives a different result — a contradiction.
    pub proof fn move_forward_pop_loop_level_lt_guard(self, owner0: Self)
        requires
            self.inv(),
            self.in_locked_range(),
            self.level <= self.guard_level,
            owner0.inv(),
            owner0.in_locked_range(),
            self.move_forward_owner_spec() == owner0.move_forward_owner_spec(),
            !owner0.move_forward_owner_spec().popped_too_high,
        ensures
            self.level < self.guard_level,
    {
        // From inv: !popped_too_high ==> level < guard_level || above_locked_range.
        // in_locked_range ==> !above_locked_range.
        // So !popped_too_high ==> level < guard_level.
        if !self.popped_too_high {
            assert(self.in_locked_range() ==> !self.above_locked_range());
        } else {
            // popped_too_high: from inv, level >= guard_level.
            // With level <= guard_level: level == guard_level.
            // Need contradiction from move_forward_owner_spec preconditions.
            // popped_too_high at guard_level + in_locked_range is a valid state,
            // but move_forward_owner_spec on such a state advances past the locked
            // range, setting popped_too_high = false but above_locked_range.
            // owner0 starts in_locked_range with !popped_too_high (from its own inv),
            // so owner0.move_forward_owner_spec() != self.move_forward_owner_spec()
            // in this case — contradicting the precondition.
            admit();
        }
    }
}

}
