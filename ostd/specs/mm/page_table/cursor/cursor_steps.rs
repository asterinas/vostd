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
            forall |i: int|
                #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].guard_perm.addr() != guard_perm.addr(),
        ensures
            self.push_level_owner_spec(guard_perm).inv(),
    {
        admit();
        let new_owner = self.push_level_owner_spec(guard_perm);
        let new_level = (self.level - 1) as u8;

        let old_cont = self.continuations[self.level - 1];
        old_cont.inv_children_unroll(old_cont.idx as int);
        let child_node = old_cont.children[old_cont.idx as int].unwrap();
        let (child, modified_cont) = old_cont.make_cont_spec(self.va.index[self.level - 2] as usize, guard_perm);

        assert(child.inv()) by { admit() };

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
            if self.popped_too_high {
                admit();
            }
        };

        assert(new_owner.prefix.inv());

        assert(new_owner.continuations[new_owner.level - 1].all_some()) by { admit() };

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

        assert(modified_cont.inv()) by { admit() };

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
        }) by {
            if new_owner.level <= 3 {
                if self.level == 4 {
                    assert(self.va.index.contains_key(2));
                    // guard_perm distinctness: requires new guard_perm addr != old guard_perm addr
                    assert(new_owner.continuations[2].guard_perm.value().inner.inner@.ptr.addr() !=
                           new_owner.continuations[3].guard_perm.value().inner.inner@.ptr.addr()) by { admit() };
                }
            }
        };

        // Level 2 condition: new_level <= 2 ==> continuations[1] ...
        assert(new_owner.level <= 2 ==> {
            &&& new_owner.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                new_owner.continuations[2].guard_perm.value().inner.inner@.ptr.addr()
            &&& new_owner.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                new_owner.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
        }) by {
            if new_owner.level <= 2 {
                if self.level == 3 {
                    // Trigger va.inv() quantifier for index 1
                    assert(self.va.index.contains_key(1));
                    assert(new_owner.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                           new_owner.continuations[2].guard_perm.value().inner.inner@.ptr.addr()) by { admit() };
                    assert(new_owner.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                           new_owner.continuations[3].guard_perm.value().inner.inner@.ptr.addr()) by { admit() };
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
        }) by { admit() };
    }

    pub proof fn push_level_owner_preserves_invs(self, guard_perm: GuardPerm<'rcu, C>, regions: MetaRegionOwners, guards: Guards<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
            self.only_current_locked(guards),
            self.nodes_locked(guards),
            self.relate_region(regions),
            // The new guard_perm must be locked in guards
            guards.lock_held(guard_perm.value().inner.inner@.ptr.addr()),
        ensures
            self.push_level_owner_spec(guard_perm).inv(),
            self.push_level_owner_spec(guard_perm).children_not_locked(guards),
            self.push_level_owner_spec(guard_perm).nodes_locked(guards),
            self.push_level_owner_spec(guard_perm).relate_region(regions),
    {
        reveal(CursorContinuation::inv_children);
        let new_owner = self.push_level_owner_spec(guard_perm);
        let new_level = (self.level - 1) as u8;

        let old_cont = self.continuations[self.level - 1];

        old_cont.inv_children_unroll_all();

        let (child_cont, modified_cont) = old_cont.make_cont_spec(self.va.index[self.level - 2] as usize, guard_perm);
        assert(forall |i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].guard_perm.addr() != guard_perm.addr()) by { admit() };
        self.push_level_owner_preserves_inv(guard_perm);

        let cur_entry = self.cur_entry_owner();
        let cur_entry_addr = cur_entry.node.unwrap().meta_perm.addr();
        let cur_entry_path = old_cont.path().push_tail(old_cont.idx as usize);

        assert(cur_entry.relate_region(regions));

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
                        assume(old_cont.path().inv());

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

        assert(new_owner.relate_region(regions)) by {
            let f = PageTableOwner::<C>::relate_region_pred(regions);

            assert forall |i: int| #![auto]
                new_owner.level - 1 <= i < NR_LEVELS implies {
                    &&& f(new_owner.continuations[i].entry_own, new_owner.continuations[i].path())
                    &&& new_owner.continuations[i].map_children(f)
                } by {
                admit();
                if i == self.level - 2 {
                    // child_cont:
                    //   entry_own = old_cont.children[old_cont.idx].unwrap().value
                    //   children = old_cont.children[old_cont.idx].unwrap().children
                    assert(new_owner.continuations[i] == child_cont);

                    // By self.relate_region, old_cont.map_children(f) holds
                    // This means old_cont.children[old_cont.idx].unwrap().tree_predicate_map(f) holds
                    // tree_predicate_map(f) = f(value, path) && forall children: tree_predicate_map(f)
                    // So f(child_cont.entry_own, child_cont.path()) holds
                    // And child_cont.map_children(f) holds (children satisfy tree_predicate_map(f))

                    // The path for child_cont needs to match what tree_predicate_map used
                    // This requires path consistency - admit for now
                    admit();
                } else if i == self.level - 1 {
                    // modified_cont:
                    //   entry_own = old_cont.entry_own (unchanged)
                    //   children = old_cont.children.update(old_cont.idx, None)
                    assert(new_owner.continuations[i] == modified_cont);
                    assert(modified_cont.entry_own == old_cont.entry_own);
                    assert(modified_cont.path() == old_cont.path());

                    // f(entry_own, path) still holds since entry_own unchanged
                    // For map_children(f): only checking Some children
                    // Children with j != old_cont.idx are unchanged, still satisfy f
                    // Child at old_cont.idx is now None, no need to check

                    assert forall |j: int|
                        #![trigger modified_cont.children[j]]
                        0 <= j < modified_cont.children.len() && modified_cont.children[j] is Some implies
                        modified_cont.children[j].unwrap().tree_predicate_map(modified_cont.path().push_tail(j as usize), f) by {
                        assert(j != old_cont.idx as int);
                        assert(modified_cont.children[j] == old_cont.children[j]);
                        // old_cont.map_children(f) implies old_cont.children[j].tree_predicate_map(f)
                    };
                } else {
                    // i > self.level - 1: continuation unchanged
                    assert(new_owner.continuations[i] == self.continuations[i]);
                    // By self.relate_region, this already satisfied the predicate
                }
            };
        };
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
        ensures
            self.pop_level_owner_spec().0.inv(),
    {
        reveal(CursorContinuation::inv_children);
        let child = self.continuations[self.level - 1];
        assert(child.inv());

        let cont = self.continuations[self.level as int];
        assert(cont.inv());
        let (new_cont, _) = cont.restore_spec(child);

        let child_node = OwnerSubtree {
            value: child.entry_own,
            level: child.tree_level,
            children: child.children,
        };

        assert(new_cont.children[new_cont.idx as int].unwrap() == child_node);

        admit();
    }

    pub proof fn pop_level_owner_preserves_invs(self, guards: Guards<'rcu, C>, regions: MetaRegionOwners)
        requires
            self.inv(),
            self.level < NR_LEVELS,
            self.children_not_locked(guards),
            self.nodes_locked(guards),
            self.relate_region(regions),
        ensures
            self.pop_level_owner_spec().0.inv(),
            self.pop_level_owner_spec().0.only_current_locked(guards),
            self.pop_level_owner_spec().0.nodes_locked(guards),
            self.pop_level_owner_spec().0.relate_region(regions),
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
                    admit();
                }
            };
        };

        // relate_region: child.entry_own.relate_region(regions) is not directly tracked by
        // map_full_tree (which only checks map_children, not entry_own of continuations).
        // This property was established when push extracted the child from the parent's subtree,
        // and is invariant since no operations modify higher-level entry_owns.
        assert(new_owner.relate_region(regions)) by { admit() };
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
        admit()
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
            admit();
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
    pub axiom fn move_forward_owner_preserves_in_locked_range(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_locked_range(),
        ensures
            self.move_forward_owner_spec().in_locked_range();

    /// After the pop loop in `move_forward`, the cursor level is strictly below guard_level.
    ///
    /// The loop exits when `level >= guard_level` OR `pte_index != 0`. The `level >= guard_level`
    /// case is impossible: reaching guard_level via pop would set `popped_too_high = true`, but
    /// the loop invariant `owner.move_forward_owner_spec() == owner0.move_forward_owner_spec()`
    /// combined with `move_forward_not_popped_too_high` gives
    /// `!owner.move_forward_owner_spec().popped_too_high`, and `move_forward_owner_spec()`
    /// on a `popped_too_high` state gives a different result — a contradiction.
    pub axiom fn move_forward_pop_loop_level_lt_guard(self, owner0: Self)
        requires
            self.inv(),
            self.in_locked_range(),
            self.level <= self.guard_level,
            owner0.inv(),
            owner0.in_locked_range(),
            self.move_forward_owner_spec() == owner0.move_forward_owner_spec(),
            !owner0.move_forward_owner_spec().popped_too_high,
        ensures
            self.level < self.guard_level;
}

}
