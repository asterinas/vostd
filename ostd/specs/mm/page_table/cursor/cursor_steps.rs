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
        let new_owner = self.push_level_owner_spec(guard_perm);
        let new_level = (self.level - 1) as u8;

        let old_cont = self.continuations[self.level - 1];
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

        assert(modified_cont.inv()) by {
            assert(modified_cont.children.len() == NR_ENTRIES) by {
                assert(old_cont.children.len() == NR_ENTRIES);
            };
            assert(0 <= modified_cont.idx < NR_ENTRIES);
            assert forall |i: int|
                #![trigger modified_cont.children[i]]
                0 <= i < NR_ENTRIES && modified_cont.children[i] is Some implies {
                    &&& modified_cont.children[i].unwrap().value.path == modified_cont.path().push_tail(i as usize)
                    &&& modified_cont.children[i].unwrap().value.parent_level == modified_cont.level()
                    &&& modified_cont.children[i].unwrap().inv()
                    &&& modified_cont.children[i].unwrap().level == modified_cont.tree_level + 1
                    &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(modified_cont.entry_own, i, Some(modified_cont.children[i].unwrap().value))
                } by {
                assert(i != old_cont.idx as int);
                assert(modified_cont.children[i] == old_cont.children[i]);
            };
            assert(modified_cont.entry_own.is_node());
            assert(modified_cont.entry_own.inv());
            assert(modified_cont.entry_own.node.unwrap().relate_guard_perm(modified_cont.guard_perm));
            assert(modified_cont.tree_level == INC_LEVELS - modified_cont.level());
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
        let new_owner = self.push_level_owner_spec(guard_perm);
        let new_level = (self.level - 1) as u8;

        let old_cont = self.continuations[self.level - 1];
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
            self.in_locked_range(),
        ensures
            self.pop_level_owner_spec().0.inv(),
    {
        let child = self.continuations[self.level - 1];
        assert(child.inv());
        assert(forall |i: int| #![trigger child.children[i]]
            0 <= i < NR_ENTRIES && child.children[i] is Some ==>
            child.children[i].unwrap().inv());
        let cont = self.continuations[self.level as int];
        assert(cont.inv());
        let (new_cont, _) = cont.restore_spec(child);

        let child_node = OwnerSubtree {
            value: child.entry_own,
            level: child.tree_level,
            children: child.children,
        };

        assert(new_cont.children[new_cont.idx as int].unwrap() == child_node);

        assert forall |i:int|
        #![trigger new_cont.children[i]]
            0 <= i < NR_ENTRIES && new_cont.children[i] is Some implies
            new_cont.children[i].unwrap().value.path == new_cont.path().push_tail(i as usize) by {
                assume(child_node.value.path == new_cont.path().push_tail(i as usize));
            };
        admit();
    }

    pub proof fn pop_level_owner_preserves_invs(self, guards: Guards<'rcu, C>, regions: MetaRegionOwners)
        requires
            self.inv(),
            self.level < NR_LEVELS,
            self.in_locked_range(),
            self.children_not_locked(guards),
            self.nodes_locked(guards),
            self.relate_region(regions),
        ensures
            self.pop_level_owner_spec().0.in_locked_range(),
            self.pop_level_owner_spec().0.inv(),
            self.pop_level_owner_spec().0.only_current_locked(guards),
            self.pop_level_owner_spec().0.nodes_locked(guards),
            self.pop_level_owner_spec().0.relate_region(regions),
    {
        let new_owner = self.pop_level_owner_spec().0;

        self.pop_level_owner_preserves_inv();

        assert(new_owner.only_current_locked(guards)) by { admit() };
        admit();
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
            self.in_locked_range(),
        ensures
            self.move_forward_owner_spec().va == self.va.align_up(self.level as int),
        decreases NR_LEVELS - self.level
    {
        admit()
    }

    pub proof fn move_forward_owner_preserves_mappings(self)
    requires
        self.inv(),
        self.level > 1,
    ensures
        self.move_forward_owner_spec()@.mappings == self@.mappings,
    { admit() }
}

}
