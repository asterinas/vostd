use vstd::prelude::*;

use vstd_extra::ownership::*;
use vstd_extra::prelude::TreePath;

use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::page_table::cursor::owners::*;

use core::ops::Range;

verus! {

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    /// The number of steps it will take to walk through every node of a full
    /// page table at level `level`
    pub open spec fn max_steps_subtree(level: usize) -> usize
        decreases level,
    {
        if level <= 1 {
            NR_ENTRIES()
        } else {
            // One step to push down a level, then the number for that subtree
            (NR_ENTRIES() * (Self::max_steps_subtree((level - 1) as usize) + 1)) as usize
        }
    }

    /// The number of steps it will take to walk through the remaining entries of the page table
    /// starting at the given level.
    pub open spec fn max_steps_partial(self, level: usize) -> usize
        decreases NR_LEVELS() - level,
        when level <= NR_LEVELS()
    {
        if level == NR_LEVELS() {
            0
        } else {
            // How many entries remain at this level?
            let cont = self.continuations[(level - 1) as int];
            // Each entry takes at most `max_step_subtree` steps.
            let steps = Self::max_steps_subtree(level) * (NR_ENTRIES() - cont.idx);
            // Then the number of steps for the remaining entries at higer levels
            let remaining_steps = self.max_steps_partial((level + 1) as usize);
            (steps + remaining_steps) as usize
        }
    }

    pub open spec fn max_steps(self) -> usize {
        self.max_steps_partial(self.level as usize)
    }

    pub open spec fn push_level_owner_spec(self) -> Self
    {
        let cont = self.continuations[self.level - 1];
        let (child, cont) = cont.make_cont_spec(self.va.index[self.level - 2] as usize);
        let new_continuations = self.continuations.insert(self.level - 1, cont);
        let new_continuations = new_continuations.insert(self.level - 2, child);

        let new_level = (self.level - 1) as u8;
        Self {
            continuations: new_continuations,
            level: new_level,
            ..self
        }
    }

    pub proof fn push_level_owner_decreases_steps(self)
        requires
            self.inv(),
            self.level > 0,
        ensures
            self.push_level_owner_spec().max_steps() < self.max_steps()
    { admit() }

    pub proof fn push_level_owner_preserves_va(self)
        requires
            self.inv(),
            self.level > 1,
        ensures
            self.push_level_owner_spec().va == self.va,
            self.push_level_owner_spec().continuations[self.level - 2].idx == self.va.index[self.level - 2],
    {
        assert(self.va.index.contains_key(self.level - 2));
    }

    #[verifier::returns(proof)]
    pub proof fn push_level_owner(tracked &mut self)
        requires
            old(self).inv(),
            old(self).level > 1,
        ensures
            self == old(self).push_level_owner_spec(),
    {
        assert(self.va.index.contains_key(self.level - 2));

        let ghost self0 = *self;
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);
        let ghost cont0 = cont;
        let tracked child = cont.make_cont(self.va.index[self.level - 2] as usize);

        assert((child, cont) == cont0.make_cont_spec(self.va.index[self.level - 2] as usize));

        self.continuations.tracked_insert(self.level - 1, cont);
        self.continuations.tracked_insert(self.level - 2, child);

        assert(self.continuations == self0.continuations.insert(self.level - 1, cont).insert(self.level - 2, child));

        self.level = (self.level - 1) as u8;
    }

    pub open spec fn pop_level_owner_spec(self) -> Self
    {
        let child = self.continuations[self.level - 1];
        let cont = self.continuations[self.level as int];
        let new_cont = cont.restore_spec(child);
        let new_continuations = self.continuations.insert(self.level as int, new_cont);
        let new_continuations = new_continuations.remove(self.level - 1);
        let new_level = (self.level + 1) as u8;
        Self {
            continuations: new_continuations,
            level: new_level,
            ..self
        }
    }

    #[verifier::returns(proof)]
    pub proof fn pop_level_owner(tracked &mut self)
        requires
            old(self).inv(),
            old(self).level < NR_LEVELS(),
        ensures
            self == old(self).pop_level_owner_spec(),
    {
        let ghost self0 = *self;
        let tracked mut parent = self.continuations.tracked_remove(self.level as int);
        let tracked child = self.continuations.tracked_remove(self.level - 1);

        parent.restore(child);

        self.continuations.tracked_insert(self.level as int, parent);

        assert(self.continuations == self0.continuations.insert(self.level as int, parent).remove(self.level - 1));

//        self.path.0.tracked_pop();
        self.level = (self.level + 1) as u8;
    }

    pub open spec fn move_forward_owner_spec(self) -> Self
        decreases NR_LEVELS() - self.level when self.level <= NR_LEVELS()
    {
        if self.index() + 1 < NR_ENTRIES() {
            self.inc_index()
        } else if self.level < NR_LEVELS() {
            self.pop_level_owner_spec().move_forward_owner_spec()
        } else {
            // We are at the last entry of the last level, so we stay at the same index
            self
        }
    }

    pub proof fn move_forward_owner_decreases_steps(self)
        requires
            self.inv(),
            self.level < NR_LEVELS(),
        ensures
            self.move_forward_owner_spec().max_steps() < self.max_steps()
    { admit() }

}

}
