pub mod locking;

use std::{marker::PhantomData, ops::Range};
use core::ops::Deref;

use vstd::prelude::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::{common::*, cpu::*};
use super::page_table::PageTable;
use super::node::PageTableGuard;
use super::node::spinlock::guard_forget::SubTreeForgotGuard;
use crate::mm::page_table::cursor::MAX_NR_LEVELS;
use crate::task::DisabledPreemptGuard;
use crate::mm::page_table::PageTableConfig;

verus! {

pub struct Cursor<'rcu, C: PageTableConfig> {
    pub path: [Option<PageTableGuard<'rcu, C>>; MAX_NR_LEVELS],
    pub level: PagingLevel,
    pub guard_level: PagingLevel,
    pub va: Vaddr,
    pub barrier_va: Range<Vaddr>,
    pub rcu_guard: &'rcu DisabledPreemptGuard,
    pub inst: Tracked<SpecInstance>,
    // pub _phantom: PhantomData<&'rcu PageTable<C>>,
    pub g_level: Ghost<PagingLevel>,  // Ghost level, used in 'unlock_range'
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    pub open spec fn wf(&self) -> bool {
        &&& 1 <= self.level <= self.guard_level <= 4
        &&& self.level <= self.g_level@ <= self.guard_level + 1
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
        &&& self.wf_path()
        &&& self.guards_in_path_relation()
    }

    pub open spec fn guards_in_path_relation(&self) -> bool
        recommends
            self.wf_path(),
    {
        &&& forall|level: PagingLevel|
            #![trigger self.path[level - 1]]
            self.g_level@ < level <= self.guard_level ==> {
                let nid1 = self.path[level - 1]->Some_0.nid();
                let nid2 = self.path[level - 2]->Some_0.nid();
                NodeHelper::is_child(nid1, nid2)
            }
    }

    pub open spec fn wf_path(&self) -> bool {
        &&& self.path.len() == 4
        &&& forall|level: PagingLevel|
            #![trigger self.path[level - 1]]
            1 <= level <= 4 ==> {
                if level > self.guard_level {
                    self.path[level - 1] is None
                } else if level >= self.g_level@ {
                    &&& self.path[level - 1] is Some
                    &&& self.path[level - 1]->Some_0.wf()
                    &&& self.path[level - 1]->Some_0.inst_id() == self.inst@.id()
                    &&& self.path[level - 1]->Some_0.guard->Some_0.stray_perm().value() == false
                    &&& self.path[level - 1]->Some_0.guard->Some_0.in_protocol() == true
                } else {
                    self.path[level - 1] is None
                }
            }
    }

    pub open spec fn get_guard(&self, idx: int) -> PageTableGuard<C>
        recommends
            self.path[idx] is Some,
    {
        self.path[idx]->Some_0
    }

    pub open spec fn guard_in_path_nid_diff(
        &self,
        level1: PagingLevel,
        level2: PagingLevel,
    ) -> bool {
        self.get_guard(level1 - 1).nid() != self.get_guard(level2 - 1).nid()
    }

    pub proof fn lemma_guard_in_path_relation_implies_nid_diff(&self)
        requires
            self.wf(),
        ensures
            forall|level1: PagingLevel, level2: PagingLevel|
                self.g_level@ <= level1 < level2 <= self.guard_level && self.g_level@ <= level2
                    <= self.guard_level && level1 != level2
                    ==> #[trigger] self.guard_in_path_nid_diff(level1, level2),
    {
        admit();
    }

    pub proof fn lemma_guard_in_path_relation_implies_in_subtree_range(&self)
        requires
            self.wf(),
        ensures
            forall|level: PagingLevel|
                self.g_level@ <= level <= self.guard_level
                    ==> #[trigger] NodeHelper::in_subtree_range(
                    self.get_guard(self.guard_level - 1).nid(),
                    self.get_guard(level - 1).nid(),
                ),
    {
        admit();
    }

    pub open spec fn rec_put_guard_from_path(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
        cur_level: PagingLevel,
    ) -> SubTreeForgotGuard<C>
        recommends
            self.g_level@ <= cur_level <= self.guard_level,
        decreases cur_level - self.g_level@,
    {
        if cur_level < self.g_level@ {
            forgot_guards
        } else {
            let res = if cur_level == self.g_level@ {
                forgot_guards
            } else {
                self.rec_put_guard_from_path(forgot_guards, (cur_level - 1) as PagingLevel)
            };
            let guard = self.path[cur_level - 1]->Some_0;
            res.put_spec(
                guard.nid(),
                guard.guard->Some_0.inner@,
                guard.inner.deref().meta_spec().lock,
            )
        }
    }

    pub open spec fn wf_with_forgot_guards(&self, forgot_guards: SubTreeForgotGuard<C>) -> bool {
        &&& {
            let res = self.rec_put_guard_from_path(forgot_guards, self.guard_level);
            {
                &&& res.wf()
                &&& res.is_root_and_contained(self.path[self.guard_level - 1]->Some_0.nid())
            }
        }
        &&& forall|level: PagingLevel|
            #![trigger self.path[level - 1]]
            self.g_level@ <= level <= self.guard_level ==> {
                !forgot_guards.inner.dom().contains(self.path[level - 1]->Some_0.nid())
            }
    }

    pub open spec fn guards_in_path_wf_with_forgot_guards(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
    ) -> bool {
        forall|level: PagingLevel|
            #![trigger self.rec_put_guard_from_path(forgot_guards, (level - 1) as PagingLevel)]
            self.g_level@ <= level <= self.guard_level ==> {
                let guard = self.get_guard(level - 1);
                let _forgot_guards = self.rec_put_guard_from_path(
                    forgot_guards,
                    (level - 1) as PagingLevel,
                );
                {
                    &&& _forgot_guards.wf()
                    &&& _forgot_guards.is_sub_root(guard.nid())
                    &&& _forgot_guards.children_are_contained(
                        guard.nid(),
                        guard.guard->Some_0.view_pte_token().value(),
                    )
                }
            }
    }

    pub proof fn lemma_wf_with_forgot_guards_sound(&self, forgot_guards: SubTreeForgotGuard<C>)
        requires
            self.wf(),
            forgot_guards.wf(),
            self.wf_with_forgot_guards(forgot_guards),
        ensures
            self.guards_in_path_wf_with_forgot_guards(forgot_guards),
    {
        admit();
    }

    // Trusted
    #[verifier::external_body]
    pub fn take(&mut self, i: usize) -> (res: Option<PageTableGuard<'a, C>>)
        requires
            0 <= i < old(self).path.len(),
            old(self).level <= i + 1 <= old(self).guard_level,
            i + 1 == old(self).g_level@,
        ensures
            res =~= old(self).path[i as int],
            self.path[i as int] is None,
            self.path.len() == old(self).path.len(),
            forall|_i|
                #![trigger self.path[_i]]
                0 <= _i < self.path.len() && _i != i ==> self.path[_i] =~= old(self).path[_i],
            self.rcu_guard =~= old(self).rcu_guard,
            self.level == old(self).level,
            self.guard_level == old(self).guard_level,
            self.va == old(self).va,
            self.barrier_va == old(self).barrier_va,
            self.inst =~= old(self).inst,
            self.g_level@ == old(self).g_level@ + 1,
            self.wf_path(),
    {
        self.g_level = Ghost((self.g_level@ + 1) as PagingLevel);
        self.path[i].take()
    }
}

} // verus!
