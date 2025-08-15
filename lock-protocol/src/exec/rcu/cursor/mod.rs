pub mod locking;

use std::{
    marker::PhantomData,
    ops::Range,
};

use vstd::prelude::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::{common::*, types::*, cpu::*};
use super::page_table::PageTable;
use super::node::PageTableGuard;
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
    pub preempt_guard: &'rcu (),
    pub inst: Tracked<SpecInstance>,
    pub _phantom: PhantomData<&'rcu PageTable<C>>,
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    pub open spec fn wf(&self) -> bool {
        &&& self.path.len() == 4
        &&& 1 <= self.level <= self.guard_level <= 4
        &&& forall |level: PagingLevel|
            #![trigger self.path[level - 1]]
            1 <= level <= 4 ==> {
                if level > self.guard_level {
                    self.path[level - 1] is None
                } else if level == self.guard_level {
                    &&& self.path[level - 1] is Some
                    &&& self.path[level - 1]->Some_0.wf()
                    &&& self.path[level - 1]->Some_0.inst_id() == self.inst@.id()
                    &&& self.path[level - 1]->Some_0.guard->Some_0.stray_perm@.value() == false
                    &&& self.path[level - 1]->Some_0.guard->Some_0.in_protocol@ == true
                } else {
                    self.path[level - 1] is Some ==> {
                        &&& self.path[level - 1]->Some_0.wf()
                        &&& self.path[level - 1]->Some_0.inst_id() == self.inst@.id()
                    }
                }
            }
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
    }

    // Trusted
    #[verifier::external_body]
    pub fn take(&mut self, i: usize) -> (res: Option<PageTableGuard<'a, C>>)
        requires
            0 <= i < old(self).path.len(),
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
            old(self).wf() && i + 1 != self.guard_level ==> self.wf(),
    {
        self.path[i].take()
    }
}

} // verus!
