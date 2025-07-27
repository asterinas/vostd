pub mod locking;

use std::ops::Range;

use vstd::prelude::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::{common::*, types::*, cpu::*};
use super::node::PageTableGuard;
use crate::mm::page_table::cursor::MAX_NR_LEVELS;

verus! {

struct_with_invariants! {
    pub struct Cursor<'rcu> {
        pub path: [Option<PageTableGuard<'rcu>>; MAX_NR_LEVELS],
        pub rcu_guard: &'rcu (),
        pub level: PagingLevel,
        pub guard_level: PagingLevel,
        pub va: Vaddr,
        pub barrier_va: Range<Vaddr>,
        pub inst: Tracked<SpecInstance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
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
    }
}

impl<'rcu> Cursor<'rcu> {
    #[verifier::external_body]  // 'take' is unsupported.
    pub fn take(&mut self, i: usize) -> (res: Option<PageTableGuard<'rcu>>)
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
