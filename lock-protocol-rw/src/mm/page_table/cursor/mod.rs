pub mod locking;
pub mod va_range;

use std::mem::ManuallyDrop;
use core::ops::Deref;
use std::ops::Range;

use vstd::invariant;
use vstd::prelude::*;
use vstd::atomic_with_ghost;
use vstd::bits::*;
use vstd::rwlock::{ReadHandle, WriteHandle};
use vstd::vpanic;
use vstd::pervasive::allow_panic;
use vstd::pervasive::unreached;

use vstd_extra::manually_drop::*;

use common::{
    mm::{Paddr, Vaddr, PagingLevel},
    mm::page_table::{PageTableConfig, PagingConstsTrait},
    spec::{common::*, node_helper::self},
    task::DisabledPreemptGuard,
    configs::GLOBAL_CPU_NUM,
};

use crate::mm::page_table::node::{
    PageTableNode, PageTableNodeRef, PageTableReadLock, PageTableWriteLock,
    child::{Child, ChildRef},
    entry::Entry,
    rwlock::{PageTablePageRwLock, RwWriteGuard, RwReadGuard},
};
use crate::mm::page_table::cursor::va_range::*;
use crate::spec::{
    rw::{SpecInstance},
    lock_protocol::LockProtocolModel,
};

verus! {

pub enum GuardInPath<'a, C: PageTableConfig> {
    Read(PageTableReadLock<'a, C>),
    Write(PageTableWriteLock<'a, C>),
    ImplicitWrite(PageTableWriteLock<'a, C>),
    Unlocked,
}

impl<'a, C: PageTableConfig> GuardInPath<'a, C> {
    /// Verus does not support replace.
    #[verifier::external_body]
    pub fn take(&mut self) -> (res: GuardInPath<'a, C>)
        ensures
            res =~= *old(self),
            *self is Unlocked,
    {
        core::mem::replace(self, Self::Unlocked)
    }
}

pub struct Cursor<'a, C: PageTableConfig> {
    pub path: [GuardInPath<'a, C>; MAX_NR_LEVELS],
    pub rcu_guard: &'a DisabledPreemptGuard,
    pub level: PagingLevel,
    pub guard_level: PagingLevel,
    pub va: Vaddr,
    pub barrier_va: Range<Vaddr>,
    pub inst: Tracked<SpecInstance<C>>,
    // Used for `unlock_range`
    pub unlock_level: Ghost<PagingLevel>,
}

/// The maximum value of `PagingConstsTrait::NR_LEVELS`.
pub const MAX_NR_LEVELS: usize = 5;

impl<C: PageTableConfig> Cursor<'_, C> {
    pub open spec fn wf(&self) -> bool {
        &&& self.path@.len() == MAX_NR_LEVELS
        &&& 1 <= self.level <= self.guard_level <= C::NR_LEVELS() <= MAX_NR_LEVELS
        &&& forall|level: PagingLevel|
            #![trigger self.path[level - 1]]
            1 <= level <= C::NR_LEVELS() ==> {
                if level < self.level {
                    self.path[level - 1] is Unlocked
                } else if level < self.guard_level {
                    &&& self.path[level - 1] is ImplicitWrite
                    &&& self.path[level - 1]->ImplicitWrite_0.wf()
                    &&& self.path[level - 1]->ImplicitWrite_0.inst_id() == self.inst@.id()
                    &&& self.path[level - 1]->ImplicitWrite_0.guard->Some_0.in_protocol@ == true
                } else if level == self.guard_level {
                    &&& self.path[level - 1] is Write
                    &&& self.path[level - 1]->Write_0.wf()
                    &&& self.path[level - 1]->Write_0.inst_id() == self.inst@.id()
                    &&& self.path[level - 1]->Write_0.guard->Some_0.in_protocol@ == false
                } else {
                    &&& self.path[level - 1] is Read
                    &&& self.path[level - 1]->Read_0.wf()
                    &&& self.path[level - 1]->Read_0.inst_id() == self.inst@.id()
                }
            }
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
        &&& self.unlock_level@ == self.level
    }

    // Used for `unlock_range`
    pub open spec fn wf_unlocking(&self) -> bool {
        &&& self.path@.len() == MAX_NR_LEVELS
        &&& 1 <= self.level <= self.guard_level <= C::NR_LEVELS() <= MAX_NR_LEVELS
        &&& forall|level: PagingLevel|
            #![trigger self.path[level - 1]]
            1 <= level <= C::NR_LEVELS() ==> {
                if level < self.unlock_level@ {
                    self.path[level - 1] is Unlocked
                } else if level < self.guard_level {
                    &&& self.path[level - 1] is ImplicitWrite
                    &&& self.path[level - 1]->ImplicitWrite_0.wf()
                    &&& self.path[level - 1]->ImplicitWrite_0.inst_id() == self.inst@.id()
                    &&& self.path[level - 1]->ImplicitWrite_0.guard->Some_0.in_protocol@ == true
                } else if level == self.guard_level {
                    &&& self.path[level - 1] is Write
                    &&& self.path[level - 1]->Write_0.wf()
                    &&& self.path[level - 1]->Write_0.inst_id() == self.inst@.id()
                    &&& self.path[level - 1]->Write_0.guard->Some_0.in_protocol@ == false
                } else {
                    &&& self.path[level - 1] is Read
                    &&& self.path[level - 1]->Read_0.wf()
                    &&& self.path[level - 1]->Read_0.inst_id() == self.inst@.id()
                }
            }
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
        &&& self.level <= self.unlock_level@ <= C::NR_LEVELS() + 1
    }

    pub open spec fn wf_init(&self, va: Range<Vaddr>) -> bool
        recommends
            va_range_wf::<C>(va),
    {
        &&& self.level == self.guard_level
        &&& self.va == va.start
        &&& self.barrier_va =~= (va.start..va.end)
        &&& self.level == va_range_get_guard_level::<C>(va)
    }

    pub open spec fn wf_unlock(&self) -> bool {
        &&& self.unlock_level@ == C::NR_LEVELS() + 1
        &&& forall|level: int|
            #![trigger self.path@[level - 1]]
            1 <= level <= C::NR_LEVELS() ==> self.path@[level - 1] is Unlocked
    }

    pub open spec fn wf_with_lock_protocol_model(&self, m: LockProtocolModel<C>) -> bool {
        &&& m.inst_id() == self.inst@.id()
        &&& if self.unlock_level@ >= self.guard_level {
            &&& m.path().len() == C::NR_LEVELS() + 1 - self.unlock_level@
            &&& forall|level: int|
                #![trigger self.path[level - 1]]
                self.unlock_level@ <= level <= C::NR_LEVELS() ==> {
                    &&& !(self.path[level - 1] is Unlocked)
                    &&& match self.path[level - 1] {
                        GuardInPath::Read(rguard) => m.path()[C::NR_LEVELS() - level]
                            == rguard.nid(),
                        GuardInPath::Write(wguard) => m.path()[C::NR_LEVELS() - level]
                            == wguard.nid(),
                        GuardInPath::ImplicitWrite(wguard) => true,
                        GuardInPath::Unlocked => true,
                    }
                }
        } else {
            &&& m.path().len() == C::NR_LEVELS() + 1 - self.guard_level@
            &&& forall|level: int|
                #![trigger self.path[level - 1]]
                self.guard_level@ <= level <= C::NR_LEVELS() ==> {
                    &&& !(self.path[level - 1] is Unlocked)
                    &&& match self.path[level - 1] {
                        GuardInPath::Read(rguard) => m.path()[C::NR_LEVELS() - level]
                            == rguard.nid(),
                        GuardInPath::Write(wguard) => m.path()[C::NR_LEVELS() - level]
                            == wguard.nid(),
                        GuardInPath::ImplicitWrite(wguard) => true,
                        GuardInPath::Unlocked => true,
                    }
                }
        }
    }

    /// Verus does not support index for &mut.
    #[verifier::external_body]
    pub fn take_guard(&mut self, idx: usize) -> (res: GuardInPath<'_, C>)
        requires
            0 <= idx < old(self).path@.len(),
        ensures
            res =~= old(self).path@[idx as int],
            self.path@ =~= old(self).path@.update(idx as int, GuardInPath::Unlocked),
            self.level == old(self).level,
            self.guard_level == old(self).guard_level,
            self.va =~= old(self).va,
            self.barrier_va =~= old(self).barrier_va,
            self.inst@ =~= old(self).inst@,
            self.unlock_level@ == old(self).unlock_level@,
    {
        self.path[idx].take()
    }
}

} // verus!
