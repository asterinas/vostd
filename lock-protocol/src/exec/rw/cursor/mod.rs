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

use crate::spec::{common::*, utils::*, rw::*};
use crate::task::guard;
use super::{common::*, types::*, cpu::*, frame::*, page_table::*};
use super::node::{
    PageTableNode, PageTableReadLock, PageTableWriteLock, child::Child, entry::Entry, rwlock::*,
};
use crate::mm::page_table::cursor::MAX_NR_LEVELS;
use va_range::*;

verus! {

pub enum GuardInPath {
    Read(PageTableReadLock),
    Write(PageTableWriteLock),
    ImplicitWrite(PageTableWriteLock),
    Unlocked,
}

impl GuardInPath {
    #[verifier::external_body]  // Verus does not support replace.
    pub fn take(&mut self) -> (res: Self)
        ensures
            res =~= *old(self),
            *self is Unlocked,
    {
        core::mem::replace(self, Self::Unlocked)
    }
}

pub struct Cursor {
    pub path: [GuardInPath; MAX_NR_LEVELS],
    pub level: PagingLevel,
    pub guard_level: PagingLevel,
    pub va: Vaddr,
    pub inst: Tracked<SpecInstance>,
    pub unlock_level: Ghost<PagingLevel>  // Used for 'unlock_range'.
    ,
}

impl Cursor {
    pub open spec fn wf(&self) -> bool {
        &&& self.path@.len() == 4
        &&& 1 <= self.level <= self.guard_level <= 4
        &&& forall|level: PagingLevel|
            #![trigger self.path[level - 1]]
            1 <= level <= 4 ==> {
                if level < self.guard_level {
                    self.path[level - 1] is Unlocked
                } else if level == self.guard_level {
                    &&& self.path[level - 1] is Write
                    &&& self.path[level - 1]->Write_0.wf()
                    &&& self.path[level - 1]->Write_0.inst_id() == self.inst@.id()
                } else {
                    &&& self.path[level - 1] is Read
                    &&& self.path[level - 1]->Read_0.wf()
                    &&& self.path[level - 1]->Read_0.inst_id() == self.inst@.id()
                }
            }
            // &&& valid_vaddr(self.va)
            // &&& vaddr_is_aligned(self.va)
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
        &&& self.unlock_level@ == self.guard_level
    }

    pub open spec fn wf_init(&self, va: Range<Vaddr>) -> bool
        recommends
            va_range_wf(va),
    {
        &&& self.level == self.guard_level
        &&& self.va == va.start
        &&& self.level == va_range_get_guard_level(va)
    }

    pub open spec fn wf_unlock(&self) -> bool {
        &&& self.unlock_level@ == 5
        &&& forall|level: int|
            #![trigger self.path@[level - 1]]
            1 <= level <= 4 ==> self.path@[level - 1] is Unlocked
    }

    pub open spec fn wf_with_lock_protocol_model(&self, m: LockProtocolModel) -> bool {
        &&& m.inst_id() == self.inst@.id()
        &&& m.path().len() == 5 - self.unlock_level@
        &&& forall|level: int|
            #![trigger self.path[level - 1]]
            self.unlock_level@ <= level <= 4 ==> {
                &&& !(self.path[level - 1] is Unlocked)
                &&& match self.path[level - 1] {
                    GuardInPath::Read(rguard) => m.path()[4 - level] == rguard.nid(),
                    GuardInPath::Write(wguard) => m.path()[4 - level] == wguard.nid(),
                    GuardInPath::ImplicitWrite(wguard) => m.path()[4 - level] == wguard.nid(),
                    GuardInPath::Unlocked => true,
                }
            }
    }

    #[verifier::external_body]  // Verus does not support index for &mut.
    pub fn take_guard(&mut self, idx: usize) -> (res: GuardInPath)
        requires
            0 <= idx < old(self).path@.len(),
        ensures
            res =~= old(self).path@[idx as int],
            self.path@ =~= old(self).path@.update(idx as int, GuardInPath::Unlocked),
            self.level == old(self).level,
            self.guard_level == old(self).guard_level,
            self.va =~= old(self).va,
            self.inst@ =~= old(self).inst@,
            self.unlock_level@ == old(self).unlock_level@,
    {
        self.path[idx].take()
    }
}

} // verus!