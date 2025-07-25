pub mod child;
pub mod entry;
pub mod rwlock;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::{PointsTo, ptr_ref};

use vstd_extra::array_ptr::*;

use crate::spec::{common::*, utils::*, rw::*};
use super::{common::*, types::*, mem_content::*, cpu::*};
use super::pte::Pte;
use rwlock::{PageTablePageRwLock, RwReadGuard, RwWriteGuard};
use child::Child;
use entry::Entry;

verus! {

pub struct PageTableNode {
    pub ptr: *const MetaSlot,
    pub perm: Tracked<MetaSlotPerm>,
    pub nid: Ghost<NodeId>,
    pub inst: Tracked<SpecInstance>,
}

// Functions defined in struct 'Frame'.
impl PageTableNode {
    pub open spec fn meta_spec(&self) -> PageTablePageMeta {
        self.perm@.get_pt()
    }

    #[verus_spec]
    pub fn meta(&self) -> (res: &PageTablePageMeta)
        requires
            self.wf(),
        ensures
            *res =~= self.meta_spec(),
    {
        proof_decl!{let tracked perm = self.perm.borrow();}
        let meta_slot: &MetaSlot = ptr_ref(self.ptr, (Tracked(&perm.ptr_perm)));
        proof_with!{Tracked(perm)}
        meta_slot.get_inner_pt()
    }

    pub uninterp spec fn from_raw_spec(paddr: Paddr) -> Self;

    #[verifier::external_body]
    pub fn from_raw(paddr: Paddr, nid: Ghost<NodeId>, inst_id: Ghost<InstanceId>) -> (res: Self)
        ensures
            res =~= Self::from_raw_spec(paddr),
            res.wf(),
            paddr == res.perm@.frame_paddr(),
            res.nid@ == nid@,
            res.inst@.id() == inst_id@,
    {
        unimplemented!();
    }

    pub uninterp spec fn into_raw_spec(self) -> Paddr;

    #[verifier::external_body]
    pub fn into_raw(self) -> (res: Paddr)
        requires
            self.wf(),
        ensures
            res == self.into_raw_spec(),
            res == self.perm@.frame_paddr(),
    {
        unimplemented!();
    }

    #[verifier::allow_in_spec]
    pub fn start_paddr(&self) -> (res: Paddr)
        requires
            self.wf(),
        returns
            self.perm@.frame_paddr(),
    {
        meta_to_frame(self.ptr.addr())
    }
}

// Functions defined in struct 'PageTableNode'.
impl PageTableNode {
    pub open spec fn wf(&self) -> bool {
        &&& self.perm@.wf()
        &&& self.perm@.relate(self.ptr)
        &&& self.perm@.is_pt()
        &&& NodeHelper::valid_nid(self.nid@)
        &&& self.nid@ == self.meta_spec().nid@
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
        &&& self.inst@.id() == self.meta_spec().inst@.id()
    }

    pub open spec fn level_spec(&self) -> PagingLevel {
        self.meta_spec().level
    }

    pub fn level(&self) -> (res: PagingLevel)
        requires
            self.wf(),
        ensures
            res == self.level_spec(),
    {
        self.meta().level
    }

    pub fn lock_write(self, m: Tracked<LockProtocolModel>) -> (res: (
        PageTableWriteLock,
        Tracked<LockProtocolModel>,
    ))
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.inst@.id(),
            m@.state() is ReadLocking,
            wf_tree_path(m@.path().push(self.nid@)),
        ensures
            res.0.wf(),
            res.0.frame->Some_0 =~= self,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst_id(),
            res.1@.state() is WriteLocked,
            res.1@.path() =~= m@.path().push(res.0.nid()),
    {
        let tracked mut m = m.get();
        let res = self.meta().lock.lock_write(Tracked(m));
        proof {
            m = res.1.get();
        }
        let write_guard = PageTableWriteLock { frame: Some(self), guard: Some(res.0) };
        (write_guard, Tracked(m))
    }

    pub fn lock_read(self, m: Tracked<LockProtocolModel>) -> (res: (
        PageTableReadLock,
        Tracked<LockProtocolModel>,
    ))
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.inst@.id(),
            m@.state() is ReadLocking,
            m@.path().len() < 3,
            wf_tree_path(m@.path().push(self.nid@)),
        ensures
            res.0.wf(),
            res.0.frame->Some_0 =~= self,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst_id(),
            res.1@.state() is ReadLocking,
            res.1@.path() =~= m@.path().push(res.0.nid()),
    {
        let tracked mut m = m.get();
        let res = self.meta().lock.lock_read(Tracked(m));
        proof {
            m = res.1.get();
        }
        let read_guard = PageTableReadLock { frame: Some(self), guard: Some(res.0) };
        (read_guard, Tracked(m))
    }
}

pub struct PageTableReadLock {
    pub frame: Option<PageTableNode>,
    pub guard: Option<RwReadGuard>,
}

impl PageTableReadLock {
    pub open spec fn wf_frame(&self) -> bool {
        &&& self.frame is Some
        &&& self.frame->Some_0.wf()
    }

    pub open spec fn wf_guard(&self) -> bool {
        &&& self.guard is Some
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.wf_frame()
        &&& self.wf_guard()
        &&& self.guard->Some_0.wf(&self.meta_spec().lock)
    }

    pub open spec fn inst_id(&self) -> InstanceId {
        self.frame->Some_0.inst@.id()
    }

    pub open spec fn nid(&self) -> NodeId {
        self.frame->Some_0.nid@
    }

    #[verifier::allow_in_spec]
    pub fn paddr(&self) -> (res: Paddr)
        requires
            self.wf_frame(),
        returns
            self.frame->Some_0.start_paddr(),
    {
        self.frame.as_ref().unwrap().start_paddr()
    }

    pub open spec fn level_spec(&self) -> PagingLevel {
        self.frame->Some_0.level_spec()
    }

    pub fn level(&self) -> (res: PagingLevel)
        requires
            self.wf_frame(),
        ensures
            res == self.level_spec(),
    {
        self.meta().level
    }

    pub fn read_child_ref(&self, idx: usize) -> (res: Child)
        requires
            self.wf(),
            0 <= idx < 512,
        ensures
            res.wf(),
            !(res is PageTable),
            res is Frame ==> res->Frame_1 == self.level_spec(),
    {
        let pte: Pte = self.read_pte(idx);
        // SAFETY: The provided `level` and `is_tracked` are the same as
        // the node containing the PTE.
        // unsafe { Child::ref_from_pte(&pte, self.level(), self.is_tracked(), false) }
        Child::ref_from_pte(&pte, self.level(), false)
    }

    pub fn unlock(&mut self, m: Tracked<LockProtocolModel>) -> (res: (
        PageTableNode,
        Tracked<LockProtocolModel>,
    ))
        requires
            old(self).wf(),
            m@.inv(),
            m@.inst_id() == old(self).inst_id(),
            m@.state() is ReadLocking,
            m@.path().len() > 0 && m@.path().last() == old(self).nid(),
        ensures
            self.frame is None,
            self.guard is None,
            res.0.wf(),
            res.0 =~= old(self).frame->Some_0,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst@.id(),
            res.1@.state() is ReadLocking,
            res.1@.path() =~= m@.path().drop_last(),
    {
        let tracked mut m = m.get();
        let guard = self.guard.take().unwrap();
        let res = self.meta().lock.unlock_read(guard, Tracked(m));
        proof {
            m = res.get();
        }
        let frame = self.frame.take().unwrap();
        (frame, Tracked(m))
    }

    pub fn read_pte(&self, idx: usize) -> (res: Pte)
        requires
            self.wf(),
            0 <= idx < 512,
        ensures
            res.wf(),
            res.wf_with_node_info(
                self.frame->Some_0.level_spec(),
                self.frame->Some_0.inst@.id(),
                self.frame->Some_0.nid@,
                idx as nat,
            ),
    {
        let va = paddr_to_vaddr(self.paddr());
        let ptr: ArrayPtr<Pte, PTE_NUM> = ArrayPtr::from_addr(va);
        let guard: &RwReadGuard = self.guard.as_ref().unwrap();
        let res = guard.borrow_perms(&self.meta().lock);
        let tracked perms = res.get();
        assert(perms.inner.value()[idx as int].wf());
        let pte: Pte = ptr.get(Tracked(&perms.inner), idx);
        pte
    }

    pub open spec fn meta_spec(&self) -> PageTablePageMeta {
        self.frame->Some_0.meta_spec()
    }

    pub fn meta(&self) -> (res: &PageTablePageMeta)
        requires
            self.wf_frame(),
        ensures
            *res =~= self.meta_spec(),
    {
        self.frame.as_ref().unwrap().meta()
    }
}

pub struct PageTableWriteLock {
    pub frame: Option<PageTableNode>,
    pub guard: Option<RwWriteGuard>,
}

impl PageTableWriteLock {
    pub open spec fn wf_frame(&self) -> bool {
        &&& self.frame is Some
        &&& self.frame->Some_0.wf()
    }

    pub open spec fn wf_guard(&self) -> bool {
        &&& self.guard is Some
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.wf_frame()
        &&& self.wf_guard()
        &&& self.guard->Some_0.wf(&self.meta_spec().lock)
    }

    pub open spec fn inst_id(&self) -> InstanceId {
        self.frame->Some_0.inst@.id()
    }

    pub open spec fn nid(&self) -> NodeId {
        self.frame->Some_0.nid@
    }

    pub proof fn tracked_pt_inst(tracked &self) -> (tracked res: SpecInstance)
        requires
            self.wf(),
        ensures
            res =~= self.frame->Some_0.inst@,
    {
        self.frame.tracked_borrow().inst.borrow().clone()
    }

    pub fn entry(&self, idx: usize) -> (res: Entry)
        requires
            self.wf(),
            0 <= idx < 512,
        ensures
            res.wf(),
            res.wf_with_node(*self),
            res.idx == idx,
    {
        Entry::new_at(idx, self)
    }

    #[verifier::allow_in_spec]
    pub fn paddr(&self) -> (res: Paddr)
        requires
            self.wf_frame(),
        returns
            self.frame->Some_0.start_paddr(),
    {
        self.frame.as_ref().unwrap().start_paddr()
    }

    pub open spec fn level_spec(&self) -> PagingLevel {
        self.frame->Some_0.level_spec()
    }

    pub fn level(&self) -> (res: PagingLevel)
        requires
            self.wf_frame(),
        ensures
            res == self.level_spec(),
    {
        self.meta().level
    }

    pub fn unlock(&mut self, m: Tracked<LockProtocolModel>) -> (res: (
        PageTableNode,
        Tracked<LockProtocolModel>,
    ))
        requires
            old(self).wf(),
            m@.inv(),
            m@.inst_id() == old(self).inst_id(),
            m@.state() is WriteLocked,
            m@.path().len() > 0 && m@.path().last() == old(self).nid(),
        ensures
            self.frame is None,
            self.guard is None,
            res.0.wf(),
            res.0 =~= old(self).frame->Some_0,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst@.id(),
            res.1@.state() is ReadLocking,
            res.1@.path() =~= m@.path().drop_last(),
    {
        let tracked mut m = m.get();
        let guard = self.guard.take().unwrap();
        let res = self.meta().lock.unlock_write(guard, Tracked(m));
        proof {
            m = res.get();
        }
        let frame = self.frame.take().unwrap();
        (frame, Tracked(m))
    }

    pub fn read_pte(&self, idx: usize) -> (res: Pte)
        requires
            self.wf(),
            0 <= idx < 512,
        ensures
            res.wf(),
            res.wf_with_node_info(
                self.frame->Some_0.level_spec(),
                self.frame->Some_0.inst@.id(),
                self.frame->Some_0.nid@,
                idx as nat,
            ),
    {
        let va = paddr_to_vaddr(self.paddr());
        let ptr: ArrayPtr<Pte, PTE_NUM> = ArrayPtr::from_addr(va);
        let guard: &RwWriteGuard = self.guard.as_ref().unwrap();
        let tracked perms = guard.perms.borrow();
        assert(perms.inner.value()[idx as int].wf());
        let pte: Pte = ptr.get(Tracked(&perms.inner), idx);
        pte
    }

    pub fn write_pte(&mut self, idx: usize, pte: Pte)
        requires
            old(self).wf(),
            0 <= idx < 512,
            pte.wf(),
            pte.wf_with_node_info(
                old(self).frame->Some_0.level_spec(),
                old(self).frame->Some_0.inst@.id(),
                old(self).frame->Some_0.nid@,
                idx as nat,
            ),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            self.nid() == old(self).nid(),
    {
        let va = paddr_to_vaddr(self.paddr());
        let ptr: ArrayPtr<Pte, PTE_NUM> = ArrayPtr::from_addr(va);
        let mut guard = self.guard.take().unwrap();
        assert forall|i: int|
            #![trigger guard.perms@.inner.opt_value()[i]]
            0 <= i < 512 && i != idx implies {
            &&& guard.perms@.inner.opt_value()[i]->Init_0.wf()
            &&& guard.perms@.inner.opt_value()[i]->Init_0.wf_with_node_info(
                self.meta_spec().lock.level@,
                self.meta_spec().lock.pt_inst@.id(),
                self.meta_spec().lock.nid@,
                i as nat,
            )
        } by {
            assert(guard.perms@.inner.value()[i].wf());
            assert(guard.perms@.inner.value()[i].wf_with_node_info(
                self.meta_spec().lock.level@,
                self.meta_spec().lock.pt_inst@.id(),
                self.meta_spec().lock.nid@,
                i as nat,
            ));
        };
        ptr.overwrite(Tracked(&mut guard.perms.borrow_mut().inner), idx, pte);
        self.guard = Some(guard);
    }

    pub open spec fn meta_spec(&self) -> PageTablePageMeta {
        self.frame->Some_0.meta_spec()
    }

    pub fn meta(&self) -> (res: &PageTablePageMeta)
        requires
            self.wf_frame(),
        ensures
            *res =~= self.meta_spec(),
    {
        self.frame.as_ref().unwrap().meta()
    }
}

} // verus!
