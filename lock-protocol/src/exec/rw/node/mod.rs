pub mod child;
pub mod entry;
pub mod rwlock;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::simple_pptr::{PPtr, PointsTo};

use vstd_extra::array_ptr::*;

use crate::spec::{common::*, utils::*, tree::*};
use super::{common::*, types::*, mem_content::*, cpu::*};
use super::pte::Pte;
use rwlock::{PageTablePageRwLock, RwReadGuard, RwWriteGuard};
use child::Child;
use entry::Entry;

verus! {

pub struct PageTableNode {
    pub ptr: PPtr<MetaSlot>,
    pub perm: Tracked<MetaSlotPerm>,
    pub nid: Ghost<NodeId>,
    pub inst: Tracked<SpecInstance>,
}

// Functions defined in struct 'Frame'.
impl PageTableNode {
    pub open spec fn meta_spec(&self) -> PageTablePageMeta {
        self.perm@.value().get_inner_pt_spec()
    }

    pub fn meta(&self, mem: &MemContent) -> (res: &PageTablePageMeta)
        requires
            self.wf(mem),
        ensures
            *res =~= self.meta_spec(),
    {
        let tracked perm: &PointsTo<MetaSlot> = &self.perm.borrow().inner;
        let meta_slot: &MetaSlot = self.ptr.borrow(Tracked(perm));
        assert(meta_slot.is_pt());
        &meta_slot.get_inner_pt()
    }

    pub uninterp spec fn from_raw_spec(paddr: Paddr) -> Self;

    #[verifier::external_body]
    pub fn from_raw(
        paddr: Paddr,
        mem: &MemContent,
        nid: Ghost<NodeId>,
        inst_id: Ghost<InstanceId>,
    ) -> (res: Self)
        ensures
            res =~= Self::from_raw_spec(paddr),
            res.wf(mem),
            paddr == res.perm@.frame_paddr(),
            res.nid@ == nid@,
            res.inst@.id() == inst_id@,
    {
        unimplemented!();
    }

    pub uninterp spec fn into_raw_spec(self) -> Paddr;

    #[verifier::external_body]
    pub fn into_raw(self, mem: &MemContent) -> (res: Paddr)
        requires
            self.wf(mem),
        ensures
            res == self.into_raw_spec(),
            res == self.perm@.frame_paddr(),
    {
        unimplemented!();
    }

    pub open spec fn start_paddr_spec(&self) -> Paddr {
        self.perm@.frame_paddr()
    }

    pub fn start_paddr(&self, mem: &MemContent) -> (res: Paddr)
        requires
            self.wf(mem),
        ensures
            res == self.start_paddr_spec(),
    {
        meta_to_frame(self.ptr.addr())
    }
}

// Functions defined in struct 'PageTableNode'.
impl PageTableNode {
    pub open spec fn wf(&self, mem: &MemContent) -> bool {
        &&& self.perm@.wf(&mem.meta_slot_array)
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

    pub fn level(&self, mem: &MemContent) -> (res: PagingLevel)
        requires
            self.wf(mem),
        ensures
            res == self.level_spec(),
    {
        let tracked perm: &PointsTo<MetaSlot> = &self.perm.borrow().inner;
        let meta_slot: &MetaSlot = self.ptr.borrow(Tracked(perm));
        assert(meta_slot.is_pt());
        meta_slot.get_inner_pt().level
    }

    pub fn lock_write(self, mem: &MemContent, m: Tracked<LockProtocolModel>) -> (res: (
        PageTableWriteLock,
        Tracked<LockProtocolModel>,
    ))
        requires
            self.wf(mem),
            m@.inv(),
            m@.inst_id() == self.inst@.id(),
            m@.state() is ReadLocking,
            wf_tree_path(m@.path().push(self.nid@)),
        ensures
            res.0.wf(mem),
            res.0.frame->Some_0 =~= self,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst_id(),
            res.1@.state() is WriteLocked,
            res.1@.path() =~= m@.path().push(res.0.nid()),
    {
        let tracked mut m = m.get();
        let res = self.meta(mem).lock.lock_write(Tracked(m));
        proof {
            m = res.1.get();
        }
        let write_guard = PageTableWriteLock { frame: Some(self), guard: Some(res.0) };
        (write_guard, Tracked(m))
    }

    pub fn lock_read(self, mem: &MemContent, m: Tracked<LockProtocolModel>) -> (res: (
        PageTableReadLock,
        Tracked<LockProtocolModel>,
    ))
        requires
            self.wf(mem),
            m@.inv(),
            m@.inst_id() == self.inst@.id(),
            m@.state() is ReadLocking,
            m@.path().len() < 3,
            wf_tree_path(m@.path().push(self.nid@)),
        ensures
            res.0.wf(mem),
            res.0.frame->Some_0 =~= self,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst_id(),
            res.1@.state() is ReadLocking,
            res.1@.path() =~= m@.path().push(res.0.nid()),
    {
        let tracked mut m = m.get();
        let res = self.meta(mem).lock.lock_read(Tracked(m));
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
    pub open spec fn wf_frame(&self, mem: &MemContent) -> bool {
        &&& self.frame is Some
        &&& self.frame->Some_0.wf(mem)
    }

    pub open spec fn wf_guard(&self, mem: &MemContent) -> bool {
        &&& self.guard is Some
    }

    pub open spec fn wf(&self, mem: &MemContent) -> bool {
        &&& self.wf_frame(mem)
        &&& self.wf_guard(mem)
        &&& self.guard->Some_0.wf(&self.meta_spec().lock)
    }

    pub open spec fn inst_id(&self) -> InstanceId {
        self.frame->Some_0.inst@.id()
    }

    pub open spec fn nid(&self) -> NodeId {
        self.frame->Some_0.nid@
    }

    pub open spec fn paddr_spec(&self) -> Paddr {
        self.frame->Some_0.start_paddr_spec()
    }

    pub fn paddr(&self, mem: &MemContent) -> (res: Paddr)
        requires
            self.wf_frame(mem),
        ensures
            res == self.paddr_spec(),
    {
        self.frame.as_ref().unwrap().start_paddr(mem)
    }

    pub open spec fn level_spec(&self) -> PagingLevel {
        self.frame->Some_0.level_spec()
    }

    pub fn level(&self, mem: &MemContent) -> (res: PagingLevel)
        requires
            self.wf_frame(mem),
        ensures
            res == self.level_spec(),
    {
        self.meta(mem).level
    }

    pub fn read_child_ref(&self, idx: usize, mem: &MemContent) -> (res: Child)
        requires
            self.wf(mem),
            0 <= idx < 512,
        ensures
            res.wf(mem),
            !(res is PageTable),
            res is Frame ==> res->Frame_1 == self.level_spec(),
    {
        let pte: Pte = self.read_pte(idx, mem);
        // SAFETY: The provided `level` and `is_tracked` are the same as
        // the node containing the PTE.
        // unsafe { Child::ref_from_pte(&pte, self.level(), self.is_tracked(), false) }
        Child::ref_from_pte(&pte, self.level(mem), false, mem)
    }

    pub fn unlock(&mut self, mem: &MemContent, m: Tracked<LockProtocolModel>) -> (res: (
        PageTableNode,
        Tracked<LockProtocolModel>,
    ))
        requires
            old(self).wf(mem),
            m@.inv(),
            m@.inst_id() == old(self).inst_id(),
            m@.state() is ReadLocking,
            m@.path().len() > 0 && m@.path().last() == old(self).nid(),
        ensures
            self.frame is None,
            self.guard is None,
            res.0.wf(mem),
            res.0 =~= old(self).frame->Some_0,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst@.id(),
            res.1@.state() is ReadLocking,
            res.1@.path() =~= m@.path().drop_last(),
    {
        let tracked mut m = m.get();
        let guard = self.guard.take().unwrap();
        let res = self.meta(mem).lock.unlock_read(guard, Tracked(m));
        proof {
            m = res.get();
        }
        let frame = self.frame.take().unwrap();
        (frame, Tracked(m))
    }

    #[verifier::external_body]  // TODO
    pub fn read_pte(&self, idx: usize, mem: &MemContent) -> (res: Pte)
        requires
            self.wf(mem),
            0 <= idx < 512,
        ensures
            res.wf(),
            res.wf_with_node_info(
                self.frame->Some_0.start_paddr_spec(),
                self.frame->Some_0.level_spec(),
                self.frame->Some_0.inst@.id(),
                self.frame->Some_0.nid@,
                idx as nat,
            ),
    {
        let va = paddr_to_vaddr(self.paddr(mem));
        let ptr: ArrayPtr<Pte, PTE_NUM> = ArrayPtr::from_addr(va);
        let guard: &RwReadGuard = self.guard.as_ref().unwrap();
        let res = guard.borrow_perms(&self.meta(mem).lock);
        let tracked perms = res.get();
        let pte: Pte = ptr.get(Tracked(&perms.inner), idx);
        pte
    }

    pub open spec fn meta_spec(&self) -> PageTablePageMeta {
        self.frame->Some_0.meta_spec()
    }

    pub fn meta(&self, mem: &MemContent) -> (res: &PageTablePageMeta)
        requires
            self.wf_frame(mem),
        ensures
            *res =~= self.meta_spec(),
    {
        self.frame.as_ref().unwrap().meta(mem)
    }
}

pub struct PageTableWriteLock {
    pub frame: Option<PageTableNode>,
    pub guard: Option<RwWriteGuard>,
}

impl PageTableWriteLock {
    pub open spec fn wf_frame(&self, mem: &MemContent) -> bool {
        &&& self.frame is Some
        &&& self.frame->Some_0.wf(mem)
    }

    pub open spec fn wf_guard(&self, mem: &MemContent) -> bool {
        &&& self.guard is Some
    }

    pub open spec fn wf(&self, mem: &MemContent) -> bool {
        &&& self.wf_frame(mem)
        &&& self.wf_guard(mem)
        &&& self.guard->Some_0.wf(&self.meta_spec().lock)
    }

    pub open spec fn inst_id(&self) -> InstanceId {
        self.frame->Some_0.inst@.id()
    }

    pub open spec fn nid(&self) -> NodeId {
        self.frame->Some_0.nid@
    }

    pub proof fn tracked_pt_inst(tracked &self, mem: &MemContent) -> (tracked res: SpecInstance)
        requires
            self.wf(mem),
        ensures
            res =~= self.frame->Some_0.inst@,
    {
        self.frame.tracked_borrow().inst.borrow().clone()
    }

    pub fn entry(&self, idx: usize, mem: &MemContent) -> (res: Entry)
        requires
            self.wf(mem),
            0 <= idx < 512,
        ensures
            self.wf(mem),
            res.wf(),
            res.wf_with_node(*self),
    {
        Entry::new_at(idx, self, mem)
    }

    pub open spec fn paddr_spec(&self) -> Paddr {
        self.frame->Some_0.start_paddr_spec()
    }

    pub fn paddr(&self, mem: &MemContent) -> (res: Paddr)
        requires
            self.wf_frame(mem),
        ensures
            res == self.paddr_spec(),
    {
        self.frame.as_ref().unwrap().start_paddr(mem)
    }

    pub open spec fn level_spec(&self) -> PagingLevel {
        self.frame->Some_0.level_spec()
    }

    pub fn level(&self, mem: &MemContent) -> (res: PagingLevel)
        requires
            self.wf_frame(mem),
        ensures
            res == self.level_spec(),
    {
        self.meta(mem).level
    }

    pub fn unlock(&mut self, mem: &MemContent, m: Tracked<LockProtocolModel>) -> (res: (
        PageTableNode,
        Tracked<LockProtocolModel>,
    ))
        requires
            old(self).wf(mem),
            m@.inv(),
            m@.inst_id() == old(self).inst_id(),
            m@.state() is WriteLocked,
            m@.path().len() > 0 && m@.path().last() == old(self).nid(),
        ensures
            self.frame is None,
            self.guard is None,
            res.0.wf(mem),
            res.0 =~= old(self).frame->Some_0,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst@.id(),
            res.1@.state() is ReadLocking,
            res.1@.path() =~= m@.path().drop_last(),
    {
        let tracked mut m = m.get();
        let guard = self.guard.take().unwrap();
        let res = self.meta(mem).lock.unlock_write(guard, Tracked(m));
        proof {
            m = res.get();
        }
        let frame = self.frame.take().unwrap();
        (frame, Tracked(m))
    }

    #[verifier::external_body]  // TODO
    pub fn read_pte(&self, idx: usize, mem: &MemContent) -> (res: Pte)
        requires
            self.wf(mem),
            0 <= idx < 512,
        ensures
            res.wf(),
            res.wf_with_node_info(
                self.frame->Some_0.start_paddr_spec(),
                self.frame->Some_0.level_spec(),
                self.frame->Some_0.inst@.id(),
                self.frame->Some_0.nid@,
                idx as nat,
            ),
    {
        let va = paddr_to_vaddr(self.paddr(mem));
        let ptr: ArrayPtr<Pte, PTE_NUM> = ArrayPtr::from_addr(va);
        let guard: &RwWriteGuard = self.guard.as_ref().unwrap();
        let tracked perms = guard.perms.borrow();
        let pte: Pte = ptr.get(Tracked(&perms.inner), idx);
        pte
    }

    #[verifier::external_body]  // TODO
    pub fn write_pte(&mut self, idx: usize, pte: Pte, mem: &MemContent)
        requires
            old(self).wf(mem),
            0 <= idx < 512,
            pte.wf(),
            pte.wf_with_node_info(
                old(self).frame->Some_0.start_paddr_spec(),
                old(self).frame->Some_0.level_spec(),
                old(self).frame->Some_0.inst@.id(),
                old(self).frame->Some_0.nid@,
                idx as nat,
            ),
        ensures
            self.wf(mem),
    {
        let va = paddr_to_vaddr(self.paddr(mem));
        let ptr: ArrayPtr<Pte, PTE_NUM> = ArrayPtr::from_addr(va);
        let mut guard = self.guard.take().unwrap();
        ptr.overwrite(Tracked(&mut guard.perms.borrow_mut().inner), idx, pte);
        self.guard = Some(guard);
    }

    pub open spec fn meta_spec(&self) -> PageTablePageMeta {
        self.frame->Some_0.meta_spec()
    }

    pub fn meta(&self, mem: &MemContent) -> (res: &PageTablePageMeta)
        requires
            self.wf_frame(mem),
        ensures
            *res =~= self.meta_spec(),
    {
        self.frame.as_ref().unwrap().meta(mem)
    }
}

} // verus!
