pub mod child;
pub mod entry;
pub mod spinlock;
pub mod stray;

use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::marker::PhantomData;

use vstd::prelude::*;
use vstd::raw_ptr::{PointsTo, ptr_ref};
use vstd::cell::{PCell, PointsTo as CellPointsTo};

use vstd_extra::{manually_drop::*, array_ptr::*};

use crate::spec::{common::*, utils::*, rcu::*};
use super::{common::*, types::*, cpu::*, frame::meta::*};
use super::pte::Pte;
use spinlock::{PageTablePageSpinLock, SpinGuard};
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
        self.perm@.value().get_inner_pt_spec()
    }

    pub fn meta(&self) -> (res: &PageTablePageMeta)
        requires
            self.wf(),
        ensures
            *res =~= self.meta_spec(),
    {
        let tracked perm: &PointsTo<MetaSlot> = &self.perm.borrow().inner;
        let meta_slot: &MetaSlot = ptr_ref(self.ptr, (Tracked(perm)));
        &meta_slot.get_inner_pt()
    }

    pub uninterp spec fn from_raw_spec(paddr: Paddr) -> Self;

    // Trusted
    #[verifier::external_body]
    pub fn from_raw(
        paddr: Paddr,
        nid: Ghost<NodeId>,
        inst_id: Ghost<InstanceId>,
        level: Ghost<PagingLevel>,
    ) -> (res: Self)
        ensures
            res =~= Self::from_raw_spec(paddr),
            res.wf(),
            paddr == res.perm@.frame_paddr(),
            res.nid@ == nid@,
            res.inst@.id() == inst_id@,
            res.inst@.cpu_num() == GLOBAL_CPU_NUM,
            res.level_spec() == level@,
    {
        unimplemented!();
    }

    pub uninterp spec fn into_raw_spec(self) -> Paddr;

    // Trusted
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
        let tracked perm: &PointsTo<MetaSlot> = &self.perm.borrow().inner;
        let meta_slot: &MetaSlot = ptr_ref(self.ptr, Tracked(perm));
        meta_slot.get_inner_pt().level
    }

    // Trusted
    #[verifier::external_body]
    pub fn alloc(
        level: PagingLevel,
        nid: Ghost<NodeId>,
        inst_id: Ghost<InstanceId>,
        node_token: Tracked<NodeToken>,
        pte_token: Tracked<PteToken>,
    ) -> (res: Self)
        requires
            level as nat == NodeHelper::nid_to_level(nid@),
            node_token@.instance_id() == inst_id@,
            node_token@.key() == nid@,
            node_token@.value() is Free,
            pte_token@.instance_id() == inst_id@,
            pte_token@.key() == nid@,
            pte_token@.value() =~= PteState::empty(),
        ensures
            res.wf(),
            res.nid@ == nid@,
            res.inst@.id() == inst_id@,
            res.level_spec() == level,
    {
        unimplemented!()
    }
}

pub struct PageTableNodeRef<'a> {
    pub inner: ManuallyDrop<PageTableNode>,
    pub _marker: PhantomData<&'a ()>,
}

// Functions defined in struct 'FrameRef'.
impl PageTableNodeRef<'_> {
    pub open spec fn borrow_paddr_spec(raw: Paddr) -> Self {
        Self { inner: ManuallyDrop::new(PageTableNode::from_raw_spec(raw)), _marker: PhantomData }
    }

    pub fn borrow_paddr(
        raw: Paddr,
        nid: Ghost<NodeId>,
        inst_id: Ghost<InstanceId>,
        level: Ghost<PagingLevel>,
    ) -> (res: Self)
        requires  // TODO

        ensures
            res =~= Self::borrow_paddr_spec(raw),
            res.wf(),
            raw == res.perm@.frame_paddr(),
            res.nid@ == nid@,
            res.inst@.id() == inst_id@,
            res.inst@.cpu_num() == GLOBAL_CPU_NUM,
            res.deref().level_spec() == level@,
    {
        Self {
            // SAFETY: The caller ensures the safety.
            inner: ManuallyDrop::new(PageTableNode::from_raw(raw, nid, inst_id, level)),
            _marker: PhantomData,
        }
    }
}

pub open spec fn pt_node_ref_deref_spec<'a>(
    pt_node_ref: &'a PageTableNodeRef<'_>,
) -> &'a PageTableNode {
    &pt_node_ref.inner.deref()
}

impl Deref for PageTableNodeRef<'_> {
    type Target = PageTableNode;

    #[verifier::when_used_as_spec(pt_node_ref_deref_spec)]
    fn deref(&self) -> (ret: &Self::Target)
        ensures
            ret == self.inner.deref(),
    {
        &self.inner.deref()
    }
}

// Functions defined in struct 'PageTableNodeRef'.
impl<'a> PageTableNodeRef<'a> {
    pub open spec fn wf(&self) -> bool {
        self.deref().wf()
    }

    pub fn normal_lock<'rcu>(
        self,
        guard: &'rcu (),  // TODO
    ) -> (res: PageTableGuard<'rcu>) where 'a: 'rcu
        requires
            self.wf(),
        ensures
            res.wf(),
            res.inner =~= self,
            res.guard->Some_0.in_protocol@ == false,
    {
        let guard = self.meta().lock.normal_lock();
        PageTableGuard { inner: self, guard: Some(guard) }
    }

    pub fn lock<'rcu>(
        self,
        guard: &'rcu (),  // TODO
        m: Tracked<LockProtocolModel>,
    ) -> (res: (PageTableGuard<'rcu>, Tracked<LockProtocolModel>)) where 'a: 'rcu
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.inst@.id(),
            m@.state() is Locking,
            m@.cur_node() == self.nid@,
        ensures
            res.0.wf(),
            res.0.inner =~= self,
            res.0.guard->Some_0.in_protocol@ == true,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst_id(),
            res.1@.state() is Locking,
            res.1@.sub_tree_rt() == m@.sub_tree_rt(),
            res.1@.cur_node() == self.nid@ + 1,
    {
        let tracked mut m = m.get();
        let res = self.meta().lock.lock(Tracked(m));
        proof {
            m = res.1.get();
        }
        let guard = PageTableGuard { inner: self, guard: Some(res.0) };
        (guard, Tracked(m))
    }

    #[verifier::external_body]
    pub fn make_guard_unchecked<'rcu>(
        self,
        _guard: &'rcu (),
        m: Tracked<&LockProtocolModel>,
    ) -> (res: PageTableGuard<'rcu>) where 'a: 'rcu
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.deref().inst@.id(),
            !(m@.state() is Void),
            m@.node_is_locked(self.deref().nid@),
        ensures
            res.wf(),
            res.inner =~= self,
            res.guard->Some_0.stray_perm@.value() == false,
            res.guard->Some_0.in_protocol@ == true,
    {
        // PageTableGuard { inner: self }
        unimplemented!()
    }
}

pub struct PageTableGuard<'rcu> {
    pub inner: PageTableNodeRef<'rcu>,
    pub guard: Option<SpinGuard>,
}

impl<'rcu> PageTableGuard<'rcu> {
    pub open spec fn wf(&self) -> bool {
        &&& self.inner.wf()
        &&& self.guard is Some
        &&& self.guard->Some_0.wf(&self.deref().deref().meta_spec().lock)
    }

    pub open spec fn wf_except(&self, idx: nat) -> bool {
        &&& self.inner.wf()
        &&& self.guard is Some
        &&& self.guard->Some_0.wf_except(&self.deref().deref().meta_spec().lock, idx)
    }

    pub open spec fn inst(&self) -> SpecInstance {
        self.deref().deref().inst@
    }

    pub open spec fn inst_id(&self) -> InstanceId {
        self.inst().id()
    }

    pub open spec fn nid(&self) -> NodeId {
        self.deref().deref().nid@
    }

    #[verifier::external_body]  // TODO
    pub proof fn tracked_pt_inst(tracked &self) -> (tracked res: SpecInstance)
        requires
            self.inner.wf(),
        ensures
            res =~= self.inst(),
    {
        // self.inner.inner.inst.borrow().clone()
        unimplemented!()
    }

    pub fn entry(&self, idx: usize) -> (res: Entry)
        requires
            self.wf(),
            0 <= idx < 512,
        ensures
            res.wf(*self),
            res.idx == idx,
    {
        Entry::new_at(idx, self)
    }

    pub fn read_stray(&self) -> (res: bool)
        requires
            self.wf(),
        ensures
            res == self.guard->Some_0.stray_perm@.value(),
    {
        let stray_cell: &PCell<bool> = &self.deref().deref().meta().stray;
        let guard: &SpinGuard = self.guard.as_ref().unwrap();
        let tracked stray_perm = guard.stray_perm.borrow();
        let b = *stray_cell.borrow(Tracked(stray_perm));
        b
    }

    pub fn read_pte(&self, idx: usize) -> (res: Pte)
        requires
            self.wf(),
            0 <= idx < 512,
        ensures
            res.wf_with_node(*self.deref().deref(), idx as nat),
            self.guard->Some_0.perms@.relate_pte(res, idx as nat),
    {
        let va = paddr_to_vaddr(self.deref().deref().start_paddr());
        let ptr: ArrayPtr<Pte, PTE_NUM> = ArrayPtr::from_addr(va);
        let guard: &SpinGuard = self.guard.as_ref().unwrap();
        let tracked perms = guard.perms.borrow();
        // assert(perms.inner.value()[idx as int].wf());
        let pte: Pte = ptr.get(Tracked(&perms.inner), idx);
        assert(self.guard->Some_0.perms@.relate_pte(pte, idx as nat)) by {
            assert(pte =~= guard.perms@.inner.opt_value()[idx as int]->Init_0);
        };
        pte
    }

    pub fn write_pte(&mut self, idx: usize, pte: Pte)
        requires
            if pte.is_pt(old(self).inner.deref().level_spec()) {
                // Called in Entry::alloc_if_none
                &&& old(self).wf_except(idx as nat)
                &&& old(self).guard->Some_0.pte_token@->Some_0.value().is_alive(idx as nat)
            } else {
                // Called in Entry::replace
                old(self).wf()
            },
            0 <= idx < 512,
            pte.wf_with_node(*(old(self).inner.deref()), idx as nat),
        ensures
            if pte.is_pt(old(self).inner.deref().level_spec()) {
                self.wf()
            } else {
                self.wf_except(idx as nat)
            },
            self.inner =~= old(self).inner,
            self.guard->Some_0.perms@.relate_pte(pte, idx as nat),
            self.guard->Some_0.pte_token =~= old(self).guard->Some_0.pte_token,
            self.guard->Some_0.in_protocol == old(self).guard->Some_0.in_protocol,
    {
        let va = paddr_to_vaddr(self.inner.deref().start_paddr());
        let ptr: ArrayPtr<Pte, PTE_NUM> = ArrayPtr::from_addr(va);
        let mut guard = self.guard.take().unwrap();
        assert forall|i: int|
            #![trigger guard.perms@.inner.opt_value()[i]]
            0 <= i < 512 && i != idx implies {
            &&& guard.perms@.inner.opt_value()[i]->Init_0.wf_with_node(
                *self.inner.deref(),
                i as nat,
            )
        } by {
            assert(guard.perms@.inner.value()[i].wf_with_node(*self.inner.deref(), i as nat));
        };
        ptr.overwrite(Tracked(&mut guard.perms.borrow_mut().inner), idx, pte);
        self.guard = Some(guard);
        assert(self.wf()) by {
            admit();
        }  // TODO
    }

    pub fn trans_lock_protocol(&mut self, m: Tracked<LockProtocolModel>) -> (res: Tracked<
        LockProtocolModel,
    >)
        requires
            old(self).wf(),
            old(self).guard->Some_0.in_protocol@ == false,
            m@.inv(),
            m@.inst_id() == old(self).inst_id(),
            m@.state() is Locking,
            m@.cur_node() == old(self).nid(),
        ensures
            self.wf(),
            self.guard->Some_0.in_protocol@ == true,
            self.inner =~= old(self).inner,
            self.guard->Some_0.wf_trans_lock_protocol(&old(self).guard->Some_0),
            res@.inv(),
            res@.inst_id() == self.inst_id(),
            res@.state() is Locking,
            res@.sub_tree_rt() == m@.sub_tree_rt(),
            res@.cur_node() == self.nid() + 1,
    {
        let tracked mut m = m.get();
        let guard = self.guard.take().unwrap();
        let res = guard.trans_lock_protocol(&self.inner.deref().meta().lock, Tracked(m));
        let trans_guard = res.0;
        proof {
            m = res.1.get();
        }
        self.guard = Some(trans_guard);
        Tracked(m)
    }
}

pub open spec fn pt_guard_deref_spec<'a, 'rcu>(
    guard: &'a PageTableGuard<'rcu>,
) -> &'a PageTableNodeRef<'rcu> {
    &guard.inner
}

impl<'rcu> Deref for PageTableGuard<'rcu> {
    type Target = PageTableNodeRef<'rcu>;

    #[verifier::when_used_as_spec(pt_guard_deref_spec)]
    fn deref(&self) -> (ret: &Self::Target)
        ensures
            ret == self.inner,
    {
        &self.inner
    }
}

// impl Drop for PageTableGuard<'_>
impl PageTableGuard<'_> {
    pub fn normal_drop<'a>(&'a mut self)
        requires
            old(self).wf(),
            old(self).guard->Some_0.in_protocol@ == false,
        ensures
            self.guard is None,
    {
        let guard = self.guard.take().unwrap();
        self.inner.deref().meta().lock.normal_unlock(guard);
    }

    pub fn drop<'a>(&'a mut self, m: Tracked<LockProtocolModel>) -> (res: Tracked<
        LockProtocolModel,
    >)
        requires
            old(self).wf(),
            old(self).guard->Some_0.in_protocol@ == true,
            m@.inv(),
            m@.inst_id() == old(self).inst_id(),
            m@.state() is Locking,
            m@.cur_node() == old(self).nid() + 1,
        ensures
            self.guard is None,
            res@.inv(),
            res@.inst_id() == old(self).inst_id(),
            res@.state() is Locking,
            res@.sub_tree_rt() == m@.sub_tree_rt(),
            res@.cur_node() == old(self).nid(),
    {
        let tracked mut m = m.get();
        let guard = self.guard.take().unwrap();
        let res = self.inner.deref().meta().lock.unlock(guard, Tracked(m));
        proof {
            m = res.get();
        }
        Tracked(m)
    }
}

struct_with_invariants! {
    pub struct PageTablePageMeta {
        pub lock: PageTablePageSpinLock,
        // The stray flag indicates whether this frame is a page table node.
        pub stray: PCell<bool>, // TODO
        pub level: PagingLevel,
        pub frame_paddr: Paddr,
        // pub frame_paddr: Ghost<Paddr>, // TODO
        pub nid: Ghost<NodeId>,
        pub inst: Tracked<SpecInstance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            &&& self.lock.wf()
            &&& self.frame_paddr == self.lock.paddr_spec()
            &&& self.level == self.lock.level_spec()
            &&& valid_paddr(self.frame_paddr)
            &&& 1 <= self.level <= 4
            &&& NodeHelper::valid_nid(self.nid@)
            &&& self.nid@ == self.lock.nid@
            &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
            &&& self.inst@.id() == self.lock.pt_inst_id()
            &&& self.level as nat == NodeHelper::nid_to_level(self.nid@)
            &&& self.stray.id() == self.lock.stray_cell_id@
        }
    }
}

} // verus!
