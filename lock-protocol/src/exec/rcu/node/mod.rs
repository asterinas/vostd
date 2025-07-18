pub mod child;
pub mod entry;
pub mod spinlock;

use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::marker::PhantomData;
use builtin::*;
use builtin_macros::*;
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
        let tracked perm: &PointsTo<MetaSlot> = &self.perm.borrow().inner;
        let meta_slot: &MetaSlot = ptr_ref(self.ptr, Tracked(perm));
        meta_slot.get_inner_pt().level
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

    pub fn borrow_paddr(raw: Paddr, nid: Ghost<NodeId>, inst_id: Ghost<InstanceId>) -> (res: Self)
        requires  // TODO

        ensures
            res =~= Self::borrow_paddr_spec(raw),
            res.wf(),
            raw == res.perm@.frame_paddr(),
            res.nid@ == nid@,
            res.inst@.id() == inst_id@,
    {
        Self {
            // SAFETY: The caller ensures the safety.
            inner: ManuallyDrop::new(PageTableNode::from_raw(raw, nid, inst_id)),
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
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst_id(),
            res.1@.state() is Locking,
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
            self.wf(),
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
            res.wf(),
            res.wf_with_node(*self),
            res.idx == idx,
    {
        Entry::new_at(idx, self)
    }

    // TODO
    // pub fn stray_mut(&mut self) -> &mut bool {
    //     &mut *self.meta().stray.get()
    // }
    pub fn read_pte(&self, idx: usize) -> (res: Pte)
        requires
            self.wf(),
            0 <= idx < 512,
        ensures
            res.wf(),
            res.wf_with_node_info(
                self.deref().deref().level_spec(),
                self.inst_id(),
                self.nid(),
                idx as nat,
            ),
    {
        let va = paddr_to_vaddr(self.deref().deref().start_paddr());
        let ptr: ArrayPtr<Pte, PTE_NUM> = ArrayPtr::from_addr(va);
        let guard: &SpinGuard = self.guard.as_ref().unwrap();
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
                old(self).inner.deref().level_spec(),
                old(self).inst_id(),
                old(self).nid(),
                idx as nat,
            ),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            self.nid() == old(self).nid(),
    {
        let va = paddr_to_vaddr(self.inner.deref().start_paddr());
        let ptr: ArrayPtr<Pte, PTE_NUM> = ArrayPtr::from_addr(va);
        let mut guard = self.guard.take().unwrap();
        assert forall|i: int|
            #![trigger guard.perms@.inner.opt_value()[i]]
            0 <= i < 512 && i != idx implies {
            &&& guard.perms@.inner.opt_value()[i]->Init_0.wf()
            &&& guard.perms@.inner.opt_value()[i]->Init_0.wf_with_node_info(
                self.inner.deref().meta_spec().lock.level@,
                self.inner.deref().meta_spec().lock.pt_inst@.id(),
                self.inner.deref().meta_spec().lock.nid@,
                i as nat,
            )
        } by {
            assert(guard.perms@.inner.value()[i].wf());
            assert(guard.perms@.inner.value()[i].wf_with_node_info(
                self.inner.deref().meta_spec().lock.level@,
                self.inner.deref().meta_spec().lock.pt_inst@.id(),
                self.inner.deref().meta_spec().lock.nid@,
                i as nat,
            ));
        };
        ptr.overwrite(Tracked(&mut guard.perms.borrow_mut().inner), idx, pte);
        self.guard = Some(guard);
        assert(self.wf()) by {
            admit();
        }  // TODO
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

// impl Drop for PageTableNodeRef<'_> {
//     fn drop(&mut self) {}
// }
struct_with_invariants! {
    pub struct PageTablePageMeta {
        pub lock: PageTablePageSpinLock,
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
        }
    }
}

} // verus!
