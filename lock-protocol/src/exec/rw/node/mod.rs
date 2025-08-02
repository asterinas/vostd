pub mod child;
pub mod entry;
pub mod rwlock;

use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::marker::PhantomData;

use vstd::prelude::*;
use vstd::raw_ptr::{PointsTo, ptr_ref};

use vstd_extra::{manually_drop::*, array_ptr::*};

use crate::spec::{common::*, utils::*, rw::*};
use super::{common::*, types::*, frame::*, cpu::*};
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
            res.level_spec() == level@,
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

    #[verifier::external_body]
    pub fn borrow<'a>(&'a self) -> (res: PageTableNodeRef<'a>)
        ensures
            *res.deref() =~= *self,
    {
        PageTableNodeRef::borrow_paddr(
            self.start_paddr(),
            Ghost(self.nid@),
            Ghost(self.inst@.id()),
            Ghost(self.level_spec()),
        )
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

    // Trusted
    #[verifier::external_body]
    pub fn alloc(
        level: PagingLevel,
        nid: Ghost<NodeId>,
        inst: Tracked<SpecInstance>,
        pa_nid: Ghost<NodeId>,
        offset: Ghost<nat>,
        node_token: Tracked<&NodeToken>,
        pte_array_token: Tracked<PteArrayToken>,
    ) -> (res: (Self, Tracked<PteArrayToken>))
        requires
            level as nat == NodeHelper::nid_to_level(nid@),
            NodeHelper::valid_nid(nid@),
            nid@ != NodeHelper::root_id(),
            inst@.cpu_num() == GLOBAL_CPU_NUM,
            NodeHelper::valid_nid(pa_nid@),
            NodeHelper::is_not_leaf(pa_nid@),
            nid@ == NodeHelper::get_child(pa_nid@, offset@),
            0 <= offset@ < 512,
            node_token@.instance_id() == inst@.id(),
            node_token@.key() == pa_nid@,
            node_token@.value().is_write_locked(),
            pte_array_token@.instance_id() == inst@.id(),
            pte_array_token@.key() == pa_nid@,
            pte_array_token@.value().is_void(offset@),
        ensures
            res.0.wf(),
            res.0.nid@ == nid@,
            res.0.inst@ =~= inst@,
            res.0.level_spec() == level,
            res.1@.instance_id() == inst@.id(),
            res.1@.key() == pa_nid@,
            res.1@.value() =~= pte_array_token@.value().update(offset@, PteState::Alive),
    {
        unimplemented!();
    }
}

pub struct PageTableNodeRef<'a> {
    pub inner: ManuallyDrop<PageTableNode>,
    pub _marker: PhantomData<&'a ()>,
}

// Functions defined in struct 'FrameRef'.
impl<'a> PageTableNodeRef<'a> {
    #[verifier::external_body]
    pub fn clone_ref(&self) -> (res: PageTableNodeRef<'a>)
        ensures
            *res.deref() =~= *self.deref(),
    {
        Self::borrow_paddr(
            self.deref().start_paddr(),
            Ghost(self.deref().nid@),
            Ghost(self.deref().inst@.id()),
            Ghost(self.deref().level_spec()),
        )
    }

    pub open spec fn borrow_paddr_spec(raw: Paddr) -> Self {
        Self { inner: ManuallyDrop::new(PageTableNode::from_raw_spec(raw)), _marker: PhantomData }
    }

    pub fn borrow_paddr(
        raw: Paddr,
        nid: Ghost<NodeId>,
        inst_id: Ghost<InstanceId>,
        level: Ghost<PagingLevel>,
    ) -> (res: Self)
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

    pub fn lock_write(self, guard: &'a (), m: Tracked<LockProtocolModel>) -> (res: (
        PageTableWriteLock<'a>,
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
            res.0.inner =~= self,
            res.0.guard->Some_0.in_protocol@ == false,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst_id(),
            res.1@.state() is WriteLocked,
            res.1@.path() =~= m@.path().push(res.0.nid()),
    {
        let tracked mut m = m.get();
        let res = self.deref().meta().lock.lock_write(Tracked(m));
        proof {
            m = res.1.get();
        }
        let write_guard = PageTableWriteLock { inner: self, guard: Some(res.0) };
        (write_guard, Tracked(m))
    }

    pub fn lock_read(self, guard: &'a (), m: Tracked<LockProtocolModel>) -> (res: (
        PageTableReadLock<'a>,
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
            res.0.inner =~= self,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst_id(),
            res.1@.state() is ReadLocking,
            res.1@.path() =~= m@.path().push(res.0.nid()),
    {
        let tracked mut m = m.get();
        let res = self.deref().meta().lock.lock_read(Tracked(m));
        proof {
            m = res.1.get();
        }
        let read_guard = PageTableReadLock { inner: self, guard: Some(res.0) };
        (read_guard, Tracked(m))
    }

    pub fn make_write_guard_unchecked(self, _guard: &'a (), m: Tracked<&LockProtocolModel>) -> (res:
        PageTableWriteLock<'a>) where 'a: 'a
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.inst@.id(),
            m@.state() is WriteLocked,
            m@.node_is_locked(NodeHelper::get_parent(self.nid@)),
        ensures
            res.wf(),
            res.inner =~= self,
            res.guard->Some_0.in_protocol@ == true,
    {
        let guard = self.deref().meta().lock.in_protocol_lock_write(m);
        let write_guard = PageTableWriteLock { inner: self, guard: Some(guard) };
        write_guard
    }
}

pub struct PageTableReadLock<'a> {
    pub inner: PageTableNodeRef<'a>,
    pub guard: Option<RwReadGuard>,
}

impl<'a> PageTableReadLock<'a> {
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

    pub fn tracked_pt_inst(&self) -> (res: Tracked<SpecInstance>)
        requires
            self.inner.wf(),
        ensures
            res@ =~= self.inst(),
    {
        let tracked_inst = self.deref().deref().inst;
        Tracked(tracked_inst.borrow().clone())
    }

    pub fn entry(&self, idx: usize) -> (res: Entry)
        requires
            self.wf(),
            0 <= idx < 512,
        ensures
            res.wf_read(*self),
            res.idx == idx,
    {
        Entry::new_at_read(idx, self)
    }

    /// Gets the reference to the page table node.
    pub fn as_ref(&self) -> (res: PageTableNodeRef<'a>)
        requires
            self.wf(),
        ensures
            res.deref() =~= self.inner.deref(),
    {
        self.inner.clone_ref()
    }

    pub fn read_pte(&self, idx: usize) -> (res: Pte)
        requires
            self.wf(),
            0 <= idx < 512,
        ensures
            res.wf_with_node(*self.deref().deref(), idx as nat),
            self.guard->Some_0.view_perms().relate_pte(res, idx as nat),
    {
        let va = paddr_to_vaddr(self.deref().deref().start_paddr());
        let ptr: ArrayPtr<Pte, PTE_NUM> = ArrayPtr::from_addr(va);
        let guard: &RwReadGuard = self.guard.as_ref().unwrap();
        let res = guard.borrow_perms(&self.deref().deref().meta().lock);
        let tracked perms = res.get();
        let pte: Pte = ptr.get(Tracked(&perms.inner), idx);
        assert(self.guard->Some_0.view_perms().relate_pte(pte, idx as nat)) by {
            assert(pte =~= guard.view_perms().inner.opt_value()[idx as int]->Init_0);
        };
        pte
    }
}

pub open spec fn pt_read_guard_deref_spec<'a, 'b>(
    guard: &'a PageTableReadLock<'b>,
) -> &'a PageTableNodeRef<'b> {
    &guard.inner
}

impl<'a> Deref for PageTableReadLock<'a> {
    type Target = PageTableNodeRef<'a>;

    #[verifier::when_used_as_spec(pt_read_guard_deref_spec)]
    fn deref(&self) -> (ret: &Self::Target)
        ensures
            ret == self.inner,
    {
        &self.inner
    }
}

impl PageTableReadLock<'_> {
    pub fn drop<'a>(&'a mut self, m: Tracked<LockProtocolModel>) -> (res: Tracked<
        LockProtocolModel,
    >)
        requires
            old(self).wf(),
            m@.inv(),
            m@.inst_id() == old(self).inst_id(),
            m@.state() is ReadLocking,
            m@.path().len() > 0 && m@.path().last() == old(self).nid(),
        ensures
            self.guard is None,
            res@.inv(),
            res@.inst_id() == old(self).inst_id(),
            res@.state() is ReadLocking,
            res@.path() =~= m@.path().drop_last(),
    {
        let tracked mut m = m.get();
        let guard = self.guard.take().unwrap();
        let res = self.inner.deref().meta().lock.unlock_read(guard, Tracked(m));
        proof {
            m = res.get();
        }
        Tracked(m)
    }
}

pub struct PageTableWriteLock<'a> {
    pub inner: PageTableNodeRef<'a>,
    pub guard: Option<RwWriteGuard>,
}

impl<'a> PageTableWriteLock<'a> {
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

    pub fn tracked_pt_inst(&self) -> (res: Tracked<SpecInstance>)
        requires
            self.inner.wf(),
        ensures
            res@ =~= self.inst(),
    {
        let tracked_inst = self.deref().deref().inst;
        Tracked(tracked_inst.borrow().clone())
    }

    pub fn entry(&self, idx: usize) -> (res: Entry)
        requires
            self.wf(),
            0 <= idx < 512,
        ensures
            res.wf_write(*self),
            res.idx == idx,
    {
        Entry::new_at_write(idx, self)
    }

    /// Gets the reference to the page table node.
    pub fn as_ref(&self) -> (res: PageTableNodeRef<'a>)
        requires
            self.wf(),
        ensures
            res.deref() =~= self.inner.deref(),
    {
        self.inner.clone_ref()
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
        let guard: &RwWriteGuard = self.guard.as_ref().unwrap();
        let tracked perms = guard.perms.borrow();
        let pte: Pte = ptr.get(Tracked(&perms.inner), idx);
        assert(self.guard->Some_0.view_perms().relate_pte(pte, idx as nat)) by {
            assert(pte =~= guard.view_perms().inner.opt_value()[idx as int]->Init_0);
        };
        pte
    }

    pub fn write_pte(&mut self, idx: usize, pte: Pte)
        requires
            if pte.is_pt(old(self).inner.deref().level_spec()) {
                // Called in Entry::alloc_if_none
                &&& old(self).wf_except(idx as nat)
                &&& old(self).guard->Some_0.pte_array_token@.value().is_alive(idx as nat)
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
            self.guard->Some_0.handle =~= old(self).guard->Some_0.handle,
            self.guard->Some_0.node_token =~= old(self).guard->Some_0.node_token,
            self.guard->Some_0.pte_array_token =~= old(self).guard->Some_0.pte_array_token,
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
        proof {
            let ghost level = self.inner.deref().level_spec();
            if pte.is_pt(level) {
                assert(self.wf()) by {
                    assert forall|i: int| #![auto] 0 <= i < 512 implies {
                        self.guard->Some_0.perms@.inner.value()[i].is_pt(level)
                            <==> self.guard->Some_0.pte_array_token@.value().is_alive(i as nat)
                    } by {
                        if i != idx as int {
                            assert(old(self).wf_except(idx as nat));
                            assert(old(self).guard->Some_0.perms@.relate_pte_state_except(
                                old(self).inner.deref().meta_spec().level,
                                old(self).guard->Some_0.pte_array_token@.value(),
                                idx as nat,
                            ));
                            assert(self.guard->Some_0.pte_array_token@.value() =~= old(
                                self,
                            ).guard->Some_0.pte_array_token@.value());
                            assert(self.guard->Some_0.perms@.inner.value()[i] =~= old(
                                self,
                            ).guard->Some_0.perms@.inner.value()[i]);
                        }
                    };
                };
            } else {
                assert(self.wf_except(idx as nat)) by {
                    assert forall|i: int| #![auto] 0 <= i < 512 && i != idx as int implies {
                        self.guard->Some_0.perms@.inner.value()[i].is_pt(level)
                            <==> self.guard->Some_0.pte_array_token@.value().is_alive(i as nat)
                    } by {
                        assert(old(self).wf_except(idx as nat));
                        assert(old(self).guard->Some_0.perms@.relate_pte_state_except(
                            old(self).inner.deref().meta_spec().level,
                            old(self).guard->Some_0.pte_array_token@.value(),
                            idx as nat,
                        ));
                        assert(self.guard->Some_0.pte_array_token@.value() =~= old(
                            self,
                        ).guard->Some_0.pte_array_token@.value());
                        assert(self.guard->Some_0.perms@.inner.value()[i] =~= old(
                            self,
                        ).guard->Some_0.perms@.inner.value()[i]);
                    };
                };
            }
        }
    }
}

pub open spec fn pt_write_guard_deref_spec<'a, 'b>(
    guard: &'a PageTableWriteLock<'b>,
) -> &'a PageTableNodeRef<'b> {
    &guard.inner
}

impl<'a> Deref for PageTableWriteLock<'a> {
    type Target = PageTableNodeRef<'a>;

    #[verifier::when_used_as_spec(pt_write_guard_deref_spec)]
    fn deref(&self) -> (ret: &Self::Target)
        ensures
            ret == self.inner,
    {
        &self.inner
    }
}

impl PageTableWriteLock<'_> {
    pub fn drop<'a>(&'a mut self, m: Tracked<LockProtocolModel>) -> (res: Tracked<
        LockProtocolModel,
    >)
        requires
            old(self).wf(),
            old(self).guard->Some_0.in_protocol@ == false,
            m@.inv(),
            m@.inst_id() == old(self).inst_id(),
            m@.state() is WriteLocked,
            m@.path().len() > 0 && m@.path().last() == old(self).nid(),
        ensures
            self.guard is None,
            res@.inv(),
            res@.inst_id() == old(self).inst_id(),
            res@.state() is ReadLocking,
            res@.path() =~= m@.path().drop_last(),
    {
        let tracked mut m = m.get();
        let guard = self.guard.take().unwrap();
        let res = self.inner.deref().meta().lock.unlock_write(guard, Tracked(m));
        proof {
            m = res.get();
        }
        Tracked(m)
    }
}

} // verus!
