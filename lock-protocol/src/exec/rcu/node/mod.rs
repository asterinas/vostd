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
use super::pte::{Pte, page_table_entry_trait::*};
use spinlock::{PageTablePageSpinLock, SpinGuard};
use child::Child;
use entry::Entry;
use stray::{StrayFlag, StrayPerm};

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

    // Allocator is trusted so we can assume the paddr is free.
    #[verifier::external_body]
    pub proof fn assume_free_paddr_token(inst: SpecInstance) -> (res: FreePaddrToken)
        ensures
            res.instance_id() == inst.id(),
    {
        unimplemented!();
    }

    // Trusted
    #[verifier::external_body]
    pub fn normal_alloc(
        level: PagingLevel,
        nid: Ghost<NodeId>,
        inst: Tracked<SpecInstance>,
        pa_nid: Ghost<NodeId>,
        offset: Ghost<nat>,
        node_token: Tracked<&NodeToken>,
        pte_token: Tracked<PteArrayToken>,
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
            node_token@.value() is LockedOutside,
            pte_token@.instance_id() == inst@.id(),
            pte_token@.key() == pa_nid@,
            pte_token@.value().is_void(offset@),
        ensures
            res.0.wf(),
            res.0.nid@ == nid@,
            res.0.inst@ =~= inst@,
            res.0.level_spec() == level,
            res.1@.instance_id() == inst@.id(),
            res.1@.key() == pa_nid@,
            res.1@.value() =~= pte_token@.value().update(
                offset@,
                PteState::Alive(res.0.start_paddr()),
            ),
    {
        let tracked node_token = node_token.get();
        let tracked mut pte_token = pte_token.get();
        let paddr: Paddr = 0;

        assert(pa_nid@ == NodeHelper::get_parent(nid@)) by {
            NodeHelper::lemma_get_child_sound(pa_nid@, offset@);
        };
        assert(offset@ == NodeHelper::get_offset(nid@)) by {
            NodeHelper::lemma_get_child_sound(pa_nid@, offset@);
        };

        let tracked ch_node_token;
        let tracked ch_pte_token;
        let tracked stray_token;
        let tracked free_paddr_token = Self::assume_free_paddr_token(inst@);
        proof {
            let tracked res = inst.borrow().normal_allocate(
                nid@,
                paddr,
                &node_token,
                pte_token,
                free_paddr_token,
            );
            ch_node_token = res.0.get();
            pte_token = res.1.get();
            ch_pte_token = res.2.get();
            stray_token = res.3.get();
        }

        unimplemented!();
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
    ) -> (res: Self)  // requires// TODOFORMATTER_NOT_INLINE_MARKER
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

    pub fn normal_lock_new_allocated_node<'rcu>(
        self,
        guard: &'rcu (),  // TODO
        pa_pte_array_token: Tracked<&PteArrayToken>,
    ) -> (res: PageTableGuard<'rcu>) where 'a: 'rcu
        requires
            self.wf(),
            self.nid@ != NodeHelper::root_id(),
            pa_pte_array_token@.instance_id() == self.inst@.id(),
            pa_pte_array_token@.key() == NodeHelper::get_parent(self.nid@),
            pa_pte_array_token@.value().is_alive(NodeHelper::get_offset(self.nid@)),
            pa_pte_array_token@.value().get_paddr(NodeHelper::get_offset(self.nid@))
                == self.start_paddr(),
        ensures
            res.wf(),
            res.inner =~= self,
            res.guard->Some_0.stray_perm@.value() == false,
            res.guard->Some_0.in_protocol@ == false,
    {
        let guard = self.meta().lock.normal_lock_new_allocated_node(pa_pte_array_token);
        PageTableGuard { inner: self, guard: Some(guard) }
    }

    pub fn lock<'rcu>(
        self,
        guard: &'rcu (),  // TODO
        m: Tracked<LockProtocolModel>,
        pa_pte_array_token: Tracked<&PteArrayToken>,
    ) -> (res: (PageTableGuard<'rcu>, Tracked<LockProtocolModel>)) where 'a: 'rcu
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.inst@.id(),
            m@.state() is Locking,
            m@.cur_node() == self.nid@,
            NodeHelper::in_subtree_range(m@.sub_tree_rt(), self.nid@),
            pa_pte_array_token@.instance_id() == self.inst@.id(),
            pa_pte_array_token@.key() == NodeHelper::get_parent(self.nid@),
            m@.node_is_locked(pa_pte_array_token@.key()),
            pa_pte_array_token@.value().is_alive(NodeHelper::get_offset(self.nid@)),
            pa_pte_array_token@.value().get_paddr(NodeHelper::get_offset(self.nid@))
                == self.start_paddr(),
        ensures
            res.0.wf(),
            res.0.inner =~= self,
            res.0.guard->Some_0.stray_perm@.value() == false,
            res.0.guard->Some_0.in_protocol@ == true,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst_id(),
            res.1@.state() is Locking,
            res.1@.sub_tree_rt() == m@.sub_tree_rt(),
            res.1@.cur_node() == self.nid@ + 1,
    {
        let tracked mut m = m.get();
        let res = self.meta().lock.lock(Tracked(m), pa_pte_array_token);
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
        pa_pte_array_token: Tracked<&PteArrayToken>,
    ) -> (res: PageTableGuard<'rcu>) where 'a: 'rcu
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.deref().inst@.id(),
            !(m@.state() is Void),
            m@.node_is_locked(self.deref().nid@),
            pa_pte_array_token@.instance_id() == self.deref().inst@.id(),
            pa_pte_array_token@.key() == NodeHelper::get_parent(self.deref().nid@),
            pa_pte_array_token@.value().is_alive(NodeHelper::get_offset(self.deref().nid@)),
            self.deref().start_paddr() == pa_pte_array_token@.value().get_paddr(
                NodeHelper::get_offset(self.deref().nid@),
            ),
            m@.node_is_locked(pa_pte_array_token@.key()),
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
        let stray_cell: &StrayFlag = &self.deref().deref().meta().stray;
        let guard: &SpinGuard = self.guard.as_ref().unwrap();
        let tracked stray_perm = guard.stray_perm.borrow();
        stray_cell.read(Tracked(stray_perm))
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
                &&& pte.inner.paddr() == old(
                    self,
                ).guard->Some_0.pte_token@->Some_0.value().get_paddr(idx as nat)
            } else {
                // Called in Entry::replace
                old(self).wf()
            },
            old(self).guard->Some_0.stray_perm@.value() == false,
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
            self.guard->Some_0.stray_perm@.value() == old(self).guard->Some_0.stray_perm@.value(),
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
                    assert(self.guard->Some_0.pte_token@ is Some);
                    assert forall|i: int| #![auto] 0 <= i < 512 implies {
                        self.guard->Some_0.perms@.inner.value()[i].is_pt(level)
                            <==> self.guard->Some_0.pte_token@->Some_0.value().is_alive(i as nat)
                    } by {
                        if i != idx as int {
                            assert(old(self).wf_except(idx as nat));
                            assert(old(self).guard->Some_0.perms@.relate_pte_state_except(
                                old(self).inner.deref().meta_spec().level,
                                old(self).guard->Some_0.pte_token@->Some_0.value(),
                                idx as nat,
                            ));
                            assert(self.guard->Some_0.pte_token@->Some_0.value() =~= old(
                                self,
                            ).guard->Some_0.pte_token@->Some_0.value());
                            assert(self.guard->Some_0.perms@.inner.value()[i] =~= old(
                                self,
                            ).guard->Some_0.perms@.inner.value()[i]);
                        }
                    };
                    assert forall|i: int|
                        #![auto]
                        0 <= i < 512 && self.guard->Some_0.perms@.inner.value()[i].is_pt(
                            level,
                        ) implies {
                        self.guard->Some_0.perms@.inner.value()[i].inner.paddr()
                            == self.guard->Some_0.pte_token@->Some_0.value().get_paddr(i as nat)
                    } by {
                        if i != idx as int {
                            assert(old(self).wf_except(idx as nat));
                            assert(old(self).guard->Some_0.perms@.relate_pte_state_except(
                                old(self).inner.deref().meta_spec().level,
                                old(self).guard->Some_0.pte_token@->Some_0.value(),
                                idx as nat,
                            ));
                            assert(self.guard->Some_0.pte_token@->Some_0.value() =~= old(
                                self,
                            ).guard->Some_0.pte_token@->Some_0.value());
                            assert(self.guard->Some_0.perms@.inner.value()[i] =~= old(
                                self,
                            ).guard->Some_0.perms@.inner.value()[i]);
                        }
                    };
                };
            } else {
                assert(self.wf_except(idx as nat)) by {
                    assert(self.guard->Some_0.pte_token@ is Some);
                    assert forall|i: int| #![auto] 0 <= i < 512 && i != idx as int implies {
                        self.guard->Some_0.perms@.inner.value()[i].is_pt(level)
                            <==> self.guard->Some_0.pte_token@->Some_0.value().is_alive(i as nat)
                    } by {
                        assert(old(self).wf_except(idx as nat));
                        assert(old(self).guard->Some_0.perms@.relate_pte_state_except(
                            old(self).inner.deref().meta_spec().level,
                            old(self).guard->Some_0.pte_token@->Some_0.value(),
                            idx as nat,
                        ));
                        assert(self.guard->Some_0.pte_token@->Some_0.value() =~= old(
                            self,
                        ).guard->Some_0.pte_token@->Some_0.value());
                        assert(self.guard->Some_0.perms@.inner.value()[i] =~= old(
                            self,
                        ).guard->Some_0.perms@.inner.value()[i]);
                    };
                    assert forall|i: int|
                        #![auto]
                        0 <= i < 512 && i != idx
                            && self.guard->Some_0.perms@.inner.value()[i].is_pt(level) implies {
                        self.guard->Some_0.perms@.inner.value()[i].inner.paddr()
                            == self.guard->Some_0.pte_token@->Some_0.value().get_paddr(i as nat)
                    } by {
                        assert(old(self).wf_except(idx as nat));
                        assert(old(self).guard->Some_0.perms@.relate_pte_state_except(
                            old(self).inner.deref().meta_spec().level,
                            old(self).guard->Some_0.pte_token@->Some_0.value(),
                            idx as nat,
                        ));
                        assert(self.guard->Some_0.pte_token@->Some_0.value() =~= old(
                            self,
                        ).guard->Some_0.pte_token@->Some_0.value());
                        assert(self.guard->Some_0.perms@.inner.value()[i] =~= old(
                            self,
                        ).guard->Some_0.perms@.inner.value()[i]);
                    };
                };
            }
        }
    }

    pub fn trans_lock_protocol(&mut self, m: Tracked<LockProtocolModel>) -> (res: Tracked<
        LockProtocolModel,
    >)
        requires
            old(self).wf(),
            old(self).guard->Some_0.stray_perm@.value() == false,
            old(self).guard->Some_0.in_protocol@ == false,
            m@.inv(),
            m@.inst_id() == old(self).inst_id(),
            m@.state() is Locking,
            m@.cur_node() == old(self).nid(),
            NodeHelper::in_subtree_range(m@.sub_tree_rt(), old(self).nid()),
        ensures
            self.wf(),
            self.guard->Some_0.stray_perm@.value() == false,
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

    pub proof fn tracked_borrow_guard(tracked &self) -> (tracked res: &SpinGuard)
        requires
            self.guard is Some,
        ensures
            *res =~= self.guard->Some_0,
    {
        self.guard.tracked_borrow()
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
            old(self).guard->Some_0.stray_perm@.value() == false,
            old(self).guard->Some_0.in_protocol@ == true,
            m@.inv(),
            m@.inst_id() == old(self).inst_id(),
            m@.state() is Locking,
            m@.cur_node() == old(self).nid() + 1,
            m@.node_is_locked(old(self).nid()),
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
        pub stray: StrayFlag,
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
