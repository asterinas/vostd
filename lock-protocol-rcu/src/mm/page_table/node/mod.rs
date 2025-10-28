pub mod child;
pub mod entry;
pub mod stray;

use std::cell::Cell;
use std::cell::SyncUnsafeCell;
use std::marker::PhantomData;
use std::ops::Range;
use core::mem::ManuallyDrop;
use std::ops::Deref;

use vstd::cell::PCell;
use vstd::prelude::*;
use vstd::raw_ptr;
use vstd::simple_pptr::MemContents;
use vstd::simple_pptr::PPtr;
use vstd::simple_pptr;

use vstd_extra::{manually_drop::*, array_ptr::*};

// use entry_local::EntryLocal;
use entry::Entry;
use stray::{StrayFlag, StrayPerm};
use crate::{
    mm::{
        NR_ENTRIES,
        frame::{self, meta::AnyFrameMeta},
        nr_subpage_per_huge,
        page_prop::PageProperty,
        page_size_spec,
        page_table::PageTableEntryTrait,
        Paddr, PagingConsts, PagingConstsTrait, PagingLevel, Vaddr, PAGE_SIZE,
    },
    sync::spinlock::{PageTablePageSpinLock, SpinGuard, SpinGuardGhostInner},
    task::DisabledPreemptGuard,
    x86_64::kspace::paddr_to_vaddr,
};
use crate::mm::frame::meta::{MetaSlot, meta_to_frame, MetaSlotPerm};
use crate::mm::page_table::{pte::Pte, GLOBAL_CPU_NUM};

// use crate::exec::{
//     self, MAX_FRAME_NUM, get_pte_from_addr_spec, SIZEOF_PAGETABLEENTRY, frame_addr_to_index,
//     frame_addr_to_index_spec, MockPageTableEntry, MockPageTablePage,
// };
use crate::configs::PTE_NUM;
// use crate::spec::sub_pt::{pa_is_valid_pt_address, SubPageTable, level_is_in_range, index_pte_paddr};
use crate::spec::{
    lock_protocol::LockProtocolModel,
    common::NodeId,
    node_helper,
    rcu::{SpecInstance, NodeToken, PteArrayToken, PteArrayState, PteState, FreePaddrToken},
};

// use super::cursor::spec_helpers;
use super::PageTableConfig;

verus! {

pub struct PageTableNode<C: PageTableConfig> {
    pub ptr: *const MetaSlot<C>,
    pub perm: Tracked<MetaSlotPerm<C>>,
    pub nid: Ghost<NodeId>,
    pub inst: Tracked<SpecInstance<C>>,
}

// Functions defined in struct 'Frame'.
impl<C: PageTableConfig> PageTableNode<C> {
    pub open spec fn meta_spec(&self) -> PageTablePageMeta<C> {
        self.perm@.value().get_inner_pt_spec()
    }

    pub fn meta(&self) -> (res: &PageTablePageMeta<C>)
        requires
            self.wf(),
        ensures
            *res =~= self.meta_spec(),
    {
        let tracked perm: &raw_ptr::PointsTo<MetaSlot<C>> = &self.perm.borrow().inner;
        let meta_slot: &MetaSlot<C> = raw_ptr::ptr_ref(self.ptr, (Tracked(perm)));
        &meta_slot.get_inner_pt()
    }

    pub uninterp spec fn from_raw_spec(paddr: Paddr) -> PageTableNode<C>;

    // Trusted
    #[verifier::external_body]
    pub fn from_raw(
        paddr: Paddr,
        nid: Ghost<NodeId>,
        inst_id: Ghost<InstanceId>,
        level: Ghost<PagingLevel>,
    ) -> (res: PageTableNode<C>)
        ensures
            res =~= PageTableNode::<C>::from_raw_spec(paddr),
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

    #[verifier::external_body]
    pub proof fn axiom_from_raw_sound(&self)
        requires
            self.wf(),
        ensures
            Self::from_raw_spec(self.start_paddr()) =~= *self,
    {
    }

    #[verifier::external_body]
    pub fn borrow(&self) -> (res: PageTableNodeRef<'_, C>)
        requires
            self.wf(),
        ensures
            *res.inner.deref() =~= *self,
            res.wf(),
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
impl<C: PageTableConfig> PageTableNode<C> {
    pub open spec fn wf(&self) -> bool {
        &&& self.perm@.wf()
        &&& self.perm@.relate(self.ptr)
        &&& self.perm@.is_pt()
        &&& node_helper::valid_nid::<C>(self.nid@)
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
        let tracked perm: &raw_ptr::PointsTo<MetaSlot<C>> = &self.perm.borrow().inner;
        let meta_slot: &MetaSlot<C> = raw_ptr::ptr_ref(self.ptr, Tracked(perm));
        meta_slot.get_inner_pt().level
    }

    // Allocator is trusted so we can assume the paddr is free.
    #[verifier::external_body]
    pub proof fn assume_free_paddr_token(inst: SpecInstance<C>) -> (res: FreePaddrToken<C>)
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
        inst: Tracked<SpecInstance<C>>,
        pa_nid: Ghost<NodeId>,
        offset: Ghost<nat>,
        node_token: Tracked<&NodeToken<C>>,
        pte_token: Tracked<PteArrayToken<C>>,
    ) -> (res: (PageTableNode<C>, Tracked<PteArrayToken<C>>))
        requires
            level as nat == node_helper::nid_to_level::<C>(nid@),
            node_helper::valid_nid::<C>(nid@),
            nid@ != node_helper::root_id::<C>(),
            inst@.cpu_num() == GLOBAL_CPU_NUM,
            node_helper::valid_nid::<C>(pa_nid@),
            node_helper::is_not_leaf::<C>(pa_nid@),
            nid@ == node_helper::get_child::<C>(pa_nid@, offset@),
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

        assert(pa_nid@ == node_helper::get_parent::<C>(nid@)) by {
            node_helper::lemma_get_child_sound::<C>(pa_nid@, offset@);
        };
        assert(offset@ == node_helper::get_offset::<C>(nid@)) by {
            node_helper::lemma_get_child_sound::<C>(pa_nid@, offset@);
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

pub struct PageTableNodeRef<'a, C: PageTableConfig> {
    pub inner: ManuallyDrop<PageTableNode<C>>,
    pub _marker: PhantomData<&'a ()>,
}

pub open spec fn pt_node_ref_deref_spec<'a, C: PageTableConfig>(
    pt_node_ref: &'a PageTableNodeRef<'_, C>,
) -> &'a PageTableNode<C> {
    &pt_node_ref.inner.deref()
}

impl<C: PageTableConfig> Deref for PageTableNodeRef<'_, C> {
    type Target = PageTableNode<C>;

    #[verifier::when_used_as_spec(pt_node_ref_deref_spec)]
    fn deref(&self) -> (ret: &Self::Target)
        ensures
            ret == self.inner.deref(),
    {
        &self.inner.deref()
    }
}

// Functions defined in struct 'FrameRef'.
impl<C: PageTableConfig> PageTableNodeRef<'_, C> {
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

// Functions defined in struct 'PageTableNodeRef'.
impl<'a, C: PageTableConfig> PageTableNodeRef<'a, C> {
    pub open spec fn wf(&self) -> bool {
        self.deref().wf()
    }

    pub fn normal_lock<'rcu>(self, guard: &'rcu DisabledPreemptGuard) -> (res: PageTableGuard<
        'rcu,
        C,
    >) where 'a: 'rcu
        requires
            self.wf(),
        ensures
            res.wf(),
            res.inner =~= self,
            res.guard->Some_0.in_protocol() == false,
    {
        let guard = self.deref().meta().lock.normal_lock();
        PageTableGuard { inner: self, guard: Some(guard) }
    }

    pub fn normal_lock_new_allocated_node<'rcu>(
        self,
        guard: &'rcu DisabledPreemptGuard,
        pa_pte_array_token: Tracked<&PteArrayToken<C>>,
    ) -> (res: PageTableGuard<'rcu, C>) where 'a: 'rcu
        requires
            self.wf(),
            self.nid@ != node_helper::root_id::<C>(),
            pa_pte_array_token@.instance_id() == self.inst@.id(),
            pa_pte_array_token@.key() == node_helper::get_parent::<C>(self.nid@),
            pa_pte_array_token@.value().is_alive(node_helper::get_offset::<C>(self.nid@)),
            pa_pte_array_token@.value().get_paddr(node_helper::get_offset::<C>(self.nid@))
                == self.deref().start_paddr(),
        ensures
            res.wf(),
            res.inner =~= self,
            // res.guard->Some_0.view_pte_token().value() =~= PteArrayState::empty(),
            res.guard->Some_0.stray_perm().value() == false,
            res.guard->Some_0.in_protocol() == false,
    {
        let guard = self.deref().meta().lock.normal_lock_new_allocated_node(pa_pte_array_token);
        PageTableGuard { inner: self, guard: Some(guard) }
    }

    pub fn lock<'rcu>(
        self,
        guard: &'rcu DisabledPreemptGuard,
        m: Tracked<LockProtocolModel<C>>,
        pa_pte_array_token: Tracked<&PteArrayToken<C>>,
    ) -> (res: (PageTableGuard<'rcu, C>, Tracked<LockProtocolModel<C>>)) where 'a: 'rcu
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.inst@.id(),
            m@.state() is Locking,
            m@.cur_node() == self.nid@,
            node_helper::in_subtree_range::<C>(m@.sub_tree_rt(), self.nid@),
            pa_pte_array_token@.instance_id() == self.inst@.id(),
            pa_pte_array_token@.key() == node_helper::get_parent::<C>(self.nid@),
            m@.node_is_locked(pa_pte_array_token@.key()),
            pa_pte_array_token@.value().is_alive(node_helper::get_offset::<C>(self.nid@)),
            pa_pte_array_token@.value().get_paddr(node_helper::get_offset::<C>(self.nid@))
                == self.deref().start_paddr(),
        ensures
            res.0.wf(),
            res.0.inner =~= self,
            res.0.guard->Some_0.stray_perm().value() == false,
            res.0.guard->Some_0.in_protocol() == true,
            res.1@.inv(),
            res.1@.inst_id() == res.0.inst_id(),
            res.1@.state() is Locking,
            res.1@.sub_tree_rt() == m@.sub_tree_rt(),
            res.1@.cur_node() == self.nid@ + 1,
    {
        let tracked mut m = m.get();
        let res = self.deref().meta().lock.lock(Tracked(m), pa_pte_array_token);
        proof {
            m = res.1.get();
        }
        let guard = PageTableGuard { inner: self, guard: Some(res.0) };
        (guard, Tracked(m))
    }

    pub fn make_guard_unchecked<'rcu>(
        self,
        _guard: &'rcu DisabledPreemptGuard,
        forgot_guard: Tracked<SpinGuardGhostInner<C>>,
        spin_lock: Ghost<PageTablePageSpinLock<C>>,
    ) -> (res: PageTableGuard<'rcu, C>) where 'a: 'rcu
        requires
            self.wf(),
            forgot_guard@.wf(&spin_lock@),
            forgot_guard@.stray_perm.value() == false,
            forgot_guard@.in_protocol@ == true,
            self.deref().meta_spec().lock =~= spin_lock@,
        ensures
            res.wf(),
            res.inner =~= self,
            res.guard->Some_0.stray_perm().value() == false,
            res.guard->Some_0.in_protocol() == true,
            res.guard->Some_0.inner@ =~= forgot_guard@,
            res.deref().deref().meta_spec().lock =~= spin_lock@,
    {
        let spin_guard: SpinGuard<C> = SpinGuard { inner: forgot_guard };
        let res = PageTableGuard { inner: self, guard: Some(spin_guard) };
        res
    }
}

pub struct PageTableGuard<'a, C: PageTableConfig> {
    pub inner: PageTableNodeRef<'a, C>,
    pub guard: Option<SpinGuard<C>>,
}

impl<'rcu, C: PageTableConfig> PageTableGuard<'rcu, C> {
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

    pub open spec fn inst(&self) -> SpecInstance<C> {
        self.deref().deref().inst@
    }

    pub open spec fn inst_id(&self) -> InstanceId {
        self.inst().id()
    }

    pub open spec fn nid(&self) -> NodeId {
        self.deref().deref().nid@
    }

    pub fn tracked_pt_inst(&self) -> (res: Tracked<SpecInstance<C>>)
        requires
            self.inner.wf(),
        ensures
            res@ =~= self.inst(),
    {
        let tracked_inst = self.deref().deref().inst;
        Tracked(tracked_inst.borrow().clone())
    }

    pub fn entry(&self, idx: usize) -> (res: Entry<C>)
        requires
            self.wf(),
            0 <= idx < nr_subpage_per_huge::<C>(),
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
            res == self.guard->Some_0.stray_perm().value(),
    {
        let stray_cell: &StrayFlag = &self.deref().deref().meta().stray;
        let guard: &SpinGuard<C> = self.guard.as_ref().unwrap();
        let tracked stray_perm = &guard.inner.borrow().stray_perm;
        stray_cell.read(Tracked(stray_perm))
    }

    pub fn read_pte(&self, idx: usize) -> (res: Pte<C>)
        requires
            self.wf(),
            0 <= idx < nr_subpage_per_huge::<C>(),
        ensures
            res.wf_with_node(*self.deref().deref(), idx as nat),
            self.guard->Some_0.perms().relate_pte(res, idx as nat),
    {
        let va = paddr_to_vaddr(self.deref().deref().start_paddr());
        let ptr: ArrayPtr<Pte<C>, PTE_NUM> = ArrayPtr::from_addr(va);
        let guard: &SpinGuard<C> = self.guard.as_ref().unwrap();
        let tracked perms = &guard.inner.borrow().perms;
        assert((idx as nat) < 512) by {
            C::lemma_nr_subpage_per_huge_is_512();
        };
        let pte: Pte<C> = ptr.get(Tracked(&perms.inner), idx);
        assert(self.guard->Some_0.perms().relate_pte(pte, idx as nat)) by {
            assert(pte =~= guard.perms().inner.opt_value()[idx as int]->Init_0);
        };
        pte
    }

    pub fn write_pte(&mut self, idx: usize, pte: Pte<C>)
        requires
            if pte.is_pt(old(self).inner.deref().level_spec()) {
                // Called in Entry::alloc_if_none
                &&& old(self).wf_except(idx as nat)
                &&& old(self).guard->Some_0.pte_token()->Some_0.value().is_alive(idx as nat)
                &&& pte.inner.paddr() == old(
                    self,
                ).guard->Some_0.pte_token()->Some_0.value().get_paddr(idx as nat)
            } else {
                // Called in Entry::replace
                old(self).wf()
            },
            old(self).guard->Some_0.stray_perm().value() == false,
            0 <= idx < 512,
            pte.wf_with_node(*(old(self).inner.deref()), idx as nat),
        ensures
            if pte.is_pt(old(self).inner.deref().level_spec()) {
                self.wf()
            } else {
                self.wf_except(idx as nat)
            },
            self.inner =~= old(self).inner,
            self.guard->Some_0.perms().relate_pte(pte, idx as nat),
            self.guard->Some_0.pte_token() =~= old(self).guard->Some_0.pte_token(),
            self.guard->Some_0.stray_perm().value() == old(self).guard->Some_0.stray_perm().value(),
            self.guard->Some_0.in_protocol() == old(self).guard->Some_0.in_protocol(),
    {
        let va = paddr_to_vaddr(self.inner.deref().start_paddr());
        let ptr: ArrayPtr<Pte<C>, PTE_NUM> = ArrayPtr::from_addr(va);
        let mut guard = self.guard.take().unwrap();
        assert forall|i: int|
            #![trigger guard.perms().inner.opt_value()[i]]
            0 <= i < 512 && i != idx implies {
            &&& guard.perms().inner.opt_value()[i]->Init_0.wf_with_node(
                *self.inner.deref(),
                i as nat,
            )
        } by {
            assert(guard.perms().inner.value()[i].wf_with_node(*self.inner.deref(), i as nat));
        };
        ptr.overwrite(Tracked(&mut guard.inner.borrow_mut().perms.inner), idx, pte);
        self.guard = Some(guard);
        proof {
            let ghost level = self.inner.deref().level_spec();
            if pte.is_pt(level) {
                assert(self.wf()) by {
                    assert(self.guard->Some_0.pte_token() is Some);
                    assert forall|i: int| #![auto] 0 <= i < 512 implies {
                        self.guard->Some_0.perms().inner.value()[i].is_pt(level)
                            <==> self.guard->Some_0.pte_token()->Some_0.value().is_alive(i as nat)
                    } by {
                        if i != idx as int {
                            assert(old(self).wf_except(idx as nat));
                            assert(old(self).guard->Some_0.perms().relate_pte_state_except(
                                old(self).inner.deref().meta_spec().level,
                                old(self).guard->Some_0.pte_token()->Some_0.value(),
                                idx as nat,
                            ));
                            assert(self.guard->Some_0.pte_token()->Some_0.value() =~= old(
                                self,
                            ).guard->Some_0.pte_token()->Some_0.value());
                            assert(self.guard->Some_0.perms().inner.value()[i] =~= old(
                                self,
                            ).guard->Some_0.perms().inner.value()[i]);
                        }
                    };
                    assert forall|i: int|
                        #![auto]
                        0 <= i < 512 && self.guard->Some_0.perms().inner.value()[i].is_pt(
                            level,
                        ) implies {
                        self.guard->Some_0.perms().inner.value()[i].inner.paddr()
                            == self.guard->Some_0.pte_token()->Some_0.value().get_paddr(i as nat)
                    } by {
                        if i != idx as int {
                            assert(old(self).wf_except(idx as nat));
                            assert(old(self).guard->Some_0.perms().relate_pte_state_except(
                                old(self).inner.deref().meta_spec().level,
                                old(self).guard->Some_0.pte_token()->Some_0.value(),
                                idx as nat,
                            ));
                            assert(self.guard->Some_0.pte_token()->Some_0.value() =~= old(
                                self,
                            ).guard->Some_0.pte_token()->Some_0.value());
                            assert(self.guard->Some_0.perms().inner.value()[i] =~= old(
                                self,
                            ).guard->Some_0.perms().inner.value()[i]);
                        }
                    };
                };
            } else {
                assert(self.wf_except(idx as nat)) by {
                    assert(self.guard->Some_0.pte_token() is Some);
                    assert forall|i: int| #![auto] 0 <= i < 512 && i != idx as int implies {
                        self.guard->Some_0.perms().inner.value()[i].is_pt(level)
                            <==> self.guard->Some_0.pte_token()->Some_0.value().is_alive(i as nat)
                    } by {
                        assert(old(self).wf_except(idx as nat));
                        assert(old(self).guard->Some_0.perms().relate_pte_state_except(
                            old(self).inner.deref().meta_spec().level,
                            old(self).guard->Some_0.pte_token()->Some_0.value(),
                            idx as nat,
                        ));
                        assert(self.guard->Some_0.pte_token()->Some_0.value() =~= old(
                            self,
                        ).guard->Some_0.pte_token()->Some_0.value());
                        assert(self.guard->Some_0.perms().inner.value()[i] =~= old(
                            self,
                        ).guard->Some_0.perms().inner.value()[i]);
                    };
                    assert forall|i: int|
                        #![auto]
                        0 <= i < 512 && i != idx
                            && self.guard->Some_0.perms().inner.value()[i].is_pt(level) implies {
                        self.guard->Some_0.perms().inner.value()[i].inner.paddr()
                            == self.guard->Some_0.pte_token()->Some_0.value().get_paddr(i as nat)
                    } by {
                        assert(old(self).wf_except(idx as nat));
                        assert(old(self).guard->Some_0.perms().relate_pte_state_except(
                            old(self).inner.deref().meta_spec().level,
                            old(self).guard->Some_0.pte_token()->Some_0.value(),
                            idx as nat,
                        ));
                        assert(self.guard->Some_0.pte_token()->Some_0.value() =~= old(
                            self,
                        ).guard->Some_0.pte_token()->Some_0.value());
                        assert(self.guard->Some_0.perms().inner.value()[i] =~= old(
                            self,
                        ).guard->Some_0.perms().inner.value()[i]);
                    };
                };
            }
        }
    }

    //Although this function has mode exec, its operations are pure logical
    pub fn take_node_token(&mut self) -> (res: Tracked<NodeToken<C>>)
        requires
            old(self).guard is Some,
            old(self).guard->Some_0.node_token() is Some,
        ensures
            res@ == old(self).guard->Some_0.node_token()->Some_0,
            self.guard->Some_0.node_token() == None::<NodeToken<C>>,
            self.guard->Some_0.pte_token() == old(self).guard->Some_0.pte_token(),
            self.guard->Some_0.stray_perm() == old(self).guard->Some_0.stray_perm(),
            self.guard->Some_0.perms() == old(self).guard->Some_0.perms(),
            self.guard->Some_0.in_protocol() == old(self).guard->Some_0.in_protocol(),
            self.guard->Some_0.handle() == old(self).guard->Some_0.handle(),
            self.inner == old(self).inner,
            self.guard is Some,
    {
        let mut guard = self.guard.take().unwrap();
        let res = guard.take_node_token();
        self.guard = Some(guard);
        res
    }

    //Although this function has mode exec, its operations are pure logical
    pub fn put_node_token(&mut self, token: Tracked<NodeToken<C>>)
        requires
            old(self).guard is Some,
            old(self).guard->Some_0.node_token() is None,
        ensures
            self.guard->Some_0.node_token() == Some(token@),
            self.guard->Some_0.pte_token() == old(self).guard->Some_0.pte_token(),
            self.guard->Some_0.stray_perm() == old(self).guard->Some_0.stray_perm(),
            self.guard->Some_0.perms() == old(self).guard->Some_0.perms(),
            self.guard->Some_0.in_protocol() == old(self).guard->Some_0.in_protocol(),
            self.guard->Some_0.handle() == old(self).guard->Some_0.handle(),
            self.inner == old(self).inner,
            self.guard is Some,
    {
        let mut guard = self.guard.take().unwrap();
        guard.put_node_token(token);
        self.guard = Some(guard);
    }

    pub fn update_in_protocol(&mut self, in_protocol: Tracked<bool>)
        requires
            old(self).guard is Some,
        ensures
            self.guard->Some_0.in_protocol() == in_protocol@,
            self.guard->Some_0.node_token() == old(self).guard->Some_0.node_token(),
            self.guard->Some_0.pte_token() == old(self).guard->Some_0.pte_token(),
            self.guard->Some_0.stray_perm() == old(self).guard->Some_0.stray_perm(),
            self.guard->Some_0.perms() == old(self).guard->Some_0.perms(),
            self.guard->Some_0.handle() == old(self).guard->Some_0.handle(),
            self.inner == old(self).inner,
            self.guard is Some,
    {
        let mut guard = self.guard.take().unwrap();
        guard.update_in_protocol(in_protocol);
        self.guard = Some(guard);
    }

    pub proof fn tracked_borrow_guard(tracked &self) -> (tracked res: &SpinGuard<C>)
        requires
            self.guard is Some,
        ensures
            *res =~= self.guard->Some_0,
    {
        self.guard.tracked_borrow()
    }

    #[verifier::external_body]
    pub fn nr_children(&self) -> u16 {
        unimplemented!("nr_children")
    }
}

pub open spec fn pt_guard_deref_spec<'a, 'rcu, C: PageTableConfig>(
    guard: &'a PageTableGuard<'rcu, C>,
) -> &'a PageTableNodeRef<'rcu, C> {
    &guard.inner
}

impl<'rcu, C: PageTableConfig> Deref for PageTableGuard<'rcu, C> {
    type Target = PageTableNodeRef<'rcu, C>;

    #[verifier::when_used_as_spec(pt_guard_deref_spec)]
    fn deref(&self) -> (ret: &Self::Target)
        ensures
            ret == self.inner,
    {
        &self.inner
    }
}

// impl Drop for PageTableGuard<'_>
impl<C: PageTableConfig> PageTableGuard<'_, C> {
    pub fn normal_drop<'a>(&'a mut self)
        requires
            old(self).wf(),
            old(self).guard->Some_0.in_protocol() == false,
        ensures
            self.guard is None,
    {
        let guard = self.guard.take().unwrap();
        self.inner.deref().meta().lock.normal_unlock(guard);
    }

    pub fn drop<'a>(&'a mut self, m: Tracked<LockProtocolModel<C>>) -> (res: Tracked<
        LockProtocolModel<C>,
    >)
        requires
            old(self).wf(),
            old(self).guard->Some_0.stray_perm().value() == false,
            old(self).guard->Some_0.in_protocol() == true,
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

pub struct PageTablePageMeta<C: PageTableConfig> {
    pub lock: PageTablePageSpinLock<C>,
    // TODO: PCell or Cell?
    // pub nr_children: SyncUnsafeCell<u16>,
    pub nr_children: PCell<u16>,
    // The stray flag indicates whether this frame is a page table node.
    pub stray: StrayFlag,
    pub level: PagingLevel,
    pub frame_paddr: Paddr,  // TODO: should be a ghost type
    pub nid: Ghost<NodeId>,
    pub inst: Tracked<SpecInstance<C>>,
}

impl<C: PageTableConfig> PageTablePageMeta<C> {
    #[verifier::external_body]
    pub fn new(level: PagingLevel) -> Self {
        unimplemented!()
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.frame_paddr == self.lock.paddr_spec()
        &&& self.level
            == self.lock.level_spec()
        // &&& valid_paddr(self.frame_paddr)
        &&& 1 <= self.level <= C::NR_LEVELS_SPEC()
        &&& node_helper::valid_nid::<C>(self.nid@)
        &&& self.nid@ == self.lock.nid@
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
        &&& self.inst@.id() == self.lock.pt_inst_id()
        &&& self.level as nat == node_helper::nid_to_level::<C>(self.nid@)
        &&& self.stray.id() == self.lock.stray_cell_id@
    }
}

// SAFETY: The layout of the `PageTablePageMeta` is ensured to be the same for
// all possible generic parameters. And the layout fits the requirements.
// unsafe
impl<C: PageTableConfig> AnyFrameMeta for PageTablePageMeta<C> {
    // TODO: Implement AnyFrameMeta for PageTablePageMeta

}

} // verus!
