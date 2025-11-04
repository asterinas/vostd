pub mod child;
pub mod entry;
pub mod rwlock;

use std::cell::Cell;
use std::cell::SyncUnsafeCell;
use std::marker::PhantomData;
use std::ops::Range;
use core::mem::ManuallyDrop;
use std::ops::Deref;

use vstd::prelude::*;
use vstd::cell::PCell;
use vstd::raw_ptr::{self, PointsTo, ptr_ref};
use vstd::simple_pptr::MemContents;
use vstd::simple_pptr::PPtr;
use vstd::simple_pptr;

use vstd_extra::{manually_drop::*, array_ptr::*};

use common::{
    mm::{
        NR_ENTRIES,
        frame::meta::AnyFrameMeta,
        frame::meta::mapping::meta_to_frame,
        nr_subpage_per_huge,
        page_prop::PageProperty,
        page_size_spec,
        page_table::{PagingConsts, PageTableEntryTrait, PagingConstsTrait, PageTableConfig},
        Paddr, PagingLevel, Vaddr, PAGE_SIZE,
    },
    task::DisabledPreemptGuard,
    x86_64::kspace::paddr_to_vaddr,
};
use common::configs::{PTE_NUM, GLOBAL_CPU_NUM};
use common::spec::{common::NodeId, node_helper};

use crate::mm::frame::meta::{MetaSlot, MetaSlotPerm};
use crate::mm::page_table::node::entry::Entry;
use crate::mm::page_table::node::rwlock::{PageTablePageRwLock, RwReadGuard, RwWriteGuard};
use crate::mm::page_table::pte::Pte;
use crate::spec::{
    lock_protocol::LockProtocolModel,
    rw::{wf_tree_path, SpecInstance, NodeToken, PteArrayToken, PteState},
};

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

    // Trusted
    #[verifier::external_body]
    pub fn alloc(
        level: PagingLevel,
        nid: Ghost<NodeId>,
        inst: Tracked<SpecInstance<C>>,
        pa_nid: Ghost<NodeId>,
        offset: Ghost<nat>,
        node_token: Tracked<&NodeToken<C>>,
        pte_array_token: Tracked<PteArrayToken<C>>,
    ) -> (res: (Self, Tracked<PteArrayToken<C>>))
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

pub struct PageTableNodeRef<'a, C: PageTableConfig> {
    pub inner: ManuallyDrop<PageTableNode<C>>,
    pub _marker: PhantomData<&'a ()>,
}

// Functions defined in struct 'FrameRef'.
impl<'a, C: PageTableConfig> PageTableNodeRef<'a, C> {
    #[verifier::external_body]
    pub fn clone_ref(&self) -> (res: PageTableNodeRef<'a, C>)
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

// Functions defined in struct 'PageTableNodeRef'.
impl<'a, C: PageTableConfig> PageTableNodeRef<'a, C> {
    pub open spec fn wf(&self) -> bool {
        self.deref().wf()
    }

    pub fn lock_write(
        self,
        guard: &'a DisabledPreemptGuard,
        m: Tracked<LockProtocolModel<C>>,
    ) -> (res: (PageTableWriteLock<'a, C>, Tracked<LockProtocolModel<C>>))
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.inst@.id(),
            m@.state() is ReadLocking,
            wf_tree_path::<C>(m@.path().push(self.nid@)),
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

    pub fn lock_read(
        self,
        guard: &'a DisabledPreemptGuard,
        m: Tracked<LockProtocolModel<C>>,
    ) -> (res: (PageTableReadLock<'a, C>, Tracked<LockProtocolModel<C>>))
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.inst@.id(),
            m@.state() is ReadLocking,
            m@.path().len() < 3,
            wf_tree_path::<C>(m@.path().push(self.nid@)),
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

    pub fn make_write_guard_unchecked(
        self,
        _guard: &'a DisabledPreemptGuard,
        m: Tracked<&LockProtocolModel<C>>,
    ) -> (res: PageTableWriteLock<'a, C>)
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.inst@.id(),
            m@.state() is WriteLocked,
            m@.node_is_locked(node_helper::get_parent::<C>(self.nid@)),
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

pub struct PageTableReadLock<'a, C: PageTableConfig> {
    pub inner: PageTableNodeRef<'a, C>,
    pub guard: Option<RwReadGuard<C>>,
}

impl<'a, C: PageTableConfig> PageTableReadLock<'a, C> {
    pub open spec fn wf(&self) -> bool {
        &&& self.inner.wf()
        &&& self.guard is Some
        &&& self.guard->Some_0.wf(&self.deref().deref().meta_spec().lock)
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
            0 <= idx < 512,
        ensures
            res.wf_read(*self),
            res.idx == idx,
    {
        Entry::<C>::new_at_read(idx, self)
    }

    /// Gets the reference to the page table node.
    pub fn as_ref(&self) -> (res: PageTableNodeRef<'a, C>)
        requires
            self.wf(),
        ensures
            res.deref() =~= self.inner.deref(),
    {
        self.inner.clone_ref()
    }

    pub fn read_pte(&self, idx: usize) -> (res: Pte<C>)
        requires
            self.wf(),
            0 <= idx < 512,
        ensures
            res.wf_with_node(*self.deref().deref(), idx as nat),
            self.guard->Some_0.view_perms().relate_pte(res, idx as nat),
    {
        let va = paddr_to_vaddr(self.deref().deref().start_paddr());
        let ptr: ArrayPtr<Pte<C>, PTE_NUM> = ArrayPtr::from_addr(va);
        let guard: &RwReadGuard<C> = self.guard.as_ref().unwrap();
        let res = guard.borrow_perms(&self.deref().deref().meta().lock);
        let tracked perms = res.get();
        let pte: Pte<C> = ptr.get(Tracked(&perms.inner), idx);
        assert(self.guard->Some_0.view_perms().relate_pte(pte, idx as nat)) by {
            assert(pte =~= guard.view_perms().inner.opt_value()[idx as int]->Init_0);
        };
        pte
    }
}

pub open spec fn pt_read_guard_deref_spec<'a, 'b, C: PageTableConfig>(
    guard: &'a PageTableReadLock<'b, C>,
) -> &'a PageTableNodeRef<'b, C> {
    &guard.inner
}

impl<'a, C: PageTableConfig> Deref for PageTableReadLock<'a, C> {
    type Target = PageTableNodeRef<'a, C>;

    #[verifier::when_used_as_spec(pt_read_guard_deref_spec)]
    fn deref(&self) -> (ret: &Self::Target)
        ensures
            ret == self.inner,
    {
        &self.inner
    }
}

impl<C: PageTableConfig> PageTableReadLock<'_, C> {
    pub fn drop<'a>(&'a mut self, m: Tracked<LockProtocolModel<C>>) -> (res: Tracked<
        LockProtocolModel<C>,
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

pub struct PageTableWriteLock<'a, C: PageTableConfig> {
    pub inner: PageTableNodeRef<'a, C>,
    pub guard: Option<RwWriteGuard<C>>,
}

impl<'a, C: PageTableConfig> PageTableWriteLock<'a, C> {
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
            res.wf_write(*self),
            res.idx == idx,
    {
        Entry::<C>::new_at_write(idx, self)
    }

    /// Gets the reference to the page table node.
    pub fn as_ref(&self) -> (res: PageTableNodeRef<'a, C>)
        requires
            self.wf(),
        ensures
            res.deref() =~= self.inner.deref(),
    {
        self.inner.clone_ref()
    }

    pub fn read_pte(&self, idx: usize) -> (res: Pte<C>)
        requires
            self.wf(),
            0 <= idx < nr_subpage_per_huge::<C>(),
        ensures
            res.wf_with_node(*self.deref().deref(), idx as nat),
            self.guard->Some_0.perms@.relate_pte(res, idx as nat),
    {
        let va = paddr_to_vaddr(self.deref().deref().start_paddr());
        let ptr: ArrayPtr<Pte<C>, PTE_NUM> = ArrayPtr::from_addr(va);
        let guard: &RwWriteGuard<C> = self.guard.as_ref().unwrap();
        let tracked perms = guard.perms.borrow();
        let pte: Pte<C> = ptr.get(Tracked(&perms.inner), idx);
        assert(self.guard->Some_0.view_perms().relate_pte(pte, idx as nat)) by {
            assert(pte =~= guard.view_perms().inner.opt_value()[idx as int]->Init_0);
        };
        pte
    }

    pub fn write_pte(&mut self, idx: usize, pte: Pte<C>)
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
        let ptr: ArrayPtr<Pte<C>, PTE_NUM> = ArrayPtr::from_addr(va);
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

pub open spec fn pt_write_guard_deref_spec<'a, 'b, C: PageTableConfig>(
    guard: &'a PageTableWriteLock<'b, C>,
) -> &'a PageTableNodeRef<'b, C> {
    &guard.inner
}

impl<'a, C: PageTableConfig> Deref for PageTableWriteLock<'a, C> {
    type Target = PageTableNodeRef<'a, C>;

    #[verifier::when_used_as_spec(pt_write_guard_deref_spec)]
    fn deref(&self) -> (ret: &Self::Target)
        ensures
            ret == self.inner,
    {
        &self.inner
    }
}

impl<C: PageTableConfig> PageTableWriteLock<'_, C> {
    pub fn drop<'a>(&'a mut self, m: Tracked<LockProtocolModel<C>>) -> (res: Tracked<
        LockProtocolModel<C>,
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

pub struct PageTablePageMeta<C: PageTableConfig> {
    /// The number of valid PTEs. It is mutable if the lock is held.
    pub nr_children: PCell<u16>,
    /// The level of the page table page. A page table page cannot be
    /// referenced by page tables of different levels.
    pub level: PagingLevel,
    /// The lock for the page table page.
    pub lock: PageTablePageRwLock<C>,
    pub frame_paddr: Paddr,  // TODO: should be a ghost type
    pub nid: Ghost<NodeId>,
    pub inst: Tracked<SpecInstance<C>>,
}

impl<C: PageTableConfig> PageTablePageMeta<C> {
    pub open spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.frame_paddr == self.lock.paddr_spec()
        &&& self.level == self.lock.level_spec()
        &&& 1 <= self.level <= C::NR_LEVELS_SPEC()
        &&& node_helper::valid_nid::<C>(self.nid@)
        &&& self.nid@ == self.lock.nid@
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
        &&& self.inst@.id() == self.lock.pt_inst_id()
        &&& self.level as nat == node_helper::nid_to_level::<C>(self.nid@)
    }
}

} // verus!
