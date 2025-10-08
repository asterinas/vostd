pub mod child_local;
pub mod child;
pub mod entry_local;
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

use entry_local::EntryLocal;
use entry::Entry;
use stray::{StrayFlag, StrayPerm};
use crate::{
    mm::{
        NR_ENTRIES,
        frame::{
            self,
            allocator::{pa_is_valid_kernel_address, AllocatorModel},
            meta::AnyFrameMeta,
            Frame, FrameRef,
        },
        nr_subpage_per_huge,
        page_prop::PageProperty,
        page_size_spec,
        page_table::PageTableEntryTrait,
        Paddr, PagingConsts, PagingConstsTrait, PagingLevel, Vaddr, PAGE_SIZE,
    },
    sync::spinlock::{PageTablePageSpinLock, SpinGuard},
    task::DisabledPreemptGuard,
    x86_64::kspace::paddr_to_vaddr,
};
use crate::mm::frame_concurrent::meta::{MetaSlot, meta_to_frame, MetaSlotPerm};
use crate::mm::page_table::{pte::Pte, GLOBAL_CPU_NUM};
use crate::mm::lock_protocol_utils::PTE_NUM;

use crate::exec::{
    self, MAX_FRAME_NUM, get_pte_from_addr_spec, SIZEOF_PAGETABLEENTRY, frame_addr_to_index,
    frame_addr_to_index_spec, MockPageTableEntry, MockPageTablePage,
};
use crate::spec::sub_pt::{pa_is_valid_pt_address, SubPageTable, level_is_in_range, index_pte_paddr};
use crate::spec::{
    lock_protocol::LockProtocolModel,
    common::NodeId,
    utils::NodeHelper,
    rcu::{SpecInstance, NodeToken, PteArrayToken, PteState, FreePaddrToken},
};

use super::cursor::spec_helpers;
use super::PageTableConfig;

verus! {

pub struct PageTableNode<C: PageTableConfig> {
    pub meta_ptr_l: PPtr<PageTablePageMeta<C>>,
    pub ptr_l: PPtr<MockPageTablePage>,

    pub ptr: *const MetaSlot<C>,
    pub perm: Tracked<MetaSlotPerm<C>>,
    pub nid: Ghost<NodeId>,
    pub inst: Tracked<SpecInstance>,
}

impl<C: PageTableConfig> PageTableNode<C> {
    /// Gets the metadata of this page.
    pub fn meta_local<'a>(
        &'a self, 
        Tracked(alloc_model): Tracked<&'a AllocatorModel<PageTablePageMeta<C>>>,
    ) -> &'a PageTablePageMeta<C>
        requires
            alloc_model.invariants(),
            alloc_model.meta_map.contains_key(self.start_paddr_local() as int),
            alloc_model.meta_map[self.start_paddr_local() as int].pptr() == self.meta_ptr_l,
        returns
            self.meta_local_spec(alloc_model),
    {
        self.meta_ptr_l.borrow(
            Tracked(alloc_model.meta_map.tracked_borrow(self.start_paddr_local() as int)),
        )
    }

    pub open spec fn meta_local_spec(
        &self, 
        alloc_model: &AllocatorModel<PageTablePageMeta<C>>,
    ) -> &PageTablePageMeta<C> {
        &alloc_model.meta_map[self.start_paddr_local() as int].value()
    }
}

impl<C: PageTableConfig> PageTableNode<C> {
     /// Gets the physical address of the start of the frame.
    // TODO: Implement
    #[verifier::allow_in_spec]
    pub fn start_paddr_local(&self) -> Paddr
        returns
            self.ptr_l.addr() as Paddr,
    {
        // self.slot().frame_paddr() // TODO
        self.ptr_l.addr() as Paddr
    }

    /// Gets the paging level of this page.
    ///
    /// This is the level of the page table entry that maps the frame,
    /// which determines the size of the frame.
    ///
    /// Currently, the level is always 1, which means the frame is a regular
    /// page frame.
    #[verifier::allow_in_spec]
    pub const fn map_level(&self) -> (res: PagingLevel)
        returns
            1 as PagingLevel,
    {
        1
    }

    /// Gets the size of this page in bytes.
    #[verifier::allow_in_spec]
    pub fn size(&self) -> (res: usize)
        returns
            PAGE_SIZE(),
    {
        PAGE_SIZE()
    }

    /// Borrows a reference from the given frame.
    pub fn borrow(
        &self, 
        Tracked(alloc_model): Tracked<&AllocatorModel<PageTablePageMeta<C>>>,
    ) -> (res: PageTableNodeRef<'_, C>)
        requires
            alloc_model.invariants(),
            alloc_model.meta_map.contains_key(self.start_paddr_local() as int),
            alloc_model.meta_map[self.start_paddr_local() as int].pptr() == self.meta_ptr_l,
            alloc_model.meta_map[self.start_paddr_local() as int].value() == self.meta_local_spec(alloc_model),
            level_is_in_range::<C>(alloc_model.meta_map[self.start_paddr_local() as int].value().level as int),
        ensures
            res.deref() == self,
    {
        let res = PageTableNodeRef::borrow_paddr_local(self.start_paddr_local(), Tracked(alloc_model));
        assert(res.deref() =~= self) by {
            assert(res.ptr =~= self.ptr) by { admit(); };
            assert(res.perm =~= self.perm) by { admit(); };
            assert(res.nid =~= self.nid) by { admit(); };
            assert(res.inst =~= self.inst) by { admit(); };
        };
        res
    }

    /// Forgets the handle to the frame.
    ///
    /// This will result in the frame being leaked without calling the custom dropper.
    ///
    /// A physical address to the frame is returned in case the frame needs to be
    /// restored using [`Frame::from_raw`] later. This is useful when some architectural
    /// data structures need to hold the frame handle such as the page table.
    /// TODO: Implement Frame::into_raw
    #[verifier::external_body]
    pub(in crate::mm) fn into_raw_local(self) -> (res: Paddr)
        ensures
            res == self.start_paddr_local(),
    {
        let this = ManuallyDrop::new(self);
        this.start_paddr_local()
    }

    /// Restores a forgotten [`Frame`] from a physical address.
    ///
    /// # Safety
    ///
    /// The caller should only restore a `Frame` that was previously forgotten using
    /// [`Frame::into_raw`].
    ///
    /// And the restoring operation should only be done once for a forgotten
    /// [`Frame`]. Otherwise double-free will happen.
    ///
    /// Also, the caller ensures that the usage of the frame is correct. There's
    /// no checking of the usage in this function.
    #[verifier::external_body]
    pub(crate) fn from_raw_local(
        paddr: Paddr, 
        Tracked(alloc_model): Tracked<&AllocatorModel<PageTablePageMeta<C>>>,
    ) -> (res: Self)
        requires
            alloc_model.invariants(),
            alloc_model.meta_map.contains_key(paddr as int),
        ensures
            res.ptr_l.addr() == paddr,
            res.meta_ptr_l == alloc_model.meta_map[paddr as int].pptr(),
    {
        // let vaddr = mapping::frame_to_meta::<PagingConsts>(paddr);
        // let ptr = vaddr as *const MetaSlot;
        // Self {
        //     ptr_l: PPtr::from_addr(paddr),
        //     meta_ptr_l: PPtr::from_addr(
        //         paddr,
        //     ),  // FIXME: This is wrong, we need to use the meta_map.
        // }
        unimplemented!()
    }
}

impl<C: PageTableConfig> PageTableNode<C> {
    pub open spec fn wf_local(&self, alloc_model: &AllocatorModel<PageTablePageMeta<C>>) -> bool {
        &&& pa_is_valid_pt_address(self.paddr_local() as int)
        &&& level_is_in_range::<C>(self.level_local_spec(alloc_model) as int)
        &&& alloc_model.meta_map.contains_key(self.paddr_local() as int)
        &&& alloc_model.meta_map[self.paddr_local() as int].pptr() == self.meta_ptr_l
        &&& alloc_model.meta_map[self.paddr_local() as int].value().level == self.level_local_spec(alloc_model)
    }

    #[verifier::allow_in_spec]
    pub fn paddr_local(&self) -> Paddr
        returns
            self.start_paddr_local(),
    {
        self.start_paddr_local()
    }

    pub fn level_local(
        &self,
        Tracked(alloc_model): Tracked<&AllocatorModel<PageTablePageMeta<C>>>,
    ) -> PagingLevel
        requires
            alloc_model.invariants(),
            alloc_model.meta_map.contains_key(self.start_paddr_local() as int),
            alloc_model.meta_map[self.start_paddr_local() as int].pptr() == self.meta_ptr_l,
        returns
            self.level_local_spec(alloc_model),
    {
        self.meta_local(Tracked(alloc_model)).level
    }

    pub open spec fn level_local_spec(
        &self,
        alloc_model: &AllocatorModel<PageTablePageMeta<C>>,
    ) -> PagingLevel {
        self.meta_local_spec(alloc_model).level
    }

    #[verifier::external_body]
    pub fn alloc_local(
        level: PagingLevel,
        Tracked(model): Tracked<&mut AllocatorModel<PageTablePageMeta<C>>>,
    ) -> (res: (Self, Tracked<simple_pptr::PointsTo<MockPageTablePage>>))
        requires
            old(model).invariants(),
            crate::spec::sub_pt::level_is_in_range::<C>(level as int),
        ensures
            res.1@.pptr() == res.0.ptr_l,
            res.1@.mem_contents().is_init(),
            pa_is_valid_kernel_address(res.0.start_paddr_local() as int),
            model.invariants(),
            !old(model).meta_map.contains_key(res.0.start_paddr_local() as int),
            model.meta_map.contains_key(res.0.start_paddr_local() as int),
            model.meta_map[res.0.start_paddr_local() as int].pptr() == res.0.meta_ptr_l,
            model.meta_map[res.0.start_paddr_local() as int].value().level == level,
            forall|i: int|
                #![trigger res.1@.value().ptes[i]]
                0 <= i < NR_ENTRIES ==> {
                    &&& res.1@.value().ptes[i].pte_addr == (res.0.start_paddr_local() + i
                        * SIZEOF_PAGETABLEENTRY) as u64
                    &&& res.1@.value().ptes[i].frame_pa == 0
                    &&& res.1@.value().ptes[i].level == level
                    &&& res.1@.value().ptes[i].prop == PageProperty::new_absent()
                },
            res.0.start_paddr_local() % page_size_spec::<C>(level) == 0,
            // old model does not change
            forall|pa: Paddr| #[trigger]
                old(model).meta_map.contains_key(pa as int) <==> {
                    &&& #[trigger] model.meta_map.contains_key(pa as int)
                    &&& res.0.start_paddr_local() != pa
                },
            forall|pa: Paddr| #[trigger]
                model.meta_map.contains_key(pa as int) && old(model).meta_map.contains_key(
                    pa as int,
                ) ==> {
                    &&& model.meta_map[pa as int] == old(model).meta_map[pa as int]
                },
    {
        // crate::exec::alloc_page_table(level, Tracked(model))
        unimplemented!()
    }
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
}

// Functions defined in struct 'PageTableNode'.
impl<C: PageTableConfig> PageTableNode<C> {
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
        let tracked perm: &raw_ptr::PointsTo<MetaSlot<C>> = &self.perm.borrow().inner;
        let meta_slot: &MetaSlot<C> = raw_ptr::ptr_ref(self.ptr, Tracked(perm));
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
    ) -> (res: (PageTableNode<C>, Tracked<PteArrayToken>))
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

pub struct PageTableNodeRef<'a, C: PageTableConfig> {
    pub inner: ManuallyDrop<PageTableNode<C>>,
    pub _marker: PhantomData<&'a ()>,
}

impl<'a, C: PageTableConfig> PageTableNodeRef<'a, C> {
    pub fn borrow_paddr_local(
        raw: Paddr,
        Tracked(alloc_model): Tracked<&AllocatorModel<PageTablePageMeta<C>>>,
    ) -> (res: Self)
        requires
            alloc_model.invariants(),
            alloc_model.meta_map.contains_key(raw as int),
            pa_is_valid_pt_address(raw as int),
            level_is_in_range::<C>(alloc_model.meta_map[raw as int].value().level as int),
        ensures
            res.deref().start_paddr_local() == raw,
            res.deref().meta_ptr_l == alloc_model.meta_map[raw as int].pptr(),
            res.wf_local(alloc_model),
            alloc_model.invariants(),
    {
        Self {
            inner: ManuallyDrop::new(
                PageTableNode::from_raw_local(raw, Tracked(alloc_model))
            ),
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

impl<'a, C: PageTableConfig> PageTableNodeRef<'a, C> {
    pub open spec fn wf_local(
        &self, 
        alloc_model: &AllocatorModel<PageTablePageMeta<C>>,
    ) -> bool {
        self.deref().wf_local(alloc_model)
    }

    // Actually should be checked after verification. Just can't be checked in pure Rust.
    // TODO: fix me
    #[verifier::external_body]
    pub fn make_guard_unchecked_local<'rcu>(
        self,
        _guard: &'rcu crate::task::DisabledPreemptGuard,
        Ghost(va): Ghost<Vaddr>,
    ) -> (res: PageTableGuard<'rcu, C>) where 'a: 'rcu
        ensures
            res.inner == self,
            res.va() == va,
    {
        // PageTableGuard { inner: self, va: Ghost(va) }
        unimplemented!()
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

    pub fn normal_lock<'rcu>(
        self,
        guard: &'rcu DisabledPreemptGuard,
    ) -> (res: PageTableGuard<'rcu, C>) where 'a: 'rcu
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
        pa_pte_array_token: Tracked<&PteArrayToken>,
    ) -> (res: PageTableGuard<'rcu, C>) where 'a: 'rcu
        requires
            self.wf(),
            self.nid@ != NodeHelper::root_id(),
            pa_pte_array_token@.instance_id() == self.inst@.id(),
            pa_pte_array_token@.key() == NodeHelper::get_parent(self.nid@),
            pa_pte_array_token@.value().is_alive(NodeHelper::get_offset(self.nid@)),
            pa_pte_array_token@.value().get_paddr(NodeHelper::get_offset(self.nid@))
                == self.deref().start_paddr(),
        ensures
            res.wf(),
            res.inner =~= self,
            res.guard->Some_0.stray_perm().value() == false,
            res.guard->Some_0.in_protocol() == false,
    {
        let guard = self.deref().meta().lock.normal_lock_new_allocated_node(pa_pte_array_token);
        PageTableGuard { inner: self, guard: Some(guard) }
    }

    pub fn lock<'rcu>(
        self,
        guard: &'rcu DisabledPreemptGuard,
        m: Tracked<LockProtocolModel>,
        pa_pte_array_token: Tracked<&PteArrayToken>,
    ) -> (res: (PageTableGuard<'rcu, C>, Tracked<LockProtocolModel>)) where 'a: 'rcu
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

    #[verifier::external_body]
    pub fn make_guard_unchecked<'rcu>(
        self,
        _guard: &'rcu (),
        m: Tracked<&LockProtocolModel>,
        pa_pte_array_token: Tracked<&PteArrayToken>,
    ) -> (res: PageTableGuard<'rcu, C>) where 'a: 'rcu
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
            res.guard->Some_0.stray_perm().value() == false,
            res.guard->Some_0.in_protocol() == true,
    {
        // PageTableGuard { inner: self }
        unimplemented!()
    }
}

pub struct PageTableGuard<'a, C: PageTableConfig> {
    pub inner: PageTableNodeRef<'a, C>,
    pub guard: Option<SpinGuard<C>>,
    // pub va: Ghost<Vaddr>,
}

impl<'rcu, C: PageTableConfig> PageTableGuard<'rcu, C> {
    pub uninterp spec fn va(&self) -> Vaddr;
}

impl<'a, C: PageTableConfig> PageTableGuard<'a, C> {
    pub open spec fn wf_local(
        &self, 
        alloc_model: &AllocatorModel<PageTablePageMeta<C>>,
    ) -> bool {
        self.inner.wf_local(alloc_model)
    }

    #[verifier::allow_in_spec]
    pub fn paddr_local(&self) -> Paddr
        returns
            self.inner.start_paddr_local(),
    {
        self.inner.start_paddr_local()
    }

    pub fn level_local(
        &self,
        Tracked(alloc_model): Tracked<&AllocatorModel<PageTablePageMeta<C>>>,
    ) -> (res: PagingLevel)
        requires
            alloc_model.invariants(),
            alloc_model.meta_map.contains_key(self.inner.start_paddr_local() as int),
            alloc_model.meta_map[self.inner.start_paddr_local() as int].pptr() == self.inner.meta_ptr_l,
        returns
            self.level_local_spec(alloc_model),
    {
        self.inner.meta_local(Tracked(alloc_model)).level
    }

    pub open spec fn level_local_spec(
        &self,
        alloc_model: &AllocatorModel<PageTablePageMeta<C>>,
    ) -> PagingLevel {
        self.inner.meta_local_spec(alloc_model).level
    }

    pub fn into_raw_paddr(self: Self) -> Paddr where Self: Sized {
        self.paddr_local()
    }

    #[verifier::external_body]
    fn read_pte_local(&self, idx: usize, Tracked(spt): Tracked<&SubPageTable<C>>) -> (res: C::E) {
        let e = self.inner.ptr_l.read(Tracked(spt.perms.tracked_borrow(self.paddr_local()))).ptes[idx];
        // todo!("e -> usize -> C::E");
        let c_e = &e as *const _ as *const C::E;
        unsafe { (*c_e).clone() }
    }

    fn write_pte_local(
        &self,
        idx: usize,
        pte: C::E,
        level: PagingLevel,
        Tracked(spt): Tracked<&mut SubPageTable<C>>,
    )
        requires
            idx < nr_subpage_per_huge::<C>(),
            old(spt).wf(),
            old(spt).perms.contains_key(self.paddr_local()),
            self.wf_local(&old(spt).alloc_model),
            old(spt).i_ptes.value().contains_key(
                index_pte_paddr(self.paddr_local() as int, idx as int) as int,
            ),
        ensures
            spt.wf(),
            spt.root == old(spt).root,
            spt.frames == old(spt).frames,
            spt.i_ptes == old(spt).i_ptes,
            spt.ptes == old(spt).ptes,
            old(spt).alloc_model == spt.alloc_model,
            old(spt).perms.dom() == spt.perms.dom(),
    {
        assert(spt.perms.contains_key(self.paddr_local()));
        assert(old(spt).i_ptes.value().contains_key(
            index_pte_paddr(self.paddr_local() as int, idx as int) as int,
        ));

        let p = PPtr::from_addr(self.paddr_local());

        assert(spt.perms.get(self.paddr_local()).unwrap().mem_contents().is_init());
        let tracked points_to = spt.perms.tracked_remove(self.paddr_local());

        assert(points_to.mem_contents().is_init());
        assert(points_to.pptr().addr() as int == self.paddr_local() as int);
        assert(points_to.pptr() == p);

        let mut frame: MockPageTablePage = p.read(Tracked(&points_to));
        assume(idx < frame.ptes.len());
        frame.ptes[idx] = MockPageTableEntry {
            pte_addr: pte.pte_paddr() as u64,
            frame_pa: pte.frame_paddr() as u64,
            level: level as u8,
            prop: pte.prop(),
        };
        // TODO: P0 currently, the last level frame will cause the inconsistency
        // between spt.perms and spt.frames
        p.write(Tracked(&mut points_to), frame);

        proof {
            spt.perms.tracked_insert(self.paddr_local(), points_to);
        }

        assert(spt.wf());
    }

    // #[verifier::external_body]
    // pub fn meta(&self) -> &PageTablePageMeta<C> {
    //     unimplemented!("meta")
    // }

    // Note: mutable types not supported.
    // #[verifier::external_body]
    // pub fn nr_children_mut(&mut self) -> &mut u16 {
    //     unimplemented!("nr_children_mut")
    // }

    #[verifier::external_body]
    pub fn nr_children(&self) -> u16 {
        unimplemented!("nr_children")
    }

    pub fn change_children(&self, delta: i16) {
        // TODO: implement this function
    }
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

    pub fn entry(&self, idx: usize) -> (res: Entry<C>)
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
            0 <= idx < 512,
        ensures
            res.wf_with_node(*self.deref().deref(), idx as nat),
            self.guard->Some_0.perms().relate_pte(res, idx as nat),
    {
        let va = paddr_to_vaddr(self.deref().deref().start_paddr());
        let ptr: ArrayPtr<Pte<C>, PTE_NUM> = ArrayPtr::from_addr(va);
        let guard: &SpinGuard<C> = self.guard.as_ref().unwrap();
        let tracked perms = &guard.inner.borrow().perms;
        // assert(perms.inner.value()[idx as int].wf());
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
    pub fn take_node_token(&mut self) -> (res: Tracked<NodeToken>)
        requires
            old(self).guard is Some,
            old(self).guard->Some_0.node_token() is Some,
        ensures
            res@ == old(self).guard->Some_0.node_token()->Some_0,
            self.guard->Some_0.node_token() == None::<NodeToken>,
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
    pub fn put_node_token(&mut self, token: Tracked<NodeToken>)
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

    pub fn drop<'a>(&'a mut self, m: Tracked<LockProtocolModel>) -> (res: Tracked<
        LockProtocolModel,
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
    pub frame_paddr: Paddr, // TODO: should be a ghost type
    pub nid: Ghost<NodeId>,
    pub inst: Tracked<SpecInstance>,
}

impl<C: PageTableConfig> PageTablePageMeta<C> {
    #[verifier::external_body]
    pub fn new(level: PagingLevel) -> Self {
        unimplemented!()
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.frame_paddr == self.lock.paddr_spec()
        &&& self.level == self.lock.level_spec()
        // &&& valid_paddr(self.frame_paddr)
        &&& 1 <= self.level <= 4
        &&& NodeHelper::valid_nid(self.nid@)
        &&& self.nid@ == self.lock.nid@
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
        &&& self.inst@.id() == self.lock.pt_inst_id()
        &&& self.level as nat == NodeHelper::nid_to_level(self.nid@)
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
