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
use vstd::simple_pptr::MemContents;
use vstd::simple_pptr::PPtr;
use vstd::simple_pptr::PointsTo;

use vstd_extra::manually_drop::*;

use entry::EntryLocal;
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
    x86_64::kspace::paddr_to_vaddr,
};
use crate::mm::frame_concurrent::meta::{MetaSlot, meta_to_frame, MetaSlotPerm};


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
    ) -> (res: (Self, Tracked<PointsTo<MockPageTablePage>>))
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
    pub fn make_guard_unchecked<'rcu>(
        self,
        _guard: &'rcu crate::task::DisabledPreemptGuard,
        Ghost(va): Ghost<Vaddr>,
    ) -> (res: PageTableGuard<'rcu, C>) where 'a: 'rcu
        ensures
            res.inner == self,
            res.va == va,
    {
        // PageTableGuard { inner: self, va: Ghost(va) }
        unimplemented!()
    }
}

pub struct PageTableGuard<'a, C: PageTableConfig> {
    pub inner: PageTableNodeRef<'a, C>,
    pub guard: Option<SpinGuard<C>>,
    pub va: Ghost<Vaddr>,
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

    // pub open spec fn wf(&self) -> bool {
    //     &&& self.lock.wf()
    //     &&& self.frame_paddr == self.lock.paddr_spec()
    //     &&& self.level == self.lock.level_spec()
    //     &&& valid_paddr(self.frame_paddr)
    //     &&& 1 <= self.level <= 4
    //     &&& NodeHelper::valid_nid(self.nid@)
    //     &&& self.nid@ == self.lock.nid@
    //     &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
    //     &&& self.inst@.id() == self.lock.pt_inst_id()
    //     &&& self.level as nat == NodeHelper::nid_to_level(self.nid@)
    //     &&& self.stray.id() == self.lock.stray_cell_id@
    // }
}

// SAFETY: The layout of the `PageTablePageMeta` is ensured to be the same for
// all possible generic parameters. And the layout fits the requirements.
// unsafe
impl<C: PageTableConfig> AnyFrameMeta for PageTablePageMeta<C> {
    // TODO: Implement AnyFrameMeta for PageTablePageMeta

}

} // verus!
