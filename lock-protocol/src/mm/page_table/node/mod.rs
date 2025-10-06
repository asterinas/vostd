pub mod child;
pub mod entry;

use std::cell::Cell;
use std::cell::SyncUnsafeCell;
use std::marker::PhantomData;
use std::ops::Range;
use core::mem::ManuallyDrop;

use vstd::cell::PCell;
use vstd::prelude::*;
use vstd::simple_pptr::MemContents;
use vstd::simple_pptr::PPtr;
use vstd::simple_pptr::PointsTo;

use vstd_extra::manually_drop::*;

use entry::Entry;
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
    sync::spin,
    x86_64::kspace::paddr_to_vaddr,
};

use crate::exec::{
    self, MAX_FRAME_NUM, get_pte_from_addr_spec, SIZEOF_PAGETABLEENTRY, frame_addr_to_index,
    frame_addr_to_index_spec, MockPageTableEntry, MockPageTablePage,
};
use crate::spec::sub_pt::{pa_is_valid_pt_address, SubPageTable, level_is_in_range, index_pte_paddr};

use super::cursor::spec_helpers;
use super::PageTableConfig;
use std::ops::Deref;

verus! {

pub struct PageTableNode<C: PageTableConfig> {
    pub meta_ptr_l: PPtr<PageTablePageMeta<C>>,
    pub ptr_l: PPtr<MockPageTablePage>,
}

impl<C: PageTableConfig> PageTableNode<C> {
    /// Gets the metadata of this page.
    pub fn meta<'a>(
        &'a self, 
        Tracked(alloc_model): Tracked<&'a AllocatorModel<PageTablePageMeta<C>>>,
    ) -> &'a PageTablePageMeta<C>
        requires
            alloc_model.invariants(),
            alloc_model.meta_map.contains_key(self.start_paddr() as int),
            alloc_model.meta_map[self.start_paddr() as int].pptr() == self.meta_ptr_l,
        returns
            self.meta_spec(alloc_model),
    {
        self.meta_ptr_l.borrow(
            Tracked(alloc_model.meta_map.tracked_borrow(self.start_paddr() as int)),
        )
    }

    pub open spec fn meta_spec(
        &self, 
        alloc_model: &AllocatorModel<PageTablePageMeta<C>>,
    ) -> &PageTablePageMeta<C> {
        &alloc_model.meta_map[self.start_paddr() as int].value()
    }
}

impl<C: PageTableConfig> PageTableNode<C> {
     /// Gets the physical address of the start of the frame.
    // TODO: Implement
    #[verifier::allow_in_spec]
    pub fn start_paddr(&self) -> Paddr
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
            alloc_model.meta_map.contains_key(self.start_paddr() as int),
            alloc_model.meta_map[self.start_paddr() as int].pptr() == self.meta_ptr_l,
            alloc_model.meta_map[self.start_paddr() as int].value() == self.meta_spec(alloc_model),
            level_is_in_range::<C>(alloc_model.meta_map[self.start_paddr() as int].value().level as int),
        ensures
            res.deref() == self,
    {
        PageTableNodeRef::borrow_paddr(self.start_paddr(), Tracked(alloc_model))
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
    pub(in crate::mm) fn into_raw(self) -> (res: Paddr)
        ensures
            res == self.start_paddr(),
    {
        let this = ManuallyDrop::new(self);
        this.start_paddr()
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
    pub(crate) fn from_raw(
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
    pub open spec fn wf(&self, alloc_model: &AllocatorModel<PageTablePageMeta<C>>) -> bool {
        &&& pa_is_valid_pt_address(self.paddr() as int)
        &&& level_is_in_range::<C>(self.level_spec(alloc_model) as int)
        &&& alloc_model.meta_map.contains_key(self.paddr() as int)
        &&& alloc_model.meta_map[self.paddr() as int].pptr() == self.meta_ptr_l
        &&& alloc_model.meta_map[self.paddr() as int].value().level == self.level_spec(alloc_model)
    }

    #[verifier::allow_in_spec]
    pub fn paddr(&self) -> Paddr
        returns
            self.start_paddr(),
    {
        self.start_paddr()
    }

    pub fn level(
        &self,
        Tracked(alloc_model): Tracked<&AllocatorModel<PageTablePageMeta<C>>>,
    ) -> PagingLevel
        requires
            alloc_model.invariants(),
            alloc_model.meta_map.contains_key(self.start_paddr() as int),
            alloc_model.meta_map[self.start_paddr() as int].pptr() == self.meta_ptr_l,
        returns
            self.level_spec(alloc_model),
    {
        self.meta(Tracked(alloc_model)).level
    }

    pub open spec fn level_spec(
        &self,
        alloc_model: &AllocatorModel<PageTablePageMeta<C>>,
    ) -> PagingLevel {
        self.meta_spec(alloc_model).level
    }

    #[verifier::external_body]
    pub fn alloc(
        level: PagingLevel,
        Tracked(model): Tracked<&mut AllocatorModel<PageTablePageMeta<C>>>,
    ) -> (res: (Self, Tracked<PointsTo<MockPageTablePage>>))
        requires
            old(model).invariants(),
            crate::spec::sub_pt::level_is_in_range::<C>(level as int),
        ensures
            res.1@.pptr() == res.0.ptr_l,
            res.1@.mem_contents().is_init(),
            pa_is_valid_kernel_address(res.0.start_paddr() as int),
            model.invariants(),
            !old(model).meta_map.contains_key(res.0.start_paddr() as int),
            model.meta_map.contains_key(res.0.start_paddr() as int),
            model.meta_map[res.0.start_paddr() as int].pptr() == res.0.meta_ptr_l,
            model.meta_map[res.0.start_paddr() as int].value().level == level,
            forall|i: int|
                #![trigger res.1@.value().ptes[i]]
                0 <= i < NR_ENTRIES ==> {
                    &&& res.1@.value().ptes[i].pte_addr == (res.0.start_paddr() + i
                        * SIZEOF_PAGETABLEENTRY) as u64
                    &&& res.1@.value().ptes[i].frame_pa == 0
                    &&& res.1@.value().ptes[i].level == level
                    &&& res.1@.value().ptes[i].prop == PageProperty::new_absent()
                },
            res.0.start_paddr() % page_size_spec::<C>(level) == 0,
            // old model does not change
            forall|pa: Paddr| #[trigger]
                old(model).meta_map.contains_key(pa as int) <==> {
                    &&& #[trigger] model.meta_map.contains_key(pa as int)
                    &&& res.0.start_paddr() != pa
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
    pub fn borrow_paddr(
        raw: Paddr,
        Tracked(alloc_model): Tracked<&AllocatorModel<PageTablePageMeta<C>>>,
    ) -> (res: Self)
        requires
            alloc_model.invariants(),
            alloc_model.meta_map.contains_key(raw as int),
            pa_is_valid_pt_address(raw as int),
            level_is_in_range::<C>(alloc_model.meta_map[raw as int].value().level as int),
        ensures
            res.deref().start_paddr() == raw,
            res.deref().meta_ptr_l == alloc_model.meta_map[raw as int].pptr(),
            res.wf(alloc_model),
            alloc_model.invariants(),
    {
        Self {
            inner: ManuallyDrop::new(
                PageTableNode::from_raw(raw, Tracked(alloc_model))
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
    pub open spec fn wf(&self, alloc_model: &AllocatorModel<PageTablePageMeta<C>>) -> bool {
        self.deref().wf(alloc_model)
    }

    // Actually should be checked after verification. Just can't be checked in pure Rust.
    pub fn make_guard_unchecked<'rcu>(
        self,
        _guard: &'rcu crate::task::DisabledPreemptGuard,
        Ghost(va): Ghost<Vaddr>,
    ) -> (res: PageTableGuard<'rcu, C>) where 'a: 'rcu
        ensures
            res.inner == self,
            res.va == va,
    {
        PageTableGuard { inner: self, va: Ghost(va) }
    }
}

pub struct PageTableGuard<'a, C: PageTableConfig> {
    pub inner: PageTableNodeRef<'a, C>,
    pub va: Ghost<Vaddr>,
}

impl<'a, C: PageTableConfig> PageTableGuard<'a, C> {
    pub open spec fn wf(&self, alloc_model: &AllocatorModel<PageTablePageMeta<C>>) -> bool {
        self.inner.wf(alloc_model)
    }

    #[verifier::allow_in_spec]
    pub fn paddr(&self) -> Paddr
        returns
            self.inner.start_paddr(),
    {
        self.inner.start_paddr()
    }

    pub fn level(
        &self,
        Tracked(alloc_model): Tracked<&AllocatorModel<PageTablePageMeta<C>>>,
    ) -> (res: PagingLevel)
        requires
            alloc_model.invariants(),
            alloc_model.meta_map.contains_key(self.inner.start_paddr() as int),
            alloc_model.meta_map[self.inner.start_paddr() as int].pptr() == self.inner.meta_ptr_l,
        returns
            self.level_spec(alloc_model),
    {
        self.inner.meta(Tracked(alloc_model)).level
    }

    pub open spec fn level_spec(
        &self,
        alloc_model: &AllocatorModel<PageTablePageMeta<C>>,
    ) -> PagingLevel {
        self.inner.meta_spec(alloc_model).level
    }

    #[verifier::external_body]
    fn unlock(self) {
        todo!()
    }

    pub fn into_raw_paddr(self: Self) -> Paddr where Self: Sized {
        self.paddr()
    }

    #[verifier::external_body]
    fn read_pte(&self, idx: usize, Tracked(spt): Tracked<&SubPageTable<C>>) -> (res: C::E) {
        let e = self.inner.ptr_l.read(Tracked(spt.perms.tracked_borrow(self.paddr()))).ptes[idx];
        // todo!("e -> usize -> C::E");
        let c_e = &e as *const _ as *const C::E;
        unsafe { (*c_e).clone() }
    }

    fn write_pte(
        &self,
        idx: usize,
        pte: C::E,
        level: PagingLevel,
        Tracked(spt): Tracked<&mut SubPageTable<C>>,
    )
        requires
            idx < nr_subpage_per_huge::<C>(),
            old(spt).wf(),
            old(spt).perms.contains_key(self.paddr()),
            self.wf(&old(spt).alloc_model),
            old(spt).i_ptes.value().contains_key(
                index_pte_paddr(self.paddr() as int, idx as int) as int,
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
        assert(spt.perms.contains_key(self.paddr()));
        assert(old(spt).i_ptes.value().contains_key(
            index_pte_paddr(self.paddr() as int, idx as int) as int,
        ));

        let p = PPtr::from_addr(self.paddr());

        assert(spt.perms.get(self.paddr()).unwrap().mem_contents().is_init());
        let tracked points_to = spt.perms.tracked_remove(self.paddr());

        assert(points_to.mem_contents().is_init());
        assert(points_to.pptr().addr() as int == self.paddr() as int);
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
            spt.perms.tracked_insert(self.paddr(), points_to);
        }

        assert(spt.wf());
    }

    #[verifier::external_body]
    pub fn meta(&self) -> &PageTablePageMeta<C> {
        unimplemented!("meta")
    }

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

/// The metadata of any kinds of page table pages.
/// Make sure the the generic parameters don't effect the memory layout.
// #[derive(Debug)] // TODO: Debug for PageTablePageMeta
pub struct PageTablePageMeta<C: PageTableConfig> {
    /// The lock for the page table page.
    pub lock: spin::queued::LockBody,
    /// The number of valid PTEs. It is mutable if the lock is held.
    // TODO: PCell or Cell?
    // pub nr_children: SyncUnsafeCell<u16>,
    pub nr_children: PCell<u16>,
    /// If the page table is detached from its parent.
    ///
    /// A page table can be detached from its parent while still being accessed,
    /// since we use a RCU scheme to recycle page tables. If this flag is set,
    /// it means that the parent is recycling the page table.
    pub astray: PCell<bool>,
    /// The level of the page table page. A page table page cannot be
    /// referenced by page tables of different levels.
    pub level: PagingLevel,
    pub _phantom: core::marker::PhantomData<C>,
}

impl<C: PageTableConfig> PageTablePageMeta<C> {
    pub fn new(level: PagingLevel) -> Self {
        Self {
            nr_children: PCell::new(0u16).0,
            astray: PCell::new(false).0,
            level,
            lock: spin::queued::LockBody::new(),
            _phantom: PhantomData,
        }
    }
}

// SAFETY: The layout of the `PageTablePageMeta` is ensured to be the same for
// all possible generic parameters. And the layout fits the requirements.
// unsafe
impl<C: PageTableConfig> AnyFrameMeta for PageTablePageMeta<C> {
    // TODO: Implement AnyFrameMeta for PageTablePageMeta

}

} // verus!
