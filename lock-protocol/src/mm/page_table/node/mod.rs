pub mod child;
pub mod entry;

use std::cell::Cell;
use std::cell::SyncUnsafeCell;
use std::marker::PhantomData;
use std::ops::Range;

use entry::Entry;
use vstd::cell::PCell;
use vstd::prelude::*;

#[allow(unused_imports)]
use child::*;
use vstd::simple_pptr::MemContents;
use vstd::simple_pptr::PPtr;
use vstd::simple_pptr::PointsTo;
use crate::mm::frame;
use crate::mm::meta::AnyFrameMeta;
use crate::mm::nr_subpage_per_huge;
use crate::mm::page_prop::PageProperty;
use crate::mm::page_size_spec;
use crate::mm::Paddr;
use crate::mm::PageTableEntryTrait;
use crate::mm::PagingConstsTrait;
use crate::mm::PagingConsts;

use crate::mm::frame::{
    Frame, FrameRef,
    allocator::{AllocatorModel, pa_is_valid_kernel_address},
};
use crate::mm::PagingLevel;

use crate::mm::Vaddr;
use crate::sync::spin;
// TODO: Use a generic style?
use crate::x86_64::paddr_to_vaddr;

use crate::exec::{
    self, MAX_FRAME_NUM, get_pte_from_addr_spec, SIZEOF_PAGETABLEENTRY, frame_addr_to_index,
    frame_addr_to_index_spec, MockPageTableEntry, MockPageTablePage,
};
use crate::spec::sub_pt::{pa_is_valid_pt_address, SubPageTable, level_is_in_range, index_pte_paddr};

use crate::mm::NR_ENTRIES;

use super::cursor::spec_helpers;
use super::PageTableConfig;

verus! {

// #[derive(Debug)] // TODO: Debug for PageTableNode
pub type PageTableNode<C: PageTableConfig> = Frame<PageTablePageMeta<C>>;

impl<C: PageTableConfig> PageTableNode<C> {
    pub open spec fn wf(&self, alloc_model: &AllocatorModel<PageTablePageMeta<C>>) -> bool {
        &&& pa_is_valid_pt_address(self.paddr() as int)
        &&& level_is_in_range::<C>(self.level_spec(alloc_model) as int)
        &&& alloc_model.meta_map.contains_key(self.paddr() as int)
        &&& alloc_model.meta_map[self.paddr() as int].pptr() == self.meta_ptr
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
            alloc_model.meta_map[self.start_paddr() as int].pptr() == self.meta_ptr,
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

    pub fn alloc(
        level: PagingLevel,
        Tracked(model): Tracked<&mut AllocatorModel<PageTablePageMeta<C>>>,
    ) -> (res: (Self, Tracked<PointsTo<MockPageTablePage>>))
        requires
            old(model).invariants(),
            crate::spec::sub_pt::level_is_in_range::<C>(level as int),
        ensures
            res.1@.pptr() == res.0.ptr,
            res.1@.mem_contents().is_init(),
            pa_is_valid_kernel_address(res.0.start_paddr() as int),
            model.invariants(),
            !old(model).meta_map.contains_key(res.0.start_paddr() as int),
            model.meta_map.contains_key(res.0.start_paddr() as int),
            model.meta_map[res.0.start_paddr() as int].pptr() == res.0.meta_ptr,
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
                old(model).meta_map.contains_key(pa as int)
                    ==> #[trigger] model.meta_map.contains_key(pa as int),
            forall|p: Paddr| #[trigger]
                old(model).meta_map.contains_key(p as int) ==> {
                    &&& #[trigger] model.meta_map.contains_key(p as int)
                    &&& (#[trigger] model.meta_map[p as int]).pptr() == (#[trigger] old(
                        model,
                    ).meta_map[p as int]).pptr()
                    &&& model.meta_map[p as int].value() == old(model).meta_map[p as int].value()
                },
    {
        crate::exec::alloc_page_table(level, Tracked(model))
    }
}

pub type PageTableNodeRef<'a, C: PageTableConfig> = FrameRef<'a, PageTablePageMeta<C>>;

impl<'a, C: PageTableConfig> PageTableNodeRef<'a, C> {
    // Actually should be checked after verification. Just can't be checked in pure Rust.
    pub fn make_guard_unchecked<'rcu>(
        self,
        _guard: &'rcu crate::task::DisabledPreemptGuard,
        Ghost(va): Ghost<Vaddr>,
    ) -> (res: PageTableGuard<'rcu, C>) where 'a: 'rcu
        ensures
            res.inner == self,
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
        &&& self.inner.wf(alloc_model)
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
            alloc_model.meta_map[self.inner.start_paddr() as int].pptr() == self.inner.meta_ptr,
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
        let e = self.inner.ptr.read(Tracked(spt.perms.tracked_borrow(self.paddr()))).ptes[idx];
        todo!("e -> usize -> C::E");
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
