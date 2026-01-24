use vstd::prelude::*;

use vstd::cell;
use vstd::simple_pptr::*;

use crate::mm::frame::meta::MetaSlot;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::kspace::{FRAME_METADATA_RANGE, VMALLOC_BASE_VADDR, LINEAR_MAPPING_BASE_VADDR};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE, CONST_NR_ENTRIES, MAX_NR_PAGES, MAX_PADDR};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::frame::mapping::{meta_to_frame, META_SLOT_SIZE};
use crate::specs::mm::page_table::GuardPerm;

use vstd_extra::cast_ptr::Repr;
use vstd_extra::ownership::*;
use vstd_extra::array_ptr;

verus! {

pub tracked struct PageMetaOwner {
    pub nr_children: vstd::cell::PointsTo<u16>,
    pub stray: vstd::cell::PointsTo<bool>,
}

impl Inv for PageMetaOwner {
    open spec fn inv(self) -> bool {
        &&& self.nr_children.is_init()
        &&& 0 <= self.nr_children.value() <= NR_ENTRIES()
        &&& self.stray.is_init()
    }
}

pub ghost struct PageMetaModel {
    pub nr_children: u16,
    pub stray: bool,
}

impl Inv for PageMetaModel {
    open spec fn inv(self) -> bool {
        true
    }
}

impl View for PageMetaOwner {
    type V = PageMetaModel;

    open spec fn view(&self) -> <Self as View>::V {
        PageMetaModel { nr_children: self.nr_children.value(), stray: self.stray.value() }
    }
}

impl InvView for PageMetaOwner {
    proof fn view_preserves_inv(self) {
    }
}

impl<C: PageTableConfig> OwnerOf for PageTablePageMeta<C> {
    type Owner = PageMetaOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.nr_children.id() == owner.nr_children.id()
        &&& self.stray.id() == owner.stray.id()
    }
}

pub tracked struct NodeOwner<C: PageTableConfig> {
    pub meta_own: PageMetaOwner,
    pub meta_perm: vstd_extra::cast_ptr::PointsTo<MetaSlot, PageTablePageMeta<C>>,
    pub children_perm: array_ptr::PointsTo<C::E, CONST_NR_ENTRIES>,
}

impl<C: PageTableConfig> Inv for NodeOwner<C> {
    open spec fn inv(self) -> bool {
        &&& self.meta_perm.points_to.is_init()
        &&& <PageTablePageMeta<C> as Repr<MetaSlot>>::wf(self.meta_perm.points_to.value())
        &&& self.meta_perm.addr() == self.meta_perm.points_to.addr()
        &&& self.meta_own.inv()
        &&& self.meta_perm.value().wf(self.meta_own)
        &&& self.meta_perm.is_init()
        &&& self.meta_perm.wf()
        &&& FRAME_METADATA_RANGE().start <= self.meta_perm.addr() < FRAME_METADATA_RANGE().end
        &&& self.meta_perm.addr() % META_SLOT_SIZE() == 0
        &&& meta_to_frame(self.meta_perm.addr()) < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR()
        &&& meta_to_frame(self.meta_perm.addr()) < MAX_PADDR()
        &&& meta_to_frame(self.meta_perm.addr()) == self.children_perm.addr()
        &&& self.meta_own.nr_children.id() == self.meta_perm.value().nr_children.id()
        &&& 0 <= self.meta_own.nr_children.value() <= NR_ENTRIES()
    }
}

impl<'rcu, C: PageTableConfig> NodeOwner<C> {
    pub open spec fn relate_guard_perm(self, guard_perm: GuardPerm<'rcu, C>) -> bool {
        &&& guard_perm.is_init()
        &&& guard_perm.value().inner.inner@.ptr.addr() == self.meta_perm.addr()
        &&& guard_perm.value().inner.inner@.ptr.addr() == self.meta_perm.points_to.addr()
        &&& guard_perm.value().inner.inner@.wf(self)
        &&& self.meta_perm.is_init()
        &&& self.meta_perm.wf()
    }
}

pub ghost struct NodeModel<C: PageTableConfig> {
    pub meta: PageTablePageMeta<C>,
}

impl<C: PageTableConfig> Inv for NodeModel<C> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<C: PageTableConfig> View for NodeOwner<C> {
    type V = NodeModel<C>;

    open spec fn view(&self) -> <Self as View>::V {
        NodeModel { meta: self.meta_perm.value() }
    }
}

impl<C: PageTableConfig> InvView for NodeOwner<C> {
    proof fn view_preserves_inv(self) {
    }
}

impl<C: PageTableConfig> OwnerOf for PageTableNode<C> {
    type Owner = NodeOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.ptr.addr() == owner.meta_perm.addr()
    }
}

} // verus!
