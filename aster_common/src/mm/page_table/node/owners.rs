use vstd::prelude::*;

use vstd::cell;
use vstd::simple_pptr::*;

use super::*;

verus! {

pub tracked struct PageMetaOwner {
    pub nr_children: Tracked<vstd::cell::PointsTo<u16>>,
    pub stray: Tracked<vstd::cell::PointsTo<bool>>,
}

impl Inv for PageMetaOwner {
    open spec fn inv(self) -> bool {
        &&& self.nr_children@.is_init()
        &&& self.stray@.is_init()
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

impl InvView for PageMetaOwner {
    type V = PageMetaModel;

    open spec fn view(self) -> <Self as InvView>::V {
        PageMetaModel { nr_children: self.nr_children@.value(), stray: self.stray@.value() }
    }

    proof fn view_preserves_inv(self) {
    }
}

impl<C: PageTableConfig> OwnerOf for PageTablePageMeta<C> {
    type Owner = PageMetaOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.nr_children.id() == owner.nr_children@.id()
        &&& self.stray.id() == owner.stray@.id()
    }
}

pub tracked struct NodeOwner<C: PageTableConfig> {
    pub meta_own: PageMetaOwner,
    pub meta_perm: Tracked<vstd_extra::cast_ptr::PointsTo<MetaSlotStorage, PageTablePageMeta<C>>>,
}

impl<C: PageTableConfig> Inv for NodeOwner<C> {
    open spec fn inv(self) -> bool {
        &&& self.meta_perm@.points_to@.is_init()
        &&& <PageTablePageMeta<C> as Repr<MetaSlotStorage>>::wf(self.meta_perm@.points_to@.value())
        &&& self.meta_own.inv()
        &&& self.meta_perm@.value().wf(self.meta_own)
        &&& self.meta_perm@.is_init()
        &&& self.meta_perm@.wf()
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

impl<C: PageTableConfig> InvView for NodeOwner<C> {
    type V = NodeModel<C>;

    open spec fn view(self) -> <Self as InvView>::V {
        NodeModel { meta: self.meta_perm@.value() }
    }

    proof fn view_preserves_inv(self) {
    }
}

impl<C: PageTableConfig> OwnerOf for PageTableNode<C> {
    type Owner = NodeOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        true
    }
}

} // verus!
