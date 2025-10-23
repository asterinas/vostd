use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr;

use vstd_extra::ownership::*;

use crate::prelude::*;

verus! {

/// A smart pointer to a page table node.
///
/// This smart pointer is an owner of a page table node. Thus creating and
/// dropping it will affect the reference count of the page table node. If
/// dropped it as the last reference, the page table node and subsequent
/// children will be freed.
///
/// [`PageTableNode`] is read-only. To modify the page table node, lock and use
/// [`PageTableGuard`].
pub type PageTableNode<C> = Frame<PageTablePageMeta<C>>;

impl<C: PageTableConfig> PageTableNode<C> {
    #[vstd::contrib::auto_spec]
    pub fn paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        ensures
    //            res % PAGE_SIZE() == 0,
    //            res < MAX_PADDR(),

    {
        self.ptr.addr()
    }/*    pub fn meta<'a>(
        &'a self,
        Tracked(p_slot): Tracked<&'a simple_pptr::PointsTo<MetaSlot>>,
        owner: MetaSlotOwner,
    ) -> (res: &PageTablePageMeta<C>)
        requires
            self.inv(),
            p_slot.pptr() == self.ptr,
            p_slot.is_init(),
            p_slot.value().wf(&owner),
            is_variant(owner.view().storage.value(), "PTNode"),
    {
        self.meta_pt(Tracked(p_slot), owner)
    }

    pub fn level(
        &self,
        Tracked(p_slot): Tracked<&simple_pptr::PointsTo<MetaSlot>>,
        owner: MetaSlotOwner,
    ) -> (res: PagingLevel)
        requires
            self.inv(),
            p_slot.pptr() == self.ptr,
            p_slot.is_init(),
            p_slot.value().wf(&owner),
            is_variant(owner.view().storage.value(), "PTNode"),
    {
        self.meta(Tracked(p_slot), owner).level
    }

    pub fn is_tracked(
        &self,
        Tracked(p_slot): Tracked<&simple_pptr::PointsTo<MetaSlot>>,
        Tracked(p_inner): Tracked<&cell::PointsTo<MetaSlotInner>>,
        Tracked(pt_inner): Tracked<&cell::PointsTo<PageTablePageMetaInner>>,
    ) -> (res: MapTrackingStatus)
        requires
            self.inv(),
            p_slot.pptr() == self.page.ptr,
            p_slot.is_init(),
            p_slot.value().wf(),
            p_inner.id() == p_slot.value()._inner.id(),
            p_inner.is_init(),
            is_variant(p_inner.value(), "_pt"),
            pt_inner.id() == p_slot.value().borrow_pt_spec(p_inner).inner.id(),
            pt_inner.is_init(),
    {
        let meta = self.meta(Tracked(p_slot), Tracked(p_inner));
        assume(meta.inner.id() == pt_inner.id());
        let inner = meta.inner.borrow(Tracked(pt_inner));
        inner.is_tracked
    }*/

}

} // verus!
