use vstd::prelude::*;
use vstd::simple_pptr;
use vstd::cell;

use crate::prelude::*;

verus! {

#[rustc_has_incoherent_inherent_impls]
pub struct PageTableNode {
    pub page: Page<PageTablePageMeta>,
}

impl PageTableNode {
    pub open spec fn inv(self) -> bool {
        self.page.inv_ptr() && self.page.paddr() < VMALLOC_BASE_VADDR()
            - LINEAR_MAPPING_BASE_VADDR()
    }

    pub open spec fn paddr_spec(&self) -> Paddr {
        self.page.paddr()
    }

    #[verifier::when_used_as_spec(paddr_spec)]
    pub fn paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        ensures
            res == self.paddr_spec(),
            res % PAGE_SIZE() == 0,
            res < MAX_PADDR(),
    {
        self.page.paddr()
    }

    pub fn meta<'a>(
        &'a self,
        Tracked(p_slot): Tracked<&'a simple_pptr::PointsTo<MetaSlot>>,
        Tracked(p_inner): Tracked<&'a cell::PointsTo<MetaSlotInner>>,
    ) -> (res: &'a PageTablePageMeta)
        requires
            self.inv(),
            p_slot.pptr() == self.page.ptr,
            p_slot.is_init(),
            p_slot.value().wf(),
            p_inner.id() == p_slot.value()._inner.id(),
            p_inner.is_init(),
            is_variant(p_inner.value(), "_pt"),
    {
        self.page.meta_pt(Tracked(p_slot), Tracked(p_inner))
    }

    pub fn level(
        &self,
        Tracked(p_slot): Tracked<&simple_pptr::PointsTo<MetaSlot>>,
        Tracked(p_inner): Tracked<&cell::PointsTo<MetaSlotInner>>,
        Tracked(pt_inner): Tracked<&cell::PointsTo<PageTablePageMetaInner>>,
    ) -> (res: PagingLevel)
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
        inner.level
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
    }
}

} // verus!
