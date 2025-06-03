use vstd::prelude::*;
use vstd::cell::{PointsTo, PCell};
use vstd::atomic_ghost::*;
use vstd::atomic::PAtomicU32;

use super::*;

use core::mem::ManuallyDrop;
use core::ops::Deref;

#[allow(unused_imports)]
use vstd_extra::manually_drop::*;

verus! {

#[repr(C)]
#[rustc_has_incoherent_inherent_impls]
pub union MetaSlotInner {
    pub _frame: ManuallyDrop<FrameMeta>,
    pub _pt: ManuallyDrop<PageTablePageMeta>,
}

pub tracked enum ActualUsage {
    Unused(PointsTo<MetaSlotInner>),
    Used(PageUsage),
}

struct_with_invariants! {
#[rustc_has_incoherent_inherent_impls]
#[repr(C, align(16))]
pub struct MetaSlot {
    pub _inner: PCell<MetaSlotInner>,
    pub usage: AtomicU8<_, ActualUsage, _>,
    pub ref_count: PAtomicU32,
}

pub open spec fn wf(&self) -> bool {
    invariant on usage with (_inner) is (v: u8, g: ActualUsage) {
        match g {
            ActualUsage::Unused(perm) => {
            &&& v == 0
            &&& perm.id() == _inner.id()
            &&& perm.is_uninit()
            },
            ActualUsage::Used(usage) => {
            &&& v == usage.as_u8()
            &&& v != 0
            },
        }
    }
}

}

impl MetaSlotInner {

    pub open spec fn borrow_pt_spec(& self) -> & PageTablePageMeta
    {
        &manually_drop_unwrap(get_union_field::<MetaSlotInner, ManuallyDrop<PageTablePageMeta>>(*self, "_pt"))
    }

    #[verifier::external_body]
    pub fn borrow_pt(&self)
        -> (res: &PageTablePageMeta)
        ensures
            res == self.borrow_pt_spec(),
    {
        unsafe {
            self._pt.deref()
        }
    }

    pub open spec fn borrow_frame_spec(&self) -> & FrameMeta
    {
        &manually_drop_unwrap(get_union_field::<MetaSlotInner, ManuallyDrop<FrameMeta>>(*self, "_frame"))
    }

    #[verifier::external_body]
    pub fn borrow_frame(&self)
        -> (res: &FrameMeta)
        ensures
            res == self.borrow_frame_spec(),
    {
        unsafe {
            self._frame.deref()
        }
    }
}

impl MetaSlot {

    pub open spec fn borrow_pt_spec<'a>(&'a self, inner_perm: &'a PointsTo<MetaSlotInner>) -> &'a PageTablePageMeta
        recommends
            inner_perm.is_init(),
            is_variant(inner_perm.value(), "_pt"),
    {
        &manually_drop_unwrap(get_union_field::<MetaSlotInner, ManuallyDrop<PageTablePageMeta>>(inner_perm.value(), "_pt"))
    }

    pub fn borrow_pt<'a>(&'a self,
        inner_perm: Tracked<&'a PointsTo<MetaSlotInner>>)
        -> (res: &'a PageTablePageMeta)
        requires
            //self.wf(),
            self._inner.id() == inner_perm@.id(),
            inner_perm@.is_init(),
            is_variant(inner_perm@.value(), "_pt"),
        ensures
            res == self.borrow_pt_spec(inner_perm@),
    {
        let inner: &MetaSlotInner = self._inner.borrow(inner_perm);
        assert(is_variant(inner, "_pt"));
        inner.borrow_pt()
    }

    pub open spec fn borrow_frame_spec<'a>(&'a self, inner_perm: &'a PointsTo<MetaSlotInner>) -> &'a FrameMeta
        recommends
            inner_perm.is_init(),
            is_variant(inner_perm.value(), "_frame"),
    {
        &manually_drop_unwrap(get_union_field::<MetaSlotInner, ManuallyDrop<FrameMeta>>(inner_perm.value(), "_frame"))
    }

    pub fn borrow_frame<'a>(&'a self,
        Tracked(inner_perm): Tracked<&'a PointsTo<MetaSlotInner>>)
        -> (res: &'a FrameMeta)
        requires
            //self.wf(),
            self._inner.id() == inner_perm.id(),
            inner_perm.is_init(),
            is_variant(inner_perm.value(), "_frame"),
        ensures
            res == self.borrow_frame_spec(inner_perm),
    {
        let inner: &MetaSlotInner = self._inner.borrow(Tracked(inner_perm));
        assert(is_variant(inner, "_frame"));
        inner.borrow_frame()
    }

}

} // verus!

verus! {
impl Default for MetaSlotInner {
    #[verifier::external_body]
    fn default() -> Self {
        Self {
            _frame: ManuallyDrop::new(FrameMeta::default()),
        }
    }
}
}
