pub mod mapping;

use vstd::prelude::*;
use vstd::raw_ptr::{PointsTo};

use crate::spec::{common::*, utils::*};
use super::super::{common::*, types::*};
use super::super::node::PageTablePageMeta;

pub use mapping::*;

verus! {

pub enum MetaSlotType {
    PageTablePageMeta,
    Others,
}

struct_with_invariants! {
    pub struct MetaSlot {
        pub usage: MetaSlotType,
        pub inner: Option<PageTablePageMeta>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            &&& self.usage is PageTablePageMeta <==> self.inner is Some
            &&& self.inner is Some ==> self.inner->Some_0.wf()
        }
    }
}

impl MetaSlot {
    pub open spec fn is_pt(&self) -> bool {
        self.usage is PageTablePageMeta
    }

    pub open spec fn get_inner_pt_spec(&self) -> PageTablePageMeta
        recommends
            self.is_pt(),
    {
        self.inner->Some_0
    }

    pub fn get_inner_pt(&self) -> (res: &PageTablePageMeta)
        requires
            self.wf(),
            self.is_pt(),
        ensures
            *res =~= self.get_inner_pt_spec(),
    {
        self.inner.as_ref().unwrap()
    }
}

pub tracked struct MetaSlotPerm {
    pub inner: PointsTo<MetaSlot>,
    pub slot_idx: nat,
}

impl MetaSlotPerm {
    pub open spec fn relate(&self, ptr: *const MetaSlot) -> bool {
        &&& self.inner.ptr() == ptr
    }

    pub open spec fn wf(&self) -> bool {
        //&&& 0 <= self.slot_idx < meta_slot_array.len()
        //&&& self.relate(meta_slot_array.vec[self.slot_idx as int])
        &&& self.inner.is_init()
        &&& self.inner.value().wf()
        &&& self.inner.value().is_pt() ==> {
            &&& self.frame_paddr() == meta_to_frame(self.meta_vaddr())
            &&& frame_to_meta(self.frame_paddr()) == self.meta_vaddr()
        }
    }

    pub open spec fn is_pt(&self) -> bool {
        self.inner.value().is_pt()
    }

    pub open spec fn frame_paddr(&self) -> Paddr {
        self.inner.value().get_inner_pt_spec().frame_paddr
    }

    pub open spec fn meta_vaddr(&self) -> Vaddr {
        self.inner.ptr() as usize
    }

    pub open spec fn value(&self) -> MetaSlot {
        self.inner.value()
    }
}

} // verus!
