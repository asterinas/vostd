pub mod mapping;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::{PointsTo};

use crate::spec::{common::*, utils::*};
use super::super::{common::*, types::*};
use super::super::node::rwlock::PageTablePageRwLock;

pub use mapping::*;

verus! {

struct_with_invariants! {
    pub struct PageTablePageMeta {
        pub lock: PageTablePageRwLock,
        pub frame_paddr: Paddr,
        pub level: PagingLevel,
        pub nid: Ghost<NodeId>,
        pub inst: Tracked<SpecInstance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            &&& self.lock.wf()
            &&& self.frame_paddr == self.lock.paddr_spec()
            &&& self.level == self.lock.level_spec()
            &&& valid_paddr(self.frame_paddr)
            &&& 1 <= self.level <= 4
            &&& NodeHelper::valid_nid(self.nid@)
            &&& self.nid@ == self.lock.nid@
            &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
            &&& self.inst@.id() == self.lock.pt_inst_id()
            &&& self.level as nat == NodeHelper::nid_to_level(self.nid@)
        }
    }
}

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

    pub open spec fn wf(&self, meta_slot_array: &MetaSlotArray) -> bool {
        &&& 0 <= self.slot_idx < meta_slot_array.len()
        &&& self.relate(meta_slot_array.vec[self.slot_idx as int])
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

struct_with_invariants! {
    pub struct MetaSlotArray {
        pub vec: Vec<* const MetaSlot>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            &&& self.vec@.len() == GLOBAL_FRAME_NUM
        }
    }
}

impl MetaSlotArray {
    pub open spec fn len(&self) -> nat {
        self.vec@.len()
    }
}

} // verus!
