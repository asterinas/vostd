use std::collections::HashMap;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::hash_map::*;
use vstd::tokens::*;
use vstd::atomic_ghost::*;

use crate::spec::utils::*;
use super::super::spec::{common::*, tree::*};
use super::{common::*, types::*, frame::*};

verus! {

struct_with_invariants!{

pub tracked struct PageTableNode {
    pub nid: NodeId,
    // pub childs: Seq<Option<NodeId>>,
    pub tokens: Option<(NodeToken, RcToken)>,
    pub inst: SpecInstance,
}

pub open spec fn inv(&self) -> bool {
    predicate {
        &&& NodeHelper::valid_nid(self.nid)

        &&& self.tokens.is_Some() ==> {
            &&& self.tokens.get_Some_0().0.instance_id() == self.inst.id()
            &&& self.tokens.get_Some_0().0.key() == self.nid
            &&& self.tokens.get_Some_0().0.value() is UnAllocated

            &&& self.tokens.get_Some_0().1.instance_id() == self.inst.id()
            &&& self.tokens.get_Some_0().1.key() == self.nid
            &&& self.tokens.get_Some_0().1.value() == 0
        }

        &&& self.inst.cpu_num() == GLOBAL_CPU_NUM
    }
}

}

struct_with_invariants!{

pub struct PageTable {
    pub nodes: Vec<AtomicU64<_, PageTableNode, _>>,
    pub inst: Tracked<SpecInstance>,
}

pub open spec fn wf(&self, allocator: FrameAllocator) -> bool {
    predicate {
        &&& self.nodes@.len() == NodeHelper::total_size()

        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
    }

    invariant on nodes with (inst)
        forall |nid: NodeId| where (NodeHelper::valid_nid(nid))
        specifically (self.nodes@[nid as int])
        is (pa: u64, g: PageTableNode)
    {
        &&& g.inv()

        &&& g.nid == nid
        &&& g.inst.id() == inst@.id()

        &&& pa == INVALID_PADDR <==> g.tokens.is_Some()
        &&& pa != INVALID_PADDR ==> {
            &&& valid_paddr(pa)
            &&& paddr_is_aligned(pa)
            // &&& allocator.usages@[pa_to_fid(pa)].is_PageTable()
            // &&& allocator.get_pt_frame_from_pa_spec(pa).nid@ == nid
            // &&& allocator.get_pt_frame_from_pa_spec(pa).inst@.id() == inst@.id()
        }
    }
}

}

impl PageTable {

}

} // verus!
