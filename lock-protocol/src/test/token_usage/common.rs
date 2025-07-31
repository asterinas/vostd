use super::super::super::spec::{common::*, utils::*};

verus! {

pub type Paddr = u64;

pub type Vaddr = u64;

pub type Level = u64;

pub open spec fn valid_paddr(paddr: Paddr) -> bool {
    true
}

// pub open spec fn va_level_to_trace_rec(vaddr: Vaddr, level: Level) -> Seq<nat>
//     decreases NodeHelper::level_to_dep(level as nat),
// {
//     if NodeHelper::level_to_dep(level as nat) == 0 { Seq::empty() }
//     else {
//         va_level_to_trace_rec(vaddr, level + 1).push((vaddr >> (level * 9)) & low_bits_mask(9))
//     }
// }
// pub open spec fn va_level_to_trace(vaddr: Vaddr, level: Level) -> Seq<nat> {
//     va_level_to_trace_rec(vaddr >> 12, level)
// }
// pub open spec fn va_level_to_nid(vaddr: Vaddr, level: Level) -> NodeId {
//     NodeHelper::trace_to_nid_from_root(va_level_to_trace(vaddr, level))
// }
pub tracked struct PagePerm {
    pub paddr: Paddr,
}

} // verus!
verus! {

impl CursorState {
    pub open spec fn trans_cursor_create_start(self, nid: NodeId) -> Self {
        Self::Creating(nid, NodeHelper::next_outside_subtree(nid), nid)
    }

    pub open spec fn trans_node_acquire(self, nid: NodeId) -> Self {
        Self::Creating(self.get_Creating_0(), self.get_Creating_1(), nid + 1)
    }

    pub open spec fn trans_node_acquire_skip(self, nid: NodeId) -> Self {
        Self::Creating(
            self.get_Creating_0(),
            self.get_Creating_1(),
            NodeHelper::next_outside_subtree(nid),
        )
    }

    pub open spec fn trans_cursor_create_end(self) -> Self {
        Self::Hold(self.get_Creating_0(), self.get_Creating_1())
    }

    pub open spec fn trans_cursor_destroy_start(self) -> Self {
        Self::Destroying(self.get_Hold_0(), self.get_Hold_1(), self.get_Hold_1())
    }

    pub open spec fn trans_node_release(self, nid: NodeId) -> Self {
        Self::Destroying(self.get_Destroying_0(), self.get_Destroying_1(), nid)
    }

    pub open spec fn trans_node_release_skip(self, nid: NodeId) -> Self {
        Self::Destroying(self.get_Destroying_0(), self.get_Destroying_1(), nid)
    }

    pub open spec fn trans_cursor_destroy_end(self) -> Self {
        Self::Empty
    }
}

} // verus!
