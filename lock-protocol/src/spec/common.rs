use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

pub type CpuId = nat;

pub type NodeId = nat;

pub open spec fn valid_cpu(cpu_num: CpuId, cpu: CpuId) -> bool {
    0 <= cpu < cpu_num
}

pub open spec fn valid_pos(size: nat, p: nat) -> bool {
    0 <= p < size
}

pub open spec fn valid_range(size: nat, l: nat, r: nat) -> bool {
    0 <= l < r <= size
}

pub open spec fn pos_in_range(l: nat, r: nat, p: nat) -> bool {
    l <= p < r
}

pub open spec fn valid_pte_offset(offset: nat) -> bool {
    0 <= offset < 512
}

} // verus!
verus! {

pub enum NodeState {
    Empty,
    EmptyLocked,
    Free,
    Locked,
    LockedOutside,
}

pub enum CursorState {
    Empty,
    Creating(NodeId, NodeId, NodeId),
    Hold(NodeId, NodeId),
    Destroying(NodeId, NodeId, NodeId),
}

impl CursorState {
    pub open spec fn inv(&self) -> bool {
        match *self {
            Self::Empty => true,
            Self::Creating(st, en, cur_nid) => st < en && st <= cur_nid <= en,
            Self::Hold(st, en) => st < en,
            Self::Destroying(st, en, cur_nid) => st < en && st <= cur_nid <= en,
        }
    }

    pub open spec fn get_locked_range(&self) -> (NodeId, NodeId) {
        match *self {
            CursorState::Empty => (arbitrary(), arbitrary()),
            CursorState::Creating(st, _, en)
            | CursorState::Hold(st, en)
            | CursorState::Destroying(st, _, en) => (st, en),
        }
    }

    pub open spec fn node_is_held(&self, nid: NodeId) -> bool {
        match *self {
            Self::Empty => false,
            Self::Creating(st, en, cur_nid) => st <= nid < cur_nid,
            Self::Hold(st, en) => st <= nid < en,
            Self::Destroying(st, en, cur_nid) => st <= nid < cur_nid,
        }
    }

    pub open spec fn node_is_not_held(&self, nid: NodeId) -> bool {
        !self.node_is_held(nid)
    }

    pub open spec fn no_overlap(&self, cursor: &CursorState) -> bool {
        match *self {
            Self::Empty => true,
            Self::Creating(st1, _, en1) | Self::Hold(st1, en1) | Self::Destroying(st1, _, en1) => {
                match *cursor {
                    Self::Empty => true,
                    Self::Creating(st2, _, en2)
                    | Self::Hold(st2, en2)
                    | Self::Destroying(st2, _, en2) => st1 == en1 || st2 == en2 || en1 <= st2 || en2
                        <= st1,
                }
            },
        }
    }
}

} // verus!
verus! {

#[is_variant]
pub enum SlotState {
    Empty,
    EmptyLocked,
    Free,
    Locked,
    LockedOutside,
}

#[is_variant]
pub enum RangeState {
    Empty,
    Creating(nat, nat, nat),
    Hold(nat, nat),
    Destroying(nat, nat, nat),
}

impl RangeState {
    pub open spec fn inv(&self) -> bool {
        match *self {
            Self::Empty => true,
            Self::Creating(l, r, cur_p) => l < r && l <= cur_p <= r,
            Self::Hold(l, r) => l < r,
            Self::Destroying(l, r, cur_p) => l < r && l <= cur_p <= r,
        }
    }

    pub open spec fn get_locked_range(&self) -> (nat, nat) {
        match *self {
            Self::Empty => (arbitrary(), arbitrary()),
            Self::Creating(l, _, r) | Self::Hold(l, r) | Self::Destroying(l, _, r) => (l, r),
        }
    }

    pub open spec fn pos_is_held(&self, p: nat) -> bool {
        match *self {
            Self::Empty => false,
            Self::Creating(l, r, cur_p) => l <= p < cur_p,
            Self::Hold(l, r) => l <= p < r,
            Self::Destroying(l, r, cur_p) => l <= p < cur_p,
        }
    }

    pub open spec fn pos_is_not_held(&self, p: nat) -> bool {
        !self.pos_is_held(p)
    }

    pub open spec fn no_overlap(&self, range: &RangeState) -> bool {
        match *self {
            Self::Empty => true,
            Self::Creating(l1, _, r1) | Self::Hold(l1, r1) | Self::Destroying(l1, _, r1) => {
                match *range {
                    Self::Empty => true,
                    Self::Creating(l2, _, r2)
                    | Self::Hold(l2, r2)
                    | Self::Destroying(l2, _, r2) => l1 == r1 || l2 == r2 || r1 <= l2 || r2 <= l1,
                }
            },
        }
    }
}

} // verus!
