use builtin::*;
use builtin_macros::*;
use vstd::{prelude::*, seq::*};

use crate::spec::{common::*, utils::*};
use vstd_extra::{ghost_tree::Node, seq_extra::*};

verus! {

pub enum NodeState {
    Free,
    Locked,
}

pub ghost struct PteState {
    pub inner: Seq<Option<()>>,
}

impl PteState {
    pub open spec fn wf(&self) -> bool {
        self.inner.len() == 512
    }

    pub open spec fn empty() -> Self {
        Self { inner: Seq::new(512, |i: int| None) }
    }

    pub open spec fn is_void(&self, idx: nat) -> bool
        recommends
            self.wf(),
            0 <= idx < 512,
    {
        self.inner[idx as int] is None
    }

    pub open spec fn is_alive(&self, idx: nat) -> bool
        recommends
            self.wf(),
            0 <= idx < 512,
    {
        self.inner[idx as int] is Some
    }

    pub open spec fn update(self, idx: nat, v: Option<()>) -> Self
        recommends
            self.wf(),
            0 <= idx < 512,
    {
        Self { inner: self.inner.update(idx as int, v) }
    }
}

pub enum CursorState {
    Void,
    Locking(NodeId, NodeId),
    Locked(NodeId),
    // UnLocking(NodeId, NodeId),
}

impl CursorState {
    pub open spec fn wf(&self) -> bool {
        match *self {
            Self::Void => true,
            Self::Locking(rt, nid) => {
                &&& NodeHelper::valid_nid(rt)
                &&& rt <= nid <= NodeHelper::next_outside_subtree(rt)
            },
            Self::Locked(rt) => NodeHelper::valid_nid(rt),
            // Self::UnLocking(rt, nid) => {
            //     &&& NodeHelper::valid_nid(rt)
            //     &&& rt <= nid <= NodeHelper::next_outside_subtree(rt)
            // },
        }
    }
}

} // verus!
