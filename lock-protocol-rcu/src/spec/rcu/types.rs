use vstd::{prelude::*, seq::*};
use vstd_extra::{ghost_tree::Node, seq_extra::*};

use crate::mm::page_table::PageTableConfig;
use crate::mm::Paddr;
use crate::spec::{common::NodeId, node_helper};

verus! {

pub enum NodeState {
    Free,
    Locked,
    /// The node is locked outside lock protocols.
    /// It's unnecessary, but it can make the state machine clearer.
    LockedOutside,
}

pub enum PteState {
    Alive(Paddr),
    None,
}

pub ghost struct PteArrayState {
    pub inner: Seq<PteState>,
}

impl PteArrayState {
    pub open spec fn wf(&self) -> bool {
        self.inner.len() == 512
    }

    pub open spec fn empty() -> Self {
        Self { inner: Seq::new(512, |i: int| PteState::None) }
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
        self.inner[idx as int] is Alive
    }

    pub open spec fn get_paddr(&self, idx: nat) -> Paddr
        recommends
            self.is_alive(idx),
    {
        self.inner[idx as int]->Alive_0
    }

    pub open spec fn update(self, idx: nat, v: PteState) -> Self
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
    pub open spec fn wf<C: PageTableConfig>(&self) -> bool {
        match *self {
            Self::Void => true,
            Self::Locking(rt, nid) => {
                &&& node_helper::valid_nid::<C>(rt)
                &&& rt <= nid <= node_helper::next_outside_subtree::<C>(rt)
            },
            Self::Locked(rt) => node_helper::valid_nid::<C>(rt),
            // Self::UnLocking(rt, nid) => {
            //     &&& node_helper::valid_nid::<C>(rt)
            //     &&& rt <= nid <= node_helper::next_outside_subtree::<C>(rt)
            // },
        }
    }

    pub open spec fn locked_range<C: PageTableConfig>(&self) -> Set<NodeId> {
        match *self {
            Self::Void => Set::<NodeId>::empty(),
            Self::Locking(rt, nid) => Set::new(|id| rt <= id < nid),
            Self::Locked(rt) => Set::new(
                |id| rt <= id < node_helper::next_outside_subtree::<C>(rt),
            ),
        }
    }

    pub open spec fn root(&self) -> NodeId
        recommends
            *self !is Void,
    {
        match *self {
            Self::Void => arbitrary(),
            Self::Locking(rt, _) => rt,
            Self::Locked(rt) => rt,
        }
    }
}

pub enum AtomicCursorState {
    Void,
    Locked(NodeId),
}

} // verus!
