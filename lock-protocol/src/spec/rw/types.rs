use vstd::{prelude::*, seq::*};

use crate::spec::{common::*, utils::*};
use super::wf_tree_path::*;
use vstd_extra::{ghost_tree::Node, seq_extra::*};

verus! {

pub enum NodeState {
    WriteUnLocked,
    WriteLocked,
    InProtocolWriteLocked,
}

impl NodeState {
    pub open spec fn is_write_locked(&self) -> bool {
        self is WriteLocked || self is InProtocolWriteLocked
    }
}

pub enum PteState {
    Alive,
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
    ReadLocking(Seq<NodeId>),
    WriteLocked(Seq<NodeId>),
}

impl CursorState {
    pub open spec fn inv(&self) -> bool {
        match *self {
            Self::Void => true,
            Self::ReadLocking(path) => {
                &&& 0 <= path.len() <= 3
                &&& wf_tree_path(path)
            },
            Self::WriteLocked(path) => {
                &&& 1 <= path.len() <= 4
                &&& wf_tree_path(path)
            },
        }
    }

    pub open spec fn get_path(&self) -> Seq<NodeId>
        recommends
            self.inv(),
    {
        match *self {
            Self::Void => Seq::empty(),
            Self::ReadLocking(path) | Self::WriteLocked(path) => path,
        }
    }

    pub open spec fn hold_write_lock(&self) -> bool
        recommends
            self.inv(),
    {
        match *self {
            Self::Void | Self::ReadLocking(_) => false,
            Self::WriteLocked(_) => true,
        }
    }

    pub open spec fn get_write_lock_node(&self) -> NodeId
        recommends
            self.inv(),
            self.hold_write_lock(),
    {
        match *self {
            Self::Void | Self::ReadLocking(_) => arbitrary(),
            Self::WriteLocked(path) => path.last(),
        }
    }

    pub open spec fn get_read_lock_path(&self) -> Seq<NodeId>
        recommends
            self.inv(),
    {
        match *self {
            Self::Void => Seq::empty(),
            Self::ReadLocking(path) => path,
            Self::WriteLocked(path) => path.drop_last(),
        }
    }

    pub open spec fn hold_read_lock(&self, nid: NodeId) -> bool
        recommends
            self.inv(),
            NodeHelper::valid_nid(nid),
    {
        let path = self.get_read_lock_path();
        path.contains(nid)
    }

    pub proof fn lemma_get_read_lock_path_is_prefix_of_get_path(&self)
        requires
            self.inv(),
        ensures
            self.get_read_lock_path().is_prefix_of(self.get_path()),
    {
    }
}

pub enum AtomicCursorState {
    Void,
    Locked(NodeId),
}

} // verus!
