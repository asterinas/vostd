use vstd::{prelude::*, seq::*};

use vstd_extra::{ghost_tree::Node, seq_extra::*};

use crate::{mm::page_table::PageTableConfig, spec::{common::NodeId, node_helper}};
use super::wf_tree_path;

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
    pub open spec fn inv<C: PageTableConfig>(&self) -> bool {
        match *self {
            Self::Void => true,
            Self::ReadLocking(path) => {
                &&& 0 <= path.len() <= 3
                &&& wf_tree_path::<C>(path)
            },
            Self::WriteLocked(path) => {
                &&& 1 <= path.len() <= 4
                &&& wf_tree_path::<C>(path)
            },
        }
    }

    pub open spec fn get_path<C: PageTableConfig>(&self) -> Seq<NodeId>
        recommends
            self.inv::<C>(),
    {
        match *self {
            Self::Void => Seq::empty(),
            Self::ReadLocking(path) | Self::WriteLocked(path) => path,
        }
    }

    pub open spec fn hold_write_lock<C: PageTableConfig>(&self) -> bool
        recommends
            self.inv::<C>(),
    {
        match *self {
            Self::Void | Self::ReadLocking(_) => false,
            Self::WriteLocked(_) => true,
        }
    }

    pub open spec fn get_write_lock_node<C: PageTableConfig>(&self) -> NodeId
        recommends
            self.inv::<C>(),
            self.hold_write_lock::<C>(),
    {
        match *self {
            Self::Void | Self::ReadLocking(_) => arbitrary(),
            Self::WriteLocked(path) => path.last(),
        }
    }

    pub open spec fn get_read_lock_path<C: PageTableConfig>(&self) -> Seq<NodeId>
        recommends
            self.inv::<C>(),
    {
        match *self {
            Self::Void => Seq::empty(),
            Self::ReadLocking(path) => path,
            Self::WriteLocked(path) => path.drop_last(),
        }
    }

    pub open spec fn hold_read_lock<C: PageTableConfig>(&self, nid: NodeId) -> bool
        recommends
            self.inv::<C>(),
            node_helper::valid_nid::<C>(nid),
    {
        let path = self.get_read_lock_path::<C>();
        path.contains(nid)
    }

    pub proof fn lemma_get_read_lock_path_is_prefix_of_get_path<C: PageTableConfig>(&self)
        requires
            self.inv::<C>(),
        ensures
            self.get_read_lock_path::<C>().is_prefix_of(self.get_path::<C>()),
    {
    }
}

pub enum AtomicCursorState {
    Void,
    Locked(NodeId),
}

} // verus!
