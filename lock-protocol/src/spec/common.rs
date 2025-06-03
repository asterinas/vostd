use std::path;

use builtin::*;
use builtin_macros::*;
use vstd::{prelude::*, seq::*};
use vstd_extra::ghost_tree::Node;

use crate::spec::utils::*;

verus! {

pub type CpuId = nat;

pub type NodeId = nat;

pub open spec fn valid_cpu(cpu_num: CpuId, cpu: CpuId) -> bool {
    0 <= cpu < cpu_num
}

pub open spec fn valid_pte_offset(offset: nat) -> bool {
    0 <= offset < 512
}

pub open spec fn wf_tree_path(path: Seq<NodeId>) -> bool {
    if path.len() == 0 {
        true
    } else {
        &&& path[0] == NodeHelper::root_id()
        &&& forall|i: int|
            1 <= i < path.len() ==> NodeHelper::is_child(path[i - 1], #[trigger] path[i])
        &&& forall|i: int| 0 <= i < path.len() ==> #[trigger] NodeHelper::valid_nid(path[i])
    }
}

} // verus!
verus! {

pub enum NodeState {
    UnAllocated,
    WriteUnLocked,
    WriteLocked,
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
}

pub proof fn lemma_wf_tree_path_nid_increasing(path: Seq<NodeId>)
    requires
        wf_tree_path(path),
    ensures
        forall|i: int, j: int|
            #![trigger path[i],path[j]]
            0 <= i < j < path.len() ==> path[i] < path[j],
    decreases path.len(),
{
    if path.len() == 0 {
    } else if path.len() == 1 {
    } else {
        assert forall|i: int, j: int| 0 <= i < j < path.len() implies path[i] < path[j] by {
            assert forall|i: int, j: int| 0 <= i < j < path.len() - 1 implies path[i] < path[j] by {
                lemma_wf_tree_path_nid_increasing(path.drop_last());
                assert(path[i] == path.drop_last()[i]);
                assert(path[j] == path.drop_last()[j]);
            }
            admit();
        }
    }
}

pub proof fn lemma_wf_tree_path_inversion(path: Seq<NodeId>)
    requires
        wf_tree_path(path),
    ensures
        path.len() > 0 ==> {
            &&& path[0] == NodeHelper::root_id()
            &&& wf_tree_path(path.drop_last())
            &&& !path.drop_last().contains(path.last())
        },
{
    if path.len() == 0 {
    } else {
        lemma_wf_tree_path_nid_increasing(path);
    }
}

pub proof fn lemma_wf_tree_path_push_inversion(path: Seq<NodeId>, nid: NodeId)
    requires
        wf_tree_path(path.push(nid)),
    ensures
        wf_tree_path(path),
        path.len() > 0 ==> NodeHelper::is_child(path.last(), nid),
        !path.contains(nid),
{
    lemma_wf_tree_path_inversion(path.push(nid));
    if (path.len() > 0) {
        assert(path.push(nid).drop_last() =~= path);
    }
}

pub enum AtomicCursorState {
    Void,
    Locked(NodeId),
}

pub enum NodeStability {
    Stable,
    Instable,
}

} // verus!
