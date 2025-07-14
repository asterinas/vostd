use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

use super::common::*;
use crate::spec::utils::*;
use vstd::{set::*, set_lib::*, map_lib::*};
use vstd_extra::{seq_extra::*, set_extra::*, map_extra::*};

tokenized_state_machine!{

TreeSpec {

fields {
    #[sharding(constant)]
    pub cpu_num: CpuId,

    #[sharding(map)]
    pub nodes: Map<NodeId, NodeState>,

    #[sharding(map)]
    pub ptes: Map<NodeId, PteState>,

    #[sharding(map)]
    pub cursors: Map<CpuId, CursorState>,
}

#[invariant]
pub fn inv_pt_node_pte_array_relationship(&self) -> bool {
    forall |nid: NodeId| #![auto]
        self.nodes.dom().contains(nid) <==>
        self.ptes.dom().contains(nid)
}

init!{
    initialize(cpu_num: CpuId) {
        require(cpu_num > 0);

        init cpu_num = cpu_num;
        init nodes = Map::new(
            |nid| nid == NodeHelper::root_id(),
            |nid| NodeState::WriteUnLocked,
        );
        init cursors = Map::new(
            |cpu| valid_cpu(cpu_num, cpu),
            |cpu| CursorState::Void,
        );
    }
}

transition!{
    locking_start(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove cursors -= [ cpu => CursorState::Void ];
        add cursors += [ cpu => CursorState::Locking(nid, nid) ];
    }
}

transition!{
    lock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove cursors -= [ cpu => let CursorState::Locking(rt, _nid) ];
        require(NodeHelper::in_subtree_range(rt, _nid));
        require(_nid == nid);
        add cursors += [ cpu => CursorState::Locking(rt, nid + 1) ];

        remove nodes -= [ nid => NodeState::Free ];
        add nodes += [ nid => NodeState::Locked ];
    }
}

transition!{
    locking_skip(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        remove cursors -= [ cpu => let CursorState::Locking(rt, _nid) ];
        require(NodeHelper::in_subtree_range(rt, _nid));
        require(_nid == nid);
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have ptes >= [ pa => let pte ];
        require(pte.is_void(offset));
        add cursors += [ cpu => CursorState::Locking(rt, NodeHelper::next_outside_subtree(nid)) ];
    }
}

transition!{
    locking_end(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => let CursorState::Locking(rt, nid) ];
        require(nid == NodeHelper::next_outside_subtree(rt));
        add cursors += [ cpu => CursorState::Locked(rt) ];
    }
}

transition!{
    unlocking_start(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => CursorState::Locked(rt) ];
        add cursors += [ cpu => CursorState::Locking(rt, rt) ];
    }
}

transition!{
    unlock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove cursors -= [ cpu => let CursorState::UnLocking(rt, _nid) ];
        require(_nid > rt);
        require(_nid == nid + 1);
        add cursors += [ cpu => CursorState::UnLocking(rt, nid) ];

        remove nodes -= [ nid => NodeState::Locked ];
        add nodes += [ nid => NodeState::Free ];
    }
}

transition!{
    unlocking_skip(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        remove cursors -= [ cpu => let CursorState::UnLocking(rt, _nid) ];
        require(_nid > rt);
        require(_nid == NodeHelper::next_outside_subtree(nid));
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have ptes >= [ pa => let pte ];
        require(pte.is_void(offset));
        add cursors += [ cpu => CursorState::UnLocking(rt, nid) ];
    }
}

transition!{
    unlocking_end(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => let CursorState::UnLocking(rt, nid) ];
        require(rt == nid);
        add cursors += [ cpu => CursorState::Void ];
    }
}

transition!{
    allocate(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have nodes >= [ pa => NodeState::Locked ];
        remove ptes -= [ pa => let pte ];
        require(pte.is_void(offset));
        add ptes += [ pa => pte.update(offset, Some(())) ];
        add nodes += [ nid => NodeState::Free ];
        add ptes += [ nid => PteState::empty() ]; // TODO
    }
}

transition!{
    deallocate(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        // TODO
    }
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: CpuId) {}

#[inductive(locking_start)]
fn locking_start_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(lock)]
fn lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(locking_skip)]
fn locking_skip_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(locking_end)]
fn locking_end_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(unlocking_start)]
fn unlocking_start_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(unlock)]
fn unlock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(unlocking_skip)]
fn unlocking_skip(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(unlocking_end)]
fn unlocking_end_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(allocate)]
fn allocate_inductive(pre: Self, post: Self, nid: NodeId) {}

#[inductive(deallocate)]
fn deallocate_inductive(pre: Self, post: Self, nid: NodeId) {}

}

}