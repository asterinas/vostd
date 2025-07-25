use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

use crate::spec::{common::*, utils::*};
use super::types::*;
use vstd::{set::*, set_lib::*, map_lib::*};
use vstd_extra::{seq_extra::*, set_extra::*, map_extra::*};

tokenized_state_machine! {

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

#[invariant]
pub fn inv_pt_node_pte_relationship(&self) -> bool {
    forall |nid: NodeId| #![auto]
        NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() ==> {
            self.nodes.dom().contains(nid) <==> {
                let pa = NodeHelper::get_parent(nid);
                let offset = NodeHelper::get_offset(nid);

                self.ptes.dom().contains(pa) &&
                self.ptes[pa].is_alive(offset)
            }
        }
}

init!{
    initialize(cpu_num: CpuId) {
        require(cpu_num > 0);

        init cpu_num = cpu_num;
        init nodes = Map::new(
            |nid| nid == NodeHelper::root_id(),
            |nid| NodeState::Free,
        );
        init ptes = Map::new(
            |nid| nid == NodeHelper::root_id(),
            |nid| PteState::empty(),
        );
        init cursors = Map::new(
            |cpu| valid_cpu(cpu_num, cpu),
            |cpu| CursorState::Void,
        );
    }
}

transition!{
    protocol_lock_start(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove cursors -= [ cpu => CursorState::Void ];
        add cursors += [ cpu => CursorState::Locking(nid, nid) ];
    }
}

transition!{
    protocol_lock(cpu: CpuId, nid: NodeId) {
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
    protocol_lock_skip(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        remove cursors -= [ cpu => let CursorState::Locking(rt, _nid) ];
        require(_nid == nid);
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have ptes >= [ pa => let pte ];
        require(pte.is_void(offset));
        add cursors += [ cpu => CursorState::Locking(rt, NodeHelper::next_outside_subtree(nid)) ];
    }
}

transition!{
    protocol_lock_end(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => let CursorState::Locking(rt, nid) ];
        require(nid == NodeHelper::next_outside_subtree(rt));
        add cursors += [ cpu => CursorState::Locked(rt) ];
    }
}

transition!{
    protocol_unlock_start(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => let CursorState::Locked(rt) ];
        add cursors += [ cpu => CursorState::Locking(rt, NodeHelper::next_outside_subtree(rt)) ];
    }
}

transition!{
    protocol_unlock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove cursors -= [ cpu => let CursorState::Locking(rt, _nid) ];
        require(_nid > rt);
        require(_nid == nid + 1);
        add cursors += [ cpu => CursorState::Locking(rt, nid) ];

        remove nodes -= [ nid => NodeState::Locked ];
        add nodes += [ nid => NodeState::Free ];
    }
}

transition!{
    protocol_unlock_skip(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        remove cursors -= [ cpu => let CursorState::Locking(rt, _nid) ];
        require(_nid == NodeHelper::next_outside_subtree(nid));
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have ptes >= [ pa => let pte ];
        require(pte.is_void(offset));
        add cursors += [ cpu => CursorState::Locking(rt, nid) ];
    }
}

transition!{
    protocol_unlock_end(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => let CursorState::Locking(rt, nid) ];
        require(rt == nid);
        add cursors += [ cpu => CursorState::Void ];
    }
}

transition!{
    protocol_allocate(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have nodes >= [ pa => NodeState::Locked ];
        remove ptes -= [ pa => let pte ];
        require(pte.is_void(offset));
        add ptes += [ pa => pte.update(offset, Some(())) ];
        add nodes += [ nid => NodeState::Free ];
        add ptes += [ nid => PteState::empty() ];
    }
}

transition!{
    // TODO
    protocol_deallocate(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());
    }
}

/// Lock a node outside the lock protocol.
/// Necessary for rcu version.
transition!{
    normal_lock(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));

        remove nodes -= [ nid => NodeState::Free ];
        add nodes += [ nid => NodeState::LockedOutside ];
    }
}

transition!{
    normal_unlock(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));

        remove nodes -= [ nid => NodeState::Locked ];
        add nodes += [ nid => NodeState::Free ];
    }
}

transition!{
    normal_allocate(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have nodes >= [ pa => NodeState::LockedOutside ];
        remove ptes -= [ pa => let pte ];
        require(pte.is_void(offset));
        add ptes += [ pa => pte.update(offset, Some(())) ];
        add nodes += [ nid => NodeState::Free ];
        add ptes += [ nid => PteState::empty() ];
    }
}

transition!{
    // TODO
    normal_deallocate(nid: NodeId) {}
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: CpuId) { admit(); }

#[inductive(protocol_lock_start)]
fn protocol_lock_start_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(protocol_lock)]
fn protocol_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(protocol_lock_skip)]
fn protocol_lock_skip_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(protocol_lock_end)]
fn protocol_lock_end_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(protocol_unlock_start)]
fn protocol_unlock_start_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(protocol_unlock)]
fn protocol_unlock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(protocol_unlock_skip)]
fn protocol_unlock_skip_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(protocol_unlock_end)]
fn protocol_unlock_end_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(protocol_allocate)]
fn protocol_allocate_inductive(pre: Self, post: Self, nid: NodeId) { admit(); }

#[inductive(protocol_deallocate)]
fn protocol_deallocate_inductive(pre: Self, post: Self, nid: NodeId) {}

#[inductive(normal_lock)]
fn normal_lock_inductive(pre: Self, post: Self, nid: NodeId) {}

#[inductive(normal_unlock)]
fn normal_unlock_inductive(pre: Self, post: Self, nid: NodeId) {}

#[inductive(normal_allocate)]
fn normal_allocate_inductive(pre: Self, post: Self, nid: NodeId) { admit(); }

#[inductive(normal_deallocate)]
fn normal_deallocate_inductive(pre: Self, post: Self, nid: NodeId) {}

}

}
