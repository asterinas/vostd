use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;
use vstd::multiset::*;

use crate::spec::{common::*, utils::*};
use super::types::*;
use vstd::{set::*, set_lib::*, map_lib::*};
use vstd_extra::{seq_extra::*, set_extra::*, map_extra::*};
use crate::mm::Paddr;

tokenized_state_machine! {

TreeSpec {

fields {
    #[sharding(constant)]
    pub cpu_num: CpuId,

    #[sharding(map)]
    pub nodes: Map<NodeId, NodeState>,

    #[sharding(map)]
    pub pte_arrays: Map<NodeId, PteArrayState>,

    #[sharding(map)]
    pub cursors: Map<CpuId, CursorState>,

    #[sharding(multiset)]
    pub strays: Multiset<(NodeId, StrayState)>,
}

#[invariant]
pub fn inv_pt_node_pte_array_relationship(&self) -> bool {
    forall |nid: NodeId| #![auto]
        self.nodes.dom().contains(nid) <==>
        self.pte_arrays.dom().contains(nid)
}

#[invariant]
pub fn inv_pt_node_pte_relationship(&self) -> bool {
    forall |nid: NodeId| #![auto]
        NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() ==> {
            self.nodes.dom().contains(nid) <==> {
                let pa = NodeHelper::get_parent(nid);
                let offset = NodeHelper::get_offset(nid);

                self.pte_arrays.dom().contains(pa) &&
                self.pte_arrays[pa].is_alive(offset)
            }
        }
}

#[invariant]
pub fn wf_strays(&self) -> bool {
    forall |pair: (NodeId, StrayState)|
        self.strays.contains(pair) ==> {
            &&& NodeHelper::valid_nid(pair.0)
            &&& pair.0 != NodeHelper::root_id()
        }
}

#[invariant]
pub fn inv_stray_at_most_one_false_per_node(&self) -> bool {
    forall |nid: NodeId|
        self.strays.filter(|pair: (NodeId, StrayState)| {
            &&& pair.0 == nid
            &&& pair.1 is False
        }).len() <= 1
}

#[invariant]
pub fn inv_pte_is_alive_iff_stray_has_false(&self) -> bool {
    forall |nid: NodeId| 
        NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() ==> {
            let pa = NodeHelper::get_parent(nid);
            let offset = NodeHelper::get_offset(nid);
            self.pte_arrays.dom().contains(pa) && self.pte_arrays[pa].is_alive(offset) <==>
            exists |pair: (NodeId, StrayState)| {
                &&& pair.0 == nid
                &&& pair.1 is False
                &&& pair.1->False_0 == self.pte_arrays[pa].get_paddr(offset)
                &&& self.strays.contains(pair)
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
        init pte_arrays = Map::new(
            |nid| nid == NodeHelper::root_id(),
            |nid| PteArrayState::empty(),
        );
        init cursors = Map::new(
            |cpu| valid_cpu(cpu_num, cpu),
            |cpu| CursorState::Void,
        );
        init strays = Multiset::empty();
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
        have pte_arrays >= [ pa => let pte_array ];
        require(pte_array.is_void(offset));
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
        have pte_arrays >= [ pa => let pte_array ];
        require(pte_array.is_void(offset));
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
    protocol_allocate(nid: NodeId, paddr: Paddr) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have nodes >= [ pa => NodeState::Locked ];
        remove pte_arrays -= [ pa => let pte_array ];
        require(pte_array.is_void(offset));
        add pte_arrays += [ pa => pte_array.update(offset, PteState::Alive(paddr)) ];
        add nodes += [ nid => NodeState::Free ];
        add pte_arrays += [ nid => PteArrayState::empty() ];
        add strays += { (nid, StrayState::False(paddr)) };
    }
}

transition!{
    protocol_deallocate(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        remove nodes -= [ nid => NodeState::Locked ];
        have nodes >= [ pa => NodeState::Locked ];
        remove pte_arrays -= [ pa => let pte_array ];
        require(pte_array.is_alive(offset));
        let paddr = pte_array.get_paddr(offset);
        remove pte_arrays -= [ nid => PteArrayState::empty() ];
        add pte_arrays += [ pa => pte_array.update(offset, PteState::None) ];
        remove strays -= { (nid, StrayState::False(paddr)) };
        add strays += { (nid, StrayState::True) };
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
    normal_allocate(nid: NodeId, paddr: Paddr) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have nodes >= [ pa => NodeState::LockedOutside ];
        remove pte_arrays -= [ pa => let pte_array ];
        require(pte_array.is_void(offset));
        add pte_arrays += [ pa => pte_array.update(offset, PteState::Alive(paddr)) ];
        add nodes += [ nid => NodeState::Free ];
        add pte_arrays += [ nid => PteArrayState::empty() ];
        add strays += { (nid, StrayState::False(paddr)) };
    }
}

transition!{
    normal_deallocate(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        remove nodes -= [ nid => NodeState::LockedOutside ];
        have nodes >= [ pa => NodeState::LockedOutside ];
        remove pte_arrays -= [ pa => let pte_array ];
        require(pte_array.is_alive(offset));
        let paddr = pte_array.get_paddr(offset);
        remove pte_arrays -= [ nid => PteArrayState::empty() ];
        add pte_arrays += [ pa => pte_array.update(offset, PteState::None) ];
        remove strays -= { (nid, StrayState::False(paddr)) };
        add strays += { (nid, StrayState::True) };
    }
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
fn protocol_allocate_inductive(pre: Self, post: Self, nid: NodeId, paddr: Paddr) { admit(); }

#[inductive(protocol_deallocate)]
fn protocol_deallocate_inductive(pre: Self, post: Self, nid: NodeId) {}

#[inductive(normal_lock)]
fn normal_lock_inductive(pre: Self, post: Self, nid: NodeId) {}

#[inductive(normal_unlock)]
fn normal_unlock_inductive(pre: Self, post: Self, nid: NodeId) {}

#[inductive(normal_allocate)]
fn normal_allocate_inductive(pre: Self, post: Self, nid: NodeId, paddr: Paddr) { admit(); }

#[inductive(normal_deallocate)]
fn normal_deallocate_inductive(pre: Self, post: Self, nid: NodeId) {}

}

}
