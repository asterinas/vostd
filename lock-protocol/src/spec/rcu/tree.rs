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

    #[sharding(map)]
    pub strays: Map<(NodeId, Paddr), bool>,
}

#[invariant]
pub fn wf_nodes(&self) -> bool {
    forall |nid: NodeId| #![auto]
        self.nodes.dom().contains(nid) ==>
            NodeHelper::valid_nid(nid)
}

#[invariant]
pub fn wf_pte_arrays(&self) -> bool {
    forall |nid: NodeId| #![auto]
        self.pte_arrays.dom().contains(nid) ==> {
            &&& NodeHelper::valid_nid(nid)
            &&& self.pte_arrays[nid].wf()
        }
}

#[invariant]
pub fn wf_cursors(&self) -> bool {
    forall |cpu: CpuId| #![auto]
        self.cursors.dom().contains(cpu) ==> {
            &&& valid_cpu(self.cpu_num, cpu)
            &&& self.cursors[cpu].wf()
        }
}

#[invariant]
pub fn wf_strays(&self) -> bool {
    forall |pair: (NodeId, Paddr)| #![auto]
        self.strays.dom().contains(pair) ==> {
            &&& NodeHelper::valid_nid(pair.0)
            &&& pair.0 != NodeHelper::root_id()
        }
}

#[invariant]
pub fn inv_pt_node_pte_array_relationship(&self) -> bool {
    forall |nid: NodeId| #![auto]
        self.nodes.dom().contains(nid) <==>
        self.pte_arrays.dom().contains(nid)
}

#[invariant]
pub fn inv_pt_node_pte_relationship(&self) -> bool {
    forall |nid: NodeId|
        #![trigger NodeHelper::valid_nid(nid)]
        #![trigger self.nodes.dom().contains(nid)]
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
pub fn inv_non_overlapping(&self) -> bool {
    forall |cpu1: CpuId, cpu2: CpuId| #![auto]
        cpu1 != cpu2 &&
        self.cursors.dom().contains(cpu1) &&
        self.cursors.dom().contains(cpu2) &&
        self.cursors[cpu1] is Locked &&
        self.cursors[cpu2] is Locked ==>
        {
            let nid1 = self.cursors[cpu1]->Locked_0;
            let nid2 = self.cursors[cpu2]->Locked_0;

            !NodeHelper::in_subtree_range(nid1, nid2) &&
            !NodeHelper::in_subtree_range(nid2, nid1)
        }
}

pub open spec fn strays_filter(
    &self,
    nid: NodeId
) -> Map<(NodeId, Paddr), bool> {
    self.strays.filter_keys(|pair: (NodeId, Paddr)| { pair.0 == nid })
}

#[invariant]
pub fn inv_stray_at_most_one_false_per_node(&self) -> bool {
    forall |nid: NodeId|
        #![auto] // TODO
        NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() ==> {
            self.strays_filter(nid)
                .kv_pairs()
                .filter(|pair: ((NodeId, Paddr), bool)| pair.1 == false)
                .len() <= 1
        }
}

#[invariant]
pub fn inv_pte_is_alive_implies_stray_has_false(&self) -> bool {
    forall |nid: NodeId|
        #![auto] // TODO
        NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() ==> {
            let pa = NodeHelper::get_parent(nid);
            let offset = NodeHelper::get_offset(nid);
            self.pte_arrays.dom().contains(pa) && self.pte_arrays[pa].is_alive(offset) ==>
            exists |pair: (NodeId, Paddr)|
                #![auto] // TODO
                {
                    &&& pair.0 == nid
                    &&& pair.1 == self.pte_arrays[pa].get_paddr(offset)
                    &&& self.strays.dom().contains(pair)
                    &&& self.strays[pair] == false
                }
        }
}

#[invariant]
pub fn inv_stray_has_false_implies_pte_is_alive(&self) -> bool {
    forall |nid: NodeId, pa: Paddr|
        NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() &&
        self.strays.contains_key((nid, pa)) &&
        #[trigger] self.strays[(nid, pa)] == false ==>
        {
            let pa = NodeHelper::get_parent(nid);
            let offset = NodeHelper::get_offset(nid);
            &&& self.pte_arrays.contains_key(pa)
            &&& self.pte_arrays[pa].is_alive(offset)
            &&& self.pte_arrays[pa].get_paddr(offset) == pa
        }
}

property! {
    stray_is_false(nid: NodeId, paddr: Paddr) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        have strays >= [ (nid, paddr) => let stray ];
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have pte_arrays >= [ pa => let pte_array ];
        require(pte_array.is_alive(offset));
        require(pte_array.get_paddr(offset) == paddr);
        assert(stray == false);
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
        init strays = Map::empty();
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
        add strays += [ (nid, paddr) => false ] by { admit(); };
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
        remove strays -= [ (nid, paddr) => false ];
        add strays += [ (nid, paddr) => true ];
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

        remove nodes -= [ nid => NodeState::LockedOutside ];
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
        add strays += [ (nid, paddr) => false ] by { admit(); };
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
        remove strays -= [ (nid, paddr) => false ];
        add strays += [ (nid, paddr) => true ];
    }
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: CpuId) {
    assert(post.wf_nodes()) by {
        assert(forall |nid: NodeId| post.nodes.dom().contains(nid) ==> #[trigger] NodeHelper::valid_nid(nid)) by {
            NodeHelper::lemma_root_id();
        }
    }

    assert forall |nid: NodeId| NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id()
    implies {
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        !(post.pte_arrays.dom().contains(pa) && post.pte_arrays[pa].is_alive(offset))
    } by {
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        if pa == NodeHelper::root_id() {
            NodeHelper::lemma_get_offset_sound(nid);
        } else {
            assert(!post.pte_arrays.dom().contains(pa));
        }
    }

    assert forall |nid: NodeId|
        #[trigger] NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id()
    implies {
        post.strays_filter(nid)
            .kv_pairs()
            .filter(|pair: ((NodeId, Paddr), bool)| pair.1 == false)
            .len() <= 1
    } by {
        assert(post.strays_filter(nid).dom() =~= Set::<(NodeId, Paddr)>::empty());
        assert(post.strays_filter(nid).kv_pairs() =~= Set::<((NodeId, Paddr), bool)>::empty());
        let filtered = post.strays_filter(nid)
            .kv_pairs()
            .filter(|pair: ((NodeId, Paddr), bool)| pair.1 == false);
        assert(filtered =~= Set::<((NodeId, Paddr), bool)>::empty());
    }
}

#[inductive(protocol_lock_start)]
fn protocol_lock_start_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) { admit(); }

#[inductive(protocol_lock)]
fn protocol_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) { admit(); }

#[inductive(protocol_lock_skip)]
fn protocol_lock_skip_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) { admit(); }

#[inductive(protocol_lock_end)]
fn protocol_lock_end_inductive(pre: Self, post: Self, cpu: CpuId) { admit(); }

#[inductive(protocol_unlock_start)]
fn protocol_unlock_start_inductive(pre: Self, post: Self, cpu: CpuId) { admit(); }

#[inductive(protocol_unlock)]
fn protocol_unlock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) { admit(); }

#[inductive(protocol_unlock_skip)]
fn protocol_unlock_skip_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) { admit(); }

#[inductive(protocol_unlock_end)]
fn protocol_unlock_end_inductive(pre: Self, post: Self, cpu: CpuId) { admit(); }

#[inductive(protocol_allocate)]
fn protocol_allocate_inductive(pre: Self, post: Self, nid: NodeId, paddr: Paddr) { admit(); }

#[inductive(protocol_deallocate)]
fn protocol_deallocate_inductive(pre: Self, post: Self, nid: NodeId) { admit(); }

#[inductive(normal_lock)]
fn normal_lock_inductive(pre: Self, post: Self, nid: NodeId) { admit(); }

#[inductive(normal_unlock)]
fn normal_unlock_inductive(pre: Self, post: Self, nid: NodeId) { admit(); }

#[inductive(normal_allocate)]
fn normal_allocate_inductive(pre: Self, post: Self, nid: NodeId, paddr: Paddr) { admit(); }

#[inductive(normal_deallocate)]
fn normal_deallocate_inductive(pre: Self, post: Self, nid: NodeId) { admit(); }

}

}
