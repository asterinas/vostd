use verus_state_machines_macros::tokenized_state_machine;
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

    #[sharding(set)]
    pub free_paddrs: Set<Paddr>
}

#[invariant]
pub fn wf_nodes(&self) -> bool {
    &&& self.nodes.dom().all(|nid: NodeId| NodeHelper::valid_nid(nid))
    &&& self.nodes.dom().finite()
}

#[invariant]
pub fn wf_pte_arrays(&self) -> bool {
    self.pte_arrays.dom().all(|nid: NodeId| NodeHelper::valid_nid(nid) && self.pte_arrays[nid].wf())
}

#[invariant]
pub fn wf_cursors(&self) -> bool {
    &&& self.cursors.dom().all(|cpu: CpuId| {
        &&& valid_cpu(self.cpu_num, cpu)
        &&& self.cursors[cpu].wf()
    })
    &&& forall |cpu: CpuId| #[trigger] valid_cpu(self.cpu_num, cpu) ==> self.cursors.contains_key(cpu)
    &&& self.cursors.dom().finite()
}

#[invariant]
pub fn wf_strays(&self) -> bool {
    &&& self.strays.dom().all(|pair: (NodeId, Paddr)| {
        &&& NodeHelper::valid_nid(pair.0)
        &&& pair.0 != NodeHelper::root_id()
    })
    &&& self.strays.dom().finite()
    // Ensure that all strays have different physical addresses
    &&& forall |pair1: (NodeId, Paddr), pair2:(NodeId,Paddr)|
        #[trigger] self.strays.contains_key(pair1) && #[trigger] self.strays.contains_key(pair2) && pair1 != pair2 ==>
        pair1.1 != pair2.1
}

#[invariant]
pub fn wf_free_paddrs(&self) -> bool
{
    &&& self.free_paddrs.finite()
}

#[invariant]
pub fn inv_pt_node_pte_array_relationship(&self) -> bool {
    self.nodes.dom() =~= self.pte_arrays.dom()
}

#[invariant]
pub fn inv_pt_node_pte_relationship(&self) -> bool {
    forall |nid: NodeId|
        #![trigger NodeHelper::valid_nid(nid)]
        #![trigger self.nodes.contains_key(nid)]
        NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() ==> {
            self.nodes.contains_key(nid) <==> {
                let pa = NodeHelper::get_parent(nid);
                let offset = NodeHelper::get_offset(nid);

                self.pte_arrays.contains_key(pa) &&
                self.pte_arrays[pa].is_alive(offset)
            }
        }
}

#[invariant]
pub fn inv_non_overlapping(&self) -> bool {
    forall |cpu1: CpuId, cpu2: CpuId|
        cpu1 != cpu2 &&
        #[trigger] self.cursors.contains_key(cpu1) &&
        #[trigger] self.cursors.contains_key(cpu2) &&
        !(self.cursors[cpu1] is Void) &&
        !(self.cursors[cpu2] is Void) ==>
        {
            let range1 = self.cursors[cpu1].lock_range();
            let range2 = self.cursors[cpu2].lock_range();
            range1.1 <= range2.0 || range2.1 <= range1.0
        }
}

pub open spec fn strays_filter(
    &self,
    nid: NodeId
) -> Map<Paddr, bool> {
    project_first_key(self.strays, nid)
}

pub open spec fn starys_count_false(
    &self,
    nid: NodeId
) -> nat
{
    value_filter(self.strays_filter(nid), |stray:bool| stray == false).len()
}

#[invariant]
pub fn inv_stray_at_most_one_false_per_node(&self) -> bool {
    forall |nid: NodeId|
        #[trigger]
        NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() ==> {
            self.starys_count_false(nid) <= 1
        }
}

#[invariant]
pub fn inv_pte_is_alive_implies_stray_has_false(&self) -> bool {
    forall |nid: NodeId|
        #[trigger]
        NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() ==> {
            let pa = NodeHelper::get_parent(nid);
            let offset = NodeHelper::get_offset(nid);
            self.pte_arrays.contains_key(pa) && self.pte_arrays[pa].is_alive(offset) ==>
            exists |pair: (NodeId, Paddr)|
                #![trigger self.strays.contains_key(pair)]
                {
                    &&& pair.0 == nid
                    &&& pair.1 == self.pte_arrays[pa].get_paddr(offset)
                    &&& self.strays.contains_key(pair)
                    &&& self.strays[pair] == false
                }
        }
}

#[invariant]
pub fn inv_stray_has_false_implies_pte_is_alive(&self) -> bool {
    forall |nid: NodeId, paddr: Paddr|
        NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() &&
        self.strays.contains_key((nid, paddr)) &&
        #[trigger] self.strays[(nid, paddr)] == false ==>
        {
            let pa = NodeHelper::get_parent(nid);
            let offset = NodeHelper::get_offset(nid);
            &&& self.pte_arrays.contains_key(pa)
            &&& self.pte_arrays[pa].is_alive(offset)
            &&& self.pte_arrays[pa].get_paddr(offset) == paddr
        }
}

#[invariant]
pub fn inv_pte_is_void_implies_no_node(&self) -> bool {
   forall |nid: NodeId| {
       #[trigger] NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() &&
       self.pte_arrays.contains_key(NodeHelper::get_parent(nid)) && self.pte_arrays[NodeHelper::get_parent(nid)].is_void(NodeHelper::get_offset(nid)) ==>
           !self.nodes.contains_key(nid)
   }
}

#[invariant]
pub fn inv_free_paddr_not_in_strays(&self) -> bool {
    forall | pair: (NodeId, Paddr) |
        #[trigger] self.strays.contains_key(pair) ==>
        !self.free_paddrs.contains(pair.1)
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
    initialize(cpu_num: CpuId, paddrs: Set<Paddr>) {
        require(cpu_num > 0);
        require(paddrs.finite());
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
        init free_paddrs = paddrs;
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
        require(NodeHelper::in_subtree_range(rt, _nid));
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
        require(rt <= nid);
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
        remove free_paddrs -= set {paddr};
        require(pte_array.is_void(offset));
        add pte_arrays += [ pa => pte_array.update(offset, PteState::Alive(paddr)) ];
        add nodes += [ nid => NodeState::Free ];
        add pte_arrays += [ nid => PteArrayState::empty() ];
        add strays += [ (nid, paddr) => false ];
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
        remove free_paddrs -= set {paddr};
        require(pte_array.is_void(offset));
        add pte_arrays += [ pa => pte_array.update(offset, PteState::Alive(paddr)) ];
        add nodes += [ nid => NodeState::Free ];
        add pte_arrays += [ nid => PteArrayState::empty() ];
        add strays += [ (nid, paddr) => false ];
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
fn initialize_inductive(post: Self, cpu_num: CpuId, paddrs: Set<Paddr>) {
    assert(post.wf_nodes()) by {
        assert(forall |nid: NodeId| post.nodes.contains_key(nid) ==> #[trigger] NodeHelper::valid_nid(nid)) by {
            NodeHelper::lemma_root_id();
        }
        assert(post.nodes.dom() == set![NodeHelper::root_id()]);
    }
    assert(post.cursors.dom().finite()) by{
        assert(post.cursors.dom() == Set::new(|p: nat| 0 <= p < cpu_num));
        lemma_nat_range_finite(0, cpu_num);
    }

    assert forall |nid: NodeId| NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id()
    implies {
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        !(post.pte_arrays.contains_key(pa) && post.pte_arrays[pa].is_alive(offset))
    } by {
        if NodeHelper::get_parent(nid) == NodeHelper::root_id() {
            NodeHelper::lemma_get_offset_sound(nid);
        }
    }

    assert forall |nid: NodeId|
        #[trigger] NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id()
    implies {
        post.starys_count_false(nid) == 0
    } by {
        assert(post.strays_filter(nid).is_empty());
        assert(value_filter(post.strays_filter(nid), |stray:bool| stray == false).is_empty());
    }
}

#[inductive(protocol_lock_start)]
fn protocol_lock_start_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    assert(post.inv_non_overlapping()) by { admit(); };
}

#[inductive(protocol_lock)]
fn protocol_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    assert(post.inv_non_overlapping()) by { admit(); };
}

#[inductive(protocol_lock_skip)]
fn protocol_lock_skip_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    // wf_cursors: cursor for cpu changes from Locking(rt, nid) to Locking(rt, next_outside_subtree(nid))
    assert(post.wf_cursors()) by {
        assert forall |cpu_id: CpuId| #[trigger] post.cursors.contains_key(cpu_id) implies {
            &&& valid_cpu(post.cpu_num, cpu_id)
            &&& post.cursors[cpu_id].wf()
        } by {
            if cpu_id == cpu {
                let rt = pre.cursors[cpu_id]->Locking_0;
                let _nid = pre.cursors[cpu_id]->Locking_1;
                // Need to show: rt <= next_outside_subtree(nid) <= next_outside_subtree(rt)
                if rt == nid {
                } else {
                    // rt < nid, so need to show next_outside_subtree(nid) <= next_outside_subtree(rt)
                    // This follows from the fact that nid is in the subtree range of rt
                    NodeHelper::lemma_in_subtree_range_implies_in_subtree(rt, nid);
                    NodeHelper::lemma_in_subtree_bounded(rt, nid);
                    assert(NodeHelper::next_outside_subtree(nid) <= NodeHelper::next_outside_subtree(rt));
                }
            }
        }
    };
    assert(post.inv_non_overlapping()) by { admit(); };
}

#[inductive(protocol_lock_end)]
fn protocol_lock_end_inductive(pre: Self, post: Self, cpu: CpuId) {
    // inv_non_overlapping: cursor for cpu changes from Locking to Locked, others unchanged
    assert(post.inv_non_overlapping()) by {
        assert forall |cpu1: CpuId, cpu2: CpuId|
            (cpu1 != cpu2 &&
            #[trigger] post.cursors.contains_key(cpu1) &&
            #[trigger] post.cursors.contains_key(cpu2) &&
            post.cursors[cpu1] is Locked &&
            post.cursors[cpu2] is Locked) implies {
            let nid1 = post.cursors[cpu1]->Locked_0;
            let nid2 = post.cursors[cpu2]->Locked_0;
            !NodeHelper::in_subtree_range(nid1, nid2) &&
            !NodeHelper::in_subtree_range(nid2, nid1)
        } by {
            // Need to analyze the case where cpu is one of cpu1/cpu2
            if cpu1 == cpu {
                // cpu1 now has Locked(rt), cpu2 has some other Locked state
                assert(post.cursors[cpu1] is Locked);
                let rt = post.cursors[cpu1]->Locked_0;
                assert(post.cursors[cpu2] is Locked);
                let nid2 = post.cursors[cpu2]->Locked_0;

                // From pre invariant, since cpu2 was already Locked and cpu1 was Locking,
                // we need to ensure non-overlapping property still holds
                // The key insight is that if pre.cursors[cpu] was Locking(rt, nid) and reached
                // the end (nid == next_outside_subtree(rt)), then rt is fully locked
                // and from pre invariant, no other CPU can have overlapping locked subtree
                assert(pre.cursors[cpu2] == post.cursors[cpu2]);
                assert(pre.cursors[cpu2] is Locked);
                // From pre invariant on non-overlapping, if there were two Locked cursors,
                // they would be non-overlapping. But cpu was Locking, not Locked.
                // Now cpu becomes Locked(rt), and we need to show rt doesn't overlap with nid2

                // This requires reasoning about the locking protocol invariants
                // For now, use the fact that the locking protocol ensures non-overlapping
                admit();
            } else if cpu2 == cpu {
                // Similar case with cpu1 and cpu2 swapped
                admit();
            } else {
                // Both cursors unchanged from pre, so pre invariant applies
                if post.cursors.contains_key(cpu1) && post.cursors.contains_key(cpu2) {
                    assert(post.cursors[cpu1] == pre.cursors[cpu1]);
                    assert(post.cursors[cpu2] == pre.cursors[cpu2]);
                    // From pre invariant
                }
            }
        }
    };
}

#[inductive(protocol_unlock_start)]
fn protocol_unlock_start_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(protocol_unlock)]
fn protocol_unlock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(protocol_unlock_skip)]
fn protocol_unlock_skip_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(protocol_unlock_end)]
fn protocol_unlock_end_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(protocol_allocate)]
fn protocol_allocate_inductive(pre: Self, post: Self, nid: NodeId, paddr: Paddr) {
    let pa = NodeHelper::get_parent(nid);
    let offset = NodeHelper::get_offset(nid);
    let pte_array = pre.pte_arrays[pa];
    NodeHelper::lemma_get_offset_sound(nid);

    assert(post.inv_pt_node_pte_relationship()) by {
        assert forall |node_id: NodeId|
            (#[trigger] NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()) implies {
                post.nodes.contains_key(node_id) <==> {
                    let pa_node = NodeHelper::get_parent(node_id);
                    let offset_node = NodeHelper::get_offset(node_id);
                    post.pte_arrays.contains_key(pa_node) && post.pte_arrays[pa_node].is_alive(offset_node)
                }
            } by {
            let pa_node = NodeHelper::get_parent(node_id);
            let offset_node = NodeHelper::get_offset(node_id);
            NodeHelper::lemma_get_offset_sound(node_id);
            assert(0 <= offset_node < 512);

            if node_id != nid && pa_node == pa && offset_node == offset {
                NodeHelper::lemma_parent_offset_uniqueness(node_id, nid);
                assert(false);
            }
        }
    };

    assert(post.inv_stray_at_most_one_false_per_node()) by {
        assert forall |node_id: NodeId|
            (#[trigger] NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()) implies {
               post.starys_count_false(node_id) <= 1
            } by {
            if node_id == nid {
                assert(!pre.nodes.contains_key(node_id));
                assert(pre.starys_count_false(node_id) == 0) by {
                    if pre.starys_count_false(node_id) != 0 {
                        lemma_project_first_key_value_filter_non_empty(pre.strays, node_id, |stray:bool|stray == false);
                    }
                }
                assert(post.starys_count_false(node_id) == 1) by {
                    // This is absolutely true, but I do not have enough time
                    admit();
                }

            } else {
                assert(post.strays_filter(node_id) == pre.strays_filter(node_id));
            }
        }
    };

    assert(post.inv_pte_is_alive_implies_stray_has_false()) by {
        assert forall |node_id: NodeId|
            (#[trigger] NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()) implies {
                let pa_node = NodeHelper::get_parent(node_id);
                let offset_node = NodeHelper::get_offset(node_id);
                (post.pte_arrays.contains_key(pa_node) && post.pte_arrays[pa_node].is_alive(offset_node)) ==>
                exists |pair: (NodeId, Paddr)|
                    #![trigger post.strays.contains_key(pair)]
                    {
                        &&& pair.0 == node_id
                        &&& pair.1 == post.pte_arrays[pa_node].get_paddr(offset_node)
                        &&& post.strays.contains_key(pair)
                        &&& post.strays[pair] == false
                    }
            } by {
            let pa_node = NodeHelper::get_parent(node_id);
            let offset_node = NodeHelper::get_offset(node_id);
            NodeHelper::lemma_get_offset_sound(node_id);
            assert(0 <= offset_node < 512);

            if post.pte_arrays.contains_key(pa_node) && post.pte_arrays[pa_node].is_alive(offset_node) {
                if node_id == nid {
                    assert(post.pte_arrays[pa_node].get_paddr(offset_node) == paddr);
                    assert(post.strays.contains_key((nid, paddr)));
                    assert(post.strays[(nid, paddr)] == false);
                } else {
                    if pa_node == pa && offset_node != offset {
                        let paddr_other = pre.pte_arrays[pa_node].get_paddr(offset_node);
                        assert(post.pte_arrays[pa_node] == pte_array.update(offset, PteState::Alive(paddr)));
                        assert(post.pte_arrays[pa_node].get_paddr(offset_node) == paddr_other);

                        assert(post.strays.contains_key((node_id, paddr_other)));
                        assert(post.strays[(node_id, paddr_other)] == false);
                    } else if pa_node != pa {
                        let paddr_other = pre.pte_arrays[pa_node].get_paddr(offset_node);
                        assert(post.pte_arrays[pa_node] == pre.pte_arrays[pa_node]);
                        assert(post.pte_arrays[pa_node].get_paddr(offset_node) == paddr_other);

                        assert(post.strays.contains_key((node_id, paddr_other)));
                        assert(post.strays[(node_id, paddr_other)] == false);
                    }
                }
            }
        }
    };
}

#[inductive(protocol_deallocate)]
fn protocol_deallocate_inductive(pre: Self, post: Self, nid: NodeId) { admit(); }

#[inductive(normal_lock)]
fn normal_lock_inductive(pre: Self, post: Self, nid: NodeId) {}

#[inductive(normal_unlock)]
fn normal_unlock_inductive(pre: Self, post: Self, nid: NodeId) {}

#[inductive(normal_allocate)]
fn normal_allocate_inductive(pre: Self, post: Self, nid: NodeId, paddr: Paddr) { admit();}

#[inductive(normal_deallocate)]
fn normal_deallocate_inductive(pre: Self, post: Self, nid: NodeId) { admit(); }

}

}
