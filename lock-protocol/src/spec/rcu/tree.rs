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
        #[trigger] self.cursors.contains_key(cpu2) ==>
        {
            let range1 = self.cursors[cpu1].locked_range();
            let range2 = self.cursors[cpu2].locked_range();
            range1.disjoint(range2)
        }
}

pub open spec fn strays_filter(
    &self,
    nid: NodeId
) -> Map<Paddr, bool> {
    project_first_key(self.strays, nid)
}

pub open spec fn strays_count_false(
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
            self.strays_count_false(nid) <= 1
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

#[invariant]
pub fn inv_locked_node_state(&self) -> bool{
    forall |cpu:CpuId, nid:NodeId| {
        &&& #[trigger] self.cursors.contains_key(cpu)
        &&& !(self.cursors[cpu] is Void)
        &&& self.cursors[cpu].locked_range().contains(nid) } ==>{
            ||| (!self.nodes.contains_key(nid))
            ||| (#[trigger] self.nodes.contains_key(nid) && self.nodes[nid] is Locked)
        }

}

#[invariant]
pub fn inv_not_allocated_subtree(&self) -> bool {
    forall |rt: NodeId, nid: NodeId| {
        &&& ! #[trigger] self.nodes.contains_key(rt)
        &&& NodeHelper::valid_nid(nid)
        &&& #[trigger] NodeHelper::in_subtree_range(rt, nid) } ==>
        !self.nodes.contains_key(nid)
    }

#[invariant]
pub fn inv_unallocated_node_locked_implies_in_subtree(&self) -> bool {
    forall |cpu: CpuId, nid: NodeId| {
        &&& #[trigger] self.cursors.contains_key(cpu)
        &&& !(self.cursors[cpu] is Void)
        &&& self.cursors[cpu].locked_range().contains(nid)
        &&& !#[trigger] self.nodes.contains_key(nid) } ==> {
            &&& self.cursors[cpu].locked_range().contains(self.cursors[cpu].root())
            &&& NodeHelper::in_subtree(self.cursors[cpu].root(), nid)
        }
}

#[invariant]
pub fn inv_cursor_root_in_nodes(&self) -> bool {
    forall_map_values(self.cursors, |cursor:CursorState|
        !cursor.locked_range().is_empty() ==> self.nodes.contains_key(cursor.root()))
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

        have nodes >= [ nid => NodeState::LockedOutside ];

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
        require(NodeHelper::in_subtree_range(rt, nid));
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        require(nid != rt);
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
    protocol_allocate(cpu: CpuId, nid: NodeId, paddr: Paddr) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have cursors >= [ cpu => let CursorState::Locked(rt) ];
        require(NodeHelper::in_subtree_range(rt, pa));
        have nodes >= [ pa => NodeState::Locked ];
        remove pte_arrays -= [ pa => let pte_array ];
        remove free_paddrs -= set {paddr};
        require(pte_array.is_void(offset));
        add pte_arrays += [ pa => pte_array.update(offset, PteState::Alive(paddr)) ];
        add nodes += [ nid => NodeState::Locked ];
        add pte_arrays += [ nid => PteArrayState::empty() ];
        add strays += [ (nid, paddr) => false ];
    }
}

transition!{
    protocol_deallocate(cpu: CpuId, nid: NodeId) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have cursors >= [ cpu => let CursorState::Locked(rt) ];
        require(NodeHelper::in_subtree_range(rt, pa));
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
    broadcast use group_node_helper_lemmas;
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

    assert forall |nid: NodeId|
        #[trigger] NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id()
    implies {
        post.strays_count_false(nid) == 0
    } by {
        assert(value_filter(post.strays_filter(nid), |stray:bool| stray == false).is_empty());
    }
}

#[inductive(protocol_lock_start)]
fn protocol_lock_start_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(protocol_lock)]
fn protocol_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(protocol_lock_skip)]
fn protocol_lock_skip_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    broadcast use group_node_helper_lemmas;

    let root = pre.cursors[cpu].root();
    // Specify what's changed in the transition
    assert(post.cursors == pre.cursors.insert(cpu, CursorState::Locking(root, NodeHelper::next_outside_subtree(nid))));

    assert forall |node_id: NodeId|
        ! #[trigger]pre.cursors[cpu].locked_range().contains(node_id) &&
        post.cursors[cpu].locked_range().contains(node_id) implies
        NodeHelper::in_subtree(nid, node_id) && !pre.nodes.contains_key(node_id) by {
            assert(NodeHelper::in_subtree(nid, node_id));
        };


    assert(post.wf_cursors()) by {
        assert forall |cpu_id: CpuId| #[trigger] post.cursors.contains_key(cpu_id) implies {
            &&& valid_cpu(post.cpu_num, cpu_id)
            &&& post.cursors[cpu_id].wf()
        } by {
            if cpu_id == cpu {
                let rt = pre.cursors[cpu_id]->Locking_0;
                if rt != nid {
                    NodeHelper::lemma_in_subtree_bounded(rt, nid);
                }
            }
        }
    };

    // Insight: The current cursor must have locked nid's parent
    assert(post.inv_non_overlapping()) by {
        assert forall |cpu1: CpuId, cpu2: CpuId|
            cpu1 != cpu2 &&
            #[trigger] post.cursors.contains_key(cpu1) &&
            #[trigger] post.cursors.contains_key(cpu2) &&
            !(post.cursors[cpu1] is Void) &&
            !(post.cursors[cpu2] is Void) implies
            {
                let range1 = post.cursors[cpu1].locked_range();
                let range2 = post.cursors[cpu2].locked_range();
                range1.disjoint(range2)
            } by {
            assert(post.cursors == pre.cursors.insert(cpu, CursorState::Locking(root, NodeHelper::next_outside_subtree(nid))));
            if cpu1 == cpu {
                assert forall |node_id: NodeId|
                    !#[trigger] pre.cursors[cpu1].locked_range().contains(node_id) &&
                    post.cursors[cpu1].locked_range().contains(node_id) implies
                    !pre.cursors[cpu2].locked_range().contains(node_id) by {
                        let pa = NodeHelper::get_parent(nid);
                        assert(NodeHelper::in_subtree(root, pa)) by
                        { NodeHelper::lemma_child_in_subtree_implies_in_subtree(root, pa, nid);};
                        assert(pre.cursors[cpu1].locked_range().contains(pa)) by {
                            NodeHelper::lemma_is_child_nid_increasing(pa,nid);
                        };
                        if pre.cursors[cpu2].locked_range().contains(node_id) {
                            let root2 = pre.cursors[cpu2].root();
                            assert(NodeHelper::in_subtree_range(root2, pa)) by {
                                NodeHelper::lemma_child_in_subtree_implies_in_subtree(root2, pa, nid);
                            };
                            assert(false);
                        }
                    }
            }
            if cpu2 == cpu {
                assert forall |node_id: NodeId|
                    !#[trigger] pre.cursors[cpu2].locked_range().contains(node_id) &&
                    post.cursors[cpu2].locked_range().contains(node_id) implies
                    !pre.cursors[cpu1].locked_range().contains(node_id) by {
                        let pa = NodeHelper::get_parent(nid);
                        assert(NodeHelper::in_subtree(root, pa)) by
                        { NodeHelper::lemma_child_in_subtree_implies_in_subtree(root, pa, nid);};
                        assert(pre.cursors[cpu2].locked_range().contains(pa)) by {
                            NodeHelper::lemma_is_child_nid_increasing(pa,nid);
                        };
                        if pre.cursors[cpu1].locked_range().contains(node_id) {
                            let root1 = pre.cursors[cpu1].root();
                            assert(NodeHelper::in_subtree_range(root1, pa)) by {
                                NodeHelper::lemma_child_in_subtree_implies_in_subtree(root1, pa, nid);
                            };
                            assert(false);
                        }
                    }
            }
            }
    };
}

#[inductive(protocol_lock_end)]
fn protocol_lock_end_inductive(pre: Self, post: Self, cpu: CpuId) {
    broadcast use group_node_helper_lemmas;
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
fn protocol_allocate_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId, paddr: Paddr) {
    broadcast use group_node_helper_lemmas;

    let pa = NodeHelper::get_parent(nid);
    let offset = NodeHelper::get_offset(nid);
    let pte_array = pre.pte_arrays[pa];

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

            if node_id != nid && pa_node == pa && offset_node == offset {
                NodeHelper::lemma_parent_offset_uniqueness(node_id, nid);
                assert(false);
            }
        }
    };

    assert(post.inv_stray_at_most_one_false_per_node()) by {
        assert forall |node_id: NodeId|
            (#[trigger] NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()) implies {
               post.strays_count_false(node_id) <= 1
            } by {
            if node_id == nid {
                assert(!pre.nodes.contains_key(node_id));
                assert(pre.strays_count_false(node_id) == 0) by {
                    if pre.strays_count_false(node_id) != 0 {
                        lemma_project_first_key_value_filter_non_empty(pre.strays, node_id, |stray:bool|stray == false);
                    }
                }
                pre.lemma_insert_stray_false(node_id, paddr);

            } else {
                assert(post.strays_filter(node_id) == pre.strays_filter(node_id));
            }
        }
    };

    assert(post.inv_pte_is_alive_implies_stray_has_false()) by {
        Self::lemma_allocate_keep_inv_pte_is_alive_implies_stray_has_false(pre, post, nid, paddr);
    };
    assert(post.inv_not_allocated_subtree()) by {
        assert forall |rt: NodeId, node_id: NodeId|
            !#[trigger] post.nodes.contains_key(rt) &&
            NodeHelper::valid_nid(node_id) &&
            #[trigger] NodeHelper::in_subtree_range(rt, node_id) implies
            !post.nodes.contains_key(node_id) by {
                if node_id == nid && post.nodes.contains_key(nid) {
                    assert(NodeHelper::in_subtree(rt, pa)) by {
                        NodeHelper::lemma_child_in_subtree_implies_in_subtree(rt, pa, nid);
                    };
                }
            };
    }
}

#[inductive(protocol_deallocate)]
fn protocol_deallocate_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    broadcast use group_node_helper_lemmas;
    let pa = NodeHelper::get_parent(nid);
    let offset = NodeHelper::get_offset(nid);
    let pte_array = pre.pte_arrays[pa];
    let paddr = pte_array.get_paddr(offset);

    assert(post.strays == pre.strays.insert((nid, paddr), true));
    assert(post.inv_stray_at_most_one_false_per_node()) by {
        assert forall |node_id: NodeId|
            (#[trigger] NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()) implies {
               post.strays_count_false(node_id) <= 1
            } by {
            if node_id == nid {
                lemma_project_first_key_finite(pre.strays, node_id);
                lemma_value_filter_finite(pre.strays_filter(node_id), |stray:bool| stray == false);
                assert(pre.strays_count_false(node_id) == 1) by {
                    assert(pre.strays_filter(node_id).contains_key(paddr) && pre.strays_filter(node_id)[paddr] == false);
                    assert(pre.strays_count_false(node_id) <= 1);
                    assert(pre.strays_count_false(node_id) > 0) by {
                        if pre.strays_count_false(node_id) == 0 {
                            lemma_project_first_key_value_filter_empty(pre.strays, node_id, |stray:bool| stray == false);
                        }
                    }
                }
                assert(post.strays_count_false(node_id) == 0) by {
                    pre.lemma_insert_stray_true(node_id, paddr);
                }
            }
            else {
                assert(post.strays_filter(node_id) == pre.strays_filter(node_id));
            }
        }
    };
    assert(post.inv_not_allocated_subtree()) by {
        Self::lemma_deallocate_keep_inv_not_allocated_subtree(pre,post,nid);
    };
    assert(post.inv_cursor_root_in_nodes()) by {
        assert forall |cpu_id: CpuId| #[trigger] post.cursors.contains_key(cpu_id) &&
        !post.cursors[cpu_id].locked_range().is_empty() implies {
            post.nodes.contains_key(post.cursors[cpu_id].root())
        } by {
            if cpu_id == cpu {
                let rt = pre.cursors[cpu_id]->Locked_0;
                assert(post.nodes.contains_key(rt));
            } else
            {
                assert(pre.cursors[cpu_id].locked_range() == post.cursors[cpu_id].locked_range());
                if pre.cursors[cpu_id].root() == nid {
                    assert(pre.cursors[cpu_id].locked_range().contains(nid));
                    assert(pre.cursors[cpu].locked_range().contains(nid)) by {
                        NodeHelper::lemma_is_child_nid_increasing(pa, nid);
                        NodeHelper::lemma_in_subtree_is_child_in_subtree(pre.cursors[cpu].root(), pa, nid);
                    }
                }
            }
        }
    };
}

#[inductive(normal_lock)]
fn normal_lock_inductive(pre: Self, post: Self, nid: NodeId) {}

#[inductive(normal_unlock)]
fn normal_unlock_inductive(pre: Self, post: Self, nid: NodeId) {}

#[inductive(normal_allocate)]
fn normal_allocate_inductive(pre: Self, post: Self, nid: NodeId, paddr: Paddr) {
    broadcast use group_node_helper_lemmas;
    let pa = NodeHelper::get_parent(nid);
    let offset = NodeHelper::get_offset(nid);
    let pte_array = pre.pte_arrays[pa];

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

                if node_id != nid && pa_node == pa && offset_node == offset {
                    NodeHelper::lemma_parent_offset_uniqueness(node_id, nid);
                    assert(false);
                }
            }
    }
    assert(post.inv_stray_at_most_one_false_per_node()) by {
        assert forall |node_id: NodeId|
            (#[trigger] NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()) implies {
               post.strays_count_false(node_id) <= 1
            } by {
            if node_id == nid {
                assert(!pre.nodes.contains_key(node_id));
                assert(pre.strays_count_false(node_id) == 0) by {
                    if pre.strays_count_false(node_id) != 0 {
                        lemma_project_first_key_value_filter_non_empty(pre.strays, node_id, |stray:bool|stray == false);
                    }
                }
                assert(post.strays_count_false(node_id) == 1) by {
                    pre.lemma_insert_stray_false(node_id, paddr);
                }

            } else {
                assert(post.strays_filter(node_id) == pre.strays_filter(node_id));
            }
        }
    }
    assert(post.inv_pte_is_alive_implies_stray_has_false()) by {
        Self::lemma_allocate_keep_inv_pte_is_alive_implies_stray_has_false(pre, post, nid, paddr);
    }
    assert(post.inv_locked_node_state()) by {
        assert forall |cpu: CpuId| #[trigger]
            pre.cursors.contains_key(cpu) && !(pre.cursors[cpu] is Void) implies
            !pre.cursors[cpu].locked_range().contains(nid) by
            {
                if pre.cursors[cpu].locked_range().contains(nid) {
                    let root = pre.cursors[cpu].root();
                    assert(NodeHelper::in_subtree(root, nid));
                    assert(NodeHelper::in_subtree(root, pa)) by {
                        NodeHelper::lemma_child_in_subtree_implies_in_subtree(root, pa, nid);
                    };
                    assert(pre.cursors[cpu].locked_range().contains(pa)) by {
                        NodeHelper::lemma_is_child_nid_increasing(pa,nid);
                    };
                }
            }
    }
    assert(post.inv_not_allocated_subtree()) by {
        assert forall |rt: NodeId, node_id: NodeId|
            !#[trigger] post.nodes.contains_key(rt) &&
            NodeHelper::valid_nid(node_id) &&
            #[trigger] NodeHelper::in_subtree_range(rt, node_id) implies
            !post.nodes.contains_key(node_id) by {
                if node_id == nid && post.nodes.contains_key(nid) {
                    assert(NodeHelper::is_child(pa,nid));
                    assert(NodeHelper::in_subtree(rt, pa)) by {
                        NodeHelper::lemma_child_in_subtree_implies_in_subtree(rt, pa, nid);
                    };
                }
            };
    }
}

#[inductive(normal_deallocate)]
fn normal_deallocate_inductive(pre: Self, post: Self, nid: NodeId) {
    broadcast use group_node_helper_lemmas;
    let pa = NodeHelper::get_parent(nid);
    let offset = NodeHelper::get_offset(nid);
    let pte_array = pre.pte_arrays[pa];
    let paddr = pte_array.get_paddr(offset);

    assert(post.strays == pre.strays.insert((nid, paddr), true));
    assert(post.inv_stray_at_most_one_false_per_node()) by {
        assert forall |node_id: NodeId|
            (#[trigger] NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()) implies {
               post.strays_count_false(node_id) <= 1
            } by {
            if node_id == nid {
                lemma_project_first_key_finite(pre.strays, node_id);
                lemma_value_filter_finite(pre.strays_filter(node_id), |stray:bool| stray == false);
                assert(pre.strays_count_false(node_id) == 1) by {
                    assert(pre.strays_filter(node_id).contains_key(paddr) && pre.strays_filter(node_id)[paddr] == false);
                    assert(pre.strays_count_false(node_id) <= 1);
                    assert(pre.strays_count_false(node_id) > 0) by {
                        if pre.strays_count_false(node_id) == 0 {
                            lemma_project_first_key_value_filter_empty(pre.strays, node_id, |stray:bool| stray == false);
                        }
                    }
                }
                assert(post.strays_count_false(node_id) == 0) by {
                    pre.lemma_insert_stray_true(node_id, paddr);
                }
            }
            else {
                assert(post.strays_filter(node_id) == pre.strays_filter(node_id));
            }
        }
    };
    assert(post.inv_not_allocated_subtree()) by {
        Self::lemma_deallocate_keep_inv_not_allocated_subtree(pre,post,nid);
    };
}

proof fn lemma_insert_stray_false(&self, nid: NodeId, paddr: Paddr)
requires
    self.strays_count_false(nid) == 0,
    self.strays.dom().finite(),
    forall |pair: (NodeId, Paddr)| #[trigger] self.strays.contains_key(pair) ==> NodeHelper::valid_nid(pair.0) && pair.1 != paddr,
ensures
    value_filter(project_first_key(self.strays.insert((nid, paddr), false),nid), |stray: bool| stray == false).len() == 1,
{
    broadcast use group_value_filter_lemmas;
    assert(project_first_key(self.strays.insert((nid, paddr), false),nid) == project_first_key(self.strays, nid).insert(paddr, false));
    lemma_project_first_key_finite(self.strays, nid);
    lemma_insert_value_filter_different_len_not_contains(
        project_first_key(self.strays, nid),
        |stray: bool| stray == false,
        paddr,
        false,
    );
}

proof fn lemma_insert_stray_true(&self, nid: NodeId, paddr: Paddr)
requires
    self.strays_count_false(nid) == 1,
    self.strays_filter(nid).contains_key(paddr),
    self.strays_filter(nid)[paddr] == false,
    self.strays.dom().finite(),
ensures
    value_filter(project_first_key(self.strays.insert((nid, paddr),true), nid), |stray: bool| stray == false).len() == 0,
{
    assert(project_first_key(self.strays.insert((nid, paddr), true), nid) == project_first_key(self.strays, nid).insert(paddr, true));
    lemma_project_first_key_finite(self.strays, nid);
    lemma_insert_value_filter_different_len_contains(
        project_first_key(self.strays, nid),
        |stray: bool| stray == false,
        paddr,
        true,
    );
}

proof fn lemma_deallocate_keep_inv_not_allocated_subtree(pre: Self, post: Self, nid: NodeId)
requires
    pre.inv_not_allocated_subtree(),
    pre.inv_pte_is_void_implies_no_node(),
    pre.inv_pt_node_pte_array_relationship(),
    pre.nodes.contains_key(nid),
    pre.pte_arrays[nid] == PteArrayState::empty(),
    post.nodes == pre.nodes.remove(nid),
ensures
    post.inv_not_allocated_subtree(),
    {
        broadcast use group_node_helper_lemmas;
        assert forall |rt: NodeId, node_id: NodeId|
            !#[trigger] post.nodes.contains_key(rt) &&
            NodeHelper::valid_nid(node_id) &&
            #[trigger] NodeHelper::in_subtree_range(rt, node_id) implies
            !post.nodes.contains_key(node_id) by {
                if node_id != nid && NodeHelper::in_subtree(nid,node_id) {
                    assert (!pre.nodes.contains_key(node_id)) by {
                        if pre.nodes.contains_key(node_id) {
                            let nid_trace = NodeHelper::nid_to_trace(nid);
                            let node_id_trace = NodeHelper::nid_to_trace(node_id);
                            assert(nid_trace.len() < node_id_trace.len()) by {
                                if nid_trace.len() == node_id_trace.len() {
                                    assert(nid_trace == node_id_trace);
                                    assert(nid == NodeHelper::trace_to_nid(nid_trace));
                                    assert(node_id == NodeHelper::trace_to_nid(node_id_trace));
                                }
                            }
                            let conflict_trace = node_id_trace.subrange(0, (nid_trace.len() + 1) as int);
                            let conflict_nid = NodeHelper::trace_to_nid(conflict_trace);
                            assert(NodeHelper::in_subtree_range(conflict_nid, node_id));
                            assert(nid_trace.is_prefix_of(conflict_trace));
                        }
                    };
                }
            };
    }


proof fn lemma_allocate_keep_inv_pte_is_alive_implies_stray_has_false(pre: Self, post: Self, nid: NodeId, paddr: Paddr)
requires
    NodeHelper::valid_nid(nid),
    nid != NodeHelper::root_id(),
    pre.wf_pte_arrays(),
    pre.inv_pte_is_void_implies_no_node(),
    pre.inv_pte_is_alive_implies_stray_has_false(),
    pre.nodes.contains_key(NodeHelper::get_parent(nid)),
    pre.pte_arrays.contains_key(NodeHelper::get_parent(nid)),
    pre.pte_arrays[NodeHelper::get_parent(nid)].is_void(NodeHelper::get_offset(nid)),
    post.pte_arrays =~= pre.pte_arrays.insert(NodeHelper::get_parent(nid), pre.pte_arrays[NodeHelper::get_parent(nid)].update(NodeHelper::get_offset(nid), PteState::Alive(paddr))).insert(nid,PteArrayState::empty()),
    post.nodes.dom() == pre.nodes.dom().insert(nid),
    post.strays == pre.strays.insert((nid, paddr), false),
    post.inv_pt_node_pte_relationship(),
ensures
    post.inv_pte_is_alive_implies_stray_has_false(),
{
    broadcast use group_node_helper_lemmas;
    let pa = NodeHelper::get_parent(nid);
    let offset = NodeHelper::get_offset(nid);
    let pte_array = pre.pte_arrays[pa];

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
            if post.pte_arrays.contains_key(pa_node) && post.pte_arrays[pa_node].is_alive(offset_node) {
                if node_id == nid {
                    assert(post.pte_arrays[pa_node].get_paddr(offset_node) == paddr);
                    assert(post.strays.contains_key((nid, paddr)));
                } else {
                    let paddr_other = pre.pte_arrays[pa_node].get_paddr(offset_node);
                    assert(post.strays.contains_key((node_id, paddr_other)));
                    if pa_node == pa && offset_node != offset {
                        assert(post.pte_arrays[pa_node] == pte_array.update(offset, PteState::Alive(paddr)));
                    } else if pa_node != pa {
                        assert(post.pte_arrays[pa_node] == pre.pte_arrays[pa_node]);
                    }
                }
            }
        }
}

}
}
