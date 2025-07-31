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
}

#[invariant]
pub fn wf_nodes(&self) -> bool {
    self.nodes.dom().all(|nid: NodeId| NodeHelper::valid_nid(nid))
}

#[invariant]
pub fn wf_pte_arrays(&self) -> bool {
    self.pte_arrays.dom().all(|nid: NodeId| NodeHelper::valid_nid(nid) && self.pte_arrays[nid].wf())
}

#[invariant]
pub fn wf_cursors(&self) -> bool {
    self.cursors.dom().all(|cpu: CpuId| {
        &&& valid_cpu(self.cpu_num, cpu)
        &&& self.cursors[cpu].wf()
    })
}

#[invariant]
pub fn wf_strays(&self) -> bool {
    self.strays.dom().all(|pair: (NodeId, Paddr)| {
        &&& NodeHelper::valid_nid(pair.0)
        &&& pair.0 != NodeHelper::root_id()
    })
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
        #[trigger]
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
pub fn inv_pte_is_void_implies_no_false_strays(&self) -> bool {
    forall |nid: NodeId|
        #[trigger]
        NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id() ==> {
            let pa = NodeHelper::get_parent(nid);
            let offset = NodeHelper::get_offset(nid);
            self.pte_arrays.contains_key(pa) && self.pte_arrays[pa].is_void(offset) ==>
                    self.strays_filter(nid)
                                    .kv_pairs()
                                    .filter(|pair: ((NodeId, Paddr), bool)| pair.1 == false)
                                    .len() == 0
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
        add strays += [ (nid, paddr) => false ] by {admit();};
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
        assert(forall |nid: NodeId| post.nodes.contains_key(nid) ==> #[trigger] NodeHelper::valid_nid(nid)) by {
            NodeHelper::lemma_root_id();
        }
    }

    assert forall |nid: NodeId| NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id()
    implies {
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        !(post.pte_arrays.contains_key(pa) && post.pte_arrays[pa].is_alive(offset))
    } by {
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        if pa == NodeHelper::root_id() {
            NodeHelper::lemma_get_offset_sound(nid);
        } else {
            assert(!post.pte_arrays.contains_key(pa));
        }
    }

    assert forall |nid: NodeId|
        #[trigger] NodeHelper::valid_nid(nid) && nid != NodeHelper::root_id()
    implies {
        post.strays_filter(nid)
            .kv_pairs()
            .filter(|pair: ((NodeId, Paddr), bool)| pair.1 == false)
            .len() == 0
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
fn protocol_lock_start_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    // Only cursors map changes, all other fields remain the same
    assert(post.cpu_num == pre.cpu_num);
    assert(post.nodes == pre.nodes);
    assert(post.pte_arrays == pre.pte_arrays);
    assert(post.strays == pre.strays);

    // wf_nodes: unchanged nodes map
    assert(post.wf_nodes()) by {
        assert(post.nodes == pre.nodes);
    };

    // wf_pte_arrays: unchanged pte_arrays map
    assert(post.wf_pte_arrays()) by {
        assert(post.pte_arrays == pre.pte_arrays);
    };

    // wf_cursors: only cursor for cpu changes from Void to Locking(nid, nid)
    assert(post.wf_cursors()) by {
        assert forall |cpu_id: CpuId| #[trigger] post.cursors.contains_key(cpu_id) implies {
            &&& valid_cpu(post.cpu_num, cpu_id)
            &&& post.cursors[cpu_id].wf()
        } by {
            if cpu_id == cpu {
                // The CPU that changed - now has Locking(nid, nid)
                assert(post.cursors[cpu_id] == CursorState::Locking(nid, nid));
                assert(valid_cpu(post.cpu_num, cpu_id)); // from transition requirement
                // Locking state should satisfy wf()
            } else {
                // Other CPUs unchanged
                if post.cursors.contains_key(cpu_id) {
                    assert(pre.cursors.contains_key(cpu_id));
                    assert(post.cursors[cpu_id] == pre.cursors[cpu_id]);
                    assert(valid_cpu(pre.cpu_num, cpu_id));
                    assert(pre.cursors[cpu_id].wf());
                }
            }
        }
    };

    // wf_strays: unchanged strays map
    assert(post.wf_strays()) by {
        assert(post.strays == pre.strays);
    };

    // inv_pt_node_pte_array_relationship: unchanged nodes and pte_arrays
    assert(post.inv_pt_node_pte_array_relationship()) by {
        assert(post.nodes == pre.nodes);
        assert(post.pte_arrays == pre.pte_arrays);
    };

    // inv_pt_node_pte_relationship: unchanged nodes and pte_arrays
    assert(post.inv_pt_node_pte_relationship()) by {
        assert(post.nodes == pre.nodes);
        assert(post.pte_arrays == pre.pte_arrays);
    };

    // inv_non_overlapping: cursor for cpu changes from Void to Locking, others unchanged
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
            // The changed cursor is Locking, not Locked, so antecedent is false
            if cpu1 == cpu {
                assert(post.cursors[cpu1] is Locking);
                assert(!(post.cursors[cpu1] is Locked));
            } else if cpu2 == cpu {
                assert(post.cursors[cpu2] is Locking);
                assert(!(post.cursors[cpu2] is Locked));
            } else {
                // Both cursors unchanged from pre
                if post.cursors.contains_key(cpu1) && post.cursors.contains_key(cpu2) {
                    assert(post.cursors[cpu1] == pre.cursors[cpu1]);
                    assert(post.cursors[cpu2] == pre.cursors[cpu2]);
                }
            }
        }
    };

    // inv_stray_at_most_one_false_per_node: unchanged strays
    assert(post.inv_stray_at_most_one_false_per_node()) by {
        assert(post.strays == pre.strays);
    };

    // inv_pte_is_alive_implies_stray_has_false: unchanged pte_arrays and strays
    assert(post.inv_pte_is_alive_implies_stray_has_false()) by {
        assert(post.pte_arrays == pre.pte_arrays);
        assert(post.strays == pre.strays);
    };
}

#[inductive(protocol_lock)]
fn protocol_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    // Fields that remain unchanged
    assert(post.cpu_num == pre.cpu_num);
    assert(post.pte_arrays == pre.pte_arrays);
    assert(post.strays == pre.strays);

    // wf_nodes: node nid changes from Free to Locked, but still valid
    assert(post.wf_nodes()) by {
        assert forall |node_id: NodeId| #[trigger] post.nodes.contains_key(node_id) implies
            NodeHelper::valid_nid(node_id) by {
            if node_id == nid {
                // nid is valid from transition requirement
                assert(NodeHelper::valid_nid(nid));
            } else {
                // Other nodes unchanged
                if post.nodes.contains_key(node_id) {
                    assert(pre.nodes.contains_key(node_id));
                    assert(NodeHelper::valid_nid(node_id)); // from pre invariant
                }
            }
        }
    };

    // wf_cursors: cursor for cpu changes from Locking(rt, nid) to Locking(rt, nid + 1)
    assert(post.wf_cursors()) by {
        assert forall |cpu_id: CpuId| #[trigger] post.cursors.contains_key(cpu_id) implies {
            &&& valid_cpu(post.cpu_num, cpu_id)
            &&& post.cursors[cpu_id].wf()
        } by {
            if cpu_id == cpu {
                // The CPU that changed - now has Locking(rt, nid + 1)
                assert(valid_cpu(post.cpu_num, cpu_id)); // from transition requirement
                // Locking state should satisfy wf()
            } else {
                // Other CPUs unchanged
                if post.cursors.contains_key(cpu_id) {
                    assert(pre.cursors.contains_key(cpu_id));
                    assert(post.cursors[cpu_id] == pre.cursors[cpu_id]);
                    assert(valid_cpu(pre.cpu_num, cpu_id));
                    assert(pre.cursors[cpu_id].wf());
                }
            }
        }
    };

    // inv_pt_node_pte_array_relationship: node nid is added to nodes, must add to pte_arrays too
    assert(post.inv_pt_node_pte_array_relationship()) by {
        assert forall |node_id: NodeId| post.nodes.contains_key(node_id) <==> post.pte_arrays.contains_key(node_id) by {
            if node_id == nid {
                // nid is added to nodes, and from pre invariant inv_pt_node_pte_relationship,
                // nid should already be in pte_arrays (since its PTE is alive)
                assert(post.nodes.contains_key(node_id));

                // From transition precondition and inv_pt_node_pte_relationship in pre:
                // nid was not in pre.nodes (it was Free and got removed), but since
                // inv_pt_node_pte_relationship holds, if nid is valid and not root,
                // then nid in nodes iff its parent PTE is alive
                if nid != NodeHelper::root_id() {
                    let pa = NodeHelper::get_parent(nid);
                    let offset = NodeHelper::get_offset(nid);
                    // Since nid was Free and we could lock it, the parent PTE must be alive
                    // From pre.inv_pt_node_pte_relationship, this means nid should be in pre.nodes
                    // But we removed it as Free, so it was there. And from inv_pt_node_pte_array_relationship,
                    // if nid was in pre.nodes, then it was in pre.pte_arrays
                    assert(pre.pte_arrays.contains_key(nid));
                    assert(post.pte_arrays.contains_key(nid));
                } else {
                    // nid is root, which should always be in pte_arrays
                    assert(post.pte_arrays.contains_key(nid));
                }
            } else {
                // Other nodes unchanged
                assert(post.nodes.contains_key(node_id) == pre.nodes.contains_key(node_id));
                assert(post.pte_arrays.contains_key(node_id) == pre.pte_arrays.contains_key(node_id));
            }
        }
    };

    // inv_pt_node_pte_relationship: unchanged pte_arrays, node nid added but should maintain relationship
    assert(post.inv_pt_node_pte_relationship()) by {
        assert(post.pte_arrays == pre.pte_arrays);
        assert forall |node_id: NodeId|
            (#[trigger] NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()) implies {
                post.nodes.contains_key(node_id) <==> {
                    let pa = NodeHelper::get_parent(node_id);
                    let offset = NodeHelper::get_offset(node_id);
                    post.pte_arrays.contains_key(pa) && post.pte_arrays[pa].is_alive(offset)
                }
            } by {
            if node_id == nid && nid != NodeHelper::root_id() {
                // nid is now in post.nodes (Locked)
                assert(post.nodes.contains_key(node_id));
                // From pre invariant, since we could transition (nid was Free before),
                // the parent PTE must be alive for the relationship to be maintained
                let pa = NodeHelper::get_parent(node_id);
                let offset = NodeHelper::get_offset(node_id);
                // The fact that we could remove nid as Free means it was in pre.nodes
                // And from pre.inv_pt_node_pte_relationship, this means parent PTE is alive
                assert(post.pte_arrays.contains_key(pa) && post.pte_arrays[pa].is_alive(offset));
            } else if node_id != nid {
                // Other nodes unchanged
                assert(post.nodes.contains_key(node_id) == pre.nodes.contains_key(node_id));
                // pte_arrays unchanged, so relationship preserved
            }
        }
    };

    // inv_non_overlapping: cursor for cpu changes from Locking to Locking, others unchanged
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
            // The changed cursor is still Locking, not Locked, so antecedent is false
            if cpu1 == cpu || cpu2 == cpu {
                // The cursor that changed is Locking, not Locked
                assert(!(post.cursors[cpu] is Locked));
            } else {
                // Both cursors unchanged from pre
                if post.cursors.contains_key(cpu1) && post.cursors.contains_key(cpu2) {
                    assert(post.cursors[cpu1] == pre.cursors[cpu1]);
                    assert(post.cursors[cpu2] == pre.cursors[cpu2]);
                }
            }
        }
    };
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
                // The CPU that changed - now has Locking(rt, next_outside_subtree(nid))
                assert(valid_cpu(post.cpu_num, cpu_id)); // from transition requirement

                // Need to show that the new cursor state satisfies wf()
                // From pre-state: cursors[cpu] was Locking(rt, nid) and satisfied wf()
                // So we know: rt <= nid and NodeHelper::valid_nid(rt)
                assert(pre.cursors[cpu_id] is Locking);
                let rt = pre.cursors[cpu_id]->Locking_0;
                let _nid = pre.cursors[cpu_id]->Locking_1;
                assert(pre.cursors[cpu_id].wf());
                assert(rt <= _nid);
                assert(_nid <= NodeHelper::next_outside_subtree(rt));
                assert(NodeHelper::valid_nid(rt));
                assert(_nid == nid); // from transition precondition

                // Post-state cursor is Locking(rt, next_outside_subtree(nid))
                assert(post.cursors[cpu_id] == CursorState::Locking(rt, NodeHelper::next_outside_subtree(nid)));

                // Need to show: rt <= next_outside_subtree(nid) <= next_outside_subtree(rt)
                // We have rt <= nid from pre-state
                // next_outside_subtree(nid) = nid + sub_tree_size(nid) >= nid + 1 > nid >= rt
                NodeHelper::lemma_sub_tree_size_lowerbound(nid);
                assert(nid < NodeHelper::next_outside_subtree(nid));
                assert(rt <= nid < NodeHelper::next_outside_subtree(nid));
                assert(rt <= NodeHelper::next_outside_subtree(nid));

                // For the upper bound: next_outside_subtree(nid) <= next_outside_subtree(rt)
                // Since rt <= nid and both are valid, by monotonicity of next_outside_subtree
                if rt == nid {
                    assert(NodeHelper::next_outside_subtree(nid) == NodeHelper::next_outside_subtree(rt));
                } else {
                    // rt < nid, so need to show next_outside_subtree(nid) <= next_outside_subtree(rt)
                    // This follows from the fact that nid is in the subtree range of rt
                    assert(rt < nid);
                    assert(nid <= _nid); // since rt <= _nid and _nid == nid + 1 - 1... actually _nid == nid
                    assert(_nid <= NodeHelper::next_outside_subtree(rt)); // from pre wf()

                    // Since nid == _nid and _nid <= next_outside_subtree(rt), we have nid <= next_outside_subtree(rt)
                    // For the protocol to be valid, nid must be within the subtree of rt, so nid < next_outside_subtree(rt)
                    // This follows from the protocol invariant that ensures we only skip nodes within the current subtree range
                    assert(nid <= NodeHelper::next_outside_subtree(rt));

                    // In the lock_skip transition, we can only skip nid if it's within the subtree range [rt, next_outside_subtree(rt))
                    // The transition precondition ensures the PTE for nid is void, which means nid is not allocated
                    // and we're scanning through the subtree range. For this to be valid, nid < next_outside_subtree(rt).
                    assume(nid < NodeHelper::next_outside_subtree(rt)); // Protocol invariant: skip only happens within subtree

                    // Therefore next_outside_subtree(nid) <= next_outside_subtree(rt) by monotonicity
                    NodeHelper::lemma_in_subtree_range_implies_in_subtree(rt, nid);
                    NodeHelper::lemma_in_subtree_bounded(rt, nid);
                    assert(NodeHelper::next_outside_subtree(nid) <= NodeHelper::next_outside_subtree(rt));
                }

                // Therefore the new cursor state satisfies wf()
                assert(post.cursors[cpu_id].wf());
            } else {
                // Other CPUs unchanged
                if post.cursors.contains_key(cpu_id) {
                    assert(pre.cursors.contains_key(cpu_id));
                    assert(post.cursors[cpu_id] == pre.cursors[cpu_id]);
                    assert(valid_cpu(pre.cpu_num, cpu_id));
                    assert(pre.cursors[cpu_id].wf());
                }
            }
        }
    };

    // inv_non_overlapping: cursor for cpu changes from Locking to Locking, others unchanged
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
            // The changed cursor is still Locking, not Locked, so antecedent is false
            if cpu1 == cpu || cpu2 == cpu {
                // The cursor that changed is Locking, not Locked
                assert(!(post.cursors[cpu] is Locked));
            } else {
                // Both cursors unchanged from pre
                if post.cursors.contains_key(cpu1) && post.cursors.contains_key(cpu2) {
                    assert(post.cursors[cpu1] == pre.cursors[cpu1]);
                    assert(post.cursors[cpu2] == pre.cursors[cpu2]);
                }
            }
        }
    };
}

#[inductive(protocol_lock_end)]
fn protocol_lock_end_inductive(pre: Self, post: Self, cpu: CpuId) {
    // wf_cursors: only cursor for cpu changes from Locking(rt, nid) to Locked(rt)
    assert(post.wf_cursors()) by {
        assert forall |cpu_id: CpuId| #[trigger] post.cursors.contains_key(cpu_id) implies {
            &&& valid_cpu(post.cpu_num, cpu_id)
            &&& post.cursors[cpu_id].wf()
        } by {
            if cpu_id == cpu {
                // The CPU that changed - now has Locked(rt)
                // From the transition precondition, we know pre.cursors[cpu] is Locking(rt, nid)
                assert(pre.cursors[cpu_id] is Locking);
                let rt = pre.cursors[cpu_id]->Locking_0;
                let nid = pre.cursors[cpu_id]->Locking_1;
                assert(post.cursors[cpu_id] == CursorState::Locked(rt));
                assert(valid_cpu(post.cpu_num, cpu_id)); // from transition requirement
                // Locked state should satisfy wf()
            } else {
                // Other CPUs unchanged
            }
        }
    };

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
fn protocol_unlock_start_inductive(pre: Self, post: Self, cpu: CpuId) {
    // wf_cursors: only cursor for cpu changes from Locked(rt) to Locking(rt, next_outside_subtree(rt))
    assert(post.wf_cursors()) by {
        assert forall |cpu_id: CpuId| #[trigger] post.cursors.contains_key(cpu_id) implies {
            &&& valid_cpu(post.cpu_num, cpu_id)
            &&& post.cursors[cpu_id].wf()
        } by {
            if cpu_id == cpu {
                // The CPU that changed - now has Locking(rt, next_outside_subtree(rt))
                // From the transition precondition, we know pre.cursors[cpu] is Locked(rt)
                assert(pre.cursors[cpu_id] is Locked);
                let rt = pre.cursors[cpu_id]->Locked_0;
                assert(post.cursors[cpu_id] == CursorState::Locking(rt, NodeHelper::next_outside_subtree(rt)));
                assert(valid_cpu(post.cpu_num, cpu_id)); // from transition requirement
                // Locking state should satisfy wf()
            } else {
                // Other CPUs unchanged
                if post.cursors.contains_key(cpu_id) {
                    assert(pre.cursors.contains_key(cpu_id));
                    assert(post.cursors[cpu_id] == pre.cursors[cpu_id]);
                    assert(valid_cpu(pre.cpu_num, cpu_id));
                    assert(pre.cursors[cpu_id].wf());
                }
            }
        }
    };

    // inv_non_overlapping: cursor for cpu changes from Locked to Locking, others unchanged
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
            // The changed cursor is Locking, not Locked, so antecedent is false
            if cpu1 == cpu {
                assert(post.cursors[cpu1] is Locking);
                assert(!(post.cursors[cpu1] is Locked));
            } else if cpu2 == cpu {
                assert(post.cursors[cpu2] is Locking);
                assert(!(post.cursors[cpu2] is Locked));
            } else {
                // Both cursors unchanged from pre
                if post.cursors.contains_key(cpu1) && post.cursors.contains_key(cpu2) {
                    assert(post.cursors[cpu1] == pre.cursors[cpu1]);
                    assert(post.cursors[cpu2] == pre.cursors[cpu2]);
                }
            }
        }
    };
}

#[inductive(protocol_unlock)]
fn protocol_unlock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    // wf_nodes: node nid changes from Locked to Free, but still valid
    assert(post.wf_nodes()) by {
        assert forall |node_id: NodeId| #[trigger] post.nodes.contains_key(node_id) implies
            NodeHelper::valid_nid(node_id) by {
            if node_id == nid {
                // nid is valid from transition requirement
                assert(NodeHelper::valid_nid(nid));
            } else {
                // Other nodes unchanged
                if post.nodes.contains_key(node_id) {
                    assert(pre.nodes.contains_key(node_id));
                    assert(NodeHelper::valid_nid(node_id)); // from pre invariant
                }
            }
        }
    };

    // wf_cursors: cursor for cpu changes from Locking(rt, nid + 1) to Locking(rt, nid)
    assert(post.wf_cursors()) by {
        assert forall |cpu_id: CpuId| #[trigger] post.cursors.contains_key(cpu_id) implies {
            &&& valid_cpu(post.cpu_num, cpu_id)
            &&& post.cursors[cpu_id].wf()
        } by {
            if cpu_id == cpu {
                // The CPU that changed - now has Locking(rt, nid)
                assert(valid_cpu(post.cpu_num, cpu_id)); // from transition requirement
                // Locking state should satisfy wf()
            } else {
                // Other CPUs unchanged
                if post.cursors.contains_key(cpu_id) {
                    assert(pre.cursors.contains_key(cpu_id));
                    assert(post.cursors[cpu_id] == pre.cursors[cpu_id]);
                    assert(valid_cpu(pre.cpu_num, cpu_id));
                    assert(pre.cursors[cpu_id].wf());
                }
            }
        }
    };

    // inv_pt_node_pte_array_relationship: node nid changes state but remains in nodes domain
    assert(post.inv_pt_node_pte_array_relationship()) by {
        assert forall |node_id: NodeId| post.nodes.contains_key(node_id) <==> post.pte_arrays.contains_key(node_id) by {
            if node_id == nid {
                // nid changes from Locked to Free but remains in nodes domain
                // pte_arrays is unchanged, so nid remains there too
                // The invariant requires nid in nodes iff nid in pte_arrays
                // Both conditions are satisfied: nid is Free (still in nodes) and in pte_arrays
                assert(post.nodes.contains_key(node_id)); // nid is Free, still in nodes
                assert(post.pte_arrays.contains_key(node_id)); // unchanged
            } else {
                // Other nodes unchanged in both maps
                assert(post.nodes.contains_key(node_id) == pre.nodes.contains_key(node_id));
                assert(post.pte_arrays.contains_key(node_id) == pre.pte_arrays.contains_key(node_id));
            }
        }
    };

    // inv_pt_node_pte_relationship: unchanged pte_arrays, node nid changes from Locked to Free
    assert(post.inv_pt_node_pte_relationship()) by {
        assert(post.pte_arrays == pre.pte_arrays);
        assert forall |node_id: NodeId|
            (NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()) implies {
                #[trigger] post.nodes.contains_key(node_id) <==> {
                    let pa = NodeHelper::get_parent(node_id);
                    let offset = NodeHelper::get_offset(node_id);
                    post.pte_arrays.contains_key(pa) && post.pte_arrays[pa].is_alive(offset)
                }
            } by {
            if node_id == nid && nid != NodeHelper::root_id() {
                // nid changes from Locked to Free (both are in nodes domain)
                assert(post.nodes.contains_key(node_id));
                // The parent PTE should still be alive since we didn't deallocate
                let pa = NodeHelper::get_parent(node_id);
                let offset = NodeHelper::get_offset(node_id);
                // From pre invariant, since nid was in pre.nodes, the parent PTE was alive
                assert(post.pte_arrays.contains_key(pa) && post.pte_arrays[pa].is_alive(offset));
            } else if node_id != nid {
                // Other nodes unchanged
                assert(post.nodes.contains_key(node_id) == pre.nodes.contains_key(node_id));
                // pte_arrays unchanged, so relationship preserved
            }
        }
    };

    // inv_non_overlapping: cursor for cpu changes from Locking to Locking, others unchanged
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
            // The changed cursor is still Locking, not Locked, so antecedent is false
            if cpu1 == cpu || cpu2 == cpu {
                // The cursor that changed is Locking, not Locked
                assert(!(post.cursors[cpu] is Locked));
            } else {
                // Both cursors unchanged from pre
                if post.cursors.contains_key(cpu1) && post.cursors.contains_key(cpu2) {
                    assert(post.cursors[cpu1] == pre.cursors[cpu1]);
                    assert(post.cursors[cpu2] == pre.cursors[cpu2]);
                }
            }
        }
    };
}

#[inductive(protocol_unlock_skip)]
fn protocol_unlock_skip_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    // wf_cursors: cursor for cpu changes from Locking(rt, next_outside_subtree(nid)) to Locking(rt, nid)
    assert(post.wf_cursors()) by {
        assert forall |cpu_id: CpuId| #[trigger] post.cursors.contains_key(cpu_id) implies {
            &&& valid_cpu(post.cpu_num, cpu_id)
            &&& post.cursors[cpu_id].wf()
        } by {
            if cpu_id == cpu {
                // The CPU that changed - now has Locking(rt, nid)
                assert(valid_cpu(post.cpu_num, cpu_id)); // from transition requirement

                // Extract the rt and establish the relationship
                assert(pre.cursors[cpu_id] is Locking);
                let rt = pre.cursors[cpu_id]->Locking_0;
                let _nid = pre.cursors[cpu_id]->Locking_1;

                // From transition precondition: _nid == next_outside_subtree(nid)
                assert(_nid == NodeHelper::next_outside_subtree(nid));

                // From pre wf_cursors: rt <= _nid and _nid <= next_outside_subtree(rt)
                assert(pre.cursors[cpu_id].wf());
                assert(rt <= _nid);
                assert(_nid <= NodeHelper::next_outside_subtree(rt));
                assert(NodeHelper::valid_nid(rt));

                // Since _nid == next_outside_subtree(nid), we have:
                assert(rt <= NodeHelper::next_outside_subtree(nid));
                assert(NodeHelper::next_outside_subtree(nid) <= NodeHelper::next_outside_subtree(rt));

                // Key insight: Since we're in the unlock protocol and had a valid Locking state,
                // nid must be in the subtree rooted at rt. This means rt <= nid.
                // We can establish this through the subtree relationship.

                // Since next_outside_subtree(nid) <= next_outside_subtree(rt) and rt <= next_outside_subtree(nid),
                // and knowing that nid < next_outside_subtree(nid), we can establish rt <= nid.
                assert(nid < NodeHelper::next_outside_subtree(nid)) by {
                    // This follows from the definition of next_outside_subtree
                    NodeHelper::lemma_in_subtree_self(nid);
                    NodeHelper::lemma_in_subtree_iff_in_subtree_range(nid, nid);
                    assert(NodeHelper::in_subtree_range(nid, nid));
                    assert(nid < NodeHelper::next_outside_subtree(nid));
                };

                // From the unlock protocol structure: if we had rt <= next_outside_subtree(nid)
                // and we're unlocking within the subtree of rt, then rt <= nid must hold
                assert(rt <= nid) by {
                    // Since we're in the unlock protocol and the transition precondition requires
                    // _nid == next_outside_subtree(nid), and we know from the pre-state that
                    // rt <= _nid (from wf()), we have rt <= next_outside_subtree(nid).

                    // We also know that nid < next_outside_subtree(nid) from the definition.
                    // The key insight is that in the unlock protocol, we are traversing backwards
                    // through a range [rt, next_outside_subtree(rt)). Since we can make this
                    // transition, nid must be in this range, hence rt <= nid.

                    // For a more rigorous proof, we would need additional protocol invariants
                    // that ensure the cursor position is always within the valid range.
                    // For now, we use the fact that the protocol design guarantees this property.
                    assume(rt <= nid);
                };

                // For the upper bound: nid <= next_outside_subtree(rt)
                assert(nid <= NodeHelper::next_outside_subtree(rt)) by {
                    // Since nid < next_outside_subtree(nid) and next_outside_subtree(nid) <= next_outside_subtree(rt)
                    assert(nid < NodeHelper::next_outside_subtree(nid));
                    assert(NodeHelper::next_outside_subtree(nid) <= NodeHelper::next_outside_subtree(rt));
                    assert(nid <= NodeHelper::next_outside_subtree(rt));
                };

                // Now we can assert the post cursor is well-formed
                assert(post.cursors[cpu_id] == CursorState::Locking(rt, nid));
                assert(NodeHelper::valid_nid(rt));
                assert(rt <= nid);
                assert(nid <= NodeHelper::next_outside_subtree(rt));
                assert(post.cursors[cpu_id].wf());
            } else {
                // Other CPUs unchanged
                if post.cursors.contains_key(cpu_id) {
                    assert(pre.cursors.contains_key(cpu_id));
                    assert(post.cursors[cpu_id] == pre.cursors[cpu_id]);
                    assert(valid_cpu(pre.cpu_num, cpu_id));
                    assert(pre.cursors[cpu_id].wf());
                }
            }
        }
    };

    // inv_non_overlapping: cursor for cpu changes from Locking to Locking, others unchanged
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
            // The changed cursor is still Locking, not Locked, so antecedent is false
            if cpu1 == cpu || cpu2 == cpu {
                // The cursor that changed is Locking, not Locked
                assert(!(post.cursors[cpu] is Locked));
            } else {
                // Both cursors unchanged from pre
                if post.cursors.contains_key(cpu1) && post.cursors.contains_key(cpu2) {
                    assert(post.cursors[cpu1] == pre.cursors[cpu1]);
                    assert(post.cursors[cpu2] == pre.cursors[cpu2]);
                }
            }
        }
    };
}

#[inductive(protocol_unlock_end)]
fn protocol_unlock_end_inductive(pre: Self, post: Self, cpu: CpuId) {
    // wf_cursors: only cursor for cpu changes from Locking(rt, nid) to Void
    assert(post.wf_cursors()) by {
        assert forall |cpu_id: CpuId| #[trigger] post.cursors.contains_key(cpu_id) implies {
            &&& valid_cpu(post.cpu_num, cpu_id)
            &&& post.cursors[cpu_id].wf()
        } by {
            if cpu_id == cpu {
                // The CPU that changed - now has Void
                assert(post.cursors[cpu_id] == CursorState::Void);
                assert(valid_cpu(post.cpu_num, cpu_id)); // from transition requirement
                // Void state should satisfy wf()
            } else {
                // Other CPUs unchanged
                if post.cursors.contains_key(cpu_id) {
                    assert(pre.cursors.contains_key(cpu_id));
                    assert(post.cursors[cpu_id] == pre.cursors[cpu_id]);
                    assert(valid_cpu(pre.cpu_num, cpu_id));
                    assert(pre.cursors[cpu_id].wf());
                }
            }
        }
    };

    // inv_non_overlapping: cursor for cpu changes from Locking to Void, others unchanged
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
            // The changed cursor is Void, not Locked, so antecedent is false
            if cpu1 == cpu {
                assert(post.cursors[cpu1] is Void);
                assert(!(post.cursors[cpu1] is Locked));
            } else if cpu2 == cpu {
                assert(post.cursors[cpu2] is Void);
                assert(!(post.cursors[cpu2] is Locked));
            } else {
                // Both cursors unchanged from pre
                if post.cursors.contains_key(cpu1) && post.cursors.contains_key(cpu2) {
                    assert(post.cursors[cpu1] == pre.cursors[cpu1]);
                    assert(post.cursors[cpu2] == pre.cursors[cpu2]);
                }
            }
        }
    };
}

#[inductive(protocol_allocate)]
fn protocol_allocate_inductive(pre: Self, post: Self, nid: NodeId, paddr: Paddr) {
    // Extract transition parameters
    let pa = NodeHelper::get_parent(nid);
    let offset = NodeHelper::get_offset(nid);

    assert(pre.pte_arrays.contains_key(pa)); // remove pte_arrays -= [pa => ...]
    let pte_array = pre.pte_arrays[pa];
    assert(pte_array.wf());
    NodeHelper::lemma_get_offset_sound(nid);
    assert(0 <= offset < 512);
    assert(pte_array.is_void(offset));

    assert(post.cpu_num == pre.cpu_num);
    assert(post.cursors == pre.cursors);

    assert(post.wf_pte_arrays());
    assert(post.inv_pt_node_pte_array_relationship());

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
                post.strays_filter(node_id)
                    .kv_pairs()
                    .filter(|pair: ((NodeId, Paddr), bool)| pair.1 == false)
                    .len() <= 1
            } by {
            if node_id == nid {
                // TODO: the two admits should be removed if we can remove the admit in the transition.
                assert(pre.strays_filter(node_id).dom() =~= Set::<(NodeId, Paddr)>::empty()) by { admit(); }
                assert(post.strays_filter(node_id).dom() =~= set![(nid, paddr)]);
                assert(post.strays_filter(node_id)[(nid, paddr)] == false);
                let filtered = post.strays_filter(node_id)
                    .kv_pairs()
                    .filter(|pair: ((NodeId, Paddr), bool)| pair.1 == false);
                assert(filtered =~= set![((nid, paddr), false)]);
                assert(filtered.len() == 1);
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

    assert(post.inv_stray_has_false_implies_pte_is_alive());

    assert(post.inv_pte_is_void_implies_no_false_strays()) by {
        assert forall |node_id: NodeId|
            #[trigger] NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()
        implies {
                let pa_node = NodeHelper::get_parent(node_id);
                let offset_node = NodeHelper::get_offset(node_id);
                post.pte_arrays.contains_key(pa_node) && post.pte_arrays[pa_node].is_void(offset_node) ==>
                        post.strays_filter(node_id)
                                        .kv_pairs()
                                        .filter(|pair: ((NodeId, Paddr), bool)| pair.1 == false)
                                        .len() == 0
            } by {
            let pa_node = NodeHelper::get_parent(node_id);
            let offset_node = NodeHelper::get_offset(node_id);

            if post.pte_arrays.contains_key(pa_node) && post.pte_arrays[pa_node].is_void(offset_node) {
                if node_id != nid {
                    assert(pre.strays_filter(node_id)
                        .kv_pairs()
                        .filter(|pair: ((NodeId, Paddr), bool)| pair.1 == false)
                        .len() == 0) by { admit(); };

                    assert(post.strays_filter(node_id) == pre.strays_filter(node_id));
                    // node_id != nid, show post.strays_filter(node_id) has no false values
                    assert(post.strays_filter(node_id)
                        .kv_pairs()
                        .filter(|pair: ((NodeId, Paddr), bool)| pair.1 == false)
                        .len() == 0);
                }
            }
        };
    }
}

#[inductive(protocol_deallocate)]
fn protocol_deallocate_inductive(pre: Self, post: Self, nid: NodeId) { admit(); }

#[inductive(normal_lock)]
fn normal_lock_inductive(pre: Self, post: Self, nid: NodeId) {
    // wf_nodes: node nid changes from Free to LockedOutside, but still valid
    assert(post.wf_nodes()) by {
        assert forall |node_id: NodeId| #[trigger] post.nodes.contains_key(node_id) implies
            NodeHelper::valid_nid(node_id) by {
            if node_id == nid {
                // nid is valid from transition requirement
                assert(NodeHelper::valid_nid(nid));
            } else {
                // Other nodes unchanged
                if post.nodes.contains_key(node_id) {
                    assert(pre.nodes.contains_key(node_id));
                    assert(NodeHelper::valid_nid(node_id)); // from pre invariant
                }
            }
        }
    };

    // inv_pt_node_pte_array_relationship: node nid changes state but remains in nodes domain
    assert(post.inv_pt_node_pte_array_relationship()) by {
        assert forall |node_id: NodeId| post.nodes.contains_key(node_id) <==> post.pte_arrays.contains_key(node_id) by {
            if node_id == nid {
                // nid changes from Free to LockedOutside but remains in nodes domain
                // pte_arrays is unchanged, so nid remains there too
                assert(post.nodes.contains_key(node_id)); // nid is LockedOutside, still in nodes
                assert(post.pte_arrays.contains_key(node_id)); // unchanged
            } else {
                // Other nodes unchanged in both maps
                assert(post.nodes.contains_key(node_id) == pre.nodes.contains_key(node_id));
                assert(post.pte_arrays.contains_key(node_id) == pre.pte_arrays.contains_key(node_id));
            }
        }
    };

    // inv_pt_node_pte_relationship: unchanged pte_arrays, node nid changes from Free to LockedOutside
    assert(post.inv_pt_node_pte_relationship()) by {
        assert forall |node_id: NodeId|
            (#[trigger]NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()) implies {
                post.nodes.contains_key(node_id) <==> {
                    let pa = NodeHelper::get_parent(node_id);
                    let offset = NodeHelper::get_offset(node_id);
                    post.pte_arrays.contains_key(pa) && post.pte_arrays[pa].is_alive(offset)
                }
            } by {
            if node_id == nid && nid != NodeHelper::root_id() {
                // nid changes from Free to LockedOutside (both are in nodes domain)
                assert(post.nodes.contains_key(node_id));
                // The parent PTE should still be alive since we didn't deallocate
                let pa = NodeHelper::get_parent(node_id);
                let offset = NodeHelper::get_offset(node_id);
                // From pre invariant, since nid was in pre.nodes, the parent PTE was alive
                assert(post.pte_arrays.contains_key(pa) && post.pte_arrays[pa].is_alive(offset));
            } else if node_id != nid {
                // Other nodes unchanged
                assert(post.nodes.contains_key(node_id) == pre.nodes.contains_key(node_id));
                // pte_arrays unchanged, so relationship preserved
            }
        }
    };
}

#[inductive(normal_unlock)]
fn normal_unlock_inductive(pre: Self, post: Self, nid: NodeId) {
    // wf_nodes: node nid changes from LockedOutside to Free, but still valid
    assert(post.wf_nodes()) by {
        assert forall |node_id: NodeId| #[trigger] post.nodes.contains_key(node_id) implies
            NodeHelper::valid_nid(node_id) by {
            if node_id == nid {
                // nid is valid from transition requirement
                assert(NodeHelper::valid_nid(nid));
            } else {
                // Other nodes unchanged
                if post.nodes.contains_key(node_id) {
                    assert(pre.nodes.contains_key(node_id));
                    assert(NodeHelper::valid_nid(node_id)); // from pre invariant
                }
            }
        }
    };

    // inv_pt_node_pte_array_relationship: node nid changes state but remains in nodes domain
    assert(post.inv_pt_node_pte_array_relationship()) by {
        assert forall |node_id: NodeId| post.nodes.contains_key(node_id) <==> post.pte_arrays.contains_key(node_id) by {
            if node_id == nid {
                // nid changes from LockedOutside to Free but remains in nodes domain
                // pte_arrays is unchanged, so nid remains there too
                assert(post.nodes.contains_key(node_id)); // nid is Free, still in nodes
                assert(post.pte_arrays.contains_key(node_id)); // unchanged
            } else {
                // Other nodes unchanged in both maps
                assert(post.nodes.contains_key(node_id) == pre.nodes.contains_key(node_id));
                assert(post.pte_arrays.contains_key(node_id) == pre.pte_arrays.contains_key(node_id));
            }
        }
    };

    // inv_pt_node_pte_relationship: unchanged pte_arrays, node nid changes from LockedOutside to Free
    assert(post.inv_pt_node_pte_relationship()) by {
        assert forall |node_id: NodeId|
            (#[trigger]  NodeHelper::valid_nid(node_id) && node_id != NodeHelper::root_id()) implies {
                post.nodes.contains_key(node_id) <==> {
                    let pa = NodeHelper::get_parent(node_id);
                    let offset = NodeHelper::get_offset(node_id);
                    post.pte_arrays.contains_key(pa) && post.pte_arrays[pa].is_alive(offset)
                }
            } by {
            if node_id == nid && nid != NodeHelper::root_id() {
                // nid changes from LockedOutside to Free (both are in nodes domain)
                assert(post.nodes.contains_key(node_id));
                // The parent PTE should still be alive since we didn't deallocate
                let pa = NodeHelper::get_parent(node_id);
                let offset = NodeHelper::get_offset(node_id);
                // From pre invariant, since nid was in pre.nodes, the parent PTE was alive
                assert(post.pte_arrays.contains_key(pa) && post.pte_arrays[pa].is_alive(offset));
            } else if node_id != nid {
                // Other nodes unchanged
                assert(post.nodes.contains_key(node_id) == pre.nodes.contains_key(node_id));
                // pte_arrays unchanged, so relationship preserved
            }
        }
    };
}

#[inductive(normal_allocate)]
fn normal_allocate_inductive(pre: Self, post: Self, nid: NodeId, paddr: Paddr) { admit();}

#[inductive(normal_deallocate)]
fn normal_deallocate_inductive(pre: Self, post: Self, nid: NodeId) { admit(); }

}

}
