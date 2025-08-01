use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

use crate::spec::{common::*, utils::*};
use super::{types::*, wf_tree_path::*};
use vstd::{set::*, seq::*, set_lib::*, map_lib::*};
use vstd_extra::{seq_extra::*, set_extra::*, map_extra::*};

verus! {

broadcast use {
    vstd_extra::map_extra::group_forall_map_lemmas,
    vstd_extra::map_extra::group_value_filter_lemmas,
    vstd_extra::seq_extra::group_forall_seq_lemmas,
    crate::spec::utils::group_node_helper_lemmas,
};

tokenized_state_machine!{

TreeSpec {

fields {
    /// The number of CPUs in the system.
    #[sharding(constant)]
    pub cpu_num: CpuId,

    /// The state of each node.
    #[sharding(map)]
    pub nodes: Map<NodeId, NodeState>,

    /// The state of pte array of each node.
    #[sharding(map)]
    pub pte_arrays: Map<NodeId, PteArrayState>,

    /// The number of readers holding a read lock on each node.
    #[sharding(map)]
    pub reader_counts: Map<NodeId, nat>,

    /// The state of cursors for each CPU.
    #[sharding(map)]
    pub cursors: Map<CpuId, CursorState>,
}

/// Every node should have a valid NodeId.
#[invariant]
pub fn inv_nodes(&self) -> bool {
    &&& self.nodes.contains_key(NodeHelper::root_id())
    &&& forall |nid: NodeId|
        #![trigger self.nodes.contains_key(nid)]
        self.nodes.contains_key(nid) ==> NodeHelper::valid_nid(nid)
    &&& forall |nid: NodeId|
        #![trigger self.nodes.contains_key(nid)]
        self.nodes.contains_key(nid) && nid != NodeHelper::root_id() ==> {
            let pa = NodeHelper::get_parent(nid);
            self.nodes.contains_key(pa)
        }
}

/// Every node has a corresponding pte array.
#[invariant]
pub fn inv_pte_arrays(&self) -> bool {
    &&& forall |nid: NodeId|
        #![trigger self.nodes.contains_key(nid)]
        #![trigger self.pte_arrays.contains_key(nid)]
        self.nodes.contains_key(nid) <==>
        self.pte_arrays.contains_key(nid)
    &&& forall_map_values(self.pte_arrays, |pte_array: PteArrayState| pte_array.wf())
}

/// Every node has a corresponding reader counter.
#[invariant]
pub fn inv_reader_counts(&self) -> bool {
    forall |nid: NodeId|
        #![trigger self.nodes.contains_key(nid)]
        #![trigger self.reader_counts.contains_key(nid)]
        self.nodes.contains_key(nid) <==>
        self.reader_counts.contains_key(nid)
}

/// Each cursor should be for a valid CPU, and the invariant should hold for each cursor's state.
#[invariant]
pub fn inv_cursors(&self) -> bool {
    &&& self.cursors.dom().finite()
    &&& forall |cpu: CpuId|
        #![trigger self.cursors.contains_key(cpu)]
        self.cursors.contains_key(cpu) <==> valid_cpu(self.cpu_num, cpu)
    &&& forall_map_values(self.cursors, |cursor: CursorState| cursor.inv())
}

/// Nodes in the path of cursors shold exist.
#[invariant]
pub fn inv_cursor_path_node_relation(&self) -> bool {
    forall |cpu: CpuId|
        #![trigger self.cursors.contains_key(cpu)]
        self.cursors.contains_key(cpu) ==> {
            let path = self.cursors[cpu].get_path();
            path.all(|nid| self.nodes.contains_key(nid))
        }
}

/// Node exists iff. the corresponding pte of its parent is alive.
#[invariant]
pub fn inv_node_pte_relation(&self) -> bool {
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

/// Unallocated or WriteLocked nodes should not have any reader counts.
#[invariant]
pub fn inv_nodes_reader_counts_relation(&self) -> bool {
    forall_map(self.reader_counts, |nid: NodeId, rc: nat| rc > 0 ==> self.nodes[nid] is WriteUnLocked)
    // This is equivalent to `self.nodes[nid] is UnAllocated || self.nodes[nid] is WriteUnLocked
    // ==> self.reader_counts[nid] == 0`*/
}

/// The number of cursors holding a read lock on each node should match the reader counts.
#[invariant]
pub fn inv_reader_counts_cursors_relation(&self) -> bool {
    forall_map(self.reader_counts, |nid: NodeId, rc: nat|
        rc == value_filter(
            self.cursors,
            |cursor: CursorState| cursor.hold_read_lock(nid),
        ).len()
    )
}

/// If a node is WriteLocked, it should have one cursor holding a write lock on it.
#[invariant]
pub fn inv_write_lock_nodes_cursors_relation(&self) -> bool {
    forall_map(self.nodes, |nid: NodeId, state: NodeState|
        state is WriteLocked ==>
        exists |cpu: CpuId| #[trigger] self.cursors.contains_key(cpu) &&
            self.cursors[cpu].hold_write_lock() &&
            self.cursors[cpu].get_write_lock_node() == nid
    )
}

/// If a cursor holds a read lock path, the reader count for each node in the path should be positive.
pub open spec fn rc_positive(&self, path: Seq<NodeId>) -> bool {
    path.all(|id| self.reader_counts[id] > 0)
}

/// All cursors holding read lock paths should have positive reader counts.
//  This invariant is not marked #[invariant] as it is implied by `inv_reader_counts_cursors_relation`.
pub open spec fn inv_rc_positive(&self) -> bool {
    forall_map_values(self.cursors, |cursor: CursorState|
        self.rc_positive(cursor.get_read_lock_path())
    )
}

/// The subtree rooted at `nid` should not have any read counts and should not be WriteLocked.
pub open spec fn subtree_locked(&self, nid: NodeId) -> bool {
    forall |id: NodeId|
        #![trigger self.nodes.contains_key(id)]
        #![trigger NodeHelper::in_subtree_range(nid, id)]
        self.nodes.contains_key(id) &&
        NodeHelper::in_subtree_range(nid, id) && id != nid ==>
        self.reader_counts[id] == 0 &&
        self.nodes[id] !is WriteLocked
}

/// If a cursor holds a write lock, the node should be WriteLocked and its subtree should be locked.
pub open spec fn inv_write_lock_cursors_subtree_locked(&self) -> bool {
    forall_map_values (self.cursors, |cursor: CursorState|
        cursor.hold_write_lock() ==>
        {
            let nid = cursor.get_write_lock_node();
            self.nodes[nid] is WriteLocked &&
            self.subtree_locked(nid)
        }
    )
}

/// If two cursors hold write locks, they should not be on the same node.
pub open spec fn inv_write_lock_cursors_distinct(&self) -> bool {
    forall |cpu1: CpuId, cpu2: CpuId| #![auto]
        cpu1 != cpu2 &&
        self.cursors.contains_key(cpu1) &&
        self.cursors.contains_key(cpu2) &&
        self.cursors[cpu1].hold_write_lock() &&
        self.cursors[cpu2].hold_write_lock() ==>
        {
            let nid1 = self.cursors[cpu1].get_write_lock_node();
            let nid2 = self.cursors[cpu2].get_write_lock_node();

            nid1 != nid2
        }
}

#[invariant]
pub fn inv_rw_lock(&self) -> bool
{
    &&& self.inv_write_lock_cursors_subtree_locked()
    &&& self.inv_write_lock_cursors_distinct()
}

/// If two cursors hold write locks, the write-locked node should not overlap
/// This invariant is not marked #[invariant] as it is directly implied by `inv_rw_lock`.
pub open spec fn inv_non_overlapping(&self) -> bool {
    forall |cpu1: CpuId, cpu2: CpuId| #![auto]
        cpu1 != cpu2 &&
        self.cursors.contains_key(cpu1) &&
        self.cursors.contains_key(cpu2) &&
        self.cursors[cpu1].hold_write_lock() &&
        self.cursors[cpu2].hold_write_lock() ==>
        {
            let nid1 = self.cursors[cpu1].get_write_lock_node();
            let nid2 = self.cursors[cpu2].get_write_lock_node();

            !NodeHelper::in_subtree_range(nid1, nid2) &&
            !NodeHelper::in_subtree_range(nid2, nid1)
        }
}

/// All cursors are initialized to the Void state and all nodes except the root are UnAllocated.
init!{
    initialize(cpu_num: CpuId) {
        require(cpu_num > 0);

        init cpu_num = cpu_num;
        init nodes = Map::new(
            |nid| nid == NodeHelper::root_id(),
            |nid| NodeState::WriteUnLocked,
        );
        init pte_arrays = Map::new(
            |nid| nid == NodeHelper::root_id(),
            |nid| PteArrayState::empty(),
        );
        init reader_counts = Map::new(
            |nid| nid == NodeHelper::root_id(),
            |nid| 0,
        );
        init cursors = Map::new(
            |cpu| valid_cpu(cpu_num, cpu),
            |cpu| CursorState::Void,
        );
    }
}

/// Start a read lock on the specified CPU.
transition!{
    locking_start(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => CursorState::Void ];
        add cursors += [ cpu => CursorState::ReadLocking(Seq::empty()) ];
    }
}

/// Release the cursor to the Void state if it releases all read locks in the path.
transition!{
    unlocking_end(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => let CursorState::ReadLocking(path) ];
        require(path.len() == 0);
        add cursors += [ cpu => CursorState::Void ];
    }
}

/// Acquire a read lock on the specified node and increment the reader count for that node.
transition!{
    read_lock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        have nodes >= [ nid => NodeState::WriteUnLocked ];

        remove reader_counts -= [ nid => let rc ];
        add reader_counts += [ nid => rc + 1 ];

        remove cursors -= [ cpu => let CursorState::ReadLocking(path) ];
        require(path.len()<3);
        require(wf_tree_path(path.push(nid)));
        add cursors += [ cpu => CursorState::ReadLocking(path.push(nid)) ];
    }
}

/// Release a read lock on the specified node and decrement the reader count for that node.
transition!{
    read_unlock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove reader_counts -= [ nid => let rc ];
        add reader_counts += [ nid => (rc - 1) as nat ];

        remove cursors -= [ cpu => let CursorState::ReadLocking(path) ];
        require(path.len() > 0 && path.last() == nid);
        add cursors += [ cpu => CursorState::ReadLocking(path.drop_last()) ];

        // assert(rc > 0) by {
        //     broadcast use {
        //         vstd_extra::seq_extra::group_forall_seq_lemmas,
        //     };
        //     pre.lemma_inv_implies_inv_rc_positive()
        // };
    }
}

/// Acquire a write lock on the specified node and ensure that no other CPU has a read lock on it.
transition!{
    write_lock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove nodes -= [ nid => NodeState::WriteUnLocked ];
        add nodes += [ nid => NodeState::WriteLocked ];

        have reader_counts >= [ nid => let rc ];
        require(rc == 0);

        remove cursors -= [ cpu => let CursorState::ReadLocking(path) ];
        require(wf_tree_path(path.push(nid)));
        add cursors += [ cpu => CursorState::WriteLocked(path.push(nid)) ];
    }
}

/// Release a write lock on the specified node and downgrade the cursor to ReadLocking.
transition!{
    write_unlock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove nodes -= [ nid => NodeState::WriteLocked ];
        add nodes += [ nid => NodeState::WriteUnLocked ];

        remove cursors -= [ cpu => let CursorState::WriteLocked(path) ];
        require(path.last() == nid);
        add cursors += [ cpu => CursorState::ReadLocking(path.drop_last()) ];
    }
}

/// Acquire a mock write lock in protocol.
/// Used in make_write_guard_unchecked.
transition!{
    in_protocol_write_lock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        have cursors >= [ cpu => let CursorState::WriteLocked(path) ];
        require(NodeHelper::in_subtree_range(path.last(), nid));

        remove nodes -= [ nid => NodeState::WriteUnLocked ];
        add nodes += [ nid => NodeState::InProtocolWriteLocked ];
    }
}

/// Release a mock write lock in protocol.
transition!{
    in_protocol_write_unlock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        have cursors >= [ cpu => let CursorState::WriteLocked(path) ];
        require(NodeHelper::in_subtree_range(path.last(), nid));

        remove nodes -= [ nid => NodeState::InProtocolWriteLocked ];
        add nodes += [ nid => NodeState::WriteUnLocked ];
    }
}

/// Ensure the cursor has a write lock on the specified node and allocates the node.
transition!{
    allocate(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have cursors >= [ cpu => let CursorState::WriteLocked(path) ];
        require(NodeHelper::in_subtree_range(path.last(), pa));

        have nodes >= [ pa => let pa_node ];
        require(pa_node.is_write_locked());
        remove pte_arrays -= [ pa => let pte_array ];
        require(pte_array.is_void(offset));
        add pte_arrays += [ pa => pte_array.update(offset, PteState::Alive) ];

        add nodes += [ nid => NodeState::WriteUnLocked ];
        add pte_arrays += [ nid => PteArrayState::empty() ];
        add reader_counts += [ nid => 0 ];
    }
}

/// Ensure the cursor has a write lock on the specified node and deallocates the node.
transition!{
    deallocate(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        have cursors >= [ cpu => let CursorState::WriteLocked(path) ];
        require(NodeHelper::in_subtree_range(path.last(), pa));

        remove nodes -= [ nid => NodeState::InProtocolWriteLocked ];
        remove pte_arrays -= [ nid => PteArrayState::empty() ];
        remove reader_counts -= [ nid => 0 ];

        remove pte_arrays -= [ pa => let pte_array ];
        require(pte_array.is_alive(offset));
        have nodes >= [ pa => let pa_node ];
        require(pa_node.is_write_locked());
        add pte_arrays += [ pa => pte_array.update(offset, PteState::None) ];
    }
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: CpuId) {
    assert(post.inv_nodes()) by {
        assert(post.nodes.dom() =~= Set::empty().insert(NodeHelper::root_id()));
        assert(NodeHelper::valid_nid(NodeHelper::root_id())) by {
            NodeHelper::lemma_root_id();
        };
    }
    assert(post.inv_cursors()) by {
        assert(post.cursors.dom().finite()) by {
            assert(post.cursors.dom()=~=Set::new(
                |cpu| valid_cpu(post.cpu_num, cpu),
            ));
            assert(Set::new(|cpu:CpuId| valid_cpu(post.cpu_num, cpu)).finite()) by
            {
                Self::lemma_valid_cpu_set_finite(post.cpu_num);
            }
        }
    };
    assert(post.inv_node_pte_relation()) by {
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
    }
    assert(post.inv_reader_counts_cursors_relation()) by {
        assert forall |nid: NodeId| #[trigger]post.reader_counts.contains_key(nid) implies
         post.reader_counts.index(nid) == value_filter(post.cursors, |cursor: CursorState| cursor.hold_read_lock(nid)).len() by {
                    lemma_value_filter_all_false(
                        post.cursors, |cursor: CursorState| cursor.hold_read_lock(nid)
                    );
        }
    };
}

#[inductive(locking_start)]
fn locking_start_inductive(pre: Self, post: Self, cpu: CpuId) {
    assert(post.inv_reader_counts_cursors_relation()) by {
        assert forall |nid: NodeId| #[trigger] post.reader_counts.contains_key(nid) implies
        post.reader_counts[nid] == value_filter(
            post.cursors,
            |cursor: CursorState| cursor.hold_read_lock(nid),
        ).len() by {
                let f = |cursor: CursorState| cursor.hold_read_lock(nid);
                lemma_remove_value_filter_false(
                    pre.cursors, f, cpu
                );
                lemma_insert_value_filter_false(
                    pre.cursors.remove(cpu), f, cpu, CursorState::ReadLocking(Seq::empty())
                );
            }
    };
}

#[inductive(unlocking_end)]
fn unlocking_end_inductive(pre: Self, post: Self, cpu: CpuId) {
    assert(post.inv_reader_counts_cursors_relation()) by {
        assert forall |nid: NodeId| #[trigger] post.reader_counts.contains_key(nid) implies
        post.reader_counts[nid] == value_filter(
            post.cursors,
            |cursor: CursorState| cursor.hold_read_lock(nid),
        ).len() by {
                let f = |cursor: CursorState| cursor.hold_read_lock(nid);
                lemma_remove_value_filter_false(
                    pre.cursors, f, cpu
                );
                lemma_insert_value_filter_false(
                    pre.cursors.remove(cpu), f, cpu, CursorState::Void
                );
            };
    };
}

#[inductive(read_lock)]
fn read_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    broadcast use {crate::spec::utils::group_node_helper_lemmas,
        vstd_extra::seq_extra::group_forall_seq_lemmas,
    };
    let path = pre.cursors[cpu].get_read_lock_path();
    lemma_wf_tree_path_push_inversion(path, nid);
    assert(post.cursors== pre.cursors.insert(cpu, CursorState::ReadLocking(path.push(nid))));
    assert(post.inv_reader_counts_cursors_relation()) by {
        assert forall |id: NodeId| #[trigger] post.reader_counts.contains_key(id) implies
        post.reader_counts[id] == value_filter(
            post.cursors,
            |cursor: CursorState| cursor.hold_read_lock(id),
        ).len() by {
                let f = |cursor: CursorState| cursor.hold_read_lock(id);
                if id!=nid {
                    assert(post.cursors[cpu].hold_read_lock(id) == pre.cursors[cpu].hold_read_lock(id)) by {
                        lemma_push_contains_different(path, nid, id);
                    }
                    lemma_insert_value_filter_same_len(
                        pre.cursors, f, cpu, CursorState::ReadLocking(path.push(nid))
                    )
                    }
                else {
                    assert(!pre.cursors[cpu].hold_read_lock(nid));
                    assert(post.cursors[cpu].hold_read_lock(nid)) by {
                        lemma_push_contains_same(path, nid);
                    }
                    lemma_insert_value_filter_different_len(
                        pre.cursors, f, cpu, CursorState::ReadLocking(path.push(nid))
                    );
                }
        };

    };
    assert (post.inv_write_lock_cursors_subtree_locked()) by {
        assert forall |cpu0: CpuId| #[trigger] pre.cursors.contains_key(cpu0) &&
            pre.cursors[cpu0].hold_write_lock() implies
            !NodeHelper::in_subtree_range(
                pre.cursors[cpu0].get_write_lock_node(), nid
            ) by {
                if path.len() == 0 {
                    // If the path is empty, it means we locked the root node, therefore
                    // there are no writelocked cursors in the previous state.
                    assert(nid == NodeHelper::root_id());
                    pre.lemma_write_lock_root_id_state(cpu0);
                    assert(pre.reader_counts[NodeHelper::root_id()] > 0);
                }
                else
                {
                    let locked_write_node = pre.cursors[cpu0].get_write_lock_node();
                    let read_node = pre.cursors[cpu].get_read_lock_path().last();
                    assert(pre.reader_counts[read_node]>0) by {
                        pre.lemma_inv_implies_inv_rc_positive();
                    };
                    assert(!NodeHelper::in_subtree_range(locked_write_node, read_node));
                    NodeHelper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range(
                        locked_write_node, read_node, nid);
                }
            };
    }
}

#[inductive(read_unlock)]
fn read_unlock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    let path = pre.cursors[cpu].get_read_lock_path();
    assert(post.cursors== pre.cursors.insert(cpu, CursorState::ReadLocking(path.drop_last())));
    assert(post.inv_reader_counts_cursors_relation()) by {
        assert forall |id: NodeId| #[trigger] post.reader_counts.contains_key(id) implies
        post.reader_counts[id] == value_filter(
            post.cursors,
            |cursor: CursorState| cursor.hold_read_lock(id),
        ).len() by {
                let f = |cursor: CursorState| cursor.hold_read_lock(id);
                lemma_wf_tree_path_inversion(path);
                if id!=nid {
                    assert(path.drop_last().contains(id)==path.contains(id)) by {
                        lemma_drop_last_contains_different(path, id);
                    };
                    lemma_insert_value_filter_same_len(
                        pre.cursors, f, cpu, CursorState::ReadLocking(path.drop_last())
                    );
                }
                else {
                    lemma_insert_value_filter_different_len(
                        pre.cursors, f, cpu, CursorState::ReadLocking(path.drop_last())
                    );
                }
        };
    };
    assert(pre.reader_counts[nid] > 0) by {
        broadcast use {
            vstd_extra::seq_extra::group_forall_seq_lemmas,
        };
        pre.lemma_inv_implies_inv_rc_positive()
    };
}

#[inductive(write_lock)]
fn write_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    broadcast use {crate::spec::utils::group_node_helper_lemmas,
        vstd_extra::seq_extra::group_forall_seq_lemmas,
    };
    let path = pre.cursors[cpu].get_read_lock_path();
    let read_node = path.last();
    assert(post.cursors== pre.cursors.insert(cpu, CursorState::WriteLocked(path.push(nid))));
    assert(post.cursors[cpu].get_read_lock_path() == path);
    lemma_wf_tree_path_push_inversion(path,nid);
    assert(post.inv_reader_counts_cursors_relation()) by {
        assert forall |id: NodeId| #[trigger] post.reader_counts.contains_key(id) implies
        post.reader_counts[id] == value_filter(
            post.cursors,
            |cursor: CursorState| cursor.hold_read_lock(id),
        ).len() by {
            let f = |cursor:CursorState| cursor.hold_read_lock(id);
            if id!=nid {
                lemma_insert_value_filter_same_len(
                    pre.cursors, f, cpu, CursorState::WriteLocked(path.push(nid))
                );
            }
            else {
                lemma_insert_value_filter_same_len(
                    pre.cursors, f, cpu, CursorState::WriteLocked(path.push(nid))
                );
            }
        }
    }
    assert(post.inv_write_lock_cursors_subtree_locked()) by {
       assert forall |cpu0: CpuId| #[trigger] post.cursors.contains_key(cpu0) &&
            post.cursors[cpu0].hold_write_lock() implies
            post.nodes[post.cursors[cpu0].get_write_lock_node()] is WriteLocked &&
            post.subtree_locked(post.cursors[cpu0].get_write_lock_node()) by {
                let locked_node = post.cursors[cpu0].get_write_lock_node();
                assert(NodeHelper::valid_nid(locked_node));
                if path.len() == 0 {
                    assert(nid == NodeHelper::root_id());
                    assert(pre.reader_counts[NodeHelper::root_id()] == 0);
                    if cpu != cpu0 {
                        //No write lock cursor is possible in the previous state.
                        pre.lemma_write_lock_root_id_state(cpu0);
                    } else
                    {
                        pre.lemma_read_counter_zero_implies_subtree_locked(locked_node,nid);
                    }
                } else {
                    if cpu != cpu0 {
                        assert(!NodeHelper::in_subtree_range(locked_node,nid)) by {
                            assert(NodeHelper::is_child(read_node,nid));
                            assert(pre.reader_counts[read_node]>0) by {
                                pre.lemma_inv_implies_inv_rc_positive();
                            };
                            NodeHelper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range(locked_node,read_node,nid);
                        };
                    } else
                    {
                        // nid is naturally subtree_locked
                        NodeHelper::lemma_in_subtree_self(nid);
                        pre.lemma_read_counter_zero_implies_subtree_locked(nid,nid);
                    }
                }
            }
    }
 }

 #[inductive(write_unlock)]
fn write_unlock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    assert (post.inv_reader_counts_cursors_relation()) by {
        assert forall |id: NodeId| #[trigger] post.reader_counts.contains_key(id) implies
        post.reader_counts[id] == value_filter(
            post.cursors,
            |cursor: CursorState| cursor.hold_read_lock(id),
        ).len() by {
            // The read locking state does not change.
            let f = |cursor: CursorState| cursor.hold_read_lock(id);
            assert (pre.cursors[cpu].hold_read_lock(id) == post.cursors[cpu].hold_read_lock(id));
            assert (post.cursors == pre.cursors.insert(
                cpu, CursorState::ReadLocking(pre.cursors[cpu].get_path().drop_last())
            ));
            lemma_insert_value_filter_same_len(
                pre.cursors, f, cpu, CursorState::ReadLocking(pre.cursors[cpu].get_path().drop_last())
            );
        };
    }
}

#[inductive(in_protocol_write_lock)]
fn in_protocol_write_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(in_protocol_write_unlock)]
fn in_protocol_write_unlock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(allocate)]
fn allocate_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    assert(post.inv_pte_arrays()) by {
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        assert(NodeHelper::valid_nid(pa)) by {
            NodeHelper::lemma_get_parent_sound(nid);
        };
        assert(0 <= offset < 512) by {
            NodeHelper::lemma_get_offset_sound(nid);
        };
        assert forall |id|
            #[trigger] post.pte_arrays.contains_key(id)
        implies post.pte_arrays[id].wf()
        by {
            if id == pa {
                assert(post.pte_arrays[id] =~=
                    pre.pte_arrays[id].update(offset, PteState::Alive)
                );
                assert(post.pte_arrays[id].wf());
            } else if id != nid {
                assert(pre.pte_arrays.contains_key(id));
                assert(post.pte_arrays[id] =~= pre.pte_arrays[id]);
                assert(pre.pte_arrays[id].wf());
            } else {
                assert(post.pte_arrays[id] =~= PteArrayState::empty());
                assert(post.pte_arrays[id].wf());
            }
        };
    };
    assert(post.inv_cursor_path_node_relation()) by {
        assert forall |cpu|
            post.cursors.contains_key(cpu)
        implies {
            let path = post.cursors[cpu].get_path();
            path.all(|nid| post.nodes.contains_key(nid))
        } by {
            let path = post.cursors[cpu].get_path();
            assert(post.cursors[cpu] =~= pre.cursors[cpu]);
            assert(path =~= pre.cursors[cpu].get_path());
            assert(path.all(|nid| post.nodes.contains_key(nid))) by {
                assert(pre.inv_cursor_path_node_relation());
                assert(pre.cursors.contains_key(cpu));
                assert(path.all(|nid| pre.nodes.contains_key(nid)));
                assert(post.nodes.dom() =~= pre.nodes.dom().insert(nid));
                assert(forall |id: NodeId|
                    #[trigger] pre.nodes.contains_key(id) ==>
                        post.nodes.contains_key(id)
                );
                assert forall |i|
                    0 <= i < path.len()
                implies post.nodes.contains_key(#[trigger] path[i])
                by {
                    assert(pre.nodes.contains_key(path[i])) by {
                        lemma_seq_all_index(path, |nid| pre.nodes.contains_key(nid), i);
                    };
                };
            };
        };
    };
    assert(post.inv_node_pte_relation()) by {
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        assert(NodeHelper::valid_nid(pa)) by {
            NodeHelper::lemma_get_parent_sound(nid);
        };
        assert(0 <= offset < 512) by {
            NodeHelper::lemma_get_offset_sound(nid);
        };
        assert forall |id: NodeId|
            #[trigger] NodeHelper::valid_nid(id) && id != NodeHelper::root_id()
        implies {
            post.nodes.contains_key(id) <==> {
                let pa = NodeHelper::get_parent(id);
                let offset = NodeHelper::get_offset(id);

                post.pte_arrays.contains_key(pa) &&
                post.pte_arrays[pa].is_alive(offset)
            }
        } by {
            let pa = NodeHelper::get_parent(id);
            let offset = NodeHelper::get_offset(id);
            assert(NodeHelper::valid_nid(pa)) by {
                NodeHelper::lemma_get_parent_sound(id);
            };
            assert(0 <= offset < 512) by {
                NodeHelper::lemma_get_offset_sound(id);
            };
            if id == nid {
                assert(!pre.nodes.contains_key(id));
                assert(post.nodes.contains_key(id));
                assert(post.pte_arrays[pa] =~=
                    pre.pte_arrays[pa].update(offset, PteState::Alive)
                );
            } else if pa == nid {}
            else {
                assert(pre.nodes.contains_key(id) <==> {
                    pre.pte_arrays.contains_key(pa) &&
                    pre.pte_arrays[pa].is_alive(offset)
                });
                assert(post.nodes.contains_key(id) <==>
                    pre.nodes.contains_key(id)
                );
                assert(post.pte_arrays.contains_key(pa) <==>
                    pre.pte_arrays.contains_key(pa)
                );
                if post.pte_arrays.contains_key(pa) {
                    if pa == NodeHelper::get_parent(nid) {
                        assert(offset != NodeHelper::get_offset(nid)) by {
                            NodeHelper::lemma_brothers_have_different_offset(id, nid);
                        };
                        assert(post.pte_arrays[pa] =~=
                            pre.pte_arrays[pa].update(
                                NodeHelper::get_offset(nid),
                                PteState::Alive,
                            )
                        );
                        assert(post.pte_arrays[pa].inner[offset as int] =~=
                            pre.pte_arrays[pa].inner[offset as int]
                        ) by {
                            axiom_seq_update_different(
                                pre.pte_arrays[pa].inner,
                                offset as int,
                                NodeHelper::get_offset(nid) as int,
                                PteState::Alive,
                            );
                        };
                    } else {
                        assert(post.pte_arrays[pa] =~= pre.pte_arrays[pa]);
                    }
                    assert(post.pte_arrays[pa].is_alive(offset) <==>
                        pre.pte_arrays[pa].is_alive(offset)
                    );
                }
            }
        };
    }
    assert(post.inv_reader_counts_cursors_relation()) by {
        assert(post.reader_counts[nid] == value_filter(
            post.cursors,
            |cursor: CursorState| cursor.hold_read_lock(nid),
        ).len()) by {
            assert forall |cpu|
                #[trigger] post.cursors.contains_key(cpu)
            implies !post.cursors[cpu].hold_read_lock(nid)
            by {
                assert(pre.cursors[cpu] =~= post.cursors[cpu]);
                assert(!pre.cursors[cpu].hold_read_lock(nid)) by {
                    assert(!pre.nodes.contains_key(nid));
                    if pre.cursors[cpu].hold_read_lock(nid) {
                        let path = pre.cursors[cpu].get_path();
                        assert(path.contains(nid));
                        let idx = choose |idx|
                            0 <= idx < path.len() && path[idx] == nid;
                        assert(path[idx] == nid);
                        assert(pre.nodes.contains_key(nid)) by {
                            lemma_seq_all_index(
                                path,
                                |nid| pre.nodes.contains_key(nid),
                                idx,
                            );
                        };
                    }
                }
            };
            let filtered_map = value_filter(
                post.cursors,
                |cursor: CursorState| cursor.hold_read_lock(nid),
            );
            assert(0 == filtered_map.len()) by {
                if filtered_map.len() != 0 {
                    let _cpu = filtered_map.dom().choose();
                    assert(filtered_map.contains_key(_cpu));
                    assert(filtered_map[_cpu].hold_read_lock(nid));
                }
            }
        };
    };
    assert(post.inv_rw_lock()) by {
        assert(post.inv_write_lock_cursors_subtree_locked()) by {
            assert forall |_cpu|
                #[trigger] post.cursors.contains_key(_cpu) &&
                post.cursors[_cpu].hold_write_lock()
            implies {
                let sub_rt = post.cursors[_cpu].get_write_lock_node();
                post.nodes[sub_rt] is WriteLocked &&
                post.subtree_locked(sub_rt)
            } by {
                let sub_rt = post.cursors[_cpu].get_write_lock_node();
                assert(post.nodes[sub_rt] is WriteLocked) by {
                    if sub_rt == nid {
                        assert(!pre.nodes.contains_key(nid));
                        assert(pre.nodes.contains_key(sub_rt)) by {
                            let path = pre.cursors[_cpu].get_path();
                            lemma_seq_all_index(
                                path,
                                |nid| pre.nodes.contains_key(nid),
                                path.len() - 1,
                            );
                        };
                    }
                };
            };
        };
    };
}

#[inductive(deallocate)]
fn deallocate_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    assert(post.inv_pte_arrays()) by {
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        assert(NodeHelper::valid_nid(pa)) by {
            NodeHelper::lemma_get_parent_sound(nid);
        };
        assert(0 <= offset < 512) by {
            NodeHelper::lemma_get_offset_sound(nid);
        };
        assert forall |id|
            #[trigger] post.pte_arrays.contains_key(id)
        implies post.pte_arrays[id].wf()
        by {
            if id == pa {
                assert(post.pte_arrays[id] =~=
                    pre.pte_arrays[id].update(offset, PteState::None)
                );
                assert(post.pte_arrays[id].wf());
            } else if id != nid {
                assert(pre.pte_arrays.contains_key(id));
                assert(post.pte_arrays[id] =~= pre.pte_arrays[id]);
                assert(pre.pte_arrays[id].wf());
            } else {
                assert(post.pte_arrays.contains_key(id));
            }
        };
    }
    assert(post.inv_cursor_path_node_relation()) by {
        assert forall |cpu|
            post.cursors.contains_key(cpu)
        implies {
            let path = post.cursors[cpu].get_path();
            path.all(|nid| post.nodes.contains_key(nid))
        } by {
            let path = post.cursors[cpu].get_path();
            assert(post.cursors[cpu] =~= pre.cursors[cpu]);
            assert(path =~= pre.cursors[cpu].get_path());
            assert(path.all(|nid| post.nodes.contains_key(nid))) by {
                assert(pre.inv_cursor_path_node_relation());
                assert(pre.cursors.contains_key(cpu));
                assert(path.all(|nid| pre.nodes.contains_key(nid)));
                assert(post.nodes.dom() =~= pre.nodes.dom().remove(nid));
                assert(forall |id: NodeId|
                    #[trigger] pre.nodes.contains_key(id) && id != nid ==>
                        post.nodes.contains_key(id)
                );
                assert forall |i|
                    0 <= i < path.len()
                implies post.nodes.contains_key(#[trigger] path[i])
                by {
                    assert(pre.nodes.contains_key(path[i])) by {
                        lemma_seq_all_index(path, |nid| pre.nodes.contains_key(nid), i);
                    };
                    if path[i] == nid {
                        assert(pre.nodes.contains_key(nid));
                        assert(pre.nodes[nid] !is WriteLocked);
                        assert(pre.reader_counts[nid] == 0);
                        assert(pre.nodes[nid] is WriteUnLocked || pre.nodes[nid] is WriteLocked) by {
                            if pre.cursors[cpu] is WriteLocked && i == path.len() - 1 {
                                assert(pre.nodes[nid] is WriteLocked);
                            } else {
                                assert(pre.nodes[nid] is WriteUnLocked) by {
                                    assert(pre.reader_counts[nid] > 0) by {
                                        pre.lemma_inv_implies_inv_rc_positive();
                                        let read_path = pre.cursors[cpu].get_read_lock_path();
                                        assert(pre.rc_positive(read_path));
                                        assert(0 <= i < read_path.len());
                                        assert(read_path[i] == nid);
                                        lemma_seq_all_index(
                                            read_path,
                                            |nid| pre.reader_counts[nid] > 0,
                                            i,
                                        );
                                    };
                                };
                            }
                        };
                        assert(pre.nodes[nid] is WriteUnLocked ==>
                            pre.reader_counts[nid] > 0
                        );
                    }
                };
            };
        };
    }
    assert(post.inv_node_pte_relation()) by {
        let pa = NodeHelper::get_parent(nid);
        let offset = NodeHelper::get_offset(nid);
        assert(NodeHelper::valid_nid(pa)) by {
            NodeHelper::lemma_get_parent_sound(nid);
        };
        assert(0 <= offset < 512) by {
            NodeHelper::lemma_get_offset_sound(nid);
        };
        assert forall |id: NodeId|
            #[trigger] NodeHelper::valid_nid(id) && id != NodeHelper::root_id()
        implies {
            post.nodes.contains_key(id) <==> {
                let pa = NodeHelper::get_parent(id);
                let offset = NodeHelper::get_offset(id);

                post.pte_arrays.contains_key(pa) &&
                post.pte_arrays[pa].is_alive(offset)
            }
        } by {
            let pa = NodeHelper::get_parent(id);
            let offset = NodeHelper::get_offset(id);
            assert(NodeHelper::valid_nid(pa)) by {
                NodeHelper::lemma_get_parent_sound(id);
            };
            assert(0 <= offset < 512) by {
                NodeHelper::lemma_get_offset_sound(id);
            };
            if id == nid {
                assert(pre.nodes.contains_key(id));
                assert(!post.nodes.contains_key(id));
                assert(post.pte_arrays[pa] =~=
                    pre.pte_arrays[pa].update(offset, PteState::None)
                );
            } else if pa == nid {}
            else {
                assert(pre.nodes.contains_key(id) <==> {
                    pre.pte_arrays.contains_key(pa) &&
                    pre.pte_arrays[pa].is_alive(offset)
                });
                assert(post.nodes.contains_key(id) <==>
                    pre.nodes.contains_key(id)
                );
                assert(post.pte_arrays.contains_key(pa) <==>
                    pre.pte_arrays.contains_key(pa)
                );
                if post.pte_arrays.contains_key(pa) {
                    if pa == NodeHelper::get_parent(nid) {
                        assert(offset != NodeHelper::get_offset(nid)) by {
                            NodeHelper::lemma_brothers_have_different_offset(id, nid);
                        };
                        assert(post.pte_arrays[pa] =~=
                            pre.pte_arrays[pa].update(
                                NodeHelper::get_offset(nid),
                                PteState::None,
                            )
                        );
                        assert(post.pte_arrays[pa].inner[offset as int] =~=
                            pre.pte_arrays[pa].inner[offset as int]
                        ) by {
                            axiom_seq_update_different(
                                pre.pte_arrays[pa].inner,
                                offset as int,
                                NodeHelper::get_offset(nid) as int,
                                PteState::None,
                            );
                        };
                    } else {
                        assert(post.pte_arrays[pa] =~= pre.pte_arrays[pa]);
                    }
                    assert(post.pte_arrays[pa].is_alive(offset) <==>
                        pre.pte_arrays[pa].is_alive(offset)
                    );
                }
            }
        };
    }
}

proof fn lemma_valid_cpu_set_finite(cpu_num: CpuId)
ensures
    Set::new(|cpu: CpuId| valid_cpu(cpu_num, cpu)).finite(),
    Set::new(|cpu: CpuId| valid_cpu(cpu_num, cpu)).len() == cpu_num,
{
    assert(Set::new(|cpu: CpuId| valid_cpu(cpu_num, cpu)) =~= Set::new(
        |cpu: CpuId| 0<=cpu<cpu_num,
    ));
    lemma_nat_range_finite(0, cpu_num);
}

proof fn lemma_inv_implies_inv_rc_positive(&self)
requires
    self.inv_cursors(),
    self.inv_reader_counts(),
    self.inv_reader_counts_cursors_relation(),
    self.inv_cursor_path_node_relation(),
ensures
    self.inv_rc_positive(),
{
    broadcast use {
        vstd_extra::seq_extra::group_forall_seq_lemmas,
    };
    assert forall |cpu: CpuId| #![trigger] self.cursors.contains_key(cpu) implies
        #[trigger]self.rc_positive(self.cursors[cpu].get_read_lock_path()) by {
            match self.cursors[cpu] {
                CursorState::Void => {}
                CursorState::ReadLocking(path) => {
                    assert(path == self.cursors[cpu].get_read_lock_path());
                    assert forall |i| 0 <= i < path.len() implies
                    #[trigger] self.reader_counts[path[i]] > 0 by {
                        let f = |cursor: CursorState| cursor.hold_read_lock(path[i]);
                        let filtered_cursors = value_filter(
                            self.cursors,
                            f,
                        );
                        assert(NodeHelper::valid_nid(path[i]));
                        assert(self.cursors[cpu].hold_read_lock(path[i]));
                        lemma_value_filter_finite(self.cursors, f);
                        axiom_set_contains_len(
                            filtered_cursors.dom(),
                            cpu,
                        );
                    }
                }
                CursorState::WriteLocked(path0) => {
                    let path = path0.drop_last();
                    assert(path == self.cursors[cpu].get_read_lock_path());
                    assert forall |i| 0 <= i < path.len() implies
                    #[trigger]self.reader_counts[path[i]] > 0 by {
                        let f = |cursor: CursorState| cursor.hold_read_lock(path[i]);
                        let filtered_cursors = value_filter(
                            self.cursors,
                            f,
                        );
                        assert(NodeHelper::valid_nid(path[i]));
                        assert(self.cursors[cpu].hold_read_lock(path[i]));
                        lemma_value_filter_finite(self.cursors, f);
                        axiom_set_contains_len(
                            filtered_cursors.dom(),
                            cpu,
                        );
                    }
                }
            }
        };
}

pub proof fn lemma_inv_implies_inv_non_overlapping(&self)
requires
    self.inv_cursors(),
    self.inv_cursor_path_node_relation(),
    self.inv_write_lock_cursors_subtree_locked(),
    self.inv_write_lock_cursors_distinct(),
ensures
    self.inv_non_overlapping(),
{
    assert forall |cpu1: CpuId, cpu2: CpuId|
        cpu1 != cpu2 &&
        #[trigger] self.cursors.contains_key(cpu1) &&
        #[trigger] self.cursors.contains_key(cpu2) &&
        self.cursors[cpu1].hold_write_lock() &&
        self.cursors[cpu2].hold_write_lock()
    implies {
        let nid1 = self.cursors[cpu1].get_write_lock_node();
        let nid2 = self.cursors[cpu2].get_write_lock_node();

        !NodeHelper::in_subtree_range(nid1, nid2) &&
        !NodeHelper::in_subtree_range(nid2, nid1)
    } by {
        let nid1 = self.cursors[cpu1].get_write_lock_node();
        let nid2 = self.cursors[cpu2].get_write_lock_node();
        assert(self.nodes.contains_key(nid1)) by {
            let path = self.cursors[cpu1].get_path();
            assert(path.len() > 0);
            lemma_seq_all_index(path, |nid| self.nodes.contains_key(nid), path.len() - 1);
        };
        assert(self.nodes.contains_key(nid2)) by {
            let path = self.cursors[cpu2].get_path();
            assert(path.len() > 0);
            lemma_seq_all_index(path, |nid| self.nodes.contains_key(nid), path.len() - 1);
        };
    };
}

/// If any cursor holds a write lock, the root node is either WriteLocked or has a positive reader count.
proof fn lemma_write_lock_root_id_state(&self, cpu: CpuId)
requires
    valid_cpu(self.cpu_num, cpu),
    self.cursors[cpu].hold_write_lock(),
    self.inv_cursors(),
    self.inv_reader_counts(),
    self.inv_reader_counts_cursors_relation(),
    self.inv_cursor_path_node_relation(),
    self.inv_write_lock_cursors_subtree_locked(),
ensures
    self.nodes[NodeHelper::root_id()] is WriteLocked ||
    self.reader_counts[NodeHelper::root_id()] > 0,
{
    broadcast use {
        vstd_extra::seq_extra::group_forall_seq_lemmas,
    };
    assert(self.cursors.contains_key(cpu));
    let path = self.cursors[cpu].get_path();
    if(path.len() == 1){
        assert(self.cursors[cpu].get_write_lock_node() == NodeHelper::root_id());
        assert(self.nodes[NodeHelper::root_id()] is WriteLocked);
    } else
    {
        assert(self.cursors[cpu].get_read_lock_path()[0] == NodeHelper::root_id());
        self.lemma_inv_implies_inv_rc_positive();
    }
}

/// If the reader count for a node is zero, then all its children in the subtree also have zero reader counts.
proof fn lemma_read_counter_zero_implies_subtree_zero(&self, nid: NodeId, child: NodeId)
requires
    self.inv_nodes(),
    self.inv_cursors(),
    self.inv_reader_counts(),
    self.inv_reader_counts_cursors_relation(),
    self.inv_cursor_path_node_relation(),
    self.inv_write_lock_nodes_cursors_relation(),
    self.nodes.contains_key(nid),
    self.reader_counts[nid] == 0,
    self.nodes.contains_key(child),
    NodeHelper::in_subtree_range(nid, child),
ensures
    self.reader_counts[child] == 0,
    nid != child ==> self.nodes[child] !is WriteLocked,
{
    broadcast use {
                vstd_extra::seq_extra::group_forall_seq_lemmas,
            };
    NodeHelper::lemma_in_subtree_iff_in_subtree_range(nid,child);
    let f = |cursor: CursorState| cursor.hold_read_lock(child);
    if nid == child {}
    else
    {
        broadcast use {
            vstd_extra::map_extra::group_forall_map_lemmas,
            vstd_extra::map_extra::group_value_filter_lemmas,
            crate::spec::utils::group_node_helper_lemmas,
        };
        if child == NodeHelper::root_id() {}
        else
        {
            if self.reader_counts[child] > 0 {
                // If the child has positive reader count, then there must be a cursor holding a read lock on it,
                // then the cursor must also hold nid.
                let cursor_cpu = choose |cpu| value_filter(self.cursors, f).contains_key(cpu);
                assert(value_filter(self.cursors,f).dom().finite());
                assert(value_filter(self.cursors,f).len() != 0);
                lemma_value_filter_choose(self.cursors, f);
                assert(self.cursors.contains_key(cursor_cpu)) by
                {
                    lemma_value_filter_contains_key(self.cursors,f,cursor_cpu);
                }
                self.cursors[cursor_cpu].lemma_get_read_lock_path_is_prefix_of_get_path();
                let path = self.cursors[cursor_cpu].get_path();
                let read_path = self.cursors[cursor_cpu].get_read_lock_path();
                assert (self.reader_counts[nid] > 0) by {
                    assert (read_path.contains(child));
                    lemma_wf_tree_path_contains_descendant_implies_contains_ancestor(read_path,nid,child);
                    assert (read_path.contains(nid));
                    self.lemma_inv_implies_inv_rc_positive();
                };
            }
            if self.nodes[child] is WriteLocked {
                // If the child is WriteLocked, then there must be a cursor holding a write lock on it,
                // then the cursor must also hold nid.
                assert (self.nodes.contains_key(child));
                let cursor_cpu = choose |cpu| #[trigger] self.cursors.contains_key(cpu) &&
                    self.cursors[cpu].hold_write_lock() &&
                    self.cursors[cpu].get_write_lock_node() == child;
                let path = self.cursors[cursor_cpu].get_path();
                let read_path = self.cursors[cursor_cpu].get_read_lock_path();
                assert (self.reader_counts[nid] > 0) by {
                    assert (path.contains(nid)) by {
                        lemma_wf_tree_path_contains_descendant_implies_contains_ancestor(path,nid,child);
                    }
                    assert (read_path.contains(nid)) by
                    {
                        lemma_drop_last_contains_different(path, nid);
                    }
                    self.lemma_inv_implies_inv_rc_positive();
                };
            }
        }
    }
}

proof fn lemma_read_counter_zero_implies_subtree_locked(&self, nid: NodeId, child: NodeId)
requires
    self.inv_nodes(),
    self.inv_cursors(),
    self.inv_reader_counts(),
    self.inv_reader_counts_cursors_relation(),
    self.inv_cursor_path_node_relation(),
    self.inv_write_lock_nodes_cursors_relation(),
    self.nodes.contains_key(nid),
    self.reader_counts[nid] == 0,
    self.nodes.contains_key(child),
    NodeHelper::in_subtree_range(nid, child),
ensures
    self.subtree_locked(child),
{
    broadcast use crate::spec::utils::group_node_helper_lemmas;
    assert forall |id: NodeId|
        #[trigger] self.nodes.contains_key(id) &&
        #[trigger] NodeHelper::in_subtree_range(child, id) && id != child
    implies
        self.reader_counts[id] == 0 &&
        self.nodes[id] !is WriteLocked by {
            assert(NodeHelper::valid_nid(child)) by {
                NodeHelper::lemma_in_subtree_bounded(nid,child);
            }
            assert(NodeHelper::in_subtree_range(nid,id));
            self.lemma_read_counter_zero_implies_subtree_zero(nid,id);
        };
}

}// TreeSpec
}  // tokenized_state_machine!


} // verus!
