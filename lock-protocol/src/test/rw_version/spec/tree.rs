use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

use super::common::*;
use crate::spec::utils::*;
use vstd::{set::*, set_lib::*, map_lib::*};
use vstd_extra::{seq_extra::*, set_extra::*, map_extra::*};

verus! {

broadcast use vstd_extra::map_extra::group_forall_map_lemmas;

tokenized_state_machine!{

TreeSpec {

fields {
    /// The number of CPUs in the system.
    #[sharding(constant)]
    pub cpu_num: CpuId,

    /// The state of each node.
    #[sharding(map)]
    pub nodes: Map<NodeId, NodeState>,

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
    forall |nid: NodeId| #![auto]
        self.nodes.contains_key(nid) <==> NodeHelper::valid_nid(nid)
}

/// Every reader counter should be for a valid NodeId.
#[invariant]
pub fn inv_reader_counts(&self) -> bool {
    forall |nid: NodeId| #![auto]
        self.reader_counts.contains_key(nid) <==> NodeHelper::valid_nid(nid)
}

/// Each cursor should be for a valid CPU, and the invariant should hold for each cursor's state.
#[invariant]
pub fn inv_cursors(&self) -> bool {
    &&& self.cursors.dom().finite()
    &&& forall |cpu: CpuId| #![auto]
        self.cursors.contains_key(cpu) <==> valid_cpu(self.cpu_num, cpu)
    &&& forall_map_values(self.cursors, |cursor: CursorState| cursor.inv())
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

/// If a cursor holds a read lock path, the reader count for each node in the path should be positive.
pub open spec fn rc_positive(&self, path: Seq<NodeId>) -> bool {
    forall_seq_values(path, |id| self.reader_counts[id] > 0)
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
    forall |id: NodeId| #![auto]
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
            |nid| NodeHelper::valid_nid(nid),
            |nid| if nid == NodeHelper::root_id() {
                NodeState::WriteUnLocked
            } else {
                NodeState::UnAllocated
            },
        );
        init reader_counts = Map::new(
            |nid| NodeHelper::valid_nid(nid),
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

        assert(rc > 0) by {
            Self::lemma_inv_implies_inv_rc_positive(pre)
        };
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

/// Ensure the cursor has a write lock on the specified node and allocates the node.
transition!{
    allocate(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        have cursors >= [ cpu => let CursorState::WriteLocked(path) ];
        require(NodeHelper::in_subtree_range(path.last(), nid));

        remove nodes -= [ nid => NodeState::UnAllocated ];
        add nodes += [ nid => NodeState::WriteUnLocked ];
    }
}

/// Ensure the cursor has a write lock on the specified node and deallocates the node.
transition!{
    deallocate(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        have cursors >= [ cpu => let CursorState::WriteLocked(path) ];
        require(NodeHelper::in_subtree_range(path.last(), nid));

        remove nodes -= [ nid => NodeState::WriteUnLocked ];
        add nodes += [ nid => NodeState::UnAllocated ];
    }
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: CpuId) {
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
                    );
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
                let locked_node = pre.cursors[cpu0].get_write_lock_node();
                let read_node = pre.cursors[cpu].get_read_lock_path().last();
                admit();
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
    admit();
}

#[inductive(write_lock)]
fn write_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    let path = pre.cursors[cpu].get_read_lock_path();
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
    admit();
 }

#[inductive(write_unlock)]
fn write_unlock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) { admit(); }

#[inductive(allocate)]
fn allocate_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) { admit(); }

#[inductive(deallocate)]
fn deallocate_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) { admit(); }

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


proof fn lemma_inv_implies_inv_rc_positive(s: Self)
requires
    s.inv_reader_counts(),
    s.inv_cursors(),
    s.inv_reader_counts_cursors_relation(),
ensures
    s.inv_rc_positive(),

{
    assert forall |cpu: CpuId| #![trigger] s.cursors.contains_key(cpu) implies
        #[trigger]s.rc_positive(s.cursors[cpu].get_read_lock_path()) by {
            match s.cursors[cpu] {
                CursorState::Void => {}
                CursorState::ReadLocking(path) => {
                    assert(path == s.cursors[cpu].get_read_lock_path());
                    assert forall |i| 0 <= i < path.len() implies
                    #[trigger]s.reader_counts[path[i]] > 0 by {
                        let f = |cursor: CursorState| cursor.hold_read_lock(path[i]);
                        let filtered_cursors = value_filter(
                            s.cursors,
                            f,
                        );
                        assert(NodeHelper::valid_nid(path[i]));
                        assert(s.cursors[cpu].hold_read_lock(path[i]));
                        lemma_value_filter_finite(s.cursors, f);
                        axiom_set_contains_len(
                            filtered_cursors.dom(),
                            cpu,
                        );
                }
                }
                CursorState::WriteLocked(path0) => {
                    let path = path0.drop_last();
                    assert(path == s.cursors[cpu].get_read_lock_path());
                    assert forall |i| 0 <= i < path.len() implies
                    #[trigger]s.reader_counts[path[i]] > 0 by {
                        let f = |cursor: CursorState| cursor.hold_read_lock(path[i]);
                        let filtered_cursors = value_filter(
                            s.cursors,
                            f,
                        );
                        assert(NodeHelper::valid_nid(path[i]));
                        assert(s.cursors[cpu].hold_read_lock(path[i]));
                        lemma_value_filter_finite(s.cursors, f);
                        axiom_set_contains_len(
                            filtered_cursors.dom(),
                            cpu,
                        );
                }
            }
        }
        };
}

proof fn lemma_inv_implies_inv_non_overlapping(s: Self)
requires
    s.inv_write_lock_cursors_subtree_locked(),
    s.inv_write_lock_cursors_distinct(),
ensures
    s.inv_non_overlapping(),
{
}

}// TreeSpec
}  // tokenized_state_machine!


} // verus!
