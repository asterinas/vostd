use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

use super::common::*;
use crate::spec::utils::*;
use vstd::{set::*, set_lib::*, map_lib::*};
use vstd_extra::{seq_extra::*, set_extra::*, map_extra::*};

verus! {

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
    &&& forall |nid: NodeId| #![auto]
        self.nodes.contains_key(nid) <==> NodeHelper::valid_nid(nid)
}

/// Every reader counter should be for a valid NodeId.
#[invariant]
pub fn inv_reader_counts(&self) -> bool {
    forall |nid: NodeId| #![auto]
        self.reader_counts.contains_key(nid) <==> NodeHelper::valid_nid(nid)
}

/// Unallocated nodes should not have any reader counts.
#[invariant]
pub fn inv_unallocated_has_no_rc(&self) -> bool {
    forall |nid: NodeId| #![auto] self.reader_counts.contains_key(nid) ==> {
        self.nodes[nid] is UnAllocated ==> self.reader_counts[nid] == 0
    }
}

/// The number of cursors holding a read lock on each node should match the reader counts.
#[invariant]
pub fn rc_cursors_relation(&self) -> bool {
    forall |nid: NodeId| #![auto] self.reader_counts.contains_key(nid) ==>
        self.reader_counts[nid] == value_filter(
            self.cursors,
            |cursor: CursorState| cursor.hold_read_lock(nid),
        ).len()
}

/// If a cursor holds a read lock path, the reader count for each node in the path should be positive.
pub open spec fn rc_positive(&self, path: Seq<NodeId>) -> bool {
    forall |i| #![auto] 0 <= i < path.len() ==>
    self.reader_counts[path[i]] > 0
}

/// All cursors holding read lock paths should have positive reader counts.
#[invariant]
pub fn inv_rc_positive(&self) -> bool {
    forall |cpu: CpuId| #![auto] self.cursors.contains_key(cpu) ==>
        self.rc_positive(self.cursors[cpu].get_read_lock_path())
}

/// The number of cursors should be equal to the number of CPUs and the invariant should hold for each cursor's state.
#[invariant]
pub fn inv_cursors(&self) -> bool {
    &&& self.cursors.dom().finite()
    &&& forall |cpu: CpuId| #![auto]
        self.cursors.contains_key(cpu) <==> valid_cpu(self.cpu_num, cpu)

    &&& forall |cpu: CpuId| #![auto] self.cursors.contains_key(cpu) ==>
        self.cursors[cpu].inv()
}

/// Each node with a read lock held should be in the WriteUnLocked state.
#[invariant]
pub fn inv_rw_lock(&self) -> bool {
    forall |nid: NodeId| #![auto]
        self.reader_counts.contains_key(nid) &&
        self.reader_counts[nid] > 0 ==> self.nodes[nid] is WriteUnLocked
}

#[invariant]
pub fn inv_non_overlapping(&self) -> bool {
    forall |cpu1: CpuId, cpu2: CpuId| #![auto]
        cpu1 != cpu2 &&
        self.cursors.contains_key(cpu1) &&
        self.cursors.contains_key(cpu2) ==> {
            if !self.cursors[cpu1].hold_write_lock() ||
                !self.cursors[cpu2].hold_write_lock() { true }
            else {
                let nid1 = self.cursors[cpu1].get_write_lock_node();
                let nid2 = self.cursors[cpu2].get_write_lock_node();

                !NodeHelper::in_subtree(nid1, nid2) &&
                !NodeHelper::in_subtree(nid2, nid1)
            }
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

        assert(rc > 0);
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
        require(NodeHelper::in_subtree(path.last(), nid));

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
        require(NodeHelper::in_subtree(path.last(), nid));

        remove nodes -= [ nid => NodeState::WriteUnLocked ];
        add nodes += [ nid => NodeState::UnAllocated ];
    }
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: CpuId) {
    assert(post.inv_cursors()) by{
        assert(post.cursors.dom().finite()) by{
            assert(post.cursors.dom()=~=Set::new(
                |cpu| valid_cpu(post.cpu_num, cpu),
            ));
            assert(Set::new(|cpu:CpuId| valid_cpu(post.cpu_num, cpu)).finite()) by
            {
                Self::lemma_valid_cpu_set_finite(post.cpu_num);
            }
        }
    }
    assert(post.rc_cursors_relation()) by{
        assert forall |nid: NodeId| #[trigger]post.reader_counts.contains_key(nid) implies
         post.reader_counts.index(nid) == value_filter(post.cursors, |cursor: CursorState| cursor.hold_read_lock(nid)).len() by {
                    lemma_value_filter_all_false(
                        post.cursors, |cursor: CursorState| cursor.hold_read_lock(nid)
                    );}
    }
 }

#[inductive(locking_start)]
fn locking_start_inductive(pre: Self, post: Self, cpu: CpuId) {
    assert(post.rc_cursors_relation()) by {
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
    }
 }

#[inductive(unlocking_end)]
fn unlocking_end_inductive(pre: Self, post: Self, cpu: CpuId) {
    assert(post.rc_cursors_relation()) by {
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
            }
    }
}

#[inductive(read_lock)]
fn read_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    let path = pre.cursors[cpu].get_read_lock_path();
    assert(post.cursors== pre.cursors.insert(cpu, CursorState::ReadLocking(path.push(nid))));
    assert(post.rc_cursors_relation()) by {
        assert forall |id: NodeId| #[trigger] post.reader_counts.contains_key(id) implies
        post.reader_counts[id] == value_filter(
            post.cursors,
            |cursor: CursorState| cursor.hold_read_lock(id),
        ).len() by {
                let f = |cursor: CursorState| cursor.hold_read_lock(id);
                lemma_wf_tree_path_push_inversion(path, nid);
                if id!=nid {
                    assert(post.cursors[cpu].hold_read_lock(id) == pre.cursors[cpu].hold_read_lock(id)) by {
                        lemma_push_contains_different(path, nid, id);
                    }
                    lemma_insert_value_filter_same_len(
                        pre.cursors, f, cpu, CursorState::ReadLocking(path.push(nid))
                    );
                    }
                else{
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
 }

#[inductive(read_unlock)]
fn read_unlock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    let path = pre.cursors[cpu].get_read_lock_path();
    assert(post.cursors== pre.cursors.insert(cpu, CursorState::ReadLocking(path.drop_last())));
    assert(post.rc_cursors_relation()) by {
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
                else{
                    lemma_insert_value_filter_different_len(
                        pre.cursors, f, cpu, CursorState::ReadLocking(path.drop_last())
                    );
                }
        };
    }
    assert(post.inv_rc_positive()) by {
        Self::lemma_inv_implies_inv_rc_positive(post);
    };
 }


#[inductive(write_lock)]
fn write_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    let path = pre.cursors[cpu].get_read_lock_path();
    assert(post.cursors== pre.cursors.insert(cpu, CursorState::WriteLocked(path.push(nid))));
    assert(post.cursors[cpu].get_read_lock_path() == path);
    lemma_wf_tree_path_push_inversion(path,nid);
    assert(post.rc_cursors_relation()) by {
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
            else{
                /*assert(!pre.cursors[cpu].hold_read_lock(nid));
                assert(post.cursors[cpu].hold_read_lock(nid)) by {
                    lemma_push_contains_same(path, nid);
                }
                lemma_insert_value_filter_different_len(
                    pre.cursors, f, cpu, CursorState::WriteLocked(path.push(nid))
                );*/
                admit();
            }
        }
    }
    assert(post.inv_non_overlapping()) by {
        admit();
    }
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


proof fn lemma_inv_implies_inv_rc_positive(
    s: Self
)
requires
    s.inv_reader_counts(),
    s.inv_cursors(),
    s.rc_cursors_relation(),
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

        }
}
}

}

} // verus!
