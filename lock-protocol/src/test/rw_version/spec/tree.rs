use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

use super::common::*;
use super::utils::*;
use vstd::map_lib::*;
use vstd_extra::set_extra::lemma_nat_range_finite;

verus! {

tokenized_state_machine!{

TreeSpec {

fields {
    #[sharding(constant)]
    pub cpu_num: CpuId,

    #[sharding(map)]
    pub nodes: Map<NodeId, NodeState>,

    #[sharding(map)]
    pub reader_counts: Map<NodeId, nat>,

    #[sharding(map)]
    pub cursors: Map<CpuId, CursorState>,
}

#[invariant]
pub fn inv_nodes(&self) -> bool {
    &&& forall |nid: NodeId| #![auto]
        self.nodes.dom().contains(nid) <==> NodeHelper::valid_nid(nid)
}

pub open spec fn rc_equal(
    nid: NodeId,
    rc: nat,
    cursors: Set<CursorState>,
) -> bool
    recommends cursors.finite(),
{
    rc == cursors.filter(|cursor:CursorState| cursor.hold_read_lock(nid)).len()
}

#[invariant]
pub fn inv_reader_counts(&self) -> bool {
    forall |nid: NodeId| #![auto]
        self.reader_counts.dom().contains(nid) <==> NodeHelper::valid_nid(nid)
}

#[invariant]
pub fn inv_unallocated_has_no_rc(&self) -> bool {
    forall |nid: NodeId| #![auto] self.reader_counts.dom().contains(nid) ==> {
        self.nodes[nid] is UnAllocated ==> self.reader_counts[nid] == 0
    }
}

#[invariant]
pub fn rc_cursors_relation(&self) -> bool {
    forall |nid: NodeId| #![auto] self.reader_counts.dom().contains(nid) ==>
        Self::rc_equal(nid, self.reader_counts[nid], self.cursors.values())
}

pub open spec fn rc_positive(&self, path: Seq<NodeId>) -> bool {
    forall |i| #![auto] 0 <= i < path.len() ==>
        self.reader_counts[path[i]] > 0
}

#[invariant]
pub fn inv_cursors(&self) -> bool {
    &&& self.cursors.dom().finite()
    &&& self.cursors.values().finite()
    &&& forall |cpu: CpuId| #![auto]
        self.cursors.dom().contains(cpu) <==> valid_cpu(self.cpu_num, cpu)

    &&& forall |cpu: CpuId| #![auto] self.cursors.dom().contains(cpu) ==>
        self.cursors[cpu].inv()

    &&& forall |cpu: CpuId| #![auto] self.cursors.dom().contains(cpu) ==>
        self.rc_positive(self.cursors[cpu].get_read_lock_path())
}

#[invariant]
pub fn inv_rw_lock(&self) -> bool {
    forall |nid: NodeId| #![auto]
        self.reader_counts.dom().contains(nid) &&
        self.reader_counts[nid] > 0 ==> self.nodes[nid] is WriteUnLocked
}

#[invariant]
pub fn inv_non_overlapping(&self) -> bool {
    forall |cpu1: CpuId, cpu2: CpuId| #![auto]
        cpu1 != cpu2 &&
        self.cursors.dom().contains(cpu1) &&
        self.cursors.dom().contains(cpu2) ==> {
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

transition!{
    locking_start(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => CursorState::Void ];
        add cursors += [ cpu => CursorState::ReadLocking(Seq::empty()) ];
    }
}

transition!{
    unlocking_end(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => let CursorState::ReadLocking(path) ];
        require(path.len() == 0);
        add cursors += [ cpu => CursorState::Void ];
    }
}

transition!{
    read_lock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        have nodes >= [ nid => NodeState::WriteUnLocked ];

        remove reader_counts -= [ nid => let rc ];
        add reader_counts += [ nid => rc + 1 ];

        remove cursors -= [ cpu => let CursorState::ReadLocking(path) ];
        require(wf_tree_path(path.push(nid)));
        add cursors += [ cpu => CursorState::ReadLocking(path.push(nid)) ];
    }
}

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
        assert(post.cursors.values().finite()) by {
            lemma_values_finite(
                post.cursors);
        }
    }
    assert(post.rc_cursors_relation()) by {
        assert forall |nid: NodeId| #[trigger] post.reader_counts.dom().contains(nid) implies
        Self::rc_equal(nid, post.reader_counts[nid], post.cursors.values()) by{
            assert(post.reader_counts[nid] == 0);
            assert(post.cursors.values().filter(
                |cursor: CursorState| cursor.hold_read_lock(nid)).is_empty());
        }
    }

 }

#[inductive(locking_start)]
fn locking_start_inductive(pre: Self, post: Self, cpu: CpuId) { admit(); }

#[inductive(unlocking_end)]
fn unlocking_end_inductive(pre: Self, post: Self, cpu: CpuId) { admit(); }

#[inductive(read_lock)]
fn read_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) { admit(); }

#[inductive(read_unlock)]
fn read_unlock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) { admit(); }

#[inductive(write_lock)]
fn write_lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) { admit(); }

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


}


}

} // verus!
