use builtin::*;
use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::prelude::*;

use super::utils::*;
use super::common::*;

verus! {

state_machine!{

StabilitySpec {

fields {
    pub cpu_num: CpuId,
    pub nodes: Map<NodeId, NodeStability>,
    pub cursors: Map<CpuId, CursorState>,
}

pub open spec fn valid_exclusive_lock(&self, nid: NodeId) -> bool {
    forall |cpu: CpuId| valid_cpu(self.cpu_num, nid) ==>
        !self.cursors[cpu].get_path().contains(nid)
}

#[invariant]
pub fn inv_nodes(&self) -> bool {
    forall |nid: NodeId|
        self.nodes.dom().contains(nid) <==> NodeHelper::valid_nid(nid)
}

#[invariant]
pub fn inv_cursors(&self) -> bool {
    &&& forall |cpu: CpuId|
        self.cursors.dom().contains(cpu) <==> valid_cpu(self.cpu_num, cpu)

    &&& forall |cpu: CpuId| self.cursors.dom().contains(cpu) ==>
        self.cursors[cpu].inv()
}

#[invariant]
pub fn inv_instability(&self) -> bool {
    &&& forall |cpu: CpuId|
        self.cursors.dom().contains(cpu) &&
        self.cursors[cpu].is_WriteLocked() ==> {
            let nid = self.cursors[cpu].get_write_lock_node();
            forall |_nid| NodeHelper::in_subtree(nid, _nid) ==>
                self.nodes[_nid].is_Instable()
        }

    &&& forall |nid: NodeId|
        self.nodes.dom().contains(nid) &&
        self.nodes[nid].is_Instable() ==> {
            exists |cpu: CpuId|
                self.cursors.dom().contains(cpu) &&
                self.cursors[cpu].is_WriteLocked() && {
                    let _nid = self.cursors[cpu].get_write_lock_node();
                    NodeHelper::in_subtree(_nid, nid)
                }
        }
}

#[invariant]
pub fn inv_read_stability(&self) -> bool {
    forall |cpu: CpuId| self.cursors.dom().contains(cpu) ==> {
        let read_path = self.cursors[cpu].get_read_lock_path();
        forall |i| 0 <= i < read_path.len() ==>
            self.nodes[read_path[i]].is_Stable()
    }
}

init!{
    initialize(cpu_num: CpuId) {
        init cpu_num = cpu_num;
        init nodes = Map::new(
            |nid: NodeId| NodeHelper::valid_nid(nid),
            |nid| NodeStability::Stable,
        );
        init cursors = Map::new(
            |cpu: CpuId| valid_cpu(cpu_num, cpu),
            |cpu| CursorState::Void,
        );
    }
}

transition!{
    locking_start(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        require(pre.cursors[cpu].is_Void());
        let new_cursor = CursorState::ReadLocking(Seq::empty());
        update cursors = pre.cursors.insert(cpu, new_cursor);
    }
}

transition!{
    unlocking_end(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        require(pre.cursors[cpu].is_ReadLocking());
        let path = pre.cursors[cpu].get_ReadLocking_0();
        require(path.len() == 0);
        let new_cursor = CursorState::Void;
        update cursors = pre.cursors.insert(cpu, new_cursor);
    }
}

transition!{
    read_lock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        require(pre.nodes[nid].is_Stable());

        require(pre.cursors[cpu].is_ReadLocking());
        let path = pre.cursors[cpu].get_ReadLocking_0();
        require(wf_tree_path(path.push(nid)));
        let new_cursor = CursorState::ReadLocking(path.push(nid));
        update cursors = pre.cursors.insert(cpu, new_cursor);
    }
}

transition!{
    read_unlock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        require(pre.cursors[cpu].is_ReadLocking());
        let path = pre.cursors[cpu].get_ReadLocking_0();
        require(path.len() > 0 && path.last() == nid);
        assert(wf_tree_path(path.drop_last()));
        let new_cursor = CursorState::ReadLocking(path.drop_last());
        update cursors = pre.cursors.insert(cpu, new_cursor);
    }
}

transition!{
    write_lock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        require(pre.valid_exclusive_lock(nid));
        let old_map = Map::new(
            |_nid: NodeId| NodeHelper::in_subtree(nid, _nid),
            |_nid| NodeStability::Stable,
        );
        assert(old_map.submap_of(pre.nodes)) by { admit(); };
        let new_map = Map::new(
            |_nid: NodeId| NodeHelper::in_subtree(nid, _nid),
            |_nid| NodeStability::Instable,
        );
        update nodes = pre.nodes.union_prefer_right(new_map);

        require(pre.cursors[cpu].is_ReadLocking());
        let path = pre.cursors[cpu].get_ReadLocking_0();
        require(wf_tree_path(path.push(nid)));
        let new_cursor = CursorState::WriteLocked(path.push(nid));
        update cursors = pre.cursors.insert(cpu, new_cursor);
    }
}

transition!{
    write_unlock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        let old_map = Map::new(
            |_nid: NodeId| NodeHelper::in_subtree(nid, _nid),
            |_nid| NodeStability::Instable,
        );
        assert(old_map.submap_of(pre.nodes)) by { admit(); };
        let new_map = Map::new(
            |_nid: NodeId| NodeHelper::in_subtree(nid, _nid),
            |_nid| NodeStability::Stable,
        );
        update nodes = pre.nodes.union_prefer_right(new_map);

        require(pre.cursors[cpu].is_WriteLocked());
        let path = pre.cursors[cpu].get_WriteLocked_0();
        assert(path.len() > 0);
        require(path.last() == nid);
        assert(wf_tree_path(path.drop_last()));
        let new_cursor = CursorState::ReadLocking(path.drop_last());
        update cursors = pre.cursors.insert(cpu, new_cursor);
    }
}

transition!{
    no_op() {}
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: CpuId) { admit(); }

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

#[inductive(no_op)]
fn no_op_inductive(pre: Self, post: Self) {}

}

}

} // verus!
