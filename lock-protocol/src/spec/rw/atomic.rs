use verus_state_machines_macros::state_machine;
use vstd::prelude::*;
use vstd::map::*;

use crate::spec::{common::*, utils::*};
use super::types::*;

verus! {

state_machine!{

AtomicSpec {

fields {
    pub cpu_num: CpuId,
    pub cursors: Map<CpuId, AtomicCursorState>,
}

#[invariant]
pub fn inv_cursors(&self) -> bool {
    &&& forall |cpu: CpuId| #![auto]
        self.cursors.contains_key(cpu) <==> valid_cpu(self.cpu_num, cpu)

    &&& forall |cpu: CpuId| #![auto]
        self.cursors.contains_key(cpu) &&
        self.cursors[cpu] is Locked ==>
            NodeHelper::valid_nid(self.cursors[cpu]->Locked_0)
}

#[invariant]
pub fn inv_non_overlapping(&self) -> bool {
    forall |cpu1: CpuId, cpu2: CpuId| #![auto]
        cpu1 != cpu2 &&
        self.cursors.contains_key(cpu1) &&
        self.cursors[cpu1] is Locked &&
        self.cursors.contains_key(cpu2) &&
        self.cursors[cpu2] is Locked ==> {
            let nid1 = self.cursors[cpu1]->Locked_0;
            let nid2 = self.cursors[cpu2]->Locked_0;

            !NodeHelper::in_subtree(nid1, nid2) &&
            !NodeHelper::in_subtree(nid2, nid1)
        }
}

pub open spec fn all_non_overlapping(&self, nid: NodeId) -> bool
    recommends
        NodeHelper::valid_nid(nid),
{
    forall |cpu: CpuId| #![auto]
        self.cursors.contains_key(cpu) &&
        self.cursors[cpu] is Locked ==> {
            let _nid = self.cursors[cpu]->Locked_0;

            !NodeHelper::in_subtree(nid, _nid) &&
            !NodeHelper::in_subtree(_nid, nid)
        }
}

init!{
    initialize(cpu_num: CpuId) {
        init cpu_num = cpu_num;
        init cursors = Map::new(
            |cpu| valid_cpu(cpu_num, cpu),
            |cpu| AtomicCursorState::Void,
        );
    }
}

transition!{
    lock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        require(pre.cursors[cpu] is Void);
        require(pre.all_non_overlapping(nid));
        let new_cursor = AtomicCursorState::Locked(nid);
        update cursors = pre.cursors.insert(cpu, new_cursor);
    }
}

transition!{
    unlock(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        require(pre.cursors[cpu] is Locked);
        let new_cursor = AtomicCursorState::Void;
        update cursors = pre.cursors.insert(cpu, new_cursor);
    }
}

transition!{
    no_op() {}
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: CpuId) {}

#[inductive(lock)]
fn lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(unlock)]
fn unlock_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(no_op)]
fn no_op_inductive(pre: Self, post: Self) {}

}

}

type State = AtomicSpec::State;

type Step = AtomicSpec::Step;

// Lemmas
pub proof fn lemma_mutual_exclusion(
    states: Seq<State>,
    steps: Seq<Step>,
    cpu_num: CpuId,
    cpu: CpuId,
    nid: NodeId,
)
    requires
        steps.len() >= 1,
        states.len() == steps.len() + 1,
        forall|i|
            #![auto]
            0 <= i < states.len() ==> {
                &&& states[i].invariant()
                &&& states[i].cpu_num == cpu_num
            },
        forall|i|
            #![auto]
            0 <= i < steps.len() ==> State::next_by(states[i], states[i + 1], steps[i]),
        steps[0] =~= Step::lock(cpu, nid),
        forall|i|
            #![auto]
            0 < i < steps.len() && steps[i].is_unlock() ==> {
                let _cpu = steps[i].get_unlock_0();
                cpu != _cpu
            },
        valid_cpu(cpu_num, cpu),
    ensures
        forall|i|
            #![auto]
            0 < i < states.len() ==> states[i].cursors[cpu] == AtomicCursorState::Locked(nid),
        forall|i|
            #![auto]
            0 < i < steps.len() && steps[i].is_lock() ==> {
                let _cpu = steps[i].get_lock_0();
                let _nid = steps[i].get_lock_1();

                cpu != _cpu && !NodeHelper::in_subtree(nid, _nid) && !NodeHelper::in_subtree(
                    _nid,
                    nid,
                )
            },
    decreases steps.len(),
{
    reveal(AtomicSpec::State::next_by);
    if steps.len() == 1 {
    } else {
        lemma_mutual_exclusion(states.drop_last(), steps.drop_last(), cpu_num, cpu, nid);
        let len = steps.len() as int;
        assert(states =~= states.drop_last().push(states[len]));
        assert(steps =~= steps.drop_last().push(steps[len - 1]));
    }
}

} // verus!
