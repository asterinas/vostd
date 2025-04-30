use builtin::*;
use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::*;
use vstd::map::*;

use super::common::*;

verus! {

state_machine!{

AtomicSpec {

fields {
    pub cpu_num: CpuId,
    pub size: nat,
    pub ranges: Map<CpuId, RangeState>,
}

#[invariant]
pub fn inv(&self) -> bool {
    &&& forall |cpu: CpuId| #![auto]
        self.ranges.contains_key(cpu) <==> valid_cpu(self.cpu_num, cpu)

    &&& forall |cpu: CpuId| #![auto] self.ranges.contains_key(cpu) ==> {
        &&& self.ranges[cpu].inv()
        &&& self.ranges[cpu].is_Empty() || self.ranges[cpu].is_Hold()
        &&& match self.ranges[cpu] {
            RangeState::Empty => true,
            RangeState::Hold(l, r) => valid_range(self.size, l, r),
            _ => true,
        }
    }

    &&& forall |cpu1: CpuId, cpu2: CpuId| #![auto]
        cpu1 != cpu2 && valid_cpu(self.cpu_num, cpu1) && valid_cpu(self.cpu_num, cpu2) ==>
            self.ranges[cpu1].no_overlap(&self.ranges[cpu2])
}

pub open spec fn all_no_overlap(&self, range: &RangeState) -> bool {
    forall |cpu: CpuId| #![auto] self.ranges.contains_key(cpu) ==> {
        range.no_overlap(&self.ranges[cpu])
    }
}

init!{
    initialize(cpu_num: CpuId, size: nat) {
        init cpu_num = cpu_num;
        init size = size;
        init ranges = Map::new(
            |cpu| valid_cpu(cpu_num, cpu),
            |i| RangeState::Empty,
        );
    }
}

transition!{
    acquire(cpu: CpuId, l: nat, r: nat) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(valid_range(pre.size, l, r));

        require(pre.ranges[cpu].is_Empty());
        let new_range = RangeState::Hold(l, r);
        require(pre.all_no_overlap(&new_range));
        update ranges = pre.ranges.insert(cpu, new_range);
    }
}

transition!{
    release(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        require(pre.ranges[cpu].is_Hold());
        let new_range = RangeState::Empty;
        update ranges = pre.ranges.insert(cpu, new_range);
    }
}

transition!{
    no_op() {}
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: CpuId, size: nat) {}

#[inductive(acquire)]
fn acquire_inductive(pre: Self, post: Self, cpu: CpuId, l: nat, r: nat) {}

#[inductive(release)]
fn release_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(no_op)]
fn no_op_inductive(pre: Self, post: Self) {}

}

}

type State = AtomicSpec::State;

type Step = AtomicSpec::Step;

// Lemmas
pub proof fn lemma_mutual_exclusion(s1: State, s2: State, cpu: CpuId, l: nat, r: nat)
    requires
        s1.invariant(),
        s2.invariant(),
        State::next_by(s1, s2, Step::acquire(cpu, l, r)),
    ensures
        s1.all_no_overlap(&RangeState::Hold(l, r)),
{
    assert({
        &&& s2.ranges[cpu] == RangeState::Hold(l, r)
        &&& s1.all_no_overlap(&s2.ranges[cpu])
    }) by {
        reveal(AtomicSpec::State::next_by);
    };
}

} // verus!
