use vstd::prelude::*;
use vstd_extra::{state_machine::*, temporal_logic::*};

verus! {

pub type Tid = int;

#[derive(PartialEq, Eq, Clone, Copy)]
pub ghost enum Label {
    start,
    lock,
    unlock,
    cs,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub ghost enum Procedure {
    acquire_lock,
    release_lock,
}

pub ghost struct StackFrame {
    pub procedure: Procedure,
    pub pc: Label,
}

pub ghost struct ProgramState {
    pub num_procs: nat,
    pub locked: bool,
    pub stack: Map<Tid, Seq<StackFrame>>,
    pub pc: Map<Tid, Label>,
}

pub open spec fn init(num_procs: nat) -> StatePred<ProgramState> {
    |s: ProgramState|
        {
            &&& s.num_procs == num_procs
            &&& s.locked == false
            &&& s.stack == Map::new(|i: Tid| 0 <= i < num_procs, |i| Seq::<StackFrame>::empty())
            &&& s.pc == Map::new(|i: Tid| 0 <= i < num_procs, |i| Label::start)
        }
}

pub open spec fn lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::lock
                &&& s.locked == false
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    locked: true,
                    pc: s.pc.insert(tid, s.stack[tid].first().pc),
                    stack: s.stack.insert(tid, s.stack[tid].drop_first()),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn acquire_lock(tid: Tid) -> ActionPred<ProgramState> {
    lock().forward(tid)
}

pub open spec fn unlock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::unlock
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    locked: false,
                    pc: s.pc.insert(tid, s.stack[tid].first().pc),
                    stack: s.stack.insert(tid, s.stack[tid].drop_first()),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn release_lock(tid: Tid) -> ActionPred<ProgramState> {
    unlock().forward(tid)
}

pub open spec fn start() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::start
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let pre_stack = s.stack[tid];
                let frame = StackFrame { procedure: Procedure::acquire_lock, pc: Label::cs };
                let s_prime = ProgramState {
                    stack: s.stack.insert(
                        tid,
                        Seq::<StackFrame>::empty().push(frame).add(pre_stack),
                    ),
                    pc: s.pc.insert(tid, Label::lock),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn cs() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::cs
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let pre_stack = s.stack[tid];
                let frame = StackFrame { procedure: Procedure::release_lock, pc: Label::start };
                let s_prime = ProgramState {
                    stack: s.stack.insert(
                        tid,
                        Seq::<StackFrame>::empty().push(frame).add(pre_stack),
                    ),
                    pc: s.pc.insert(tid, Label::unlock),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn P(tid: Tid) -> ActionPred<ProgramState> {
    |s: ProgramState, s_prime: ProgramState|
        {
            ||| start().forward(tid)(s, s_prime)
            ||| cs().forward(tid)(s, s_prime)
        }
}

pub open spec fn next() -> ActionPred<ProgramState> {
    |s: ProgramState, s_prime: ProgramState|
        {
            exists|tid: Tid|
                0 <= tid < s.num_procs && {
                    ||| acquire_lock(tid)(s, s_prime)
                    ||| release_lock(tid)(s, s_prime)
                    ||| P(tid)(s, s_prime)
                }
        }
}

impl ProgramState {
    pub open spec fn valid_tid(self, tid: Tid) -> bool {
        0 <= tid < self.num_procs
    }

    pub open spec fn trying(self, tid: Tid) -> bool {
        self.pc[tid] == Label::lock
    }

    pub open spec fn mutual_exclusion(self) -> bool {
        forall|i: Tid, j: Tid|
            #![auto]
            (self.valid_tid(i) && self.valid_tid(j) && i != j) ==> !(self.pc[i] == Label::cs
                && self.pc[j] == Label::cs)
    }
}

pub open spec fn starvation_free() -> TempPred<ProgramState> {
    tla_forall(
        |i: Tid|
            lift_state(|s: ProgramState| s.valid_tid(i) && s.trying(i)).leads_to(
                lift_state(|s: ProgramState| s.pc[i] == Label::cs),
            ),
    )
}

pub open spec fn dead_and_alive_lock_free() -> TempPred<ProgramState> {
    tla_exists(
        |i: Tid|
            lift_state(|s: ProgramState| s.valid_tid(i) && s.trying(i)).leads_to(
                tla_exists(
                    |j: Tid| lift_state(|s: ProgramState| s.valid_tid(j) && s.pc[j] == Label::cs),
                ),
            ),
    )
}

pub proof fn lemma_num_procs_unchanged(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(always(lift_state(|s: ProgramState| s.num_procs == n))),
{
    init_invariant(spec, init(n), next(), |s: ProgramState| { s.num_procs == n });
}

} // verus!
