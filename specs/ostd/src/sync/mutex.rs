use vstd::prelude::*;
use vstd_extra::{state_machine::*, temporal_logic::*};

verus! {

pub type Tid = int;

#[derive(PartialEq, Eq, Clone, Copy)]
pub ghost enum Label {
    start,
    pre_check_lock,
    wait_until,
    enqueue_waker,
    enqueue_waker_inc_waker,
    check_lock,
    check_has_woken,
    cs,
    release_lock,
    wake_one,
    wake_one_loop,
    wake_up,
    done,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub ghost enum Procedure {
    lock,
    unlock,
}

pub ghost struct StackFrame {
    pub procedure: Procedure,
    pub pc: Label,
    pub waker: Option<int>,
}

pub ghost struct ProgramState {
    pub num_procs: nat,
    pub locked: bool,
    pub wait_queue_num_wakers: nat,
    pub wait_queue_wakers: Seq<Tid>,
    pub has_woken: Map<Tid, bool>,
    pub waker: Map<Tid, Option<Tid>>,
    pub stack: Map<Tid, Seq<StackFrame>>,
    pub pc: Map<Tid, Label>,
}

pub open spec fn init(num_procs: nat) -> StatePred<ProgramState> {
    |s: ProgramState|
        {
            &&& s.num_procs == num_procs
            &&& s.locked == false
            &&& s.wait_queue_num_wakers == 0
            &&& s.wait_queue_wakers == Seq::<Tid>::empty()
            &&& s.has_woken == Map::new(|i: Tid| 0 <= i < num_procs, |i| false)
            &&& s.waker == Map::new(|i: Tid| 0 <= i < num_procs, |i| None::<Tid>)
            &&& s.stack == Map::new(|i: Tid| 0 <= i < num_procs, |i| Seq::<StackFrame>::empty())
            &&& s.pc == Map::new(|i: Tid| 0 <= i < num_procs, |i| Label::start)
        }
}

pub open spec fn pre_check_lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::pre_check_lock
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = if s.locked == false {
                    ProgramState {
                        locked: true,
                        pc: s.pc.insert(tid, s.stack[tid].first().pc),
                        stack: s.stack.insert(tid, s.stack[tid].drop_first()),
                        ..s
                    }
                } else {
                    ProgramState { pc: s.pc.insert(tid, Label::wait_until), ..s }
                };
                (s_prime, ())
            },
    }
}

pub open spec fn wait_until() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::wait_until
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState { pc: s.pc.insert(tid, Label::enqueue_waker), ..s };
                (s_prime, ())
            },
    }
}

pub open spec fn enqueue_waker() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::enqueue_waker
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    wait_queue_wakers: s.wait_queue_wakers.push(tid),
                    pc: s.pc.insert(tid, Label::enqueue_waker_inc_waker),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn enqueue_waker_inc_waker() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::enqueue_waker_inc_waker
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    wait_queue_num_wakers: s.wait_queue_num_wakers + 1,
                    pc: s.pc.insert(tid, Label::check_lock),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn check_lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::check_lock
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = if s.locked == false {
                    ProgramState {
                        locked: true,
                        has_woken: s.has_woken.insert(tid, true),
                        pc: s.pc.insert(tid, s.stack[tid].first().pc),
                        stack: s.stack.insert(tid, s.stack[tid].drop_first()),
                        ..s
                    }
                } else {
                    ProgramState { pc: s.pc.insert(tid, Label::check_has_woken), ..s }
                };
                (s_prime, ())
            },
    }
}

pub open spec fn check_has_woken() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::check_has_woken
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    has_woken: s.has_woken.insert(tid, false),
                    pc: s.pc.insert(tid, Label::wait_until),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn release_lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::release_lock
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    locked: false,
                    pc: s.pc.insert(tid, Label::wake_one),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn wake_one() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::wake_one
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = if s.wait_queue_num_wakers == 0 {
                    ProgramState {
                        pc: s.pc.insert(tid, s.stack[tid].first().pc),
                        waker: s.waker.insert(tid, s.stack[tid].first().waker),
                        stack: s.stack.insert(tid, s.stack[tid].drop_first()),
                        ..s
                    }
                } else {
                    ProgramState { pc: s.pc.insert(tid, Label::wake_one_loop), ..s }
                };
                (s_prime, ())
            },
    }
}

pub open spec fn wake_one_loop() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::wake_one_loop
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = if s.wait_queue_num_wakers != 0 {
                    ProgramState {
                        waker: s.waker.insert(tid, Some(s.wait_queue_wakers.first())),
                        wait_queue_wakers: s.wait_queue_wakers.drop_first(),
                        wait_queue_num_wakers: (s.wait_queue_num_wakers - 1) as nat,
                        pc: s.pc.insert(tid, Label::wake_up),
                        ..s
                    }
                } else {
                    ProgramState {
                        pc: s.pc.insert(tid, s.stack[tid].first().pc),
                        waker: s.waker.insert(tid, s.stack[tid].first().waker),
                        stack: s.stack.insert(tid, s.stack[tid].drop_first()),
                        ..s
                    }
                };
                (s_prime, ())
            },
    }
}

pub open spec fn wake_up() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::wake_up
                &&& s.waker[tid] != None::<int>
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = if s.has_woken[s.waker[tid].unwrap()] == false {
                    ProgramState {
                        has_woken: s.has_woken.insert(s.waker[tid].unwrap(), true),
                        pc: s.pc.insert(tid, s.stack[tid].first().pc),
                        waker: s.waker.insert(tid, s.stack[tid].first().waker),
                        stack: s.stack.insert(tid, s.stack[tid].drop_first()),
                        ..s
                    }
                } else {
                    ProgramState { pc: s.pc.insert(tid, Label::wake_one_loop), ..s }
                };
                (s_prime, ())
            },
    }
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
                let frame = StackFrame {
                    procedure: Procedure::lock,
                    pc: Label::cs,
                    waker: None::<int>,
                };
                let s_prime = ProgramState {
                    stack: s.stack.insert(
                        tid,
                        Seq::<StackFrame>::empty().push(frame).add(pre_stack),
                    ),
                    pc: s.pc.insert(tid, Label::pre_check_lock),
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
                let frame = StackFrame {
                    procedure: Procedure::unlock,
                    pc: Label::done,
                    waker: s.waker[tid],
                };
                let s_prime = ProgramState {
                    stack: s.stack.insert(
                        tid,
                        Seq::<StackFrame>::empty().push(frame).add(pre_stack),
                    ),
                    pc: s.pc.insert(tid, Label::release_lock),
                    ..s
                };
                (s_prime, ())
            },
    }
}

impl ProgramState {
    pub open spec fn valid_tid(self, tid: Tid) -> bool {
        0 <= tid < self.num_procs
    }

    pub open spec fn trying(self, tid: Tid) -> bool {
        self.pc[tid] == Label::pre_check_lock || self.pc[tid] == Label::wait_until || self.pc[tid]
            == Label::enqueue_waker || self.pc[tid] == Label::check_lock || self.pc[tid]
            == Label::check_has_woken
    }

    pub open spec fn mutual_exclusion(self) -> bool {
        forall|i: Tid, j: Tid|
            #![auto]
            (self.valid_tid(i) && self.valid_tid(j) && i != j) ==> !(self.pc[i] == Label::cs
                && self.pc[j] == Label::cs)
    }
}

spec fn starvation_free() -> TempPred<ProgramState> {
    tla_forall(
        |i: Tid|
            lift_state(|s: ProgramState| s.valid_tid(i) && s.trying(i)).leads_to(
                lift_state(|s: ProgramState| s.pc[i] == Label::cs),
            ),
    )
}

spec fn dead_and_alive_lock_free() -> TempPred<ProgramState> {
    tla_exists(
        |i: Tid|
            lift_state(|s: ProgramState| s.valid_tid(i) && s.trying(i)).leads_to(
                tla_exists(
                    |j: Tid| lift_state(|s: ProgramState| s.valid_tid(j) && s.pc[j] == Label::cs),
                ),
            ),
    )
}

} // verus!
