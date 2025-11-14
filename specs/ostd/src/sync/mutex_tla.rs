use vstd::prelude::*;
use vstd_extra::{state_machine::*, temporal_logic::*};

verus! {

pub type Tid = int;

#[derive(PartialEq, Eq, Clone, Copy)]
pub ghost enum Label {
    Start,
    PreCheckLock,
    WaitUntil,
    EnqueueWaker,
    EnqueueWakerIncWaker,
    CheckLock,
    CheckHasWoken,
    CS,
    ReleaseLock,
    WakeOne,
    WakeOneLoop,
    WakeUp,
    Done,
}

pub ghost enum Step {
    PreCheckLock(Tid),
    WaitUntil(Tid),
    EnqueueWaker(Tid),
    EnqueueWakerIncWaker(Tid),
    CheckLock(Tid),
    CheckHasWoken(Tid),
    CS(Tid),
    ReleaseLock(Tid),
    WakeOne(Tid),
    WakeOneLoop(Tid),
    WakeUp(Tid),
    Done(Tid),
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub ghost enum Procedure {
    Lock,
    Unlock,
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
            &&& s.pc == Map::new(|i: Tid| 0 <= i < num_procs, |i| Label::Start)
        }
}

pub open spec fn pre_check_lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::PreCheckLock
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
                    ProgramState { pc: s.pc.insert(tid, Label::WaitUntil), ..s }
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
                &&& s.pc[tid] == Label::WaitUntil
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState { pc: s.pc.insert(tid, Label::EnqueueWaker), ..s };
                (s_prime, ())
            },
    }
}

pub open spec fn enqueue_waker() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::EnqueueWaker
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    wait_queue_wakers: s.wait_queue_wakers.push(tid),
                    pc: s.pc.insert(tid, Label::EnqueueWakerIncWaker),
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
                &&& s.pc[tid] == Label::EnqueueWakerIncWaker
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    wait_queue_num_wakers: s.wait_queue_num_wakers + 1,
                    pc: s.pc.insert(tid, Label::CheckLock),
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
                &&& s.pc[tid] == Label::CheckLock
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
                    ProgramState { pc: s.pc.insert(tid, Label::CheckHasWoken), ..s }
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
                &&& s.pc[tid] == Label::CheckHasWoken
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    has_woken: s.has_woken.insert(tid, false),
                    pc: s.pc.insert(tid, Label::WaitUntil),
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
                &&& s.pc[tid] == Label::ReleaseLock
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    locked: false,
                    pc: s.pc.insert(tid, Label::WakeOne),
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
                &&& s.pc[tid] == Label::WakeOne
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
                    ProgramState { pc: s.pc.insert(tid, Label::WakeOneLoop), ..s }
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
                &&& s.pc[tid] == Label::WakeOneLoop
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = if s.wait_queue_num_wakers != 0 {
                    ProgramState {
                        waker: s.waker.insert(tid, Some(s.wait_queue_wakers.first())),
                        wait_queue_wakers: s.wait_queue_wakers.drop_first(),
                        wait_queue_num_wakers: (s.wait_queue_num_wakers - 1) as nat,
                        pc: s.pc.insert(tid, Label::WakeUp),
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
                &&& s.pc[tid] == Label::WakeUp
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
                    ProgramState { pc: s.pc.insert(tid, Label::WakeOneLoop), ..s }
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
                &&& s.pc[tid] == Label::Start
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let pre_stack = s.stack[tid];
                let frame = StackFrame {
                    procedure: Procedure::Lock,
                    pc: Label::CS,
                    waker: None::<int>,
                };
                let s_prime = ProgramState {
                    stack: s.stack.insert(
                        tid,
                        Seq::<StackFrame>::empty().push(frame).add(pre_stack),
                    ),
                    pc: s.pc.insert(tid, Label::PreCheckLock),
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
                &&& s.pc[tid] == Label::CS
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let pre_stack = s.stack[tid];
                let frame = StackFrame {
                    procedure: Procedure::Unlock,
                    pc: Label::Done,
                    waker: s.waker[tid],
                };
                let s_prime = ProgramState {
                    stack: s.stack.insert(
                        tid,
                        Seq::<StackFrame>::empty().push(frame).add(pre_stack),
                    ),
                    pc: s.pc.insert(tid, Label::ReleaseLock),
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
        self.pc[tid] == Label::PreCheckLock || self.pc[tid] == Label::WaitUntil || self.pc[tid]
            == Label::EnqueueWaker || self.pc[tid] == Label::CheckLock || self.pc[tid]
            == Label::CheckHasWoken
    }

    pub open spec fn mutual_exclusion(self) -> bool {
        forall|i: Tid, j: Tid|
            #![auto]
            (self.valid_tid(i) && self.valid_tid(j) && i != j) ==> !(self.pc[i] == Label::CS
                && self.pc[j] == Label::CS)
    }
}

spec fn starvation_free() -> TempPred<ProgramState> {
    always(
        tla_forall(
            |i: Tid|
                lift_state(|s: ProgramState| s.valid_tid(i) && s.trying(i)).leads_to(
                    lift_state(|s: ProgramState| s.pc[i] == Label::CS),
                ),
        ),
    )
}

spec fn dead_and_alive_lock_free() -> TempPred<ProgramState> {
    always(
        tla_exists(
            |i: Tid|
                lift_state(|s: ProgramState| s.valid_tid(i) && s.trying(i)).leads_to(
                    tla_exists(
                        |j: Tid|
                            lift_state(|s: ProgramState| s.valid_tid(j) && s.pc[j] == Label::CS),
                    ),
                ),
        ),
    )
}

} // verus!
