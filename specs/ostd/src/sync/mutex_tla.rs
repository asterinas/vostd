use vstd::prelude::*;
use temporal_logic::{defs::*, rules::*};
use state_machine::action::*;

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

#[derive(PartialEq, Eq, Clone, Copy)]
pub ghost enum Procedure{
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

spec fn init(num_procs: nat) -> StatePred<ProgramState> {
    |s:ProgramState| {
        &&& s.num_procs == num_procs
        &&& s.locked == false
        &&& s.wait_queue_num_wakers == 0
        &&& s.wait_queue_wakers == Seq::<Tid>::empty()
        &&& s.has_woken == Map::new(|i:Tid| 0 <= i < num_procs, |i| false)
        &&& s.waker == Map::new(|i:Tid| 0 <= i < num_procs, |i| None::<Tid>)
        &&& s.stack == Map::new(|i:Tid| 0 <= i < num_procs, |i| Seq::<StackFrame>::empty())
        &&& s.pc == Map::new(|i:Tid| 0 <= i < num_procs, |i| Label::Start)
    }
}

spec fn pre_check_lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState| {
            &&& 0 <= tid < s.num_procs
            &&& s.pc[tid] == Label::PreCheckLock
        },
        transition: |tid: Tid, s: ProgramState| {
            let s_prime = if s.locked == false {
                ProgramState {
                    locked: true,
                    pc: s.pc.insert(tid, s.stack[tid].first().pc),
                    stack: s.stack.insert(tid, s.stack[tid].drop_first()),
                    ..s
                }
            } else
            {
                ProgramState {
                    pc: s.pc.insert(tid, Label::WaitUntil),
                    ..s
                }
            };
            (s_prime,())
            }
        }
    }

spec fn mutual_exclusion() -> StatePred<ProgramState> {
    |s:ProgramState| {
        forall |i:Tid, j:Tid| {
            (0 <= i < s.num_procs && 0 <= j < s.num_procs && i != j) ==>
            !(s.pc[i] == Label::CS && s.pc[j] == Label::CS)
        }
    }
}

}