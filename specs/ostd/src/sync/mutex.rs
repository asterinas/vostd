use vstd::prelude::*;
use verus_state_machines_macros::state_machine;

verus! {
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

pub ghost struct StackFrame {
    pub pc: Label,
}

state_machine! {
    MutexSM {
        
    fields {
        pub num_procs: nat,
        pub locked: bool,
        pub wait_queue_num_wakers: nat,
        pub wait_queue_wakers: Seq<int>,
        pub has_woken: Map<int, bool>,
        pub stack: Map<int, Seq<StackFrame>>,
        pub pc: Map<int, Label>,
    }

    init!{
        initialize(num_procs: nat) {
            init num_procs = num_procs;
            init locked = false;
            init wait_queue_num_wakers = 0;
            init wait_queue_wakers = Seq::empty();
            init has_woken = Map::new(|i:int| 0 <= i < num_procs, |i| false);
            init stack = Map::new(|i:int| 0 <= i < num_procs, |i| Seq::empty());
            init pc = Map::new(|i:int| 0 <= i < num_procs, |i| Label::Start);
        }
    }

    transition!{
        pre_check_lock(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::PreCheckLock;
            if pre.locked == false {
                update locked = true;
                update pc = pre.pc.insert(proc_id, pre.stack[proc_id].first().pc);
                update stack = pre.stack.insert(proc_id, pre.stack[proc_id].drop_first());
            } else {
                update pc = pre.pc.insert(proc_id, Label::WaitUntil);
            }
        }
    }

    transition!{
        wait_until(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::WaitUntil;
            update pc = pre.pc.insert(proc_id, Label::EnqueueWaker);
        }
    }

    transition!{
        enqueue_waker(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::EnqueueWaker;
            update wait_queue_wakers = pre.wait_queue_wakers.push(proc_id);
            update pc = pre.pc.insert(proc_id, Label::EnqueueWakerIncWaker);
        }
    }

    transition!{
        enqueue_waker_inc_waker(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::EnqueueWakerIncWaker;
            update wait_queue_num_wakers = pre.wait_queue_num_wakers + 1;
            update pc = pre.pc.insert(proc_id, Label::CheckLock);
        }
    }

    transition!{
        check_lock(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::CheckLock;
            if pre.locked == false {
                update locked = true;
                update has_woken = pre.has_woken.insert(proc_id, true);
                update pc = pre.pc.insert(proc_id, pre.stack[proc_id].first().pc);
                update stack = pre.stack.insert(proc_id, pre.stack[proc_id].drop_first());
            } else {
                update pc = pre.pc.insert(proc_id, Label::CheckHasWoken);
            }
        }
    }
    
    transition!{
        check_has_woken(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::CheckHasWoken;
            update has_woken = pre.has_woken.insert(proc_id, false);
            update pc = pre.pc.insert(proc_id, Label::WaitUntil);
        }
    }

    transition!{
        release_lock(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::ReleaseLock;
            update locked = false;
            update pc = pre.pc.insert(proc_id, Label::WakeOne);
        }
    }


    spec fn mutual_exclusion(self) -> bool {
        forall |i: int, j: int| {
            0 <= i < self.num_procs && 0 <= j < self.num_procs && i != j ==>
                !(self.pc[i] == Label::CS && self.pc[j] == Label::CS)
        }
    }
    }

}

} 