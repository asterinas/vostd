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

state_machine! {
    MutexSM {
        
    fields {
        pub num_procs: nat,
        pub locked: bool,
        pub wait_queue_num_wakers: nat,
        pub wait_queue_wakers: Seq<int>,
        pub has_woken: Map<int, bool>,
        pub waker: Map<int, Option<int>>,
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
            init waker = Map::new(|i:int| 0 <= i < num_procs, |i| None);
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

    transition!{
        wake_one(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::WakeOne;
            if pre.wait_queue_num_wakers == 0 {
                update pc = pre.pc.insert(proc_id, pre.stack[proc_id].first().pc);
                update waker = pre.waker.insert(proc_id, pre.stack[proc_id].first().waker);
                update stack = pre.stack.insert(proc_id, pre.stack[proc_id].drop_first());
            } else {
                update pc = pre.pc.insert(proc_id, Label::WakeOneLoop);
            }
        }
    }


    transition!{
        wake_one_loop(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::WakeOneLoop;
            if pre.wait_queue_num_wakers != 0 {
                update waker = pre.waker.insert(proc_id, Some(pre.wait_queue_wakers.first()));
                update wait_queue_wakers = pre.wait_queue_wakers.drop_first();
                update wait_queue_num_wakers = (pre.wait_queue_num_wakers - 1) as nat;
                update pc = pre.pc.insert(proc_id, Label::WakeUp);
            } else {
                update pc = pre.pc.insert(proc_id, pre.stack[proc_id].first().pc);
                update waker = pre.waker.insert(proc_id, pre.stack[proc_id].first().waker);
                update stack = pre.stack.insert(proc_id, pre.stack[proc_id].drop_first());
            }
        }
    }

    transition!{
        wake_up(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::WakeUp;
            require pre.waker[proc_id] != None::<int>;
            if pre.has_woken[pre.waker[proc_id].unwrap()] == false {
                update has_woken = pre.has_woken.insert(pre.waker[proc_id].unwrap(), true);
                update pc = pre.pc.insert(proc_id, pre.stack[proc_id].first().pc);
                update waker = pre.waker.insert(proc_id, pre.stack[proc_id].first().waker);
                update stack = pre.stack.insert(proc_id, pre.stack[proc_id].drop_first());
            } else {
                update pc = pre.pc.insert(proc_id, Label::WakeOneLoop);
            }
        }
    }

    transition!{
        start(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::Start;
            let pre_stack = pre.stack[proc_id];
            let frame = StackFrame {
                procedure: Procedure::Lock,
                pc: Label::CS,
                waker: None,
            };
            update stack = pre.stack.insert(proc_id, Seq::empty().push(frame).add(pre_stack));
            update pc = pre.pc.insert(proc_id, Label::PreCheckLock);
        }
    }

    transition!{
        cs(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::CS;
            let pre_stack = pre.stack[proc_id];
            let frame = StackFrame {
                procedure: Procedure::Unlock,
                pc: Label::Done,
                waker: pre.waker[proc_id],
            };
            update stack = pre.stack.insert(proc_id, Seq::empty().push(frame).add(pre_stack));
            update pc = pre.pc.insert(proc_id, Label::ReleaseLock);
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