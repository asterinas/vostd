use verus_state_machines_macros::state_machine;
use vstd::prelude::*;

verus! {

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
            init pc = Map::new(|i:int| 0 <= i < num_procs, |i| Label::start);
        }
    }

    transition!{
        pre_check_lock(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::pre_check_lock;
            if pre.locked == false {
                update locked = true;
                update pc = pre.pc.insert(proc_id, pre.stack[proc_id].first().pc);
                update stack = pre.stack.insert(proc_id, pre.stack[proc_id].drop_first());
            } else {
                update pc = pre.pc.insert(proc_id, Label::wait_until);
            }
        }
    }

    transition!{
        wait_until(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::wait_until;
            update pc = pre.pc.insert(proc_id, Label::enqueue_waker);
        }
    }

    transition!{
        enqueue_waker(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::enqueue_waker;
            update wait_queue_wakers = pre.wait_queue_wakers.push(proc_id);
            update pc = pre.pc.insert(proc_id, Label::enqueue_waker_inc_waker);
        }
    }

    transition!{
        enqueue_waker_inc_waker(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::enqueue_waker_inc_waker;
            update wait_queue_num_wakers = pre.wait_queue_num_wakers + 1;
            update pc = pre.pc.insert(proc_id, Label::check_lock);
        }
    }

    transition!{
        check_lock(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::check_lock;
            if pre.locked == false {
                update locked = true;
                update has_woken = pre.has_woken.insert(proc_id, true);
                update pc = pre.pc.insert(proc_id, pre.stack[proc_id].first().pc);
                update stack = pre.stack.insert(proc_id, pre.stack[proc_id].drop_first());
            } else {
                update pc = pre.pc.insert(proc_id, Label::check_has_woken);
            }
        }
    }

    transition!{
        check_has_woken(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::check_has_woken;
            update has_woken = pre.has_woken.insert(proc_id, false);
            update pc = pre.pc.insert(proc_id, Label::wait_until);
        }
    }

    transition!{
        release_lock(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::release_lock;
            update locked = false;
            update pc = pre.pc.insert(proc_id, Label::wake_one);
        }
    }

    transition!{
        wake_one(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::wake_one;
            if pre.wait_queue_num_wakers == 0 {
                update pc = pre.pc.insert(proc_id, pre.stack[proc_id].first().pc);
                update waker = pre.waker.insert(proc_id, pre.stack[proc_id].first().waker);
                update stack = pre.stack.insert(proc_id, pre.stack[proc_id].drop_first());
            } else {
                update pc = pre.pc.insert(proc_id, Label::wake_one_loop);
            }
        }
    }


    transition!{
        wake_one_loop(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::wake_one_loop;
            if pre.wait_queue_num_wakers != 0 {
                update waker = pre.waker.insert(proc_id, Some(pre.wait_queue_wakers.first()));
                update wait_queue_wakers = pre.wait_queue_wakers.drop_first();
                update wait_queue_num_wakers = (pre.wait_queue_num_wakers - 1) as nat;
                update pc = pre.pc.insert(proc_id, Label::wake_up);
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
            require pre.pc[proc_id] == Label::wake_up;
            require pre.waker[proc_id] != None::<int>;
            if pre.has_woken[pre.waker[proc_id].unwrap()] == false {
                update has_woken = pre.has_woken.insert(pre.waker[proc_id].unwrap(), true);
                update pc = pre.pc.insert(proc_id, pre.stack[proc_id].first().pc);
                update waker = pre.waker.insert(proc_id, pre.stack[proc_id].first().waker);
                update stack = pre.stack.insert(proc_id, pre.stack[proc_id].drop_first());
            } else {
                update pc = pre.pc.insert(proc_id, Label::wake_one_loop);
            }
        }
    }

    transition!{
        start(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::start;
            let pre_stack = pre.stack[proc_id];
            let frame = StackFrame {
                procedure: Procedure::lock,
                pc: Label::cs,
                waker: None,
            };
            update stack = pre.stack.insert(proc_id, Seq::empty().push(frame).add(pre_stack));
            update pc = pre.pc.insert(proc_id, Label::pre_check_lock);
        }
    }

    transition!{
        cs(proc_id: int) {
            require 0 <= proc_id < pre.num_procs;
            require pre.pc[proc_id] == Label::cs;
            let pre_stack = pre.stack[proc_id];
            let frame = StackFrame {
                procedure: Procedure::unlock,
                pc: Label::done,
                waker: pre.waker[proc_id],
            };
            update stack = pre.stack.insert(proc_id, Seq::empty().push(frame).add(pre_stack));
            update pc = pre.pc.insert(proc_id, Label::release_lock);
        }
    }

    spec fn mutual_exclusion(self) -> bool {
        forall |i: int, j: int| {
            0 <= i < self.num_procs && 0 <= j < self.num_procs && i != j ==>
                !(self.pc[i] == Label::cs && self.pc[j] == Label::cs)
        }
    }

    }

}

} // verus!
