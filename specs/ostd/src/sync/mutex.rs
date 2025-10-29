use vstd::prelude::*;
use verus_state_machines_macros::state_machine;

verus! {
#[derive(PartialEq, Eq, Clone, Copy)]
enum Label {
    Start,
    PreCheckLock,
    WaitUntil,
    EnqueueWaker,
    EnqueueWakerInc,
    CheckLock,
    CheckHasWoken,
    CS,
    ReleaseLock,
    WakeOne,
    WakeOneLoop,
    WakeUp,
    Done,
}

state_machine! {
    MutexSM {
        
    fields {
        pub locked: bool,
        pub wait_queue: Seq<int>,
        pub has_woken: Seq<bool>,
        pub pc: Seq<Label>,
    }

    init!{
        initialize(NUM_PROCS: int) {
            init locked = false;
            init wait_queue = Seq::empty();
            init has_woken = Seq::from_elem(false, NUM_PROCS);
            init pc = Seq::from_elem(Label::Start, NUM_PROCS);
    }}

    transition!{ pre_check_lock(thread: int) {
        require(pre.pc[thread] == Label::PreCheckLock);
        if !pre.locked {
            update locked = true;
            update pc[thread] = Label::CS;
        } else {
            update pc[thread] = Label::WaitUntil;
        }
    }}

    transition!{ wait_until(thread: int) {
        require(pre.pc[thread] == Label::WaitUntil);
        update pc[thread] = Label::EnqueueWaker;
    }}

    transition!{ enqueue_waker(thread: int) {
        require(pre.pc[thread] == Label::EnqueueWaker);
        update wait_queue = pre.wait_queue.push(thread);
        update pc[thread] = Label::EnqueueWakerInc;
    }}

    transition!{ enqueue_waker_inc(thread: int) {
        require(pre.pc[thread] == Label::EnqueueWakerInc);
        update pc[thread] = Label::CheckLock;
    }}

    transition!{ check_lock(thread: int) {
        require(pre.pc[thread] == Label::CheckLock);
        if !pre.locked {
            update locked = true;
            update has_woken = pre.has_woken.update(thread, true);
            update pc[thread] = Label::CS;
        } else {
            update pc[thread] = Label::CheckHasWoken;
        }
    }}

    transition!{ check_has_woken(thread: int) {
        require(pre.pc[thread] == Label::CheckHasWoken);
        require(pre.has_woken[thread]);
        update has_woken = pre.has_woken.update(thread, false);
        update pc[thread] = Label::WaitUntil;
    }}

    transition!{ cs(thread: int) {
        require(pre.pc[thread] == Label::CS);
        update pc[thread] = Label::ReleaseLock;
    }}

    transition!{ release_lock(thread: int) {
        require(pre.pc[thread] == Label::ReleaseLock);
        update locked = false;
        update pc[thread] = Label::WakeOne;
    }}

    transition!{ wake_one(thread: int) {
        require(pre.pc[thread] == Label::WakeOne);
        if pre.wait_queue.len() == 0 {
            update pc[thread] = Label::Done;
        } else {
            update pc[thread] = Label::WakeOneLoop;
        }
    }}
    }
}
}