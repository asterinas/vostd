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
        locked: bool,
        wait_queue: Seq<usize>,
        has_woken: Seq<bool>,
        pc: Seq<Label>,
    }

    init!{
        MutexSM {
            init locked = false,
            init wait_queue = Seq::empty(),
            init has_woken = Seq::from_elem(false, NUM_PROCS),
            init pc = Seq::from_elem(Label::Start, NUM_PROCS),
        }
    }

    transition!{ pre_check_lock(thread: usize) {
        require(self.pc[thread] == Label::PreCheckLock);
        if !self.locked {
            update self.locked = true;
            update self.pc[thread] = Label::CS;
        } else {
            update self.pc[thread] = Label::WaitUntil;
        }
    }}

    transition!{ wait_until(thread: usize) {
        require(self.pc[thread] == Label::WaitUntil);
        update self.pc[thread] = Label::EnqueueWaker;
    }}

    transition!{ enqueue_waker(thread: usize) {
        require(self.pc[thread] == Label::EnqueueWaker);
        update self.wait_queue = self.wait_queue.push(thread);
        update self.pc[thread] = Label::EnqueueWakerInc;
    }}

    transition!{ enqueue_waker_inc(thread: usize) {
        require(self.pc[thread] == Label::EnqueueWakerInc);
        update self.pc[thread] = Label::CheckLock;
    }}

    transition!{ check_lock(thread: usize) {
        require(self.pc[thread] == Label::CheckLock);
        if !self.locked {
            update self.locked = true;
            update self.has_woken = self.has_woken.update(thread, true);
            update self.pc[thread] = Label::CS;
        } else {
            update self.pc[thread] = Label::CheckHasWoken;
        }
    }}

    transition!{ check_has_woken(thread: usize) {
        require(self.pc[thread] == Label::CheckHasWoken);
        assume(self.has_woken[thread]);
        update self.has_woken = self.has_woken.update(thread, false);
        update self.pc[thread] = Label::WaitUntil;
    }}

    transition!{ cs(thread: usize) {
        require(self.pc[thread] == Label::CS);
        update self.pc[thread] = Label::ReleaseLock;
    }}

    transition!{ release_lock(thread: usize) {
        require(self.pc[thread] == Label::ReleaseLock);
        update self.locked = false;
        update self.pc[thread] = Label::WakeOne;
    }}

    transition!{ wake_one(thread: usize) {
        require(self.pc[thread] == Label::WakeOne);
        if self.wait_queue.len() == 0 {
            update self.pc[thread] = Label::Done;
        } else {
            update self.pc[thread] = Label::WakeOneLoop;
        }
    }}
    }
}
} // verus!