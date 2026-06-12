// SPDX-License-Identifier: MPL-2.0
use alloc::vec::Vec;

use vstd::prelude::*;
use vstd_extra::raw_callback::RawCallback;

use crate::specs::{
    mm::cpu::{AtomicCpuSet, CpuSet},
    sync::{
        rcu as rcu_spec,
        rcu::{GracePeriodView, MonitorStateView},
        weak_memory::{History, ThreadView, WeakAtomicBool},
    },
};
use crate::sync::{LocalIrqDisabled, SpinLock};

verus! {

pub type Callbacks = Vec<RcuCallback>;

type MonitorAtomicBool =
    WeakAtomicBool<(), rcu_spec::RcuMonitorFlagGhost, rcu_spec::RcuMonitorFlagInv>;

/// RCU-specific wrapper around a type-erased executable callback.
///
/// `RawCallback` is intentionally proof-opaque. The summary records the object
/// identity that the monitor invariant will use to decide when this callback is
/// safe to run after a grace period.
#[must_use]
pub struct RcuCallback {
    raw: RawCallback,
    summary: Ghost<rcu_spec::RcuCallbackSummary>,
}

impl View for RcuCallback {
    type V = rcu_spec::RcuCallbackSummary;

    closed spec fn view(&self) -> rcu_spec::RcuCallbackSummary {
        self.summary@
    }
}

impl RcuCallback {
    /// Converts a raw callback into an RCU callback, given a proof that the callback is
    /// safe to run after a grace period.
    #[inline]
    pub fn from_raw(
        raw: RawCallback,
        Tracked(cert): Tracked<rcu_spec::RcuCallbackSafety>,
    ) -> (res: Self)
        ensures
            res@ == cert@,
    {
        let ghost summary = cert@;
        Self { raw, summary: Ghost(summary) }
    }

    /// Runs the underlying callback. The reclaim-safety precondition is not
    /// encoded here yet; the next layer will prove it from the monitor/global
    /// RCU invariant before invoking this method.
    #[inline]
    #[verifier::external_body]
    pub unsafe fn call_once(self) {
        unsafe {
            self.raw.call_once();
        }
    }
}

pub open spec fn callback_summaries(callbacks: Callbacks) -> Seq<rcu_spec::RcuCallbackSummary> {
    Seq::new(callbacks@.len(), |i: int| callbacks@[i]@)
}

proof fn callback_summaries_empty(callbacks: Callbacks)
    requires
        callbacks@ == Seq::<RcuCallback>::empty(),
    ensures
        callback_summaries(callbacks) == Seq::<rcu_spec::RcuCallbackSummary>::empty(),
{
    assert(callback_summaries(callbacks).len() == 0);
    vstd::seq_lib::assert_seqs_equal!(
        callback_summaries(callbacks) == Seq::<rcu_spec::RcuCallbackSummary>::empty()
    );
}

// The proof-facing views `GracePeriodView` and `MonitorStateView` live in
// `specs::sync::rcu` so that the monitor flag's weak-memory ghost state can
// record a state snapshot per flag message without depending on this module.
pub(super) struct GracePeriod {
    callbacks: Callbacks,
    cpu_mask: AtomicCpuSet,
    is_complete: bool,
}

impl View for GracePeriod {
    type V = GracePeriodView;

    closed spec fn view(&self) -> GracePeriodView {
        GracePeriodView {
            callbacks: callback_summaries(self.callbacks),
            is_complete: self.is_complete,
        }
    }
}

impl GracePeriod {
    /// Creates the initial completed grace period. A completed grace period may
    /// not retain callbacks, so both executable callback storage and the proof
    /// summary start empty.
    pub(super) fn new() -> (res: Self)
        ensures
            res@ == GracePeriodView::initial(),
    {
        let callbacks = Vec::new();
        let cpu_mask = AtomicCpuSet::new(CpuSet::new_empty());
        let res = Self { callbacks, cpu_mask, is_complete: true };
        proof {
            callback_summaries_empty(res.callbacks);
        }
        res
    }

    /// Starts a new incomplete grace period with the callbacks that should run
    /// after it completes. The CPU mask is reset because all CPUs must pass a
    /// fresh quiescent state for this new batch.
    fn restart(&mut self, callbacks: Callbacks)
        ensures
            final(self).callback_summaries() == callback_summaries(callbacks),
            !final(self).is_complete,
    {
        self.is_complete = false;
        self.callbacks = callbacks;
        self.cpu_mask = AtomicCpuSet::new(CpuSet::new_empty());
    }

    closed spec fn callback_summaries(self) -> Seq<rcu_spec::RcuCallbackSummary> {
        self@.callbacks
    }

    closed spec fn has_pending_work(self) -> bool {
        self@.has_pending_work()
    }

    /// Lock-protected invariant: a completed grace period has already had its
    /// callbacks taken. Monitor methods may break this transiently inside a
    /// critical section (between completing a grace period and taking its
    /// callbacks), but must restore it before releasing the monitor lock.
    closed spec fn wf(self) -> bool {
        self@.wf()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

pub(super) struct State {
    current_gp: GracePeriod,
    next_callbacks: Callbacks,
}

impl View for State {
    type V = MonitorStateView;

    closed spec fn view(&self) -> MonitorStateView {
        MonitorStateView {
            current_gp: self.current_gp@,
            next_callbacks: callback_summaries(self.next_callbacks),
        }
    }
}

impl State {
    /// Creates the lock-protected initial monitor state: there is no active
    /// grace period and no callbacks waiting to be attached to the next one.
    pub(super) fn new() -> (res: Self)
        ensures
            res@ == MonitorStateView::initial(),
            res.no_pending_work(),
    {
        let current_gp = GracePeriod::new();
        let next_callbacks = Vec::new();
        let res = Self { current_gp, next_callbacks };
        proof {
            callback_summaries_empty(res.next_callbacks);
        }
        res
    }

    /// Enqueues one callback and starts a grace period if the monitor was idle.
    ///
    /// The method preserves the lock-protected state invariant. Returning with
    /// pending work lets the caller publish `is_monitoring = true` with the
    /// resulting state view.
    fn enqueue_after_grace_period(&mut self, callback: RcuCallback)
        ensures
            final(self).wf(),
            final(self).has_pending_work(),
    {
        if self.current_gp.is_complete {
            let mut callbacks = Vec::new();
            callbacks.push(callback);
            let cpu_mask = AtomicCpuSet::new(CpuSet::new_empty());
            self.current_gp = GracePeriod { callbacks, cpu_mask, is_complete: false };
        } else {
            let mut next_callbacks = Vec::new();
            core::mem::swap(&mut next_callbacks, &mut self.next_callbacks);
            next_callbacks.push(callback);
            self.next_callbacks = next_callbacks;
        }
    }

    closed spec fn pending_summaries(self) -> Seq<rcu_spec::RcuCallbackSummary> {
        self@.pending_summaries()
    }

    closed spec fn has_pending_work(self) -> bool {
        self@.has_pending_work()
    }

    pub closed spec fn no_pending_work(self) -> bool {
        self@.no_pending_work()
    }

    /// Lock-protected invariant of the whole monitor state: the current grace
    /// period is well-formed, and a complete grace period implies an empty
    /// next-callback queue (the monitor either restarted the grace period with
    /// the queued callbacks or stopped monitoring). Holds whenever the monitor
    /// lock is free.
    closed spec fn wf(self) -> bool {
        self@.wf()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

/// Relationship maintained between one message of the weak `is_monitoring`
/// flag and the monitor-state snapshot recorded with it. A `true` flag may
/// over-approximate work, but a `false` flag must be precise enough to certify
/// no pending callbacks or grace period.
pub open spec fn monitor_flag_matches_state(flag: bool, state: MonitorStateView) -> bool {
    !flag ==> state.no_pending_work()
}

/// View-level form of the monitor flag write obligation. Executable monitor
/// code can call this while holding a guard by passing the protected state's
/// view, without moving the `State` value out of the lock.
proof fn monitor_flag_view_push_obligation(flag: bool, state: MonitorStateView)
    requires
        state.wf(),
        state.has_pending_work() ==> flag,
    ensures
        state.wf(),
        !flag ==> state.no_pending_work(),
        monitor_flag_matches_state(flag, state),
{
}

/// Every message of the monitor flag matches the state snapshot recorded with
/// it: the weak-memory history invariant implies the per-message relation
/// above, for stale messages as well as the latest one.
proof fn monitor_flag_message_matches_state(
    history: History<bool>,
    flag_ghost: rcu_spec::RcuMonitorFlagGhost,
    ts: nat,
)
    requires
        rcu_spec::rcu_monitor_flag_history_inv(history, flag_ghost),
        ts < history.len(),
    ensures
        monitor_flag_matches_state(history[ts as int].value, flag_ghost.states[ts as int]),
{
    if !history[ts as int].value {
        rcu_spec::rcu_monitor_flag_false_has_no_pending(history, flag_ghost, ts);
    }
}

/// The fast-path certificate at the executable `State` level: reading a
/// `false` flag message whose snapshot agrees with the lock-protected state
/// proves that this state has no queued callbacks and no incomplete grace
/// period. The agreement precondition is discharged by the writer protocol:
/// every flag store happens under the monitor lock and records the
/// lock-protected state as its snapshot.
proof fn monitor_flag_false_certifies_no_pending(
    history: History<bool>,
    flag_ghost: rcu_spec::RcuMonitorFlagGhost,
    ts: nat,
    state: State,
)
    requires
        rcu_spec::rcu_monitor_flag_history_inv(history, flag_ghost),
        ts < history.len(),
        !history[ts as int].value,
        flag_ghost.states[ts as int] == state@,
    ensures
        state.no_pending_work(),
        state.pending_summaries() == Seq::<rcu_spec::RcuCallbackSummary>::empty(),
{
    rcu_spec::rcu_monitor_flag_false_has_no_pending(history, flag_ghost, ts);
}

/// Bridge for the future `set_monitoring` helper: while holding the monitor
/// lock with a well-formed state, writing any flag value that over-approximates
/// the state's pending work discharges the push obligation of
/// [`rcu_spec::preserve_rcu_monitor_flag_inv_on_push`].
proof fn monitor_flag_push_obligation(flag: bool, state: State)
    requires
        state.wf(),
        state.has_pending_work() ==> flag,
    ensures
        state@.wf(),
        !flag ==> state@.no_pending_work(),
        monitor_flag_matches_state(flag, state@),
{
    monitor_flag_view_push_obligation(flag, state@);
}

/// A RCU monitor ensures the completion of _grace periods_ by keeping track
/// of each CPU's passing _quiescent states_.
pub(super) struct RcuMonitor {
    pub(super) is_monitoring: MonitorAtomicBool,
    pub(super) state: SpinLock<State, LocalIrqDisabled>,
}

impl RcuMonitor {
    /// Creates the monitor with an initially false weak flag. The flag ghost
    /// records the same initial lock-protected state snapshot, so every
    /// possible read of the initial `false` message certifies that there is no
    /// pending monitor work.
    pub(super) fn new() -> (res: Self) {
        let state = State::new();
        proof {
            rcu_spec::rcu_monitor_flag_initial_inv();
        }
        proof_decl! {
            let tracked flag_ghost = rcu_spec::RcuMonitorFlagGhost::tracked_initial();
        }
        let is_monitoring = MonitorAtomicBool::new(
            Ghost(()),
            false,
            Tracked(flag_ghost),
        );
        let state = SpinLock::new(state);
        proof {
            use_type_invariant(&is_monitoring);
            assert(is_monitoring.well_formed());
            use_type_invariant(&state);
        }
        let res = Self { is_monitoring, state };
        res
    }

    /// Stores the monitor fast-path flag together with the monitor-state
    /// snapshot that justifies the new flag message. Callers should hold the
    /// monitor lock and pass the view of the lock-protected state.
    fn set_monitoring(
        &self,
        value: bool,
        Ghost(state): Ghost<MonitorStateView>,
        Tracked(tv): Tracked<&mut ThreadView>,
    )
        requires
            self.wf(),
            state.wf(),
            state.has_pending_work() ==> value,
    {
        proof {
            use_type_invariant(self);
            monitor_flag_view_push_obligation(value, state);
        }
        self.is_monitoring.store_relaxed_rcu_monitor(value, Ghost(state), Tracked(tv));
    }

    /// Schedules `callback` to run after a future grace period and publishes a
    /// conservative `true` monitor flag message for the resulting state.
    pub(super) fn after_grace_period(&self, callback: RcuCallback) {
        proof {
            use_type_invariant(self);
        }
        let mut state = self.state.lock();
        state.enqueue_after_grace_period(callback);
        proof {
            assert(state.view().wf());
            assert(state.view().has_pending_work());
            use_type_invariant(self);
        }
        proof_decl! {
            let tracked mut tv = ThreadView::new();
        }
        self.set_monitoring(true, Ghost(state.view()@), Tracked(&mut tv));
        state.drop();
    }

    closed spec fn wf(self) -> bool {
        &&& self.is_monitoring.well_formed()
        &&& self.state.type_inv()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

} // verus!

// use vstd::{
//     atomic_ghost::AtomicBool, atomic_with_ghost, predicate::Predicate as DataPredicate, prelude::*,
// };
// use vstd_extra::ownership::Inv;

// use crate::{
//     specs::mm::cpu::{AtomicCpuSet, CpuSet},
//     sync::{AtomicDataWithOwner, LocalIrqDisabled, SpinLock, once::Predicate as OncePredicate},
// };

// verus! {

// // This thing can be very tricky to deal with
// // type Callbacks = VecDeque<Box<dyn FnOnce() + Send + 'static>>;
// pub(super) struct GracePeriod {
//     // callbacks: Callbacks,
//     cpu_mask: AtomicCpuSet,
//     is_complete: bool,
// }

// pub(super) struct State {
//     current_gp: GracePeriod,
//     // next_callbacks: Callbacks,
// }

// /// Owner of this [`RcuMonitor`].
// pub(super) tracked struct RcuMonitorOwner {}

// impl DataPredicate<RcuMonitor> for RcuMonitorOwner {
//     closed spec fn predicate(&self, v: RcuMonitor) -> bool {
//         true
//     }
// }

// impl RcuMonitor {
//     #[verifier::type_invariant]
//     closed spec fn type_inv(self) -> bool {
//         self.wf()
//     }
// }

// pub(super) struct RcuMonitorPred;

// impl OncePredicate<AtomicDataWithOwner<RcuMonitor, RcuMonitorOwner>> for RcuMonitorPred {
//     closed spec fn inv(self, v: AtomicDataWithOwner<RcuMonitor, RcuMonitorOwner>) -> bool {
//         &&& v.permission@.predicate(v.data)
//         &&& v.data.inv()
//     }
// }

// impl Inv for RcuMonitor {
//     closed spec fn inv(self) -> bool {
//         self.wf()
//     }
// }

// impl Inv for State {
//     closed spec fn inv(self) -> bool {
//         self.current_gp.inv()
//     }
// }

// impl Inv for GracePeriod {
//     closed spec fn inv(self) -> bool {
//         true
//     }
// }

// #[verus_verify]
// impl RcuMonitor {
//     /// Creates a new RCU monitor.
//     pub(super) fn new() -> Self {
//         let state = SpinLock::new(State::new());
//         proof {
//             use_type_invariant(&state);
//             assert(state.type_inv());
//         }
//         let res = RcuMonitor {
//             is_monitoring: AtomicBool::new(Ghost(state), false, Tracked(false)),
//             state,
//         };

//         proof {
//             use_type_invariant(&res.state);
//             assert(res.state.type_inv());
//             assert(res.inv());
//         }
//         res
//     }

//     /// Creates a new RCU monitor together with its tracked owner for `Once`.
//     #[verus_spec(r =>
//         ensures
//             r.inv(),
//             r.data.inv(),
//             RcuMonitorPred.inv(r),
//     )]
//     pub(super) fn new_data() -> AtomicDataWithOwner<RcuMonitor, RcuMonitorOwner> {
//         let data = Self::new();
//         proof {
//             use_type_invariant(&data);
//             assert(data.inv());
//         }
//         AtomicDataWithOwner { data, permission: Tracked(RcuMonitorOwner {  }) }
//     }

//     fn is_monitoring(&self) -> bool {
//         proof {
//             use_type_invariant(self);
//         }
//         self.is_monitoring.load()
//     }

//     fn set_monitoring(&self, value: bool) {
//         proof {
//             use_type_invariant(self);
//         }
//         atomic_with_ghost! {
//             self.is_monitoring => store(value);
//             ghost g => {
//                 g = value;
//             }
//         }
//     }
// }

// impl State {
//     fn new() -> (res: Self)
//         ensures
//             res.inv(),
//     {
//         Self { current_gp: GracePeriod::new() }
//     }
// }

// impl GracePeriod {
//     fn new() -> (res: Self)
//         ensures
//             res.inv(),
//     {
//         Self { cpu_mask: AtomicCpuSet::new(CpuSet::new_empty()), is_complete: true }
//     }
// }

// } // verus!
// /*use alloc::collections::VecDeque;
// use core::sync::atomic::{
//     AtomicBool,
//     Ordering::{self, Relaxed},
// };

// use crate::{
//     cpu::{AtomicCpuSet, CpuId, CpuSet, PinCurrentCpu},
//     prelude::*,
//     sync::SpinLock,
//     task::atomic_mode::AsAtomicModeGuard,
// };

// impl RcuMonitor {
//     /// Creates a new RCU monitor.
//     ///
//     /// This function is used to initialize a singleton instance of `RcuMonitor`.
//     /// The singleton instance is globally accessible via the `RCU_MONITOR`.
//     pub(super) fn new() -> Self {
//         Self {
//             is_monitoring: AtomicBool::new(false),
//             state: SpinLock::new(State::new()),
//         }
//     }

//     pub(super) unsafe fn finish_grace_period(&self) {
//         // Fast path
//         if !self.is_monitoring.load(Relaxed) {
//             return;
//         }

//         // Check if the current GP is complete after passing the quiescent state
//         // on the current CPU. If GP is complete, take the callbacks of the current
//         // GP.
//         let callbacks = {
//             let mut state = self.state.disable_irq().lock();
//             let cpu = state.as_atomic_mode_guard().current_cpu();
//             if state.current_gp.is_complete() {
//                 return;
//             }

//             state.current_gp.finish_grace_period(cpu);
//             if !state.current_gp.is_complete() {
//                 return;
//             }

//             // Now that the current GP is complete, take its callbacks
//             let current_callbacks = state.current_gp.take_callbacks();

//             // Check if we need to watch for a next GP
//             if !state.next_callbacks.is_empty() {
//                 let callbacks = core::mem::take(&mut state.next_callbacks);
//                 state.current_gp.restart(callbacks);
//             } else {
//                 self.is_monitoring.store(false, Relaxed);
//             }

//             current_callbacks
//         };

//         // Invoke the callbacks to notify the completion of GP
//         for f in callbacks {
//             (f)();
//         }
//     }

//     pub(super) fn after_grace_period<F>(&self, f: F)
//     where
//         F: FnOnce() + Send + 'static,
//     {
//         let mut state = self.state.disable_irq().lock();

//         state.next_callbacks.push_back(Box::new(f));

//         if !state.current_gp.is_complete() {
//             return;
//         }

//         let callbacks = core::mem::take(&mut state.next_callbacks);
//         state.current_gp.restart(callbacks);
//         self.is_monitoring.store(true, Relaxed);
//     }
// }

// impl State {
//     fn new() -> Self {
//         Self {
//             current_gp: GracePeriod::new(),
//             next_callbacks: VecDeque::new(),
//         }
//     }
// }

// impl GracePeriod {
//     fn new() -> Self {
//         Self {
//             callbacks: Callbacks::new(),
//             cpu_mask: AtomicCpuSet::new(CpuSet::new_empty()),
//             is_complete: true,
//         }
//     }

//     fn is_complete(&self) -> bool {
//         self.is_complete
//     }

//     fn finish_grace_period(&mut self, this_cpu: CpuId) {
//         self.cpu_mask.add(this_cpu, Ordering::Relaxed);

//         if self.cpu_mask.load(Ordering::Relaxed).is_full() {
//             self.is_complete = true;
//         }
//     }

//     fn take_callbacks(&mut self) -> Callbacks {
//         core::mem::take(&mut self.callbacks)
//     }

//     fn restart(&mut self, callbacks: Callbacks) {
//         self.is_complete = false;
//         self.cpu_mask.store(&CpuSet::new_empty(), Ordering::Relaxed);
//         self.callbacks = callbacks;
//     }
// }
// */
