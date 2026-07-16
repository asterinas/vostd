// SPDX-License-Identifier: MPL-2.0
use alloc::collections::VecDeque;
use core::sync::atomic::Ordering;

use vstd::{predicate::Predicate as DataPredicate, prelude::*};
use vstd_extra::raw_callback::RawCallback;

use crate::specs::{
    mm::cpu::{AtomicCpuSet, CpuId, CpuSet},
    sync::{
        rcu as rcu_spec,
        rcu::{GracePeriodView, MonitorStateView},
        weak_memory::{History, ThreadView, WeakAtomicBool},
    },
};
use crate::sync::{
    AtomicDataWithOwner, LocalIrqDisabled, SpinLock, once::Predicate as OncePredicate,
};
use crate::task::RunningTaskContext;

verus! {

pub type Callbacks = VecDeque<RcuCallback>;

type MonitorAtomicBool = WeakAtomicBool<
    (),
    rcu_spec::RcuMonitorFlagGhost,
    rcu_spec::RcuMonitorFlagInv,
>;

/// RCU-specific wrapper around a type-erased executable callback.
///
/// `RawCallback` is intentionally proof-opaque. The summary records the object
/// identity that the monitor invariant will use to decide when this callback is
/// safe to run after a grace period.
#[must_use]
pub struct RcuCallback {
    raw: RawCallback,
    summary: Ghost<rcu_spec::RcuCallbackSummary>,
    safety: Tracked<rcu_spec::RcuCallbackSafety>,
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
    fn from_raw(
        raw: RawCallback,
        Tracked(cert): Tracked<rcu_spec::RcuCallbackSafety>,
        Ghost(retire_epoch): Ghost<nat>,
    ) -> (res: Self)
        ensures
            res.wf(),
            res@ == (rcu_spec::RcuCallbackSummary {
                domain: cert.domain(),
                obj: cert.obj(),
                retire_epoch,
            }),
    {
        let ghost summary = rcu_spec::RcuCallbackSummary {
            domain: cert.domain(),
            obj: cert.obj(),
            retire_epoch,
        };
        Self { raw, summary: Ghost(summary), safety: Tracked(cert) }
    }

    /// Runs the underlying callback once the monitor has completed the grace
    /// period that contained this callback's retire summary.
    #[inline]
    #[verifier::external_body]
    unsafe fn call_once(self, Tracked(completed): Tracked<&CompletedGracePeriod>)
        requires
            self.wf(),
            completed.covers(self@),
    {
        unsafe {
            self.raw.call_once();
        }
    }

    closed spec fn wf(self) -> bool {
        self.safety@.matches(self@)
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

/// Proof token produced by the monitor when a grace period finishes.
///
/// The token is private to the monitor implementation. External code can
/// certify that a callback is safe to enqueue, but cannot manufacture the
/// completion fact needed to execute the callback.
tracked struct CompletedGracePeriod {
    ghost epoch: nat,
    ghost callbacks: Seq<rcu_spec::RcuCallbackSummary>,
}

impl CompletedGracePeriod {
    closed spec fn callbacks(self) -> Seq<rcu_spec::RcuCallbackSummary> {
        self.callbacks
    }

    closed spec fn epoch(self) -> nat {
        self.epoch
    }

    closed spec fn covers(self, callback: rcu_spec::RcuCallbackSummary) -> bool {
        &&& self.callbacks().contains(callback)
        &&& callback.retire_epoch == self.epoch()
    }
}

pub open spec fn callback_summaries(callbacks: Callbacks) -> Seq<rcu_spec::RcuCallbackSummary> {
    Seq::new(callbacks@.len(), |i: int| callbacks@[i]@)
}

fn run_completed_callbacks(
    mut callbacks: Callbacks,
    Tracked(completed): Tracked<CompletedGracePeriod>,
)
    requires
        completed.callbacks() == callback_summaries(callbacks),
        forall|i: int|
            0 <= i < callback_summaries(callbacks).len() ==> (#[trigger] callback_summaries(
                callbacks,
            )[i]).retire_epoch == completed.epoch(),
{
    proof {
        assert forall|i: int| 0 <= i < callbacks@.len() implies completed.covers(
            (#[trigger] callbacks@[i])@,
        ) by {
            callback_summaries(callbacks).lemma_index_contains(i);
        }
    }

    #[verus_spec(
        invariant
            forall|i: int|
                0 <= i < callbacks@.len() ==> completed.covers((#[trigger] callbacks@[i])@),
        decreases callbacks@.len(),
    )]
    while callbacks.len() > 0 {
        let ghost before = callbacks@;
        let callback = callbacks.pop_front().unwrap();
        proof {
            assert(completed.covers(callback@));
            assert forall|i: int| 0 <= i < callbacks@.len() implies completed.covers(
                (#[trigger] callbacks@[i])@,
            ) by {
                assert(callbacks@ == before.subrange(1, before.len() as int));
                assert(callbacks@[i] == before[i + 1]);
                assert(0 <= i + 1 < before.len());
            }
        }
        unsafe {
            proof {
                use_type_invariant(&callback);
            }
            callback.call_once(Tracked(&completed));
        }
    }
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

proof fn callback_summaries_len(callbacks: Callbacks)
    ensures
        callback_summaries(callbacks).len() == callbacks@.len(),
{
}

fn push_callback(callbacks: &mut Callbacks, callback: RcuCallback)
    ensures
        callback_summaries(*final(callbacks)) == callback_summaries(*old(callbacks)).push(
            callback@,
        ),
{
    let ghost before = callbacks@;
    callbacks.push_back(callback);
    proof {
        assert(callbacks@ == before.push(callback));
        vstd::seq_lib::assert_seqs_equal!(
            callback_summaries(*callbacks)
                == callback_summaries(*old(callbacks)).push(callback@),
            i => {
                if i < before.len() {
                    assert(callbacks@[i] == before[i]);
                } else {
                    assert(i == before.len());
                    assert(callbacks@[i] == callback);
                }
            }
        );
    }
}

// The proof-facing views `GracePeriodView` and `MonitorStateView` live in
// `specs::sync::rcu` so that the monitor flag's weak-memory ghost state can
// record a state snapshot per flag message without depending on this module.
pub(super) struct GracePeriod {
    callbacks: Callbacks,
    cpu_mask: AtomicCpuSet,
    is_complete: bool,
    ghost_epoch: Ghost<nat>,
}

impl View for GracePeriod {
    type V = GracePeriodView;

    closed spec fn view(&self) -> GracePeriodView {
        GracePeriodView {
            epoch: self.ghost_epoch@,
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
        let callbacks = Callbacks::new();
        let cpu_mask = AtomicCpuSet::new(CpuSet::new_empty());
        let res = Self { callbacks, cpu_mask, is_complete: true, ghost_epoch: Ghost(0) };
        proof {
            callback_summaries_empty(res.callbacks);
        }
        res
    }

    /// Starts a new incomplete grace period with the callbacks that should run
    /// after it completes. The CPU mask is reset because all CPUs must pass a
    /// fresh quiescent state for this new batch. Keep the same atomic object so
    /// later weak-memory ghost state can attach stable identity to this mask.
    fn restart(&mut self, callbacks: Callbacks, Ghost(epoch): Ghost<nat>)
        requires
            forall|i: int|
                0 <= i < callback_summaries(callbacks).len() ==> (#[trigger] callback_summaries(
                    callbacks,
                )[i]).retire_epoch == epoch,
        ensures
            final(self).callback_summaries() == callback_summaries(callbacks),
            final(self)@.epoch == epoch,
            !final(self).is_complete,
            final(self).wf(),
        no_unwind
    {
        self.is_complete = false;
        self.callbacks = callbacks;
        self.ghost_epoch = Ghost(epoch);
        self.cpu_mask.store(&CpuSet::new_empty(), Ordering::Relaxed);
    }

    /// Records that `this_cpu` has passed a quiescent state for this grace
    /// period and returns whether the executable CPU mask now covers all CPUs.
    ///
    /// The CPU-mask contents are not part of the current proof view, so this
    /// method refines only the executable monitor protocol. The higher-level
    /// proof still treats the returned completion bit abstractly.
    fn record_quiescent_state(&self, this_cpu: CpuId) -> (complete: bool)
        no_unwind
    {
        self.cpu_mask.add(this_cpu, Ordering::Relaxed);
        self.cpu_mask.load(Ordering::Relaxed).is_full()
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
    closed spec fn next_callback_epoch(self) -> nat {
        self@.current_gp.epoch + 1
    }

    /// Creates the lock-protected initial monitor state: there is no active
    /// grace period and no callbacks waiting to be attached to the next one.
    pub(super) fn new() -> (res: Self)
        ensures
            res@ == MonitorStateView::initial(),
            res.no_pending_work(),
    {
        let current_gp = GracePeriod::new();
        let next_callbacks = Callbacks::new();
        let res = Self { current_gp, next_callbacks };
        proof {
            callback_summaries_empty(res.next_callbacks);
        }
        res
    }

    /// Enqueues one callback and starts a grace period if the monitor was idle.
    ///
    /// This follows the upstream monitor protocol at the observable boundary:
    /// an idle monitor starts a new current grace period and the caller must
    /// publish `is_monitoring = true`; an already active monitor only appends
    /// the callback to the next batch and does not publish another flag
    /// message. The upstream implementation transiently stages the idle
    /// callback in `next_callbacks` before promoting it, but our type invariant
    /// keeps `next_callbacks` empty whenever the current grace period is
    /// complete, so the idle case constructs the current batch directly.
    fn enqueue_after_grace_period(&mut self, callback: RcuCallback) -> (started_gp: bool)
        requires
            callback.wf(),
            callback@.retire_epoch == old(self).next_callback_epoch(),
        ensures
            final(self).wf(),
            final(self).has_pending_work(),
            started_gp ==> !final(self)@.current_gp.is_complete,
            !started_gp ==> !old(self)@.current_gp.is_complete,
    {
        proof {
            use_type_invariant(&*self);
        }
        let ghost callback_epoch = self.next_callback_epoch();
        if self.current_gp.is_complete {
            let mut callbacks = Callbacks::new();
            push_callback(&mut callbacks, callback);
            proof {
                assert(callback_summaries(callbacks).len() == 1);
                assert(callback_summaries(self.next_callbacks).len() == 0);
            }
            self.current_gp.restart(callbacks, Ghost(callback_epoch));
            true
        } else {
            let mut next_callbacks = Callbacks::new();
            let ghost existing_summaries = callback_summaries(self.next_callbacks);
            proof {
                assert(self.current_gp.wf());
                assert(!self.current_gp.is_complete);
                assert(self.wf());
                assert(self@.wf());
                assert(self@.next_callbacks == existing_summaries);
                assert forall|i: int| 0 <= i < existing_summaries.len() implies (
                #[trigger] existing_summaries[i]).retire_epoch == self.current_gp@.epoch + 1 by {};
            }
            core::mem::swap(&mut next_callbacks, &mut self.next_callbacks);
            let ghost before_summaries = callback_summaries(next_callbacks);
            proof {
                assert(before_summaries == existing_summaries);
            }
            push_callback(&mut next_callbacks, callback);
            proof {
                assert forall|i: int| 0 <= i < callback_summaries(next_callbacks).len() implies (
                #[trigger] callback_summaries(next_callbacks)[i]).retire_epoch
                    == self.current_gp@.epoch + 1 by {
                    if i < before_summaries.len() {
                        assert(callback_summaries(next_callbacks)[i] == before_summaries[i]);
                    } else {
                        assert(i == before_summaries.len());
                        assert(callback_summaries(next_callbacks)[i] == callback@);
                    }
                };
            }
            self.next_callbacks = next_callbacks;
            false
        }
    }

    /// Records a quiescent state for the current CPU, returns the callbacks
    /// that become reclaimable if this completes the grace period, and
    /// immediately starts the next grace period if callbacks accumulated while
    /// the current one was running.
    ///
    /// This mirrors the upstream state machine: an incomplete CPU mask leaves
    /// the current grace period running and returns no completed callbacks.
    /// The exact CPU-mask contents are still outside the proof view; the proof
    /// treats `record_quiescent_state`'s boolean result as the completion cut.
    fn finish_grace_period(&mut self, this_cpu: CpuId) -> ((
        completed_gp,
        completed_callbacks,
        completed_token,
    ): (bool, Callbacks, Tracked<CompletedGracePeriod>))
        ensures
            final(self).wf(),
            completed_token@.callbacks() == callback_summaries(completed_callbacks),
            completed_gp ==> !old(self)@.current_gp.is_complete,
            completed_gp ==> completed_token@.callbacks() == old(self)@.current_gp.callbacks,
            completed_gp ==> completed_token@.epoch() == old(self)@.current_gp.epoch,
            !completed_gp ==> completed_token@.callbacks() == Seq::<
                rcu_spec::RcuCallbackSummary,
            >::empty(),
            forall|i: int|
                0 <= i < callback_summaries(completed_callbacks).len() ==> (
                #[trigger] callback_summaries(completed_callbacks)[i]).retire_epoch
                    == completed_token@.epoch(),
            (!completed_gp && !(old(self)@.current_gp.is_complete)) ==> !(
            final(self)@.current_gp.is_complete),
    {
        proof {
            use_type_invariant(&*self);
        }
        let ghost initially_complete = self.current_gp.is_complete;
        let ghost initial_current_callbacks = self.current_gp@.callbacks;
        let ghost initial_current_epoch = self.current_gp@.epoch;
        let ghost initial_next_callbacks = callback_summaries(self.next_callbacks);
        proof {
            assert(self.wf());
            assert(self@.wf());
            assert(self@.next_callbacks == initial_next_callbacks);
            assert forall|i: int| 0 <= i < initial_current_callbacks.len() implies (
            #[trigger] initial_current_callbacks[i]).retire_epoch == initial_current_epoch by {
                assert(self.current_gp.wf());
            };
            assert forall|i: int| 0 <= i < initial_next_callbacks.len() implies (
            #[trigger] initial_next_callbacks[i]).retire_epoch == initial_current_epoch + 1 by {
                assert(self.wf());
            };
        }
        let mut completed_callbacks = Callbacks::new();
        let mut completed_gp = false;
        if !self.current_gp.is_complete {
            let is_complete = self.current_gp.record_quiescent_state(this_cpu);
            if is_complete {
                completed_gp = true;
                core::mem::swap(&mut completed_callbacks, &mut self.current_gp.callbacks);
                proof {
                    assert(callback_summaries(completed_callbacks) == initial_current_callbacks);
                    callback_summaries_empty(self.current_gp.callbacks);
                }
                if self.next_callbacks.len() > 0 {
                    let mut next_callbacks = Callbacks::new();
                    core::mem::swap(&mut next_callbacks, &mut self.next_callbacks);
                    proof {
                        callback_summaries_empty(self.next_callbacks);
                        assert(callback_summaries(next_callbacks) == initial_next_callbacks);
                    }
                    self.current_gp.restart(next_callbacks, Ghost(initial_current_epoch + 1));
                } else {
                    self.current_gp.is_complete = true;
                    proof {
                        callback_summaries_empty(self.current_gp.callbacks);
                        callback_summaries_len(self.next_callbacks);
                        assert(self.next_callbacks@.len() == 0);
                        assert(callback_summaries(self.next_callbacks).len() == 0);
                    }
                }
            }
        }
        proof_decl! {
            let tracked completed = CompletedGracePeriod {
                epoch: if completed_gp { initial_current_epoch } else { 0 },
                callbacks: callback_summaries(completed_callbacks),
            };
        }
        proof {
            callback_summaries_len(self.current_gp.callbacks);
            callback_summaries_len(self.next_callbacks);
            assert(completed.callbacks() == callback_summaries(completed_callbacks));
            if !completed_gp {
                callback_summaries_empty(completed_callbacks);
            } else {
                assert(!initially_complete);
                assert(callback_summaries(completed_callbacks) == initial_current_callbacks);
                assert forall|i: int|
                    0 <= i < callback_summaries(completed_callbacks).len() implies (
                #[trigger] callback_summaries(completed_callbacks)[i]).retire_epoch
                    == completed.epoch() by {
                    assert(callback_summaries(completed_callbacks)[i]
                        == initial_current_callbacks[i]);
                };
            }
            if initially_complete {
                assert(initial_current_callbacks.len() == 0);
                vstd::seq_lib::assert_seqs_equal!(
                    initial_current_callbacks == Seq::<rcu_spec::RcuCallbackSummary>::empty()
                );
            }
            if self.current_gp.is_complete {
                if initially_complete {
                    assert(self.wf());
                }
                assert(self.current_gp@.callbacks.len() == 0);
                assert(self.next_callbacks@.len() == 0);
                assert(callback_summaries(self.next_callbacks).len() == 0);
            }
            assert(self.current_gp.wf());
            assert(self.wf());
        }
        (completed_gp, completed_callbacks, Tracked(completed))
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
        let is_monitoring = MonitorAtomicBool::new(Ghost(()), false, Tracked(flag_ghost));
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

    /// Schedules `callback` to run after a future grace period.
    ///
    /// Matches the upstream protocol: callbacks are first queued for the next
    /// grace period. Only an idle monitor promotes that queue into a new
    /// current grace period and publishes a `true` flag; if a grace period is
    /// already running, the existing monitor flag is left unchanged.
    #[verus_spec(
        with
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
        ensures
            final(session).wf(),
            final(session).task() == old(session).task(),
            final(session).session_id() == old(session).session_id(),
            final(session).available_fractions() == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth(),
    )]
    pub(super) fn after_grace_period(
        &self,
        raw: RawCallback,
        cert: Tracked<rcu_spec::RcuCallbackSafety>,
    ) {
        proof {
            use_type_invariant(self);
        }
        let mut state = self.state.lock();
        let ghost retire_epoch = state.view()@.current_gp.epoch + 1;
        proof_decl! {
            let tracked cert = cert.get();
        }
        let callback = RcuCallback::from_raw(raw, Tracked(cert), Ghost(retire_epoch));
        let started_gp = state.enqueue_after_grace_period(callback);
        if started_gp {
            proof {
                assert(state.view().wf());
                assert(state.view().has_pending_work());
                use_type_invariant(self);
            }
            proof_decl! {
                let tracked tv = session.tracked_borrow_thread_view_mut();
            }
            self.set_monitoring(true, Ghost(state.view()@), Tracked(tv));
        }
        state.drop();
    }

    /// Reports this CPU's quiescent state and runs a completed callback batch
    /// outside the monitor lock.
    ///
    /// The control flow is aligned with upstream: a relaxed false flag returns
    /// immediately, a stale true flag may still find a completed state under
    /// the lock and return, an incomplete CPU mask keeps monitoring without
    /// touching the flag, and callback bodies run outside the monitor lock.
    #[verus_spec(
        with
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
            old(session).is_quiescent(),
        ensures
            final(session).wf(),
            final(session).is_quiescent(),
            final(session).task() == old(session).task(),
            final(session).session_id() == old(session).session_id(),
            final(session).available_fractions() == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth(),
    )]
    pub(super) unsafe fn finish_grace_period(&self) {
        proof {
            use_type_invariant(self);
        }
        proof_decl! {
            let tracked fast_tv = session.tracked_borrow_thread_view_mut();
        }
        let is_monitoring = self.is_monitoring.load_relaxed(Tracked(fast_tv)).0;
        if !is_monitoring {
            return;
        }
        let mut state = self.state.lock();
        if state.current_gp.is_complete {
            state.drop();
            return;
        }
        let this_cpu = CpuId::current();
        let (completed_gp, completed_callbacks, Tracked(completed)) = state.finish_grace_period(
            this_cpu,
        );
        if !completed_gp {
            state.drop();
            return;
        }
        if state.current_gp.is_complete {
            proof {
                assert(state.view().wf());
                rcu_spec::monitor_state_pending_iff_incomplete(state.view()@);
                assert(state.view()@.no_pending_work());
                use_type_invariant(self);
            }
            proof_decl! {
                let tracked tv = session.tracked_borrow_thread_view_mut();
            }
            self.set_monitoring(false, Ghost(state.view()@), Tracked(tv));
        }
        state.drop();
        run_completed_callbacks(completed_callbacks, Tracked(completed));
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

/// Tracked witness stored beside the global monitor in `Once`.
pub(super) tracked struct RcuMonitorOwner {}

impl DataPredicate<RcuMonitor> for RcuMonitorOwner {
    closed spec fn predicate(&self, monitor: RcuMonitor) -> bool {
        monitor.wf()
    }
}

/// Invariant used by the global `Once` cell.
pub(super) struct RcuMonitorPred;

impl OncePredicate<AtomicDataWithOwner<RcuMonitor, RcuMonitorOwner>> for RcuMonitorPred {
    closed spec fn inv(self, value: AtomicDataWithOwner<RcuMonitor, RcuMonitorOwner>) -> bool {
        value.permission@.predicate(value.data)
    }
}

impl RcuMonitor {
    /// Packages a fresh monitor with the owner expected by the global `Once`.
    pub(super) fn new_data() -> (res: AtomicDataWithOwner<RcuMonitor, RcuMonitorOwner>)
        ensures
            RcuMonitorPred.inv(res),
    {
        let data = Self::new();
        proof_decl! {
            let tracked owner = RcuMonitorOwner {};
        }
        proof {
            use_type_invariant(&data);
        }
        let res = AtomicDataWithOwner { data, permission: Tracked(owner) };
        proof {
            assert(res.permission@.predicate(res.data));
        }
        res
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
