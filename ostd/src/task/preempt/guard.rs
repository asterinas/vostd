// SPDX-License-Identifier: MPL-2.0
use vstd::thread_view::{ThreadView as Irc11ThreadView, ViewSeen};
use vstd::{prelude::*, resource::Loc};
use vstd_extra::atomic_irc11::ThreadViewOrder;
use vstd_extra::resource::ghost_resource::count_ghost::{CountGhost, CountGhostResource};

use crate::{
    specs::sync::{
        rcu::RcuRetiredFacts,
        rcu_cpu::{
            CpuRcuClosedGeneration, CpuRcuCoreBinding, CpuRcuParticipant, CpuRcuReaderFragment,
        },
    },
    specs::task::cpu_core::{CpuCoreOwner, CpuCoreOwnerHandle, CpuCoreRegistration},
    sync::GuardTransfer, /*, task::atomic_mode::InAtomicMode*/
    task::scheduler::{SchedulerView, TaskThreadView},
};

verus! {

broadcast use vstd::thread_view::group_thread_view_axioms;

pub const PREEMPT_SESSION_FRACTIONS: usize = 1 << 31;

/// Proof token carried by a nested preemption-disable guard.
///
/// Nested guards deliberately do not carry a `TaskThreadView`; the current
/// task's weak-memory view has already been checked out by the outermost
/// guard. This token only records that the guard was created while preemption
/// was already disabled.
pub tracked struct NestedPreemptToken {
    depth_before: Ghost<nat>,
}

impl NestedPreemptToken {
    pub proof fn new(depth_before: nat) -> (tracked res: Self)
        requires
            depth_before > 0,
        ensures
            res.depth_before() == depth_before,
            res.wf(),
    {
        NestedPreemptToken { depth_before: Ghost(depth_before) }
    }

    pub closed spec fn depth_before(self) -> nat {
        self.depth_before@
    }

    pub closed spec fn wf(self) -> bool {
        self.depth_before() > 0
    }
}

/// A shareable proof token tying a guard to the active preemption session.
///
/// The token is a fractional resource-algebra fragment. Its generation changes
/// only while the session owns the full fraction, which is exactly the
/// quiescent state in which no preemption-disabled reader can remain live.
pub ghost struct PreemptSessionState {
    task: Loc,
    quiescent_generation: nat,
}

pub tracked struct PreemptSessionToken {
    token: CountGhost<PreemptSessionState, PREEMPT_SESSION_FRACTIONS>,
}

impl PreemptSessionToken {
    proof fn new_placeholder() -> (tracked res: Self)
        ensures
            res.wf(),
    {
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000usize) by (compute);
        assert(PREEMPT_SESSION_FRACTIONS > 1) by (compute);
        let tracked mut tokens = CountGhostResource::<
            PreemptSessionState,
            PREEMPT_SESSION_FRACTIONS,
        >::alloc(arbitrary());
        let tracked token = tokens.split_one();
        assert(token.frac() == 1);
        let tracked res = PreemptSessionToken { token };
        assert(res.wf());
        res
    }

    pub closed spec fn id(self) -> Loc {
        self.token.id()
    }

    pub closed spec fn task(self) -> Loc {
        self.token@.task
    }

    pub closed spec fn quiescent_generation(self) -> nat {
        self.token@.quiescent_generation
    }

    pub closed spec fn frac(self) -> int {
        self.token.frac()
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.frac() == 1
        &&& 0 < self.frac() <= PREEMPT_SESSION_FRACTIONS
    }

    pub proof fn agree(tracked &self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self.task() == other.task(),
            self.quiescent_generation() == other.quiescent_generation(),
    {
        self.token.agree(&other.token);
    }
}

/// The active preemption-disable session that owns the task-local view.
///
/// Nested preemption-disable guards do not own this resource. They can only
/// use it by borrowing the session that was established by the outermost
/// preemption-disable scope. This keeps the model to one linear
/// `ThreadView` per running task while still allowing nested RCU code to
/// perform weak atomic operations.
pub tracked struct PreemptThreadViewSession {
    task_view: TaskThreadView,
    tokens: CountGhostResource<PreemptSessionState, PREEMPT_SESSION_FRACTIONS>,
}

impl PreemptThreadViewSession {
    pub proof fn new(tracked task_view: TaskThreadView, sched_view: SchedulerView) -> (tracked res:
        Self)
        requires
            task_view.wf(sched_view),
        ensures
            res.scheduler() == task_view.scheduler(),
            res.task() == task_view.task(),
            res.view() == task_view.view(),
            res.irc11_view() == task_view.irc11_view(),
            res.session_task() == task_view.task(),
            res.quiescent_generation() == 0,
            res.available_fractions() == PREEMPT_SESSION_FRACTIONS,
            res.wf_session_resource(),
            res.wf(sched_view),
    {
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000usize) by (compute);
        assert(PREEMPT_SESSION_FRACTIONS > 1) by (compute);
        let task = task_view.task();
        let ghost state = PreemptSessionState { task, quiescent_generation: 0 };
        let tracked tokens = CountGhostResource::<
            PreemptSessionState,
            PREEMPT_SESSION_FRACTIONS,
        >::alloc(state);
        assert(tokens.is_full());
        tokens.validate();
        assert(tokens.frac() == PREEMPT_SESSION_FRACTIONS);
        let tracked res = PreemptThreadViewSession { task_view, tokens };
        assert(res.available_fractions() == PREEMPT_SESSION_FRACTIONS);
        assert(res.wf_session_resource());
        assert(res.wf(sched_view));
        res
    }

    pub closed spec fn task(self) -> Loc {
        self.task_view.task()
    }

    pub closed spec fn scheduler(self) -> Loc {
        self.task_view.scheduler()
    }

    pub closed spec fn view(self) -> Irc11ThreadView {
        self.task_view.view()
    }

    pub open spec fn irc11_view(self) -> Irc11ThreadView {
        self.view()
    }

    pub closed spec fn session_id(self) -> Loc {
        self.tokens.id()
    }

    pub closed spec fn session_task(self) -> Loc {
        self.tokens@.task
    }

    pub closed spec fn quiescent_generation(self) -> nat {
        self.tokens@.quiescent_generation
    }

    pub closed spec fn available_fractions(self) -> int {
        self.tokens.frac()
    }

    pub closed spec fn has_full_authority(self) -> bool {
        self.tokens.is_full()
    }

    pub closed spec fn wf_session_resource(self) -> bool {
        &&& self.tokens.wf()
        &&& self.session_task() == self.task()
        &&& 0 < self.available_fractions() <= PREEMPT_SESSION_FRACTIONS
    }

    pub closed spec fn wf(self, sched_view: SchedulerView) -> bool {
        &&& self.task_view.wf(sched_view)
        &&& self.wf_session_resource()
    }

    pub closed spec fn token_matches(self, token: PreemptSessionToken) -> bool {
        &&& token.wf()
        &&& token.id() == self.session_id()
        &&& token.task() == self.session_task()
        &&& token.quiescent_generation() == self.quiescent_generation()
    }

    /// Splits one guard fragment from the active session.
    ///
    /// The session keeps at least one fraction after the split so future
    /// agreement checks can still relate guard fragments back to the session.
    pub proof fn tracked_split_guard_token(tracked &mut self) -> (tracked token:
        PreemptSessionToken)
        requires
            old(self).wf_session_resource(),
            old(self).available_fractions() > 1,
        ensures
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).view() == old(self).view(),
            final(self).irc11_view() == old(self).irc11_view(),
            final(self).session_id() == old(self).session_id(),
            final(self).session_task() == old(self).session_task(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() + 1 == old(self).available_fractions(),
            final(self).wf_session_resource(),
            token.wf(),
            final(self).token_matches(token),
    {
        let tracked token = self.tokens.split_one();
        PreemptSessionToken { token }
    }

    /// Returns a guard fragment when a preemption-disable guard is dropped.
    pub proof fn tracked_return_guard_token(tracked &mut self, tracked token: PreemptSessionToken)
        requires
            old(self).wf_session_resource(),
            old(self).token_matches(token),
        ensures
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).view() == old(self).view(),
            final(self).irc11_view() == old(self).irc11_view(),
            final(self).session_id() == old(self).session_id(),
            final(self).session_task() == old(self).session_task(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() == old(self).available_fractions() + token.frac(),
            final(self).wf_session_resource(),
    {
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000usize) by (compute);
        let ghost old_frac = self.tokens.frac();
        let tracked PreemptSessionToken { token } = token;
        let ghost returned_frac = token.frac();
        assert(returned_frac == 1);
        self.tokens.combine(token);
        assert(old_frac + returned_frac > PREEMPT_SESSION_FRACTIONS ==> false);
        assert(old_frac + returned_frac <= PREEMPT_SESSION_FRACTIONS);
        self.tokens.validate();
        assert(self.tokens.frac() == old_frac + returned_frac);
        assert(0 < self.tokens.frac() <= PREEMPT_SESSION_FRACTIONS);
        assert(self.tokens@.task == self.task_view.task());
        assert(self.wf_session_resource());
    }

    /// Borrows the single task-local `ThreadView` for weak atomic operations.
    ///
    /// After the borrow mutates the view, the caller must update the scheduler
    /// snapshot with `SchedulerView::update_checked_out_task_view` before
    /// relying on `wf` again.
    pub proof fn tracked_borrow_thread_view_mut(tracked &mut self) -> (tracked tv: &mut ViewSeen)
        ensures
            (*tv)@ == old(self).view(),
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).session_id() == old(self).session_id(),
            final(self).session_task() == old(self).session_task(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).has_full_authority() == old(self).has_full_authority(),
            final(self).wf_session_resource() == old(self).wf_session_resource(),
            final(self).view() == (*final(tv))@,
            final(self).irc11_view() == (*final(tv))@,
    {
        let tracked token = self.task_view.tracked_borrow_thread_view_mut();
        token.tracked_borrow_mut()
    }

    /// Borrows the task view while preserving an existing lower bound whenever
    /// the atomic operation grows the native view.
    proof fn tracked_borrow_thread_view_mut_above(
        tracked &mut self,
        lower: Irc11ThreadView,
    ) -> (tracked tv: &mut ViewSeen)
        requires
            lower.spec_le(old(self).view()),
        ensures
            (*tv)@ == old(self).view(),
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).session_id() == old(self).session_id(),
            final(self).session_task() == old(self).session_task(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).has_full_authority() == old(self).has_full_authority(),
            final(self).wf_session_resource() == old(self).wf_session_resource(),
            final(self).view() == (*final(tv))@,
            final(self).irc11_view() == (*final(tv))@,
            old(self).view().spec_le((*final(tv))@) ==> lower.spec_le((*final(tv))@),
    {
        let ghost old_view = self.view();
        let tracked token = self.task_view.tracked_borrow_thread_view_mut();
        let tracked tv = token.tracked_borrow_mut();
        if old_view.spec_le((*final(tv))@) {
            lower.lemma_spec_le_transitive(old_view, (*final(tv))@);
        }
        tv
    }

    /// Borrows the native subjective view for an IRC11 atomic operation.
    pub proof fn tracked_borrow_irc11_view_mut(tracked &mut self) -> (tracked view: &mut ViewSeen)
        ensures
            (*view)@ == old(self).irc11_view(),
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).view() == (*final(view))@,
            final(self).session_id() == old(self).session_id(),
            final(self).session_task() == old(self).session_task(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).has_full_authority() == old(self).has_full_authority(),
            final(self).wf_session_resource() == old(self).wf_session_resource(),
            final(self).irc11_view() == (*final(view))@,
    {
        let tracked token = self.task_view.tracked_borrow_irc11_view_mut();
        token.tracked_borrow_mut()
    }

    /// Advances the session's quiescent boundary.
    ///
    /// Updating the fractional resource requires full ownership. Therefore no
    /// `PreemptSessionToken` from the previous generation can coexist with
    /// this transition. Tokens split afterwards carry the new generation.
    proof fn tracked_advance_quiescent_generation(tracked &mut self) -> (generation: nat)
        requires
            old(self).wf_session_resource(),
            old(self).available_fractions() == PREEMPT_SESSION_FRACTIONS,
            old(self).has_full_authority(),
        ensures
            generation == old(self).quiescent_generation(),
            final(self).quiescent_generation() == generation + 1,
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).view() == old(self).view(),
            final(self).irc11_view() == old(self).irc11_view(),
            final(self).session_id() == old(self).session_id(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).wf_session_resource(),
    {
        let ghost generation = self.quiescent_generation();
        let ghost state = PreemptSessionState {
            task: self.task(),
            quiescent_generation: generation + 1,
        };
        self.tokens.update(state);
        self.tokens.validate();
        assert(self.tokens.frac() == PREEMPT_SESSION_FRACTIONS);
        assert(self.tokens@.task == self.task_view.task());
        generation
    }

    /// Returns the checked-out view to the caller for scheduler check-in.
    ///
    /// This is the proof-side counterpart of dropping the outermost
    /// preemption-disable scope: the session stops owning the task view, and
    /// the caller can write it back with
    /// `SchedulerGhostState::tracked_schedule_out`.
    pub proof fn tracked_into_task_view(tracked self) -> (tracked res: TaskThreadView)
        requires
            self.wf_session_resource(),
            self.available_fractions() == PREEMPT_SESSION_FRACTIONS,
        ensures
            res.scheduler() == self.scheduler(),
            res.task() == self.task(),
            res.view() == self.view(),
            res.irc11_view() == self.irc11_view(),
    {
        self.task_view
    }

    /// Returns the checked-out view while preserving its scheduler relation.
    pub proof fn tracked_into_task_view_for_scheduler(
        tracked self,
        sched_view: SchedulerView,
    ) -> (tracked res: TaskThreadView)
        requires
            self.wf(sched_view),
            self.available_fractions() == PREEMPT_SESSION_FRACTIONS,
        ensures
            res.scheduler() == self.scheduler(),
            res.task() == self.task(),
            res.view() == self.view(),
            res.irc11_view() == self.irc11_view(),
            res.wf(sched_view),
    {
        self.task_view
    }
}

/// The proof-owned state for one task while it is running.
///
/// The scheduler creates this context after checking out the task's
/// `TaskThreadView`. Every preemption-disable guard consumes one fractional
/// session token and increments `preempt_depth`; releasing the guard performs
/// the inverse transition. Consequently the context can only be returned to
/// the scheduler when no guard remains live.
pub tracked struct RunningTaskContext {
    session: PreemptThreadViewSession,
    core_handle: CpuCoreOwnerHandle<CpuRcuParticipant>,
    rcu_participant: CpuRcuParticipant,
    rcu_binding: CpuRcuCoreBinding,
    preempt_depth: Ghost<nat>,
    cpu: Ghost<crate::specs::mm::cpu::CpuId>,
}

impl RunningTaskContext {
    /// Starts a running interval for a checked-out task view.
    pub proof fn new(
        tracked task_view: TaskThreadView,
        tracked core_handle: CpuCoreOwnerHandle<CpuRcuParticipant>,
        tracked rcu_participant: CpuRcuParticipant,
        tracked rcu_binding: CpuRcuCoreBinding,
        sched_view: SchedulerView,
        cpu: crate::specs::mm::cpu::CpuId,
    ) -> (tracked res: Self)
        requires
            task_view.wf(sched_view),
            core_handle.wf(),
            core_handle.cpu() == cpu,
            core_handle.current_task() == Some(task_view.task()),
            core_handle.expected_locals_key() == seq![rcu_participant.id()],
            rcu_participant.wf(),
            rcu_participant.cpu() == cpu,
            rcu_participant.fraction() == 1real,
            rcu_participant.view().spec_le(task_view.irc11_view()),
            rcu_binding.registry() == task_view.scheduler(),
            rcu_binding.cpu() == cpu,
            rcu_binding.owner_id() == core_handle.id(),
            rcu_binding.locals_key() == core_handle.expected_locals_key(),
            rcu_binding.single_local_id() == rcu_participant.id(),
            sched_view.cpu_has_rcu_participant(cpu),
            sched_view.cpu_rcu_participant_id(cpu) == rcu_participant.id(),
            sched_view.cpu_core_registration(cpu).owner_id == core_handle.id(),
            sched_view.cpu_core_registration(cpu).locals_key == core_handle.expected_locals_key(),
            !sched_view.cpu_rcu_participant_is_stored(cpu),
            sched_view.current.contains_key(cpu),
            sched_view.current[cpu] == Some(task_view.task()),
            crate::specs::mm::cpu::online_cpus().contains(cpu),
        ensures
            res.scheduler() == task_view.scheduler(),
            res.task() == task_view.task(),
            res.view() == task_view.view(),
            res.irc11_view() == task_view.irc11_view(),
            res.cpu() == cpu,
            res.core_owner_id() == core_handle.id(),
            res.preempt_depth() == 0,
            res.quiescent_generation() == 0,
            res.available_fractions() == PREEMPT_SESSION_FRACTIONS,
            res.rcu_participant_id() == rcu_participant.id(),
            res.rcu_generation() == rcu_participant.generation(),
            res.rcu_participant_view() == rcu_participant.view(),
            res.rcu_fraction() == 1real,
            res.rcu_binding().registry() == res.scheduler(),
            res.rcu_binding().cpu() == cpu,
            res.rcu_binding().single_local_id() == res.rcu_participant_id(),
            res.wf(),
            res.is_quiescent(),
            res.wf_scheduler(sched_view),
    {
        let tracked session = PreemptThreadViewSession::new(task_view, sched_view);
        let tracked res = RunningTaskContext {
            session,
            core_handle,
            rcu_participant,
            rcu_binding,
            preempt_depth: Ghost(0),
            cpu: Ghost(cpu),
        };
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000usize) by (compute);
        assert(res.wf());
        assert(res.session.wf(sched_view));
        assert(res.wf_scheduler(sched_view));
        res
    }

    pub closed spec fn task(self) -> Loc {
        self.session.task()
    }

    pub closed spec fn scheduler(self) -> Loc {
        self.session.scheduler()
    }

    pub closed spec fn view(self) -> Irc11ThreadView {
        self.session.view()
    }

    pub open spec fn irc11_view(self) -> Irc11ThreadView {
        self.view()
    }

    pub closed spec fn cpu(self) -> crate::specs::mm::cpu::CpuId {
        self.cpu@
    }

    pub closed spec fn core_owner_id(self) -> Loc {
        self.core_handle.id()
    }

    pub closed spec fn session_id(self) -> Loc {
        self.session.session_id()
    }

    pub closed spec fn quiescent_generation(self) -> nat {
        self.session.quiescent_generation()
    }

    pub closed spec fn available_fractions(self) -> int {
        self.session.available_fractions()
    }

    pub closed spec fn has_full_authority(self) -> bool {
        self.session.has_full_authority()
    }

    pub closed spec fn preempt_depth(self) -> nat {
        self.preempt_depth@
    }

    pub closed spec fn rcu_participant_id(self) -> Loc {
        self.rcu_participant.id()
    }

    pub closed spec fn rcu_generation(self) -> nat {
        self.rcu_participant.generation()
    }

    pub closed spec fn rcu_participant_view(self) -> Irc11ThreadView {
        self.rcu_participant.view()
    }

    pub closed spec fn rcu_fraction(self) -> real {
        self.rcu_participant.fraction()
    }

    pub closed spec fn rcu_binding(self) -> CpuRcuCoreBinding {
        self.rcu_binding
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.session.wf_session_resource()
        &&& self.view() == self.irc11_view()
        &&& self.available_fractions() + self.preempt_depth() == PREEMPT_SESSION_FRACTIONS
        &&& self.core_handle.wf()
        &&& self.core_handle.cpu() == self.cpu()
        &&& self.core_handle.current_task() == Some(self.task())
        &&& self.core_handle.expected_locals_key() == seq![self.rcu_participant_id()]
        &&& self.rcu_participant.wf()
        &&& self.rcu_binding().registry() == self.scheduler()
        &&& self.rcu_binding().cpu() == self.cpu()
        &&& self.rcu_binding().owner_id() == self.core_owner_id()
        &&& self.rcu_binding().locals_key() == self.core_handle.expected_locals_key()
        &&& self.rcu_binding().single_local_id() == self.rcu_participant_id()
        &&& self.rcu_participant.cpu() == self.cpu()
        &&& crate::specs::mm::cpu::online_cpus().contains(self.cpu())
        &&& self.rcu_participant_view().spec_le(self.irc11_view())
    }

    /// The checked-out task view includes the persistent view of this CPU's
    /// RCU participant.
    pub proof fn lemma_rcu_participant_view_le(tracked &self)
        requires
            self.wf(),
        ensures
            self.rcu_participant_view().spec_le(self.irc11_view()),
    {
    }

    /// A running task is checked out on a CPU in the scheduler's online set.
    pub proof fn lemma_cpu_online(tracked &self)
        requires
            self.wf(),
        ensures
            crate::specs::mm::cpu::online_cpus().contains(self.cpu()),
    {
    }

    /// Relates this running context to the scheduler snapshot from which its
    /// task view was checked out.
    pub closed spec fn wf_scheduler(self, sched_view: SchedulerView) -> bool {
        &&& self.wf()
        &&& self.session.wf(sched_view)
        &&& sched_view.current.contains_key(self.cpu())
        &&& sched_view.current[self.cpu()] == Some(self.task())
        &&& sched_view.cpu_has_rcu_participant(self.cpu())
        &&& sched_view.cpu_rcu_participant_id(self.cpu()) == self.rcu_participant_id()
        &&& sched_view.cpu_core_registration(self.cpu()).owner_id == self.core_owner_id()
        &&& sched_view.cpu_core_registration(self.cpu()).locals_key == seq![
            self.rcu_participant_id(),
        ]
        &&& !sched_view.cpu_rcu_participant_is_stored(self.cpu())
    }

    /// Re-establishes the scheduler relation after the checked-out task view
    /// has been updated to this context's current weak-memory view.
    pub proof fn lemma_wf_scheduler(tracked &self, sched_view: SchedulerView)
        requires
            self.wf(),
            sched_view.wf(),
            sched_view.id == self.scheduler(),
            sched_view.task_view_is_checked_out(self.task()),
            sched_view.checked_out_views[self.task()] == self.view(),
            sched_view.task_views.contains_key(self.task()),
            sched_view.task_views[self.task()] == self.view(),
            sched_view.current.contains_key(self.cpu()),
            sched_view.current[self.cpu()] == Some(self.task()),
            sched_view.cpu_has_rcu_participant(self.cpu()),
            sched_view.cpu_rcu_participant_id(self.cpu()) == self.rcu_participant_id(),
            sched_view.cpu_core_registration(self.cpu()).owner_id == self.core_owner_id(),
            sched_view.cpu_core_registration(self.cpu()).locals_key == seq![
                self.rcu_participant_id(),
            ],
            !sched_view.cpu_rcu_participant_is_stored(self.cpu()),
        ensures
            self.wf_scheduler(sched_view),
    {
        self.session.task_view.lemma_wf(sched_view);
        assert(self.session.wf(sched_view));
    }

    pub open spec fn is_quiescent(self) -> bool {
        &&& self.preempt_depth() == 0
        &&& self.available_fractions() == PREEMPT_SESSION_FRACTIONS
        &&& self.has_full_authority()
        &&& self.rcu_fraction() == 1real
    }

    /// Borrows the running task's persistent weak-memory view.
    pub proof fn tracked_borrow_thread_view_mut(tracked &mut self) -> (tracked tv: &mut ViewSeen)
        requires
            old(self).wf(),
        ensures
            (*tv)@ == old(self).view(),
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).cpu() == old(self).cpu(),
            final(self).session_id() == old(self).session_id(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).has_full_authority() == old(self).has_full_authority(),
            final(self).preempt_depth() == old(self).preempt_depth(),
            final(self).rcu_participant_id() == old(self).rcu_participant_id(),
            final(self).rcu_generation() == old(self).rcu_generation(),
            final(self).rcu_participant_view() == old(self).rcu_participant_view(),
            final(self).rcu_fraction() == old(self).rcu_fraction(),
            final(self).view() == (*final(tv))@,
            old(self).view().spec_le((*final(tv))@) ==> final(self).wf(),
    {
        let ghost participant_view = self.rcu_participant_view();
        assert(self.irc11_view() == self.view());
        assert(participant_view.spec_le(self.view()));
        self.session.tracked_borrow_thread_view_mut_above(participant_view)
    }

    /// Borrows the running task's native IRC11 view.
    pub proof fn tracked_borrow_irc11_view_mut(tracked &mut self) -> (tracked view: &mut ViewSeen)
        requires
            old(self).wf(),
        ensures
            (*view)@ == old(self).irc11_view(),
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).cpu() == old(self).cpu(),
            final(self).view() == (*final(view))@,
            final(self).session_id() == old(self).session_id(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).has_full_authority() == old(self).has_full_authority(),
            final(self).preempt_depth() == old(self).preempt_depth(),
            final(self).rcu_participant_id() == old(self).rcu_participant_id(),
            final(self).rcu_generation() == old(self).rcu_generation(),
            final(self).rcu_participant_view() == old(self).rcu_participant_view(),
            final(self).rcu_fraction() == old(self).rcu_fraction(),
            final(self).irc11_view() == (*final(view))@,
            old(self).irc11_view().spec_le((*final(view))@) ==> final(self).wf(),
    {
        self.session.tracked_borrow_irc11_view_mut()
    }

    /// Starts one RCU reader from this CPU's persistent participant.
    ///
    /// Preemption must already be disabled. The returned fragment names the
    /// participant's current CPU generation and remains live until the reader
    /// guard is destroyed.
    pub proof fn tracked_start_rcu_reader(tracked &mut self) -> (tracked reader:
        CpuRcuReaderFragment)
        requires
            old(self).wf(),
            old(self).preempt_depth() > 0,
        ensures
            final(self).wf(),
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).cpu() == old(self).cpu(),
            final(self).view() == old(self).view(),
            final(self).irc11_view() == old(self).irc11_view(),
            final(self).session_id() == old(self).session_id(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).preempt_depth() == old(self).preempt_depth(),
            final(self).rcu_participant_id() == old(self).rcu_participant_id(),
            final(self).rcu_generation() == old(self).rcu_generation(),
            final(self).rcu_participant_view() == old(self).rcu_participant_view(),
            final(self).rcu_fraction() == old(self).rcu_fraction() / 2real,
            reader.wf(),
            reader.participant_id() == old(self).rcu_participant_id(),
            reader.cpu() == old(self).cpu(),
            reader.generation() == old(self).rcu_generation(),
            reader.participant_view() == old(self).rcu_participant_view(),
            reader.fraction() == old(self).rcu_fraction() / 2real,
    {
        self.rcu_participant.tracked_start_reader_in_place(self.irc11_view())
    }

    /// Copies the persistent scheduler binding for a guard or quiescent report.
    pub proof fn tracked_rcu_binding(tracked &self) -> (tracked binding: CpuRcuCoreBinding)
        requires
            self.wf(),
        ensures
            binding.registry() == self.scheduler(),
            binding.cpu() == self.cpu(),
            binding.owner_id() == self.core_owner_id(),
            binding.locals_key() == seq![self.rcu_participant_id()],
            binding.locals_key().len() == 1,
            binding.single_local_id() == self.rcu_participant_id(),
    {
        self.rcu_binding.tracked_duplicate()
    }

    /// Returns a completed reader to this CPU's persistent participant.
    pub proof fn tracked_stop_rcu_reader(tracked &mut self, tracked reader: CpuRcuReaderFragment)
        requires
            old(self).wf(),
            old(self).preempt_depth() > 0,
            reader.wf(),
            reader.participant_id() == old(self).rcu_participant_id(),
        ensures
            final(self).wf(),
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).cpu() == old(self).cpu(),
            final(self).view() == old(self).view(),
            final(self).session_id() == old(self).session_id(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).preempt_depth() == old(self).preempt_depth(),
            final(self).rcu_participant_id() == old(self).rcu_participant_id(),
            final(self).rcu_generation() == old(self).rcu_generation(),
            final(self).rcu_participant_view() == old(self).rcu_participant_view(),
            final(self).rcu_fraction() == old(self).rcu_fraction() + reader.fraction(),
    {
        self.rcu_participant.tracked_stop_reader_in_place(reader);
    }

    /// Closes the current CPU participation generation at a quiescent point.
    ///
    /// Unlike [`Self::tracked_record_quiescent`], this transition is backed by
    /// the persistent CPU participant PCM and returns an unforgeable token
    /// that conflicts with every reader fragment from the closed generation.
    pub proof fn tracked_report_rcu_quiescent(tracked &mut self) -> (tracked closed:
        CpuRcuClosedGeneration)
        requires
            old(self).wf(),
            old(self).is_quiescent(),
        ensures
            closed.wf(),
            closed.scheduler() == old(self).scheduler(),
            closed.participant_id() == old(self).rcu_participant_id(),
            closed.cpu() == old(self).cpu(),
            closed.closed_generation() == old(self).rcu_generation(),
            closed.view() == old(self).irc11_view(),
            final(self).wf(),
            final(self).is_quiescent(),
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).cpu() == old(self).cpu(),
            final(self).view() == old(self).view(),
            final(self).irc11_view() == old(self).irc11_view(),
            final(self).session_id() == old(self).session_id(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).preempt_depth() == old(self).preempt_depth(),
            final(self).rcu_participant_id() == old(self).rcu_participant_id(),
            final(self).rcu_generation() == old(self).rcu_generation() + 1,
            final(self).rcu_participant_view() == old(self).irc11_view(),
            final(self).rcu_fraction() == 1real,
    {
        let tracked binding = self.rcu_binding.tracked_duplicate();
        self.rcu_participant.tracked_report_quiescent_in_place(binding, self.irc11_view())
    }

    /// Closes the current CPU generation while publishing retirement facts
    /// whose detachment observations are covered by this task's current view.
    pub proof fn tracked_report_rcu_quiescent_with(
        tracked &mut self,
        tracked learned: &RcuRetiredFacts,
    ) -> (tracked closed: CpuRcuClosedGeneration)
        requires
            old(self).wf(),
            old(self).is_quiescent(),
            learned.observed_by(old(self).irc11_view()),
        ensures
            closed.wf(),
            closed.scheduler() == old(self).scheduler(),
            closed.participant_id() == old(self).rcu_participant_id(),
            closed.cpu() == old(self).cpu(),
            closed.closed_generation() == old(self).rcu_generation(),
            closed.view() == old(self).irc11_view(),
            learned.records().subset_of(closed.known_retired()),
            final(self).wf(),
            final(self).is_quiescent(),
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).cpu() == old(self).cpu(),
            final(self).view() == old(self).view(),
            final(self).irc11_view() == old(self).irc11_view(),
            final(self).session_id() == old(self).session_id(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).preempt_depth() == old(self).preempt_depth(),
            final(self).rcu_participant_id() == old(self).rcu_participant_id(),
            final(self).rcu_generation() == old(self).rcu_generation() + 1,
            final(self).rcu_participant_view() == old(self).irc11_view(),
            final(self).rcu_fraction() == 1real,
    {
        let tracked binding = self.rcu_binding.tracked_duplicate();
        self.rcu_participant.tracked_report_quiescent_with_in_place(
            binding,
            self.irc11_view(),
            learned,
        )
    }

    /// Records one quiescent boundary for this running session.
    ///
    /// The returned generation names the interval that has just ended. The
    /// context advances to the next generation before another RCU reader can
    /// split a preemption-session fragment.
    pub proof fn tracked_record_quiescent(tracked &mut self) -> (generation: nat)
        requires
            old(self).wf(),
            old(self).is_quiescent(),
        ensures
            generation == old(self).quiescent_generation(),
            final(self).quiescent_generation() == generation + 1,
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).cpu() == old(self).cpu(),
            final(self).view() == old(self).view(),
            final(self).irc11_view() == old(self).irc11_view(),
            final(self).session_id() == old(self).session_id(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).preempt_depth() == old(self).preempt_depth(),
            final(self).rcu_participant_id() == old(self).rcu_participant_id(),
            final(self).rcu_generation() == old(self).rcu_generation(),
            final(self).rcu_participant_view() == old(self).rcu_participant_view(),
            final(self).rcu_fraction() == old(self).rcu_fraction(),
            final(self).wf(),
            final(self).is_quiescent(),
    {
        self.session.tracked_advance_quiescent_generation()
    }

    /// Ends a running interval and returns the updated task view to scheduler
    /// ownership. The full-fraction requirement rules out live preempt guards.
    pub proof fn tracked_into_task_view(tracked self) -> (tracked res: (
        TaskThreadView,
        CpuCoreOwner<CpuRcuParticipant>,
    ))
        requires
            self.wf(),
            self.preempt_depth() == 0,
            self.rcu_fraction() == 1real,
        ensures
            res.0.scheduler() == self.scheduler(),
            res.0.task() == self.task(),
            res.0.view() == self.view(),
            res.0.irc11_view() == self.irc11_view(),
            res.1.id() == self.core_owner_id(),
            res.1.cpu() == self.cpu(),
            res.1.current_task() == Some(self.task()),
            res.1.locals_key() == seq![self.rcu_participant_id()],
            res.1.registration() == (CpuCoreRegistration {
                owner_id: self.core_owner_id(),
                locals_key: seq![self.rcu_participant_id()],
            }),
            res.1.locals().id() == self.rcu_participant_id(),
            res.1.locals().generation() == self.rcu_generation(),
            res.1.locals().view() == self.rcu_participant_view(),
            res.1.locals().fraction() == 1real,
            res.1.locals().view().spec_le(res.0.irc11_view()),
            res.1.wf(),
    {
        assert(self.available_fractions() == PREEMPT_SESSION_FRACTIONS);
        let ghost cpu = self.cpu();
        let ghost task = self.task();
        let ghost core_owner_id = self.core_owner_id();
        let ghost rcu_participant_id = self.rcu_participant_id();
        let ghost core_view = self.core_handle@;
        assert(self.core_handle.cpu() == cpu);
        assert(self.core_handle.current_task() == Some(task));
        let tracked core = self.core_handle.tracked_restore(self.rcu_participant);
        assert(core@ == core_view);
        assert(core.id() == core_owner_id);
        assert(core.cpu() == cpu);
        assert(core.current_task() == Some(task));
        assert(core.locals_key() == seq![rcu_participant_id]);
        assert(core.registration() == (CpuCoreRegistration {
            owner_id: core_owner_id,
            locals_key: seq![rcu_participant_id],
        }));
        (self.session.tracked_into_task_view(), core)
    }

    /// Scheduler-facing form of `tracked_into_task_view` that preserves the
    /// checked-out token's relation to the supplied scheduler snapshot.
    pub proof fn tracked_into_task_view_for_scheduler(
        tracked self,
        sched_view: SchedulerView,
    ) -> (tracked res: (TaskThreadView, CpuCoreOwner<CpuRcuParticipant>))
        requires
            self.wf_scheduler(sched_view),
            self.is_quiescent(),
        ensures
            res.0.scheduler() == self.scheduler(),
            res.0.task() == self.task(),
            res.0.view() == self.view(),
            res.0.irc11_view() == self.irc11_view(),
            res.0.wf(sched_view),
            res.1.id() == self.core_owner_id(),
            res.1.cpu() == self.cpu(),
            res.1.current_task() == Some(self.task()),
            res.1.locals_key() == seq![self.rcu_participant_id()],
            res.1.registration() == (CpuCoreRegistration {
                owner_id: self.core_owner_id(),
                locals_key: seq![self.rcu_participant_id()],
            }),
            res.1.locals().id() == self.rcu_participant_id(),
            res.1.locals().generation() == self.rcu_generation(),
            res.1.locals().view() == self.rcu_participant_view(),
            res.1.locals().fraction() == 1real,
            res.1.locals().view().spec_le(res.0.irc11_view()),
            res.1.wf(),
    {
        assert(self.preempt_depth() == 0);
        assert(self.available_fractions() == PREEMPT_SESSION_FRACTIONS);
        assert(self.session.wf(sched_view));
        let ghost cpu = self.cpu();
        let ghost task = self.task();
        let ghost core_owner_id = self.core_owner_id();
        let ghost rcu_participant_id = self.rcu_participant_id();
        let ghost core_view = self.core_handle@;
        assert(self.core_handle.cpu() == cpu);
        assert(self.core_handle.current_task() == Some(task));
        let tracked task_view = self.session.tracked_into_task_view_for_scheduler(sched_view);
        let tracked core = self.core_handle.tracked_restore(self.rcu_participant);
        assert(core@ == core_view);
        assert(core.id() == core_owner_id);
        assert(core.cpu() == cpu);
        assert(core.current_task() == Some(task));
        assert(core.locals_key() == seq![rcu_participant_id]);
        assert(core.registration() == (CpuCoreRegistration {
            owner_id: core_owner_id,
            locals_key: seq![rcu_participant_id],
        }));
        (task_view, core)
    }
}

/// Proof resource carried by a `DisabledPreemptGuard`.
///
/// The guard records whether this preemption-disable scope is the outermost
/// one or a nested one. It deliberately does not own the checked-out
/// `TaskThreadView`; that linear resource lives in `PreemptThreadViewSession`.
/// This keeps nested guards from minting another `ThreadView` while allowing
/// them to borrow the active session.
pub tracked enum PreemptGuardResource {
    Outermost(PreemptSessionToken),
    Nested { tracked session: PreemptSessionToken, tracked nested: NestedPreemptToken },
}

impl PreemptGuardResource {
    proof fn new_placeholder() -> (tracked res: Self)
        ensures
            res.wf(arbitrary()),
    {
        let tracked token = PreemptSessionToken::new_placeholder();
        PreemptGuardResource::Outermost(token)
    }

    pub closed spec fn is_outermost(self) -> bool {
        self is Outermost
    }

    pub closed spec fn is_nested(self) -> bool {
        self is Nested
    }

    pub closed spec fn session_token(self) -> PreemptSessionToken
        recommends
            self is Outermost || self is Nested,
    {
        match self {
            PreemptGuardResource::Outermost(token) => token,
            PreemptGuardResource::Nested { session, nested: _ } => session,
        }
    }

    pub closed spec fn session_id(self) -> Loc {
        self.session_token().id()
    }

    pub closed spec fn task(self) -> Loc {
        self.session_token().task()
    }

    pub closed spec fn quiescent_generation(self) -> nat {
        self.session_token().quiescent_generation()
    }

    pub closed spec fn wf(self, _sched_view: SchedulerView) -> bool {
        match self {
            PreemptGuardResource::Outermost(token) => token.wf(),
            PreemptGuardResource::Nested { session, nested } => {
                &&& session.wf()
                &&& nested.wf()
            },
        }
    }

    pub closed spec fn matches_session(self, session: PreemptThreadViewSession) -> bool {
        &&& self.wf(arbitrary())
        &&& session.token_matches(self.session_token())
    }

    pub closed spec fn matches_context(self, context: RunningTaskContext) -> bool {
        &&& context.wf()
        &&& context.preempt_depth() > 0
        &&& self.matches_session(context.session)
    }

    /// Returns this guard's session fragment to its owning session.
    pub proof fn tracked_return_to_session(
        tracked self,
        tracked session: &mut PreemptThreadViewSession,
    )
        requires
            old(session).wf_session_resource(),
            self.matches_session(*old(session)),
        ensures
            final(session).wf_session_resource(),
            final(session).task() == old(session).task(),
            final(session).scheduler() == old(session).scheduler(),
            final(session).view() == old(session).view(),
            final(session).irc11_view() == old(session).irc11_view(),
            final(session).session_id() == old(session).session_id(),
            final(session).quiescent_generation() == old(session).quiescent_generation(),
            final(session).available_fractions() == old(session).available_fractions() + 1,
    {
        match self {
            PreemptGuardResource::Outermost(token) => {
                session.tracked_return_guard_token(token);
            },
            PreemptGuardResource::Nested { session: token, nested: _ } => {
                session.tracked_return_guard_token(token);
            },
        }
    }
}

impl RunningTaskContext {
    /// Performs the proof transition corresponding to incrementing the
    /// executable preemption counter.
    pub proof fn tracked_disable_preempt(tracked &mut self) -> (tracked resource:
        PreemptGuardResource)
        requires
            old(self).wf(),
            old(self).available_fractions() > 1,
        ensures
            final(self).wf(),
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).cpu() == old(self).cpu(),
            final(self).view() == old(self).view(),
            final(self).irc11_view() == old(self).irc11_view(),
            final(self).session_id() == old(self).session_id(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() + 1 == old(self).available_fractions(),
            final(self).preempt_depth() == old(self).preempt_depth() + 1,
            final(self).rcu_participant_id() == old(self).rcu_participant_id(),
            final(self).rcu_generation() == old(self).rcu_generation(),
            final(self).rcu_participant_view() == old(self).rcu_participant_view(),
            final(self).rcu_fraction() == old(self).rcu_fraction(),
            resource.matches_context(*final(self)),
            resource.is_outermost() <==> old(self).preempt_depth() == 0,
            resource.is_nested() <==> old(self).preempt_depth() > 0,
    {
        let ghost depth_before = self.preempt_depth@;
        let tracked token = self.session.tracked_split_guard_token();
        let tracked resource = if depth_before == 0 {
            PreemptGuardResource::Outermost(token)
        } else {
            let tracked nested = NestedPreemptToken::new(depth_before);
            PreemptGuardResource::Nested { session: token, nested }
        };
        self.preempt_depth = Ghost(depth_before + 1);
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000usize) by (compute);
        assert(self.wf());
        resource
    }

    /// Performs the inverse transition when a preemption-disable guard is
    /// consumed.
    pub proof fn tracked_enable_preempt(tracked &mut self, tracked resource: PreemptGuardResource)
        requires
            old(self).wf(),
            old(self).preempt_depth() > 0,
            resource.matches_context(*old(self)),
        ensures
            final(self).wf(),
            final(self).task() == old(self).task(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).cpu() == old(self).cpu(),
            final(self).view() == old(self).view(),
            final(self).irc11_view() == old(self).irc11_view(),
            final(self).session_id() == old(self).session_id(),
            final(self).quiescent_generation() == old(self).quiescent_generation(),
            final(self).available_fractions() == old(self).available_fractions() + 1,
            final(self).preempt_depth() + 1 == old(self).preempt_depth(),
            final(self).rcu_participant_id() == old(self).rcu_participant_id(),
            final(self).rcu_generation() == old(self).rcu_generation(),
            final(self).rcu_participant_view() == old(self).rcu_participant_view(),
            final(self).rcu_fraction() == old(self).rcu_fraction(),
    {
        let ghost old_depth = self.preempt_depth@;
        resource.tracked_return_to_session(&mut self.session);
        self.preempt_depth = Ghost((old_depth - 1) as nat);
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000usize) by (compute);
        assert(self.wf());
    }
}

/// A guard for disable preempt.
#[clippy::has_significant_drop]
#[must_use]
#[derive(Debug)]
pub struct DisabledPreemptGuard {
    // This private field prevents user from constructing values of this type directly.
    _private: (),
    // Proof-only guard resource.
    //
    // The guard only records whether this scope is outermost or nested. The
    // checked-out `TaskThreadView` is owned by `PreemptThreadViewSession`.
    tracked_resource: Tracked<Option<PreemptGuardResource>>,
}

/* impl !Send for DisabledPreemptGuard {}

// SAFETY: The guard disables preemptions, which meets the second
// sufficient condition for atomic mode.
unsafe impl InAtomicMode for DisabledPreemptGuard {}
*/

impl DisabledPreemptGuard {
    fn new(Tracked(tracked_resource): Tracked<PreemptGuardResource>) -> (res: DisabledPreemptGuard)
        requires
            tracked_resource.wf(arbitrary()),
        ensures
            res.wf(arbitrary()),
            res.tracked_resource@ == Some(tracked_resource),
    {
        // The CPU-local backend is outside the current Verus dependency
        // closure, but executable builds must still perform the real
        // preemption-disable transition.
        #[cfg(not(verus_keep_ghost))]
        super::cpu_local::inc_guard_count();
        Self { _private: (), tracked_resource: Tracked(Some(tracked_resource)) }
    }
}

impl DisabledPreemptGuard {
    pub(crate) closed spec fn has_resource(&self) -> bool {
        self.tracked_resource@ is Some
    }

    closed spec fn resource(&self) -> PreemptGuardResource
        recommends
            self.tracked_resource@ is Some,
    {
        self.tracked_resource@->Some_0
    }

    pub closed spec fn is_outermost(&self) -> bool {
        self.resource().is_outermost()
    }

    pub closed spec fn is_nested(&self) -> bool {
        self.resource().is_nested()
    }

    pub closed spec fn wf(&self, sched_view: SchedulerView) -> bool {
        &&& self.tracked_resource@ is Some
        &&& self.resource().wf(sched_view)
    }

    pub closed spec fn matches_session(&self, session: PreemptThreadViewSession) -> bool {
        &&& self.tracked_resource@ is Some
        &&& self.resource().matches_session(session)
    }

    pub closed spec fn matches_context(&self, context: RunningTaskContext) -> bool {
        &&& self.tracked_resource@ is Some
        &&& self.resource().matches_context(context)
    }

    pub closed spec fn quiescent_generation(&self) -> nat {
        self.resource().quiescent_generation()
    }

    /// Extracts the positive preemption depth witnessed by this guard.
    pub proof fn lemma_matches_context_depth(&self, tracked context: &RunningTaskContext)
        requires
            self.matches_context(*context),
        ensures
            context.preempt_depth() > 0,
            self.quiescent_generation() == context.quiescent_generation(),
    {
    }

    /// A live preemption guard rules out a quiescent report from the same
    /// running context. Returning every session fraction is therefore a
    /// necessary proof step before the monitor can close this generation.
    pub proof fn lemma_blocks_quiescent_report(&self, tracked context: &RunningTaskContext)
        requires
            self.matches_context(*context),
        ensures
            !context.is_quiescent(),
    {
        self.lemma_matches_context_depth(context);
    }

    /// Changing only the task's weak-memory view preserves this guard's
    /// relation to the running context.
    pub proof fn lemma_matches_context_preserved(
        &self,
        before: RunningTaskContext,
        tracked after: &RunningTaskContext,
    )
        requires
            self.matches_context(before),
            after.wf(),
            after.task() == before.task(),
            after.scheduler() == before.scheduler(),
            after.session_id() == before.session_id(),
            after.quiescent_generation() == before.quiescent_generation(),
            after.available_fractions() == before.available_fractions(),
            after.preempt_depth() == before.preempt_depth(),
        ensures
            self.matches_context(*after),
    {
        assert(before.session.session_task() == before.task());
        assert(after.session.session_task() == after.task());
        assert(self.resource().session_token().task() == before.task());
        assert(self.resource().session_token().task() == after.task());
        assert(self.resource().session_token().quiescent_generation()
            == before.quiescent_generation());
        assert(self.resource().session_token().quiescent_generation()
            == after.quiescent_generation());
        assert(after.session.token_matches(self.resource().session_token()));
    }

    /// Borrows the running task's view while this guard witnesses that
    /// preemption is disabled. Both outermost and nested guards use the same
    /// context-owned view.
    pub proof fn tracked_borrow_thread_view_mut_from_context<'context>(
        tracked context: &'context mut RunningTaskContext,
        guard: &DisabledPreemptGuard,
    ) -> (tracked tv: &'context mut ViewSeen)
        requires
            old(context).wf(),
            guard.matches_context(*old(context)),
        ensures
            (*tv)@ == old(context).view(),
            final(context).task() == old(context).task(),
            final(context).scheduler() == old(context).scheduler(),
            final(context).cpu() == old(context).cpu(),
            final(context).session_id() == old(context).session_id(),
            final(context).quiescent_generation() == old(context).quiescent_generation(),
            final(context).available_fractions() == old(context).available_fractions(),
            final(context).has_full_authority() == old(context).has_full_authority(),
            final(context).preempt_depth() == old(context).preempt_depth(),
            final(context).rcu_participant_id() == old(context).rcu_participant_id(),
            final(context).rcu_generation() == old(context).rcu_generation(),
            final(context).rcu_participant_view() == old(context).rcu_participant_view(),
            final(context).rcu_fraction() == old(context).rcu_fraction(),
            final(context).view() == (*final(tv))@,
            old(context).view().spec_le((*final(tv))@) ==> final(context).wf(),
            old(context).view().spec_le((*final(tv))@) ==> guard.matches_context(*final(context)),
    {
        context.tracked_borrow_thread_view_mut()
    }

    /// Borrows the current task's native IRC11 view while preemption is disabled.
    pub proof fn tracked_borrow_irc11_view_mut_from_context<'context>(
        tracked context: &'context mut RunningTaskContext,
        guard: &DisabledPreemptGuard,
    ) -> (tracked view: &'context mut ViewSeen)
        requires
            old(context).wf(),
            guard.matches_context(*old(context)),
        ensures
            (*view)@ == old(context).irc11_view(),
            final(context).task() == old(context).task(),
            final(context).scheduler() == old(context).scheduler(),
            final(context).cpu() == old(context).cpu(),
            final(context).view() == (*final(view))@,
            final(context).session_id() == old(context).session_id(),
            final(context).quiescent_generation() == old(context).quiescent_generation(),
            final(context).available_fractions() == old(context).available_fractions(),
            final(context).has_full_authority() == old(context).has_full_authority(),
            final(context).preempt_depth() == old(context).preempt_depth(),
            final(context).rcu_participant_id() == old(context).rcu_participant_id(),
            final(context).rcu_generation() == old(context).rcu_generation(),
            final(context).rcu_participant_view() == old(context).rcu_participant_view(),
            final(context).rcu_fraction() == old(context).rcu_fraction(),
            final(context).irc11_view() == (*final(view))@,
            old(context).irc11_view().spec_le((*final(view))@) ==> final(context).wf(),
            old(context).irc11_view().spec_le((*final(view))@) ==> guard.matches_context(
                *final(context),
            ),
    {
        context.tracked_borrow_irc11_view_mut()
    }

    /// Returns this guard's fractional witness and decrements the modeled
    /// preemption depth.
    ///
    /// The proof resource is stored in an `Option` so a containing guard's
    /// standard `Drop::drop(&mut self)` can consume it exactly once. The
    /// executable preemption counter is still decremented by this guard's Rust
    /// destructor.
    pub(crate) fn release_in_place_to_context(
        &mut self,
        Tracked(context): Tracked<&mut RunningTaskContext>,
    )
        requires
            old(context).wf(),
            old(context).preempt_depth() > 0,
            self.matches_context(*old(context)),
        ensures
            final(context).wf(),
            final(context).task() == old(context).task(),
            final(context).scheduler() == old(context).scheduler(),
            final(context).cpu() == old(context).cpu(),
            final(context).view() == old(context).view(),
            final(context).session_id() == old(context).session_id(),
            final(context).quiescent_generation() == old(context).quiescent_generation(),
            final(context).available_fractions() == old(context).available_fractions() + 1,
            final(context).preempt_depth() + 1 == old(context).preempt_depth(),
            final(context).rcu_participant_id() == old(context).rcu_participant_id(),
            final(context).rcu_generation() == old(context).rcu_generation(),
            final(context).rcu_participant_view() == old(context).rcu_participant_view(),
            final(context).rcu_fraction() == old(context).rcu_fraction(),
            !final(self).has_resource(),
        opens_invariants none
        no_unwind
    {
        proof_decl! {
            let tracked resource = self.tracked_resource.borrow_mut().tracked_take();
        }
        proof {
            context.tracked_enable_preempt(resource);
        }
    }

    /// Consuming compatibility wrapper for callers that do not need standard
    /// destructor integration.
    pub(crate) fn release_to_context(self, Tracked(context): Tracked<&mut RunningTaskContext>)
        requires
            old(context).wf(),
            old(context).preempt_depth() > 0,
            self.matches_context(*old(context)),
        ensures
            final(context).wf(),
            final(context).task() == old(context).task(),
            final(context).scheduler() == old(context).scheduler(),
            final(context).cpu() == old(context).cpu(),
            final(context).view() == old(context).view(),
            final(context).session_id() == old(context).session_id(),
            final(context).quiescent_generation() == old(context).quiescent_generation(),
            final(context).available_fractions() == old(context).available_fractions() + 1,
            final(context).preempt_depth() + 1 == old(context).preempt_depth(),
            final(context).rcu_participant_id() == old(context).rcu_participant_id(),
            final(context).rcu_generation() == old(context).rcu_generation(),
            final(context).rcu_participant_view() == old(context).rcu_participant_view(),
            final(context).rcu_fraction() == old(context).rcu_fraction(),
    {
        let mut this = self;
        this.release_in_place_to_context(Tracked(context));
    }
}

} // verus!
#[cfg(not(verus_keep_ghost))]
impl Drop for DisabledPreemptGuard {
    fn drop(&mut self) {
        super::cpu_local::dec_guard_count();
    }
}

#[verus_verify]
impl GuardTransfer for DisabledPreemptGuard {
    #[verifier::external_body]
    fn transfer_to(&mut self) -> Self {
        disable_preempt()
    }
}

verus! {

/// Disables preemption.
///
/// TODO: This API is still unsound.
pub fn disable_preempt() -> (res: DisabledPreemptGuard)
    ensures
        res.wf(arbitrary()),
{
    proof_decl! {
        let tracked tracked_resource = PreemptGuardResource::new_placeholder();
    }
    DisabledPreemptGuard::new(Tracked(tracked_resource))
}

/// Disables preemption inside the current running-task context.
///
/// This has the same executable effect as [`disable_preempt`]. Its additional
/// tracked argument updates the modeled preemption depth and ties the guard to
/// the task view checked out by the scheduler.
pub(crate) fn disable_preempt_in_context(
    Tracked(context): Tracked<&mut RunningTaskContext>,
) -> (res: DisabledPreemptGuard)
    requires
        old(context).wf(),
        old(context).available_fractions() > 1,
    ensures
        final(context).wf(),
        final(context).task() == old(context).task(),
        final(context).scheduler() == old(context).scheduler(),
        final(context).cpu() == old(context).cpu(),
        final(context).view() == old(context).view(),
        final(context).session_id() == old(context).session_id(),
        final(context).quiescent_generation() == old(context).quiescent_generation(),
        final(context).available_fractions() + 1 == old(context).available_fractions(),
        final(context).preempt_depth() == old(context).preempt_depth() + 1,
        final(context).rcu_participant_id() == old(context).rcu_participant_id(),
        final(context).rcu_generation() == old(context).rcu_generation(),
        final(context).rcu_participant_view() == old(context).rcu_participant_view(),
        final(context).rcu_fraction() == old(context).rcu_fraction(),
        res.has_resource(),
        res.is_outermost() <==> old(context).preempt_depth() == 0,
        res.is_nested() <==> old(context).preempt_depth() > 0,
        res.matches_context(*final(context)),
{
    proof_decl! {
        let tracked resource = context.tracked_disable_preempt();
    }
    DisabledPreemptGuard::new(Tracked(resource))
}

} // verus!
