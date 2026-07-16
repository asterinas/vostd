// SPDX-License-Identifier: MPL-2.0
use vstd::{prelude::*, resource::Loc};
use vstd_extra::resource::ghost_resource::{count::CountGhost, tokens::CountGhostResource};

use crate::{
    specs::sync::weak_memory::{ThreadView, WmView},
    sync::GuardTransfer, /*, task::atomic_mode::InAtomicMode*/
    task::scheduler::{SchedulerView, TaskThreadView},
};

verus! {

pub const PREEMPT_SESSION_FRACTIONS: u64 = 1 << 31;

/// Proof token carried by a nested preemption-disable guard.
///
/// Nested guards deliberately do not carry a `TaskThreadView`; the current
/// task's weak-memory view has already been checked out by the outermost
/// guard. This token only records that the guard was created while preemption
/// was already disabled.
pub tracked struct NestedPreemptToken {
    ghost depth_before: nat,
}

impl NestedPreemptToken {
    pub proof fn new(depth_before: nat) -> (tracked res: Self)
        requires
            depth_before > 0,
        ensures
            res.depth_before() == depth_before,
            res.wf(),
    {
        NestedPreemptToken { depth_before }
    }

    pub closed spec fn depth_before(self) -> nat {
        self.depth_before
    }

    pub closed spec fn wf(self) -> bool {
        self.depth_before() > 0
    }
}

/// A shareable proof token tying a guard to the active preemption session.
///
/// The token is a fractional resource-algebra fragment. It records only stable
/// session identity, currently the running task id. The mutable weak-memory
/// view is intentionally not stored here because weak atomic operations update
/// that view while guard fragments may be outstanding.
pub tracked struct PreemptSessionToken {
    token: CountGhost<Loc, PREEMPT_SESSION_FRACTIONS>,
}

impl PreemptSessionToken {
    proof fn new_placeholder() -> (tracked res: Self)
        ensures
            res.wf(),
    {
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000u64) by (compute);
        assert(PREEMPT_SESSION_FRACTIONS > 1) by (compute);
        let tracked mut tokens = CountGhostResource::<Loc, PREEMPT_SESSION_FRACTIONS>::alloc(
            arbitrary(),
        );
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
        self.token@
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
    tracked task_view: TaskThreadView,
    tracked tokens: CountGhostResource<Loc, PREEMPT_SESSION_FRACTIONS>,
}

impl PreemptThreadViewSession {
    pub proof fn new(tracked task_view: TaskThreadView, sched_view: SchedulerView) -> (tracked res:
        Self)
        requires
            task_view.wf(sched_view),
        ensures
            res.task() == task_view.task(),
            res.view() == task_view.view(),
            res.session_task() == task_view.task(),
            res.available_fractions() == PREEMPT_SESSION_FRACTIONS,
            res.wf_session_resource(),
            res.wf(sched_view),
    {
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000u64) by (compute);
        assert(PREEMPT_SESSION_FRACTIONS > 1) by (compute);
        let task = task_view.task();
        let tracked tokens = CountGhostResource::<Loc, PREEMPT_SESSION_FRACTIONS>::alloc(task);
        assert(tokens.is_full());
        tokens.validate_full();
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

    pub closed spec fn view(self) -> WmView {
        self.task_view.view()
    }

    pub closed spec fn session_id(self) -> Loc {
        self.tokens.id()
    }

    pub closed spec fn session_task(self) -> Loc {
        self.tokens@
    }

    pub closed spec fn available_fractions(self) -> int {
        self.tokens.frac()
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
            final(self).view() == old(self).view(),
            final(self).session_id() == old(self).session_id(),
            final(self).session_task() == old(self).session_task(),
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
            final(self).view() == old(self).view(),
            final(self).session_id() == old(self).session_id(),
            final(self).session_task() == old(self).session_task(),
            final(self).available_fractions() == old(self).available_fractions() + token.frac(),
            final(self).wf_session_resource(),
    {
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000u64) by (compute);
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
        assert(self.tokens@ == self.task_view.task());
        assert(self.wf_session_resource());
    }

    /// Borrows the single task-local `ThreadView` for weak atomic operations.
    ///
    /// After the borrow mutates the view, the caller must update the scheduler
    /// snapshot with `SchedulerView::update_checked_out_task_view` before
    /// relying on `wf` again.
    pub proof fn tracked_borrow_thread_view_mut(tracked &mut self) -> (tracked tv: &mut ThreadView)
        ensures
            (*tv)@ == old(self).view(),
            final(self).task() == old(self).task(),
            final(self).session_id() == old(self).session_id(),
            final(self).session_task() == old(self).session_task(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).wf_session_resource() == old(self).wf_session_resource(),
            final(self).view() == (*final(tv))@,
    {
        self.task_view.tracked_borrow_thread_view_mut()
    }

    /// Returns the checked-out view to the caller for scheduler check-in.
    ///
    /// This is the proof-side counterpart of dropping the outermost
    /// preemption-disable scope: the session stops owning the task view, and
    /// the caller can write it back with
    /// `SchedulerThreadViews::tracked_put_checked_out_thread_view`.
    pub proof fn tracked_into_task_view(tracked self) -> (tracked res: TaskThreadView)
        requires
            self.wf_session_resource(),
            self.available_fractions() == PREEMPT_SESSION_FRACTIONS,
        ensures
            res.task() == self.task(),
            res.view() == self.view(),
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
            res.task() == self.task(),
            res.view() == self.view(),
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
    tracked session: PreemptThreadViewSession,
    ghost preempt_depth: nat,
}

impl RunningTaskContext {
    /// Starts a running interval for a checked-out task view.
    pub proof fn new(tracked task_view: TaskThreadView, sched_view: SchedulerView) -> (tracked res:
        Self)
        requires
            task_view.wf(sched_view),
        ensures
            res.task() == task_view.task(),
            res.view() == task_view.view(),
            res.preempt_depth() == 0,
            res.available_fractions() == PREEMPT_SESSION_FRACTIONS,
            res.wf(),
            res.is_quiescent(),
            res.wf_scheduler(sched_view),
    {
        let tracked session = PreemptThreadViewSession::new(task_view, sched_view);
        let tracked res = RunningTaskContext { session, preempt_depth: 0 };
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000u64) by (compute);
        assert(res.wf());
        assert(res.session.wf(sched_view));
        assert(res.wf_scheduler(sched_view));
        res
    }

    pub closed spec fn task(self) -> Loc {
        self.session.task()
    }

    pub closed spec fn view(self) -> WmView {
        self.session.view()
    }

    pub closed spec fn session_id(self) -> Loc {
        self.session.session_id()
    }

    pub closed spec fn available_fractions(self) -> int {
        self.session.available_fractions()
    }

    pub closed spec fn preempt_depth(self) -> nat {
        self.preempt_depth
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.session.wf_session_resource()
        &&& self.available_fractions() + self.preempt_depth() == PREEMPT_SESSION_FRACTIONS
    }

    /// Relates this running context to the scheduler snapshot from which its
    /// task view was checked out.
    pub closed spec fn wf_scheduler(self, sched_view: SchedulerView) -> bool {
        &&& self.wf()
        &&& self.session.wf(sched_view)
    }

    /// Re-establishes the scheduler relation after the checked-out task view
    /// has been updated to this context's current weak-memory view.
    pub proof fn lemma_wf_scheduler(tracked &self, sched_view: SchedulerView)
        requires
            self.wf(),
            sched_view.wf(),
            sched_view.task_view_is_checked_out(self.task()),
            sched_view.checked_out_views[self.task()] == self.view(),
            sched_view.task_views.contains_key(self.task()),
            sched_view.task_views[self.task()] == self.view(),
        ensures
            self.wf_scheduler(sched_view),
    {
        self.session.task_view.lemma_wf(sched_view);
        assert(self.session.wf(sched_view));
    }

    pub open spec fn is_quiescent(self) -> bool {
        &&& self.preempt_depth() == 0
        &&& self.available_fractions() == PREEMPT_SESSION_FRACTIONS
    }

    /// Borrows the running task's persistent weak-memory view.
    pub proof fn tracked_borrow_thread_view_mut(tracked &mut self) -> (tracked tv: &mut ThreadView)
        requires
            old(self).wf(),
        ensures
            (*tv)@ == old(self).view(),
            final(self).task() == old(self).task(),
            final(self).session_id() == old(self).session_id(),
            final(self).available_fractions() == old(self).available_fractions(),
            final(self).preempt_depth() == old(self).preempt_depth(),
            final(self).wf(),
            final(self).view() == (*final(tv))@,
    {
        self.session.tracked_borrow_thread_view_mut()
    }

    /// Ends a running interval and returns the updated task view to scheduler
    /// ownership. The full-fraction requirement rules out live preempt guards.
    pub proof fn tracked_into_task_view(tracked self) -> (tracked res: TaskThreadView)
        requires
            self.wf(),
            self.preempt_depth() == 0,
        ensures
            res.task() == self.task(),
            res.view() == self.view(),
    {
        assert(self.available_fractions() == PREEMPT_SESSION_FRACTIONS);
        self.session.tracked_into_task_view()
    }

    /// Scheduler-facing form of `tracked_into_task_view` that preserves the
    /// checked-out token's relation to the supplied scheduler snapshot.
    pub proof fn tracked_into_task_view_for_scheduler(
        tracked self,
        sched_view: SchedulerView,
    ) -> (tracked res: TaskThreadView)
        requires
            self.wf_scheduler(sched_view),
            self.is_quiescent(),
        ensures
            res.task() == self.task(),
            res.view() == self.view(),
            res.wf(sched_view),
    {
        assert(self.preempt_depth() == 0);
        assert(self.available_fractions() == PREEMPT_SESSION_FRACTIONS);
        assert(self.session.wf(sched_view));
        let tracked res = self.session.tracked_into_task_view_for_scheduler(sched_view);
        res
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
            final(session).view() == old(session).view(),
            final(session).session_id() == old(session).session_id(),
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
            final(self).view() == old(self).view(),
            final(self).session_id() == old(self).session_id(),
            final(self).available_fractions() + 1 == old(self).available_fractions(),
            final(self).preempt_depth() == old(self).preempt_depth() + 1,
            resource.matches_context(*final(self)),
            resource.is_outermost() <==> old(self).preempt_depth() == 0,
            resource.is_nested() <==> old(self).preempt_depth() > 0,
    {
        let ghost depth_before = self.preempt_depth;
        let tracked token = self.session.tracked_split_guard_token();
        let tracked resource = if depth_before == 0 {
            PreemptGuardResource::Outermost(token)
        } else {
            let tracked nested = NestedPreemptToken::new(depth_before);
            PreemptGuardResource::Nested { session: token, nested }
        };
        self.preempt_depth = depth_before + 1;
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000u64) by (compute);
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
            final(self).view() == old(self).view(),
            final(self).session_id() == old(self).session_id(),
            final(self).available_fractions() == old(self).available_fractions() + 1,
            final(self).preempt_depth() + 1 == old(self).preempt_depth(),
    {
        let ghost old_depth = self.preempt_depth;
        resource.tracked_return_to_session(&mut self.session);
        self.preempt_depth = (old_depth - 1) as nat;
        assert(PREEMPT_SESSION_FRACTIONS == 0x8000_0000u64) by (compute);
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
    tracked_resource: Tracked<PreemptGuardResource>,
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
            res.tracked_resource@ == tracked_resource,
    {
        // The current verification slice does not include the CPU-local
        // runtime preemption counter backend. This body verifies construction
        // of the guard resource; wiring the real counter increment back in
        // should happen when that backend is part of this dependency closure.
        Self { _private: (), tracked_resource: Tracked(tracked_resource) }
    }
}

impl DisabledPreemptGuard {
    pub closed spec fn is_outermost(&self) -> bool {
        self.tracked_resource@.is_outermost()
    }

    pub closed spec fn is_nested(&self) -> bool {
        self.tracked_resource@.is_nested()
    }

    pub closed spec fn wf(&self, sched_view: SchedulerView) -> bool {
        self.tracked_resource@.wf(sched_view)
    }

    pub closed spec fn matches_session(&self, session: PreemptThreadViewSession) -> bool {
        self.tracked_resource@.matches_session(session)
    }

    pub closed spec fn matches_context(&self, context: RunningTaskContext) -> bool {
        self.tracked_resource@.matches_context(context)
    }

    /// Extracts the positive preemption depth witnessed by this guard.
    pub proof fn lemma_matches_context_depth(&self, tracked context: &RunningTaskContext)
        requires
            self.matches_context(*context),
        ensures
            context.preempt_depth() > 0,
    {
    }

    /// Borrows the running task's view while this guard witnesses that
    /// preemption is disabled. Both outermost and nested guards use the same
    /// context-owned view.
    pub proof fn tracked_borrow_thread_view_mut_from_context<'context>(
        tracked context: &'context mut RunningTaskContext,
        guard: &DisabledPreemptGuard,
    ) -> (tracked tv: &'context mut ThreadView)
        requires
            old(context).wf(),
            guard.matches_context(*old(context)),
        ensures
            (*tv)@ == old(context).view(),
            final(context).task() == old(context).task(),
            final(context).session_id() == old(context).session_id(),
            final(context).available_fractions() == old(context).available_fractions(),
            final(context).preempt_depth() == old(context).preempt_depth(),
            final(context).wf(),
            final(context).view() == (*final(tv))@,
            guard.matches_context(*final(context)),
    {
        context.tracked_borrow_thread_view_mut()
    }

    /// Consumes this guard, returns its fractional witness, and decrements the
    /// modeled preemption depth.
    pub(crate) fn release_to_context(self, Tracked(context): Tracked<&mut RunningTaskContext>)
        requires
            old(context).wf(),
            old(context).preempt_depth() > 0,
            self.matches_context(*old(context)),
        ensures
            final(context).wf(),
            final(context).task() == old(context).task(),
            final(context).view() == old(context).view(),
            final(context).session_id() == old(context).session_id(),
            final(context).available_fractions() == old(context).available_fractions() + 1,
            final(context).preempt_depth() + 1 == old(context).preempt_depth(),
    {
        proof_decl! {
            let tracked resource = self.tracked_resource.get();
        }
        proof {
            context.tracked_enable_preempt(resource);
        }
    }
}

} // verus!
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
        final(context).view() == old(context).view(),
        final(context).session_id() == old(context).session_id(),
        final(context).available_fractions() + 1 == old(context).available_fractions(),
        final(context).preempt_depth() == old(context).preempt_depth() + 1,
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
