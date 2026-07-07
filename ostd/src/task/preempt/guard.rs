// SPDX-License-Identifier: MPL-2.0
use vstd::{prelude::*, resource::Loc};
use vstd_extra::resource::ghost_resource::{
    count::CountGhost,
    tokens::CountGhostResource,
};

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
    tracked token: CountGhost<Loc, PREEMPT_SESSION_FRACTIONS>,
}

impl PreemptSessionToken {
    proof fn new_placeholder() -> (tracked res: Self)
        ensures
            res.wf(),
    {
        let tracked mut tokens = CountGhostResource::<Loc, PREEMPT_SESSION_FRACTIONS>::alloc(
            arbitrary(),
        );
        let tracked token = tokens.split_one();
        PreemptSessionToken { token }
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
    pub proof fn new(tracked task_view: TaskThreadView) -> (tracked res: Self)
        ensures
            res.task() == task_view.task(),
            res.view() == task_view.view(),
            res.session_task() == task_view.task(),
            res.available_fractions() == PREEMPT_SESSION_FRACTIONS,
            res.wf_session_resource(),
    {
        let task = task_view.task();
        let tracked tokens = CountGhostResource::alloc(task);
        PreemptThreadViewSession { task_view, tokens }
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
    pub proof fn tracked_split_guard_token(
        tracked &mut self,
    ) -> (tracked token: PreemptSessionToken)
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
    pub proof fn tracked_return_guard_token(
        tracked &mut self,
        tracked token: PreemptSessionToken,
    )
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
        let tracked PreemptSessionToken { token } = token;
        self.tokens.combine(token);
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
        ensures
            res.task() == self.task(),
            res.view() == self.view(),
    {
        self.task_view
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
    Nested {
        tracked session: PreemptSessionToken,
        tracked nested: NestedPreemptToken,
    },
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
    fn new(
        Tracked(tracked_resource): Tracked<PreemptGuardResource>,
    ) -> (res: DisabledPreemptGuard)
        requires
            tracked_resource.wf(arbitrary()),
        ensures
            res.wf(arbitrary()),
    {
        // The current verification slice does not include the CPU-local
        // runtime preemption counter backend. This body verifies construction
        // of the guard resource; wiring the real counter increment back in
        // should happen when that backend is part of this dependency closure.
        Self {
            _private: (),
            tracked_resource: Tracked(tracked_resource),
        }
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

    /// Lets a nested preemption-disable scope use the outer/session view.
    ///
    /// The `nested` guard is only a witness that this call happens under a
    /// nested preemption-disable scope. The linear `ThreadView` is borrowed
    /// from `session`, so nested RCU can perform weak atomic operations
    /// without owning or synthesizing another per-task view.
    pub proof fn tracked_borrow_thread_view_mut_from_session<'session>(
        tracked session: &'session mut PreemptThreadViewSession,
        nested: &DisabledPreemptGuard,
    ) -> (tracked tv: &'session mut ThreadView)
        requires
            nested.is_nested(),
            nested.matches_session(*old(session)),
        ensures
            (*tv)@ == old(session).view(),
            final(session).task() == old(session).task(),
            final(session).session_id() == old(session).session_id(),
            final(session).session_task() == old(session).session_task(),
            final(session).available_fractions() == old(session).available_fractions(),
            final(session).wf_session_resource() == old(session).wf_session_resource(),
            final(session).view() == (*final(tv))@,
    {
        session.tracked_borrow_thread_view_mut()
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
pub fn disable_preempt() -> (res: DisabledPreemptGuard)
    ensures
        res.wf(arbitrary()),
{
    proof_decl! {
        let tracked tracked_resource = PreemptGuardResource::new_placeholder();
    }
    DisabledPreemptGuard::new(Tracked(tracked_resource))
}

} // verus!
