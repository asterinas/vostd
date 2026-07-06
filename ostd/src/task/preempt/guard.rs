// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;

use crate::{
    sync::GuardTransfer, /*, task::atomic_mode::InAtomicMode*/
    task::scheduler::{SchedulerView, TaskThreadView},
};

verus! {

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

/// Proof resource carried by a `DisabledPreemptGuard`.
///
/// Only the outermost guard owns the checked-out task view. Nested guards own
/// a separate token that cannot be used to borrow or synthesize a `ThreadView`.
pub tracked enum PreemptGuardResource {
    Outermost(TaskThreadView),
    Nested(NestedPreemptToken),
}

impl PreemptGuardResource {
    pub closed spec fn is_outermost(self) -> bool {
        self is Outermost
    }

    pub closed spec fn is_nested(self) -> bool {
        self is Nested
    }

    pub closed spec fn wf(self, sched_view: SchedulerView) -> bool {
        match self {
            PreemptGuardResource::Outermost(task_view) => task_view.wf(sched_view),
            PreemptGuardResource::Nested(token) => token.wf(),
        }
    }
}

} // verus!

/// A guard for disable preempt.
#[verus_verify]
#[clippy::has_significant_drop]
#[must_use]
#[derive(Debug)]
pub struct DisabledPreemptGuard {
    // This private field prevents user from constructing values of this type directly.
    _private: (),

    // Proof-only guard resource.
    //
    // The outermost guard owns the current task's checked-out `TaskThreadView`.
    // Nested guards only own a nesting token, so they cannot mint another
    // `ThreadView` for the same task.
    tracked_resource: Tracked<PreemptGuardResource>,
}

/* impl !Send for DisabledPreemptGuard {}

// SAFETY: The guard disables preemptions, which meets the second
// sufficient condition for atomic mode.
unsafe impl InAtomicMode for DisabledPreemptGuard {}

impl DisabledPreemptGuard {
    fn new() -> Self {
        super::cpu_local::inc_guard_count();
        Self { _private: () }
    }
}
*/

verus! {

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
}

} // verus!

#[verus_verify]
impl GuardTransfer for DisabledPreemptGuard {
    #[verifier::external_body]
    fn transfer_to(&mut self) -> Self {
        disable_preempt()
    }
}

/*
impl Drop for DisabledPreemptGuard {
    fn drop(&mut self) {
        super::cpu_local::dec_guard_count();
    }
} */

/// Disables preemption.
#[verifier::external_body]
pub fn disable_preempt() -> DisabledPreemptGuard {
    // DisabledPreemptGuard::new()
    unimplemented!()
}
