// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;

// use crate::{sync::GuardTransfer, task::atomic_mode::InAtomicMode};

/// A guard for disable preempt.
#[clippy::has_significant_drop]
#[must_use]
#[derive(Debug)]
#[verus_verify]
pub struct DisabledPreemptGuard {
    // This private field prevents user from constructing values of this type directly.
    _private: (),
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

impl GuardTransfer for DisabledPreemptGuard {
    fn transfer_to(&mut self) -> Self {
        disable_preempt()
    }
}

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
