use vstd::prelude::*;

verus! {

#[must_use]
#[derive(Debug)]
pub struct DisabledPreemptGuard {
    _private: (),
}

impl !Send for DisabledPreemptGuard {

}

#[verifier::external_body]
extern  fn cpu_local_inc_guard_count()
    opens_invariants none
    no_unwind
;

#[verifier::external_body]
extern  fn cpu_local_dec_guard_count()
    opens_invariants none
    no_unwind
;

impl DisabledPreemptGuard {
    fn new() -> Self {
        cpu_local_inc_guard_count();
        Self { _private: () }
    }

    pub fn transfer_to(&self) -> Self {
        disable_preempt()
    }
}

impl Drop for DisabledPreemptGuard {
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        cpu_local_dec_guard_count();
    }
}

/// Disables preemption.
pub fn disable_preempt() -> DisabledPreemptGuard {
    DisabledPreemptGuard::new()
}

} // verus!
