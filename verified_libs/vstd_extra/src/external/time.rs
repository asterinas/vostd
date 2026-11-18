use vstd::prelude::*;

use crate::panic::no_panic_when;

verus! {

/// Abstract result of constructing a standard-library duration.
pub uninterp spec fn duration_new_spec(secs: u64, nanos: u32) -> core::time::Duration;

#[verifier::when_used_as_spec(duration_new_spec)]
pub assume_specification[ core::time::Duration::new ](secs: u64, nanos: u32) -> core::time::Duration
    requires
        no_panic_when(secs + nanos / 1_000_000_000 <= u64::MAX),
    returns
        duration_new_spec(secs, nanos),
    opens_invariants none
;

} // verus!
