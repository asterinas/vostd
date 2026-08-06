use vstd::prelude::*;

verus! {

/// Abstract result of constructing a standard-library duration.
pub uninterp spec fn duration_new_spec(secs: u64, nanos: u32) -> core::time::Duration;

pub assume_specification[ core::time::Duration::new ](secs: u64, nanos: u32) -> core::time::Duration
    requires
        secs + (nanos / 1_000_000_000) as u64 <= u64::MAX,
    returns
        duration_new_spec(secs, nanos),
    opens_invariants none
    no_unwind
;

} // verus!
