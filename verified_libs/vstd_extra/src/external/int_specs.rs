//! Specs for stdlib methods on integer types that aren't covered by vstd.
use vstd::arithmetic::power2::is_pow2;
use vstd::prelude::*;

verus! {

/// Spec for `<int_type>::is_power_of_two`. Returns true iff `self` is a positive
/// power of two, i.e., there exists `e: nat` with `pow2(e) == self`.
pub assume_specification[ u8::is_power_of_two ](self_: u8) -> (r: bool)
    returns
        is_pow2(self_ as int),
    opens_invariants none
    no_unwind
;

pub assume_specification[ u16::is_power_of_two ](self_: u16) -> (r: bool)
    returns
        is_pow2(self_ as int),
    opens_invariants none
    no_unwind
;

pub assume_specification[ u32::is_power_of_two ](self_: u32) -> (r: bool)
    returns
        is_pow2(self_ as int),
    opens_invariants none
    no_unwind
;

pub assume_specification[ u64::is_power_of_two ](self_: u64) -> (r: bool)
    returns
        is_pow2(self_ as int),
    opens_invariants none
    no_unwind
;

pub assume_specification[ usize::is_power_of_two ](self_: usize) -> (r: bool)
    returns
        is_pow2(self_ as int),
    opens_invariants none
    no_unwind
;

/// `usize::div_ceil` panics if `rhs` is zero; the precondition excludes that case.
pub assume_specification[ usize::div_ceil ](self_: usize, rhs: usize) -> (r: usize)
    requires
        rhs > 0,
    ensures
        r == (self_ + rhs - 1) / (rhs as int),
    opens_invariants none
    no_unwind when rhs > 0
;

} // verus!
