//! Specs for stdlib methods on integer types that aren't covered by vstd.
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;

verus! {

/// Spec for `<int_type>::is_power_of_two`. Returns true iff `self` is a positive
/// power of two, i.e., there exists `e: nat` with `pow2(e) == self`.
pub assume_specification[ u8::is_power_of_two ](self_: u8) -> (r: bool)
    ensures
        r <==> (exists|e: nat| pow2(e) == self_),
;

pub assume_specification[ u16::is_power_of_two ](self_: u16) -> (r: bool)
    ensures
        r <==> (exists|e: nat| pow2(e) == self_),
;

pub assume_specification[ u32::is_power_of_two ](self_: u32) -> (r: bool)
    ensures
        r <==> (exists|e: nat| pow2(e) == self_),
;

pub assume_specification[ u64::is_power_of_two ](self_: u64) -> (r: bool)
    ensures
        r <==> (exists|e: nat| pow2(e) == self_),
;

pub assume_specification[ usize::is_power_of_two ](self_: usize) -> (r: bool)
    ensures
        r <==> (exists|e: nat| pow2(e) == self_),
;

} // verus!
