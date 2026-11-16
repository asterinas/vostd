//! Specs for stdlib methods on integer types that aren't covered by vstd.
use vstd::arithmetic::power2::is_pow2;
use vstd::bytes::{spec_u16_to_le_bytes, spec_u32_to_le_bytes};
use vstd::prelude::*;

verus! {

/// Little-endian bytes as implemented by core's uint_macros::to_le_bytes
/// (`to_le().to_ne_bytes()`), independent of the host endianness. Source:
/// Rust 1.99.1 (58cf8f9c3), library/core/src/num/uint_macros.rs; the delegated
/// to_ne_bytes uses a transmute to the same-width byte array.
pub assume_specification[ u16::to_le_bytes ](value: u16) -> (bytes: [u8; 2])
    ensures
        bytes@ == spec_u16_to_le_bytes(value),
    opens_invariants none
    no_unwind
;

pub assume_specification[ u32::to_le_bytes ](value: u32) -> (bytes: [u8; 4])
    ensures
        bytes@ == spec_u32_to_le_bytes(value),
    opens_invariants none
    no_unwind
;

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
pub assume_specification[ usize::div_ceil ](self_: usize, rhs: usize) -> usize
    requires
        rhs > 0,
    returns
        ((self_ + rhs - 1) / (rhs as int)) as usize,
    opens_invariants none
    no_unwind when rhs > 0
;

} // verus!
