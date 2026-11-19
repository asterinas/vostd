//! Specifications for bit-related standard-library functions.
use vstd::prelude::*;
use vstd::std_specs::bits::axiom_u64_count_ones;

verus! {

/// The number of set bits in a `u64` word.
///
/// vstd specifies `u64::count_ones` itself (in terms of `nat_count_ones`), so
/// this is that count read as an `int`. It was a local recursive definition over
/// `u64_bit_is_set` plus an `assume_specification` until vstd grew one; keeping
/// both is a duplicate-specification error.
pub closed spec fn u64_set_bits(w: u64) -> int {
    w.count_ones() as int
}

/// A nonzero word has at least one set bit (and zero has none), and the
/// executable count agrees with the spec one -- the fact the local
/// `assume_specification` used to supply.
pub broadcast proof fn lemma_u64_set_bits_nonzero(w: u64)
    ensures
        #![trigger u64_set_bits(w)]
        (w != 0u64) == (1 <= u64_set_bits(w)),
        0 <= u64_set_bits(w) <= 64,
        w.count_ones() == u64_set_bits(w),
{
    broadcast use axiom_u64_count_ones;

}

} // verus!
