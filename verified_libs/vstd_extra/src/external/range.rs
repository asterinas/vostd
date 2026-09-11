use vstd::{
    prelude::*,
    std_specs::cmp::{PartialOrdIs, PartialOrdSpec},
};

use core::ops::{Range, RangeInclusive};

verus! {

/// Whether a `Range<usize>` is empty. Malformed ranges (`start > end`) are empty.
pub open spec fn range_usize_is_empty_spec(r: &Range<usize>) -> bool {
    !(r.start < r.end)
}

/// Exec-mode `is_empty` for a `Range<usize>`: use in place of `r.is_empty()`
/// which needs `Idx: PartialOrd<Idx>` bound that doesn't round-trip cleanly
/// through `assume_specification`.
#[verifier::when_used_as_spec(range_usize_is_empty_spec)]
pub fn range_usize_is_empty(r: &Range<usize>) -> (ret: bool)
    ensures
        ret == range_usize_is_empty_spec(r),
{
    !(r.start < r.end)
}

/// See [`Range::is_empty`](https://doc.rust-lang.org/std/ops/struct.Range.html#method.is_empty).
pub assume_specification<Idx: PartialOrd<Idx>>[ Range::<Idx>::is_empty ](r: &Range<Idx>) -> (res:
    bool) where Idx: PartialOrd<Idx>
    ensures
        <Idx as PartialOrdSpec<Idx>>::obeys_partial_cmp_spec() ==> res == !r.start.is_lt(&r.end),
;

pub assume_specification<Idx>[ RangeInclusive::start ](r: &RangeInclusive<Idx>) -> (ret: &Idx)
    ensures
        *ret == r@.start,
;

pub assume_specification<Idx>[ RangeInclusive::end ](r: &RangeInclusive<Idx>) -> (ret: &Idx)
    ensures
        *ret == r@.end,
;

} // verus!
