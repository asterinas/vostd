use vstd::{
    prelude::*,
    std_specs::cmp::{PartialOrdIs, PartialOrdSpec},
};

use core::ops::{Range, RangeInclusive};

verus! {

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
