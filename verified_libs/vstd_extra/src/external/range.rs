use core::ops::{Range, RangeInclusive};
use vstd::{
    prelude::*,
    std_specs::cmp::{PartialOrdIs, PartialOrdSpec},
};

verus! {

/// Length of a `Range<usize>`. Malformed ranges (`start > end`) are length 0,
/// matching `ExactSizeIterator::len` for `Range<A: Step>` where `Step::steps_between`
/// returns `None` on `end < start`, collapsed to 0.
pub open spec fn range_usize_len_spec(r: &Range<usize>) -> usize {
    if r.start < r.end {
        (r.end - r.start) as usize
    } else {
        0usize
    }
}

/// Exec-mode `len` for a `Range<usize>`: use in place of `r.len()` which is an
/// `ExactSizeIterator` provided method and can't be specced with
/// `assume_specification`.
#[verifier::when_used_as_spec(range_usize_len_spec)]
pub fn range_usize_len(r: &Range<usize>) -> (ret: usize)
    ensures
        ret == range_usize_len_spec(r),
{
    if r.start < r.end {
        r.end - r.start
    } else {
        0
    }
}

/// `Range::clone` clones each field via `Idx::clone`; each field's clone
/// `ensures` (guarded by its `requires`) applies to `res.start`/`res.end`.
pub assume_specification<Idx: Clone>[ Range::<Idx>::clone ](range: &Range<Idx>) -> (res: Range<Idx>)
    ensures
        Idx::clone.requires((&range.start,)) && Idx::clone.requires((&range.end,)) ==> {
            &&& Idx::clone.ensures((&range.start,), res.start)
            &&& Idx::clone.ensures((&range.end,), res.end)
        },
;

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
