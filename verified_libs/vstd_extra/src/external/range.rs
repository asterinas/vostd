use core::ops::Range;
use vstd::prelude::*;

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

} // verus!
