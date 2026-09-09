// SPDX-License-Identifier: MPL-2.0
use vstd::{
    laws_cmp::{
        obeys_cmp, obeys_cmp_ord, obeys_cmp_partial_ord, obeys_partial_cmp_spec_properties,
    },
    laws_eq::obeys_eq_spec_properties,
    prelude::*,
    set_lib::{FiniteRange, range_set_properties},
    std_specs::{
        cmp::PartialOrdIs,
        iter::{IteratorSpec, filter_keep, filter_postcondition},
    },
};
use vstd_extra::{
    external::{cmp::*, iter::*, range::*},
    range::{
        RangeExtraFns, finite_range_matches_ord, lemma_seq_range_union_contains, seq_range_union,
    },
};

use core::ops::Range;

verus! {

/// Operational spec of `range_difference`: the two candidate ranges,
/// dropping any empty ones, matching the executable control flow.
pub open spec fn range_difference_spec<T: Ord>(a: Range<T>, b: Range<T>) -> Seq<Range<T>> {
    let left = if !b.start.is_lt(&b.end) {
        a
    } else {
        Range { start: a.start, end: spec_ord_min(a.end, b.start) }
    };
    let right = if !b.start.is_lt(&b.end) {
        b
    } else {
        Range { start: spec_ord_max(a.start, b.end), end: a.end }
    };
    if left.start.is_lt(&left.end) {
        if right.start.is_lt(&right.end) {
            seq![left, right]
        } else {
            seq![left]
        }
    } else if right.start.is_lt(&right.end) {
        seq![right]
    } else {
        Seq::empty()
    }
}

pub proof fn lemma_range_difference_set<T: FiniteRange + Ord>(a: Range<T>, b: Range<T>)
    requires
        obeys_cmp::<T>(),
        finite_range_matches_ord::<T>(),
    ensures
        seq_range_union(range_difference_spec(a, b)) == a.view_set().difference(b.view_set()),
{
    broadcast use range_set_properties;

    reveal(obeys_partial_cmp_spec_properties);
    reveal(obeys_cmp_ord);
    reveal(obeys_eq_spec_properties);
    let s = range_difference_spec(a, b);
    assert forall|x: T| #[trigger]
        seq_range_union(s).contains(x) <==> ((s.len() >= 1 && s[0].view_set().contains(x)) || (
        s.len() == 2 && s[1].view_set().contains(x))) by {
        lemma_seq_range_union_contains(s, x);
        let pred = |r: Range<T>| r.view_set().contains(x);
        if s.any(pred) {
            let i = choose|i: int| #![auto] 0 <= i < s.len() && pred(s[i]);
            assert(i == 0 || i == 1);
        }
    }
    assert forall|x: T|
        #![trigger a.view_set().contains(x)]
        seq_range_union(s).contains(x) <==> a.view_set().difference(b.view_set()).contains(x) by {}
}

} // verus!
/// Calculates the [difference] of two [`Range`]s, i.e., `a - b`.
///
/// This method will return 0, 1, or 2 ranges. All returned ranges are
/// guaranteed to be non-empty and non-overlapping. The returned ranges
/// will be sorted in ascending order.
///
/// [difference]: https://en.wikipedia.org/wiki/Set_(mathematics)#Set_difference
#[verus_verify(spinoff_prover, rlimit(50))]
#[verus_spec(ret =>
    requires
        obeys_cmp::<T>(),
        finite_range_matches_ord::<T>(),
    ensures
        ret.obeys_prophetic_iter_laws() && ret.will_return_none() ==> {
            &&& ret.remaining() == range_difference_spec(*a, *b)
            &&& ret.remaining().len() <= 2
            &&& ret.remaining().all(
                |range: Range<T>| range.start.is_lt(&range.end),
            )
            &&& forall|i: int|
                0 <= i < ret.remaining().len() - 1 ==> (
                #[trigger] ret.remaining()[i]).end.is_le(&ret.remaining()[i + 1].start)
            &&& seq_range_union(ret.remaining()) == (*a).view_set().difference((*b).view_set())
        },
)]
pub fn range_difference<T: Ord + Copy + FiniteRange>(
    a: &Range<T>,
    b: &Range<T>,
) -> impl Iterator<Item = Range<T>> {
    use core::cmp::{max, min};

    proof! {
        reveal(obeys_cmp_partial_ord);
        reveal(obeys_cmp_ord);
    }
    let r = if b.is_empty() {
        [a.clone(), b.clone()]
    } else {
        [a.start..min(a.end, b.start), max(a.start, b.end)..a.end]
    };

    proof! {
        reveal_with_fuel(Seq::filter, 3);
    }
    // Original execution: `r.into_iter().filter(|v| !v.is_empty())`.
    // Bind its operands so the upstream filter axiom can refer to them.
    let iter = r.into_iter();
    let pred = #[verus_spec(keep: bool =>
        ensures
            keep == v.start.is_lt(&v.end),
    )]
    |v: &Range<T>| !v.is_empty();
    let ret = iter.filter(pred);
    proof! {
        filter_postcondition(iter, pred, ret);
        if ret.will_return_none() {
            let keep = filter_keep(ret);

            assert forall|j: int| #![auto] 0 <= j < keep.len() implies keep[j] ==
                iter.remaining()[j].start.is_lt(&iter.remaining()[j].end) by {}
            assert(iter.remaining().take(keep.len() as int).filter_index(|j: int| keep[j]) ==
                iter.remaining().filter(|v: Range<T>| v.start.is_lt(&v.end))) by {
                reveal_with_fuel(Seq::filter_index, 3);
            }
            assert(ret.remaining() == range_difference_spec(*a, *b));
            assert forall|i: int|
                0 <= i < ret.remaining().len() - 1 implies (
                #[trigger] ret.remaining()[i]).end.is_le(&ret.remaining()[i + 1].start) by {
                reveal(obeys_partial_cmp_spec_properties);
            }
            assert(seq_range_union(ret.remaining()) ==
                (*a).view_set().difference((*b).view_set())) by {
                lemma_range_difference_set(*a, *b);
            }
        }
    }
    ret
}

#[cfg(ktest)]
#[expect(clippy::single_range_in_vec_init)]
mod test {
    use super::*;
    use crate::prelude::ktest;

    #[track_caller]
    fn assert_range_difference<const N: usize>(
        a: Range<usize>,
        b: Range<usize>,
        expected: [Range<usize>; N],
    ) {
        let mut res = range_difference(&a, &b);
        expected
            .into_iter()
            .for_each(|val| assert_eq!(res.next(), Some(val)));
        assert!(res.next().is_none());
    }

    #[ktest]
    fn range_difference_contained() {
        assert_range_difference(0..10, 3..7, [0..3, 7..10]);
    }
    #[ktest]
    fn range_difference_all_same() {
        assert_range_difference(0..10, 0..10, []);
    }
    #[ktest]
    fn range_difference_left_same() {
        assert_range_difference(0..10, 0..5, [5..10]);
    }
    #[ktest]
    fn range_difference_right_same() {
        assert_range_difference(0..10, 5..10, [0..5]);
    }
    #[ktest]
    fn range_difference_b_empty() {
        assert_range_difference(0..10, 0..0, [0..10]);
    }
    #[ktest]
    fn range_difference_a_empty() {
        assert_range_difference(0..0, 0..10, []);
    }
    #[ktest]
    fn range_difference_all_empty() {
        assert_range_difference(0..0, 0..0, []);
    }
    #[ktest]
    fn range_difference_left_intersected() {
        assert_range_difference(5..10, 0..6, [6..10]);
    }
    #[ktest]
    fn range_difference_right_intersected() {
        assert_range_difference(5..10, 6..12, [5..6]);
    }
}
