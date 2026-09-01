// SPDX-License-Identifier: MPL-2.0
use vstd::{
    laws_cmp::obeys_cmp,
    prelude::*,
    std_specs::{
        cmp::{OrdSpec, PartialOrdIs, PartialOrdSpec},
        iter::{IteratorSpec, filter_keep, filter_postcondition},
    },
};
use vstd_extra::external::{iter::*, range::*};

use crate::specs::util::range::{
    lemma_range_difference_set, lemma_range_difference_sorted, range_as_set, range_difference_seq,
    seq_range_union, spec_ord_max, spec_ord_min,
};

use core::ops::Range;

/// Calculates the [difference] of two [`Range`]s, i.e., `a - b`.
///
/// This method will return 0, 1, or 2 ranges. All returned ranges are
/// guaranteed to be non-empty and non-overlapping. The returned ranges
/// will be sorted in ascending order.
///
/// [difference]: https://en.wikipedia.org/wiki/Set_(mathematics)#Set_difference
///
/// # Verified Properties
///
/// ## Safety
///
/// This function contains no unsafe code. Its proof relies on the trusted
/// `vstd_extra` specifications for owned-array iteration and [`Range::is_empty`].
///
/// ## Functional Correctness
///
/// When the upstream filter model reports completion, the iterator's remaining
/// sequence contains at most two non-empty, sorted ranges whose union is exactly
/// the set difference `a - b`.
///
/// ## Preconditions
///
/// `T`'s comparison implementation must obey the Verus comparison model.
///
/// ## Postconditions
///
/// Subject to the upstream iterator model's law and termination predicates, the
/// returned sequence matches [`range_difference_seq`] and satisfies the
/// functional-correctness properties above. The contract does not claim that
/// comparisons cannot panic.
#[verus_verify(spinoff_prover, rlimit(50))]
#[verus_spec(ret =>
    requires
        T::obeys_cmp_spec(),
        T::obeys_partial_cmp_spec(),
        obeys_cmp::<T>(),
    ensures
        ret.obeys_prophetic_iter_laws() && ret.will_return_none() ==> {
            &&& ret.remaining() == range_difference_seq(*a, *b)
            &&& ret.remaining().len() <= 2
            &&& forall|i: int|
                0 <= i < ret.remaining().len() ==> (
                #[trigger] ret.remaining()[i]).start.is_lt(&ret.remaining()[i].end)
            &&& forall|i: int|
                0 <= i < ret.remaining().len() - 1 ==> (
                #[trigger] ret.remaining()[i]).end.is_le(&ret.remaining()[i + 1].start)
            &&& seq_range_union(ret.remaining()) == range_as_set(*a).difference(range_as_set(*b))
        },
)]
pub fn range_difference<T: Ord + Copy>(
    a: &Range<T>,
    b: &Range<T>,
) -> impl Iterator<Item = Range<T>> {
    let r = if b.is_empty() {
        [a.clone(), b.clone()]
    } else {
        // `Ord::{min,max}` are the specified equivalents of `core::cmp::{min,max}`.
        [a.start..a.end.min(b.start), a.start.max(b.end)..a.end]
    };

    proof! {
        reveal_with_fuel(Seq::filter, 3);

        lemma_range_difference_sorted(*a, *b);
        lemma_range_difference_set(*a, *b);
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
                reveal_with_fuel(Seq::filter, 3);
            }
            assert(ret.remaining() == range_difference_seq(*a, *b)) by {
                reveal(range_difference_seq);
                reveal(spec_ord_min);
                reveal(spec_ord_max);
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
