// SPDX-License-Identifier: MPL-2.0
use vstd::iset::ISet;
use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialEqSpec, PartialOrdIs, PartialOrdSpec};
use vstd::std_specs::iter::IteratorSpec;
use vstd_extra::external::range::*;

use core::cmp::Ordering;
use core::ops::Range;

verus! {

pub open spec fn spec_ord_min<T: Ord>(x: T, y: T) -> T {
    match y.cmp_spec(&x) {
        Ordering::Less => y,
        Ordering::Equal => x,
        Ordering::Greater => x,
    }
}

pub open spec fn spec_ord_max<T: Ord>(x: T, y: T) -> T {
    match y.cmp_spec(&x) {
        Ordering::Less => x,
        Ordering::Equal => y,
        Ordering::Greater => y,
    }
}

/// The set denoted by a half-open range.
pub open spec fn range_as_set<T: PartialOrd>(r: Range<T>) -> ISet<T> {
    ISet::new(|x: T| r.start.is_le(&x) && x.is_lt(&r.end))
}

/// The union of the sets denoted by a sequence of ranges.
pub open spec fn seq_range_union<T: PartialOrd>(s: Seq<Range<T>>) -> ISet<T>
    decreases s.len(),
{
    if s.len() == 0 {
        ISet::empty()
    } else {
        range_as_set(s[0]).union(seq_range_union(s.drop_first()))
    }
}

/// Operational spec of [`range_difference`]: the two candidate ranges,
/// dropping any empty ones, matching the executable control flow.
pub open spec fn range_difference_seq<T: Ord>(a: Range<T>, b: Range<T>) -> Seq<Range<T>> {
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

proof fn lemma_ord_laws<T: Ord>()
    requires
        vstd::laws_cmp::obeys_cmp::<T>(),
    ensures
        T::obeys_cmp_spec(),
        T::obeys_partial_cmp_spec(),
        T::obeys_eq_spec(),
        forall|x: T, y: T|
            #![trigger x.partial_cmp_spec(&y)]
            #![trigger x.cmp_spec(&y)]
            x.partial_cmp_spec(&y) == Some(x.cmp_spec(&y)),
        forall|x: T, y: T| x.partial_cmp_spec(&y) == Some(Ordering::Equal) <==> x.eq_spec(&y),
        forall|x: T, y: T|
            x.partial_cmp_spec(&y) == Some(Ordering::Less) <==> y.partial_cmp_spec(&x) == Some(
                Ordering::Greater,
            ),
        forall|x: T, y: T, z: T|
            x.partial_cmp_spec(&y) == Some(Ordering::Less) && y.partial_cmp_spec(&z) == Some(
                Ordering::Less,
            ) ==> x.partial_cmp_spec(&z) == Some(Ordering::Less),
        forall|x: T, y: T| x.eq_spec(&y) <==> y.eq_spec(&x),
        forall|x: T, y: T, z: T| x.eq_spec(&y) && y.eq_spec(&z) ==> x.eq_spec(&z),
        forall|x: T, y: T|
            #![trigger x.partial_cmp_spec(&y)]
            x.is_le(&y) <==> x.cmp_spec(&y) != Ordering::Greater,
        forall|x: T, y: T| #![trigger x.partial_cmp_spec(&y)] x.is_le(&y) <==> !y.is_lt(&x),
        forall|x: T|
            #![trigger x.cmp_spec(&x)]
            x.is_le(&x) && !x.is_lt(&x) && x.cmp_spec(&x) == Ordering::Equal,
        forall|x: T, y: T|
            #![trigger spec_ord_min(x, y)]
            (spec_ord_min(x, y) == x || spec_ord_min(x, y) == y) && spec_ord_min(x, y).is_le(&x)
                && spec_ord_min(x, y).is_le(&y),
        forall|x: T, y: T|
            #![trigger spec_ord_max(x, y)]
            (spec_ord_max(x, y) == x || spec_ord_max(x, y) == y) && x.is_le(&spec_ord_max(x, y))
                && y.is_le(&spec_ord_max(x, y)),
{
    reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
    reveal(vstd::laws_cmp::obeys_cmp_partial_ord);
    reveal(vstd::laws_cmp::obeys_cmp_ord);
    reveal(vstd::laws_eq::obeys_eq_spec_properties);
    assert forall|x: T|
        #![trigger x.cmp_spec(&x)]
        x.is_le(&x) && !x.is_lt(&x) && x.cmp_spec(&x) == Ordering::Equal by {
        if x.is_lt(&x) {
            assert(false);
        }
    }
    assert forall|x: T, y: T|
        (spec_ord_min(x, y) == x || spec_ord_min(x, y) == y) && spec_ord_min(x, y).is_le(&x)
            && spec_ord_min(x, y).is_le(&y) by {}
    assert forall|x: T, y: T|
        (spec_ord_max(x, y) == x || spec_ord_max(x, y) == y) && x.is_le(&spec_ord_max(x, y))
            && y.is_le(&spec_ord_max(x, y)) by {}
}

proof fn lemma_le_lt_trans<T: Ord>(x: T, y: T, z: T)
    requires
        vstd::laws_cmp::obeys_cmp::<T>(),
        x.is_le(&y),
        y.is_lt(&z),
    ensures
        x.is_lt(&z),
{
    lemma_ord_laws::<T>();
    if !x.is_lt(&y) && !x.is_lt(&z) {
        if x.cmp_spec(&z) == Ordering::Equal {
            assert(false);
        } else {
            assert(false);
        }
    }
}

proof fn lemma_lt_le_trans<T: Ord>(x: T, y: T, z: T)
    requires
        vstd::laws_cmp::obeys_cmp::<T>(),
        x.is_lt(&y),
        y.is_le(&z),
    ensures
        x.is_lt(&z),
{
    lemma_ord_laws::<T>();
    if !y.is_lt(&z) && !x.is_lt(&z) {
        if x.cmp_spec(&z) == Ordering::Equal {
            assert(false);
        } else {
            lemma_le_lt_trans(y, z, x);
            assert(false);
        }
    }
}

proof fn lemma_le_trans<T: Ord>(x: T, y: T, z: T)
    requires
        vstd::laws_cmp::obeys_cmp::<T>(),
        x.is_le(&y),
        y.is_le(&z),
    ensures
        x.is_le(&z),
{
    lemma_ord_laws::<T>();
    if y.is_lt(&z) {
        lemma_le_lt_trans(x, y, z);
    } else if x.is_lt(&y) {
        lemma_lt_le_trans(x, y, z);
    }
}

proof fn lemma_lt_min<T: Ord>(x: T, y: T, z: T)
    requires
        vstd::laws_cmp::obeys_cmp::<T>(),
    ensures
        x.is_lt(&spec_ord_min(y, z)) <==> x.is_lt(&y) && x.is_lt(&z),
{
    lemma_ord_laws::<T>();
    if x.is_lt(&spec_ord_min(y, z)) {
        lemma_lt_le_trans(x, spec_ord_min(y, z), y);
        lemma_lt_le_trans(x, spec_ord_min(y, z), z);
    }
}

proof fn lemma_max_le<T: Ord>(x: T, y: T, z: T)
    requires
        vstd::laws_cmp::obeys_cmp::<T>(),
    ensures
        spec_ord_max(y, z).is_le(&x) <==> y.is_le(&x) && z.is_le(&x),
{
    lemma_ord_laws::<T>();
    if spec_ord_max(y, z).is_le(&x) {
        lemma_le_trans(y, spec_ord_max(y, z), x);
        lemma_le_trans(z, spec_ord_max(y, z), x);
    }
}

proof fn lemma_empty_range_as_set<T: Ord>(r: Range<T>)
    requires
        vstd::laws_cmp::obeys_cmp::<T>(),
        !r.start.is_lt(&r.end),
    ensures
        range_as_set(r) == ISet::<T>::empty(),
{
    broadcast use vstd::iset::group_iset_lemmas;

    assert forall|x: T| #![trigger range_as_set(r).contains(x)] !range_as_set(r).contains(x) by {
        if range_as_set(r).contains(x) {
            lemma_le_lt_trans(r.start, x, r.end);
            assert(false);
        }
    }
}

proof fn lemma_seq_range_union_small<T: PartialOrd>(s: Seq<Range<T>>)
    requires
        s.len() <= 2,
    ensures
        s.len() == 0 ==> seq_range_union(s) == ISet::<T>::empty(),
        s.len() == 1 ==> seq_range_union(s) == range_as_set(s[0]),
        s.len() == 2 ==> seq_range_union(s) == range_as_set(s[0]).union(range_as_set(s[1])),
    decreases s.len(),
{
    broadcast use vstd::iset::group_iset_lemmas;

    if s.len() == 1 {
        assert(seq_range_union(s) == range_as_set(s[0]).union(seq_range_union(s.drop_first())));
        assert forall|x: T|
            #![trigger range_as_set(s[0]).contains(x)]
            range_as_set(s[0]).union(ISet::<T>::empty()).contains(x) <==> range_as_set(
                s[0],
            ).contains(x) by {}
    }
    if s.len() == 2 {
        lemma_seq_range_union_small(s.drop_first());
        assert forall|x: T|
            #![trigger range_as_set(s[0]).contains(x)]
            seq_range_union(s).contains(x) <==> range_as_set(s[0]).union(
                range_as_set(s[1]),
            ).contains(x) by {}
    }
}

proof fn lemma_range_difference_sorted<T: Ord>(a: Range<T>, b: Range<T>)
    requires
        T::obeys_cmp_spec(),
        T::obeys_partial_cmp_spec(),
        vstd::laws_cmp::obeys_cmp::<T>(),
    ensures
        forall|i: int|
            0 <= i < range_difference_seq(a, b).len() - 1 ==> (#[trigger] range_difference_seq(
                a,
                b,
            )[i]).end.is_le(&range_difference_seq(a, b)[i + 1].start),
{
    let s = range_difference_seq(a, b);
    lemma_ord_laws::<T>();
    if s.len() >= 2 {
        lemma_le_lt_trans(spec_ord_min(a.end, b.start), b.start, b.end);
        lemma_lt_le_trans(spec_ord_min(a.end, b.start), b.end, spec_ord_max(a.start, b.end));
    }
}

proof fn lemma_range_difference_set<T: Ord>(a: Range<T>, b: Range<T>)
    requires
        T::obeys_cmp_spec(),
        T::obeys_partial_cmp_spec(),
        vstd::laws_cmp::obeys_cmp::<T>(),
    ensures
        seq_range_union(range_difference_seq(a, b)) == range_as_set(a).difference(range_as_set(b)),
{
    broadcast use vstd::iset::group_iset_lemmas;

    lemma_ord_laws::<T>();
    let s = range_difference_seq(a, b);
    lemma_seq_range_union_small(s);
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
    assert forall|x: T|
        #![trigger range_as_set(a).contains(x)]
        seq_range_union(s).contains(x) <==> range_as_set(a).difference(range_as_set(b)).contains(
            x,
        ) by {
        if !b.start.is_lt(&b.end) {
            lemma_empty_range_as_set(b);
            if !left.start.is_lt(&left.end) {
                lemma_empty_range_as_set(left);
            }
        } else {
            lemma_lt_min(x, a.end, b.start);
            lemma_max_le(x, a.start, b.end);
            if !left.start.is_lt(&left.end) {
                lemma_empty_range_as_set(left);
            }
            if !right.start.is_lt(&right.end) {
                lemma_empty_range_as_set(right);
            }
        }
    }
}

} // verus!
/// Calculates the [difference] of two [`Range`]s, i.e., `a - b`.
///
/// This method will return 0, 1, or 2 ranges. All returned ranges are
/// guaranteed to be non-empty and non-overlapping. The returned ranges
/// will be sorted in ascending order.
///
/// [difference]: https://en.wikipedia.org/wiki/Set_(mathematics)#Set_difference
#[verus_verify(spinoff_prover, rlimit(200))]
#[verus_spec(ret =>
    requires
        T::obeys_cmp_spec(),
        T::obeys_partial_cmp_spec(),
        vstd::laws_cmp::obeys_cmp::<T>(),
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
        [a.start..a.end.min(b.start), a.start.max(b.end)..a.end]
    };

    proof! {
        broadcast use vstd::std_specs::iter::group_iter_axioms;
        reveal_with_fuel(Seq::filter, 3);
        assert(r@.filter(|v: Range<T>| v.start.is_lt(&v.end)) == range_difference_seq(*a, *b));
        lemma_range_difference_sorted(*a, *b);
        lemma_range_difference_set(*a, *b);
    }
    // Original execution code: `r.into_iter().filter(|v| !v.is_empty())`.
    // The local names expose the same pipeline to Verus's filter proof contract.
    let iter = r.into_iter();
    let pred = #[verus_spec(keep: bool =>
        ensures
            keep == v.start.is_lt(&v.end),
    )]
    |v: &Range<T>| !v.is_empty();
    proof! {
        assert(iter.obeys_prophetic_iter_laws());
        assert(iter.decrease() is Some);
    }
    let ret = iter.filter(pred);
    proof! {
        assert(vstd::std_specs::iter::filter_post(iter, pred, ret));
        assert forall|k: int| #![auto] 0 <= k < iter.remaining().len() implies
            call_requires(pred, (&iter.remaining()[k],)) by {}
        vstd::std_specs::iter::filter_postcondition(iter, pred, ret);
        if ret.will_return_none() {
            let keep = vstd::std_specs::iter::filter_keep(ret);
            assert(keep.len() == iter.remaining().len());
            assert forall|j: int| #![auto] 0 <= j < keep.len() implies keep[j] ==
                iter.remaining()[j].start.is_lt(&iter.remaining()[j].end) by {}
            assert(iter.remaining().take(keep.len() as int).filter_index(|j: int| keep[j]) ==
                iter.remaining().filter(|v: Range<T>| v.start.is_lt(&v.end))) by {
                reveal_with_fuel(Seq::filter_index, 3);
                reveal_with_fuel(Seq::filter, 3);
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
