// SPDX-License-Identifier: MPL-2.0
use vstd::{
    laws_cmp::{
        obeys_cmp, obeys_cmp_ord, obeys_cmp_partial_ord, obeys_partial_cmp_spec_properties,
    },
    laws_eq::obeys_eq_spec_properties,
    prelude::*,
    set_lib::{FiniteRange, range_set_properties},
    std_specs::cmp::{OrdSpec, PartialEqSpec, PartialOrdIs, PartialOrdSpec},
};

use core::{cmp::Ordering, ops::Range};

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

/// The finite set denoted by a half-open range.
pub open spec fn range_as_set<T: FiniteRange>(r: Range<T>) -> Set<T> {
    T::range_set(r.start, r.end)
}

/// The union of the sets denoted by a sequence of ranges.
pub open spec fn seq_range_union<T: FiniteRange>(s: Seq<Range<T>>) -> Set<T> {
    s.map_values(|r: Range<T>| range_as_set(r)).to_set().flatten()
}

/// Whether the finite-range model agrees with the ordering model.
pub open spec fn finite_range_matches_ord<T: FiniteRange + Ord>() -> bool {
    forall|x: T, lo: T, hi: T| T::in_range(x, lo, hi) <==> lo.is_le(&x) && x.is_lt(&hi)
}

/// Operational spec of `range_difference`: the two candidate ranges,
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

proof fn lemma_ord_base_laws<T: Ord>()
    requires
        obeys_cmp::<T>(),
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
{
    reveal(obeys_partial_cmp_spec_properties);
    reveal(obeys_cmp_partial_ord);
    reveal(obeys_cmp_ord);
    reveal(obeys_eq_spec_properties);
}

proof fn lemma_seq_range_union_contains<T: FiniteRange>(s: Seq<Range<T>>, x: T)
    ensures
        seq_range_union(s).contains(x) <==> exists|i: int|
            #![trigger range_as_set(s[i]).contains(x)]
            0 <= i < s.len() && range_as_set(s[i]).contains(x),
{
    broadcast use {Seq::to_set_ensures, Set::lemma_flatten_contains};

    let range_sets = s.map_values(|r: Range<T>| range_as_set(r));
    if seq_range_union(s).contains(x) {
        range_sets.to_set().lemma_flatten_contains(x);
        let range_set = choose|range_set: Set<T>|
            #![trigger range_sets.to_set().contains(range_set)]
            range_sets.to_set().contains(range_set) && range_set.contains(x);
        let i = choose|i: int| 0 <= i < range_sets.len() && range_sets[i] == range_set;
    } else if exists|i: int|
        #![trigger range_as_set(s[i]).contains(x)]
        0 <= i < s.len() && range_as_set(s[i]).contains(x) {
        let i = choose|i: int|
            #![trigger range_as_set(s[i]).contains(x)]
            0 <= i < s.len() && range_as_set(s[i]).contains(x);
        assert(range_sets.to_set().contains(range_sets[i]));
        range_sets.to_set().lemma_flatten_contains(x);
    }
}

proof fn lemma_seq_range_union_small<T: FiniteRange>(s: Seq<Range<T>>)
    requires
        s.len() <= 2,
    ensures
        s.len() == 0 ==> seq_range_union(s) == Set::<T>::empty(),
        s.len() == 1 ==> seq_range_union(s) == range_as_set(s[0]),
        s.len() == 2 ==> seq_range_union(s) == range_as_set(s[0]).union(range_as_set(s[1])),
{
    if s.len() == 0 {
        assert forall|x: T| !seq_range_union(s).contains(x) by {
            lemma_seq_range_union_contains(s, x);
        }
    }
    if s.len() == 1 {
        assert forall|x: T|
            #![trigger seq_range_union(s).contains(x)]
            seq_range_union(s).contains(x) <==> range_as_set(s[0]).contains(x) by {
            lemma_seq_range_union_contains(s, x);
        }
    }
    if s.len() == 2 {
        assert forall|x: T|
            #![trigger seq_range_union(s).contains(x)]
            seq_range_union(s).contains(x) <==> range_as_set(s[0]).union(
                range_as_set(s[1]),
            ).contains(x) by {
            lemma_seq_range_union_contains(s, x);
        }
    }
}

pub proof fn lemma_range_difference_sorted_at<T: Ord>(a: Range<T>, b: Range<T>, i: int)
    requires
        T::obeys_cmp_spec(),
        T::obeys_partial_cmp_spec(),
        obeys_cmp::<T>(),
        0 <= i < range_difference_seq(a, b).len() - 1,
    ensures
        range_difference_seq(a, b)[i].end.is_le(&range_difference_seq(a, b)[i + 1].start),
{
    lemma_ord_base_laws::<T>();
}

pub proof fn lemma_range_difference_set<T: FiniteRange + Ord>(a: Range<T>, b: Range<T>)
    requires
        T::obeys_cmp_spec(),
        T::obeys_partial_cmp_spec(),
        obeys_cmp::<T>(),
        finite_range_matches_ord::<T>(),
    ensures
        seq_range_union(range_difference_seq(a, b)) == range_as_set(a).difference(range_as_set(b)),
{
    broadcast use range_set_properties;

    lemma_ord_base_laws::<T>();
    let s = range_difference_seq(a, b);
    lemma_seq_range_union_small(s);
    assert forall|x: T|
        #![trigger range_as_set(a).contains(x)]
        seq_range_union(s).contains(x) <==> range_as_set(a).difference(range_as_set(b)).contains(
            x,
        ) by {}
}

} // verus!
