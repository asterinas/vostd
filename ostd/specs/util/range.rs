// SPDX-License-Identifier: MPL-2.0
use vstd::{
    iset::ISet,
    laws_cmp::{
        obeys_cmp, obeys_cmp_ord, obeys_cmp_partial_ord, obeys_partial_cmp_spec_properties,
    },
    laws_eq::obeys_eq_spec_properties,
    prelude::*,
    std_specs::{
        cmp::{OrdSpec, PartialEqSpec, PartialOrdIs, PartialOrdSpec},
        range::ContainsSpec,
    },
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

/// The set denoted by a half-open range.
pub open spec fn range_as_set<T: PartialOrd>(r: Range<T>) -> ISet<T> {
    ISet::new(|x: T| r.contains_spec(&x))
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
        forall|x: T, y: T| #![trigger x.partial_cmp_spec(&y)] x.is_le(&y) <==> !y.is_lt(&x),
        forall|x: T|
            #![trigger x.cmp_spec(&x)]
            x.is_le(&x) && !x.is_lt(&x) && x.cmp_spec(&x) == Ordering::Equal,
{
    reveal(obeys_partial_cmp_spec_properties);
    reveal(obeys_cmp_partial_ord);
    reveal(obeys_cmp_ord);
    reveal(obeys_eq_spec_properties);
    assert forall|x: T|
        #![trigger x.cmp_spec(&x)]
        x.is_le(&x) && !x.is_lt(&x) && x.cmp_spec(&x) == Ordering::Equal by {
        if x.is_lt(&x) {
            assert(false);
        }
    }
}

proof fn lemma_ord_min_laws<T: Ord>()
    requires
        obeys_cmp::<T>(),
    ensures
        forall|x: T, y: T|
            #![trigger spec_ord_min(x, y)]
            (spec_ord_min(x, y) == x || spec_ord_min(x, y) == y) && spec_ord_min(x, y).is_le(&x)
                && spec_ord_min(x, y).is_le(&y),
{
    lemma_ord_base_laws::<T>();
    assert forall|x: T, y: T|
        (spec_ord_min(x, y) == x || spec_ord_min(x, y) == y) && spec_ord_min(x, y).is_le(&x)
            && spec_ord_min(x, y).is_le(&y) by {}
}

proof fn lemma_ord_max_laws<T: Ord>()
    requires
        obeys_cmp::<T>(),
    ensures
        forall|x: T, y: T|
            #![trigger spec_ord_max(x, y)]
            (spec_ord_max(x, y) == x || spec_ord_max(x, y) == y) && x.is_le(&spec_ord_max(x, y))
                && y.is_le(&spec_ord_max(x, y)),
{
    lemma_ord_base_laws::<T>();
    assert forall|x: T, y: T|
        (spec_ord_max(x, y) == x || spec_ord_max(x, y) == y) && x.is_le(&spec_ord_max(x, y))
            && y.is_le(&spec_ord_max(x, y)) by {}
}

proof fn lemma_le_lt_trans<T: Ord>(x: T, y: T, z: T)
    requires
        obeys_cmp::<T>(),
        x.is_le(&y),
        y.is_lt(&z),
    ensures
        x.is_lt(&z),
{
    lemma_ord_base_laws::<T>();
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
        obeys_cmp::<T>(),
        x.is_lt(&y),
        y.is_le(&z),
    ensures
        x.is_lt(&z),
{
    lemma_ord_base_laws::<T>();
    if !y.is_lt(&z) && !x.is_lt(&z) {
        if x.cmp_spec(&z) == Ordering::Equal {
            assert(false);
        } else {
            assert(false);
        }
    }
}

proof fn lemma_le_trans<T: Ord>(x: T, y: T, z: T)
    requires
        obeys_cmp::<T>(),
        x.is_le(&y),
        y.is_le(&z),
    ensures
        x.is_le(&z),
{
    lemma_ord_base_laws::<T>();
}

proof fn lemma_lt_min<T: Ord>(x: T, y: T, z: T)
    requires
        obeys_cmp::<T>(),
    ensures
        x.is_lt(&spec_ord_min(y, z)) <==> x.is_lt(&y) && x.is_lt(&z),
{
    lemma_ord_base_laws::<T>();
    lemma_ord_min_laws::<T>();
}

proof fn lemma_max_le<T: Ord>(x: T, y: T, z: T)
    requires
        obeys_cmp::<T>(),
    ensures
        spec_ord_max(y, z).is_le(&x) <==> y.is_le(&x) && z.is_le(&x),
{
    lemma_ord_base_laws::<T>();
    lemma_ord_max_laws::<T>();
}

proof fn lemma_empty_range_as_set<T: Ord>(r: Range<T>)
    requires
        obeys_cmp::<T>(),
        !r.start.is_lt(&r.end),
    ensures
        range_as_set(r) == ISet::<T>::empty(),
{
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

pub(crate) proof fn lemma_range_difference_sorted<T: Ord>(a: Range<T>, b: Range<T>)
    requires
        T::obeys_cmp_spec(),
        T::obeys_partial_cmp_spec(),
        obeys_cmp::<T>(),
    ensures
        forall|i: int|
            0 <= i < range_difference_seq(a, b).len() - 1 ==> (#[trigger] range_difference_seq(
                a,
                b,
            )[i]).end.is_le(&range_difference_seq(a, b)[i + 1].start),
{
    lemma_ord_base_laws::<T>();
}

pub(crate) proof fn lemma_range_difference_set<T: Ord>(a: Range<T>, b: Range<T>)
    requires
        T::obeys_cmp_spec(),
        T::obeys_partial_cmp_spec(),
        obeys_cmp::<T>(),
    ensures
        seq_range_union(range_difference_seq(a, b)) == range_as_set(a).difference(range_as_set(b)),
{
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
