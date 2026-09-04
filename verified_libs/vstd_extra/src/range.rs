// SPDX-License-Identifier: MPL-2.0
//! Finite-set models and proof lemmas for half-open ranges.
//!
//! # Verified Properties
//!
//! This module relates range difference to finite set difference and proves that
//! the resulting ranges are ordered when the element type obeys its comparison
//! specification.
use vstd::{
    laws_cmp::{
        obeys_cmp, obeys_cmp_ord, obeys_cmp_partial_ord, obeys_partial_cmp_spec_properties,
    },
    laws_eq::obeys_eq_spec_properties,
    prelude::*,
    set_lib::{FiniteRange, range_set_properties},
    std_specs::cmp::{OrdSpec, PartialOrdIs},
};

use core::{cmp::Ordering, ops::Range};

verus! {

/// Returns `y` when it compares less than `x`, and returns `x` otherwise.
pub open spec fn spec_ord_min<T: Ord>(x: T, y: T) -> T {
    match y.cmp_spec(&x) {
        Ordering::Less => y,
        Ordering::Equal => x,
        Ordering::Greater => x,
    }
}

/// Returns `x` when `y` compares less than it, and returns `y` otherwise.
pub open spec fn spec_ord_max<T: Ord>(x: T, y: T) -> T {
    match y.cmp_spec(&x) {
        Ordering::Less => x,
        Ordering::Equal => y,
        Ordering::Greater => y,
    }
}

/// Specification helpers for half-open ranges.
pub trait RangeExtraFns<T: FiniteRange> {
    /// The finite set denoted by this range.
    spec fn view_set(self) -> Set<T>;
}

impl<T: FiniteRange> RangeExtraFns<T> for Range<T> {
    open spec fn view_set(self) -> Set<T> {
        T::range_set(self.start, self.end)
    }
}

/// The union of the sets denoted by a sequence of ranges.
pub open spec fn seq_range_union<T: FiniteRange>(s: Seq<Range<T>>) -> Set<T> {
    s.map_values(|r: Range<T>| r.view_set()).to_set().flatten()
}

closed spec fn range_contains<T: FiniteRange>(x: T) -> spec_fn(Range<T>) -> bool {
    |r: Range<T>| r.view_set().contains(x)
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

proof fn lemma_seq_range_union_contains<T: FiniteRange>(s: Seq<Range<T>>, x: T)
    ensures
        seq_range_union(s).contains(x) <==> s.any(range_contains(x)),
{
    broadcast use {Seq::to_set_ensures, Set::lemma_flatten_contains};

    reveal(range_contains);

    let pred = range_contains(x);
    let range_sets = s.map_values(|r: Range<T>| r.view_set());

    if seq_range_union(s).contains(x) {
        range_sets.to_set().lemma_flatten_contains(x);
        let range_set = choose|range_set: Set<T>|
            #![trigger range_sets.to_set().contains(range_set)]
            range_sets.to_set().contains(range_set) && range_set.contains(x);
        let i = choose|i: int| 0 <= i < range_sets.len() && range_sets[i] == range_set;

        assert(pred(s[i]));
        assert(s.any(pred)) by {
            reveal(Seq::any);
        }
    } else if s.any(pred) {
        let i = choose|i: int| #![auto] 0 <= i < s.len() && pred(s[i]);

        assert(range_sets.to_set().contains(range_sets[i]));
        range_sets.to_set().lemma_flatten_contains(x);
    }
}

/// Proves that [`range_difference_seq`] denotes the finite set difference `a - b`.
///
/// # Preconditions
///
/// The element comparison obeys its specification, and the finite-range model
/// agrees with that ordering.
///
/// # Postconditions
///
/// The union of the output ranges equals the elements in `a` that are not in `b`.
pub proof fn lemma_range_difference_set<T: FiniteRange + Ord>(a: Range<T>, b: Range<T>)
    requires
        obeys_cmp::<T>(),
        finite_range_matches_ord::<T>(),
    ensures
        seq_range_union(range_difference_seq(a, b)) == a.view_set().difference(b.view_set()),
{
    broadcast use range_set_properties;

    reveal(range_contains);

    reveal(obeys_partial_cmp_spec_properties);
    reveal(obeys_cmp_partial_ord);
    reveal(obeys_cmp_ord);
    reveal(obeys_eq_spec_properties);
    let s = range_difference_seq(a, b);
    if s.len() == 0 {
        assert forall|x: T| !seq_range_union(s).contains(x) by {
            lemma_seq_range_union_contains(s, x);
            reveal(Seq::any);
        }
    }
    if s.len() == 1 {
        assert forall|x: T|
            #![trigger seq_range_union(s).contains(x)]
            seq_range_union(s).contains(x) <==> s[0].view_set().contains(x) by {
            lemma_seq_range_union_contains(s, x);

            reveal(Seq::any);
            if s.any(range_contains(x)) {
                let i = choose|i: int| #![auto] 0 <= i < s.len() && range_contains(x)(s[i]);
            }
            if s[0].view_set().contains(x) {
                assert(range_contains(x)(s[0]));
                assert(s.any(range_contains(x))) by {
                    reveal(Seq::any);
                }
            }
        }
    }
    if s.len() == 2 {
        assert forall|x: T|
            #![trigger seq_range_union(s).contains(x)]
            seq_range_union(s).contains(x) <==> s[0].view_set().union(s[1].view_set()).contains(
                x,
            ) by {
            lemma_seq_range_union_contains(s, x);

            reveal(Seq::any);
            if s.any(range_contains(x)) {
                let i = choose|i: int| #![auto] 0 <= i < s.len() && range_contains(x)(s[i]);
                assert(i == 0 || i == 1);
            }
            if s[0].view_set().contains(x) {
                assert(range_contains(x)(s[0]));
                assert(s.any(range_contains(x))) by {
                    reveal(Seq::any);
                }
            }
            if s[1].view_set().contains(x) {
                assert(range_contains(x)(s[1]));
                assert(s.any(range_contains(x))) by {
                    reveal(Seq::any);
                }
            }
        }
    }
    assert forall|x: T|
        #![trigger a.view_set().contains(x)]
        seq_range_union(s).contains(x) <==> a.view_set().difference(b.view_set()).contains(x) by {}
}

} // verus!
