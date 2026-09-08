// SPDX-License-Identifier: MPL-2.0
//! Finite-set models and proof lemmas for half-open ranges.
use vstd::{prelude::*, set_lib::FiniteRange, std_specs::cmp::PartialOrdIs};

use core::ops::Range;

verus! {

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

/// Whether the finite-range model agrees with the ordering model.
pub open spec fn finite_range_matches_ord<T: FiniteRange + Ord>() -> bool {
    forall|x: T, lo: T, hi: T| T::in_range(x, lo, hi) <==> lo.is_le(&x) && x.is_lt(&hi)
}

/// Relates membership in a union of ranges to membership in one of its ranges.
///
/// # Preconditions
///
/// No additional preconditions are required.
///
/// # Postconditions
///
/// An element belongs to the union if and only if it belongs to at least one
/// range in the sequence.
pub proof fn lemma_seq_range_union_contains<T: FiniteRange>(s: Seq<Range<T>>, x: T)
    ensures
        seq_range_union(s).contains(x) <==> s.any(|r: Range<T>| r.view_set().contains(x)),
{
    broadcast use {Seq::to_set_ensures, Set::lemma_flatten_contains};

    let pred = |r: Range<T>| r.view_set().contains(x);
    let range_sets = s.map_values(|r: Range<T>| r.view_set());

    if seq_range_union(s).contains(x) {
        range_sets.to_set().lemma_flatten_contains(x);
        let range_set = choose|range_set: Set<T>|
            #![trigger range_sets.to_set().contains(range_set)]
            range_sets.to_set().contains(range_set) && range_set.contains(x);
        let i = choose|i: int| 0 <= i < range_sets.len() && range_sets[i] == range_set;

        assert(pred(s[i]));
        assert(s.any(pred));
    } else if s.any(pred) {
        let i = choose|i: int| #![auto] 0 <= i < s.len() && pred(s[i]);

        assert(range_sets.to_set().contains(range_sets[i]));
        range_sets.to_set().lemma_flatten_contains(x);
    }
}

} // verus!
