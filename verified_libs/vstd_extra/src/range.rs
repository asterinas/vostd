// SPDX-License-Identifier: MPL-2.0
//! Finite-set models and proof lemmas for half-open ranges.
use vstd::{
    laws_cmp::{
        obeys_cmp, obeys_cmp_ord, obeys_cmp_partial_ord, obeys_partial_cmp_spec_properties,
    },
    laws_eq::{obeys_concrete_eq, obeys_eq_spec_properties},
    prelude::*,
    set_lib::{FiniteRange, range_set_properties},
    std_specs::cmp::PartialOrdIs,
};

use crate::set_extra::pairwise_disjoint;

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

/// An element belongs to the union of a sequence of ranges if and only if it
/// belongs to at least one of those ranges.
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

/// Pairwise-disjoint half-open ranges, with endpoint separation also required
/// for duplicate or empty ranges whose positions the set model would discard.
pub open spec fn ranges_disjoint<T: FiniteRange + Ord>(ranges: Seq<Range<T>>) -> bool {
    &&& pairwise_disjoint(
        ranges.map_values(|range: Range<T>| range.view_set()).to_set(),
    )
    // A set collapses duplicate ranges and omits empty ranges' positions. Preserve the
    // per-position endpoint separation for these cases.
    &&& forall|i: int, j: int|
        #![trigger ranges[i], ranges[j]]
        0 <= i < j < ranges.len() && (ranges[i] == ranges[j] || ranges[i].start.is_ge(
            &ranges[i].end,
        ) || ranges[j].start.is_ge(&ranges[j].end)) ==> ranges[i].end.is_le(&ranges[j].start)
            || ranges[j].end.is_le(&ranges[i].start)
}

/// Endpoint separation for distinct range positions, including empty ranges.
pub open spec fn ranges_separated<T: FiniteRange + Ord>(ranges: Seq<Range<T>>) -> bool {
    forall|i: int, j: int|
        #![trigger ranges[i], ranges[j]]
        0 <= i < j < ranges.len() ==> ranges[i].end.is_le(&ranges[j].start) || ranges[j].end.is_le(
            &ranges[i].start,
        )
}

/// Relates set-based disjointness to endpoint separation when the range and ordering models agree.
pub proof fn lemma_ranges_disjoint<T: FiniteRange + Ord>(ranges: Seq<Range<T>>)
    requires
        obeys_cmp::<T>(),
        obeys_concrete_eq::<T>(),
        finite_range_matches_ord::<T>(),
    ensures
        ranges_disjoint(ranges) == ranges_separated(ranges),
{
    broadcast use range_set_properties;

    reveal(obeys_partial_cmp_spec_properties);
    reveal(obeys_cmp_partial_ord);
    reveal(obeys_cmp_ord);
    reveal(obeys_eq_spec_properties);
    reveal(obeys_concrete_eq);
    let sets = ranges.map_values(|r: Range<T>| r.view_set());
    if ranges_disjoint(ranges) {
        assert forall|i: int, j: int|
            #![trigger ranges[i], ranges[j]]
            0 <= i < j < ranges.len() implies ranges[i].end.is_le(&ranges[j].start)
            || ranges[j].end.is_le(&ranges[i].start) by {
            assert(sets.to_set().contains(sets[i]));
            assert(sets.to_set().contains(sets[j]));
            if ranges[i] != ranges[j] && ranges[i].start.is_lt(&ranges[i].end)
                && ranges[j].start.is_lt(&ranges[j].end) {
                assert(sets[i] != sets[j]) by {
                    if ranges[i].start.is_lt(&ranges[j].start) {
                        assert(sets[i].contains(ranges[i].start));
                    } else if ranges[j].start.is_lt(&ranges[i].start) {
                        assert(sets[j].contains(ranges[j].start));
                    } else if ranges[i].end.is_lt(&ranges[j].end) {
                        assert(sets[j].contains(ranges[i].end));
                    } else {
                        assert(sets[i].contains(ranges[j].end));
                    }
                }
                assert(sets[i].disjoint(sets[j]));
                if ranges[i].start.is_lt(&ranges[j].end) && ranges[j].start.is_lt(&ranges[i].end) {
                    let address = if ranges[i].start.is_lt(&ranges[j].start) {
                        ranges[j].start
                    } else {
                        ranges[i].start
                    };
                    assert(sets[i].contains(address) && sets[j].contains(address));
                }
            }
        }
    } else if ranges_separated(ranges) {
        assert forall|left: Set<T>, right: Set<T>|
            #![trigger sets.to_set().contains(left), sets.to_set().contains(right)]
            sets.to_set().contains(left) && sets.to_set().contains(right) && left
                != right implies left.disjoint(right) by {
            let i = choose|i: int| 0 <= i < sets.len() && sets[i] == left;
            let j = choose|j: int| 0 <= j < sets.len() && sets[j] == right;
            assert(i != j);
            assert(ranges[i].end.is_le(&ranges[j].start) || ranges[j].end.is_le(&ranges[i].start));
            assert forall|address: T| #[trigger] left.contains(address) implies !right.contains(
                address,
            ) by {}
        }
    }
}

} // verus!
