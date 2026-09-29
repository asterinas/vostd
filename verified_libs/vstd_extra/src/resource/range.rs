//! Linear ownership of a contiguous finite range.
use vstd::{
    prelude::*,
    resource::{Loc, set::GhostSubset},
    set_lib::FiniteRange,
};

use crate::range::RangeExtraFns;
use core::ops::Range;

verus! {

/// A [`GhostSubset`] whose elements are exactly one half-open range.
#[verifier::reject_recursive_types(T)]
pub tracked struct GhostSubRange<T: FiniteRange> {
    subset: GhostSubset<T>,
    ghost range: Range<T>,
}

impl<T: FiniteRange> GhostSubRange<T> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        self.subset@ == self.range.view_set()
    }

    /// Wraps subset ownership known to represent exactly `range`.
    pub proof fn tracked_new(tracked subset: GhostSubset<T>, range: Range<T>) -> (tracked result:
        Self)
        requires
            subset@ =~= range.view_set(),
        ensures
            result.id() == subset.id(),
            result.range() == range,
            result@ == range.view_set(),
    {
        Self { subset, range }
    }

    /// The underlying ghost-resource location.
    pub closed spec fn id(self) -> Loc {
        self.subset.id()
    }

    /// The continuous half-open range represented by this resource.
    pub closed spec fn range(self) -> Range<T> {
        self.range
    }

    /// The set of elements owned by this resource.
    pub open spec fn view(self) -> Set<T> {
        self.range().view_set()
    }

    /// Borrows this range resource as an ordinary [`GhostSubset`].
    pub proof fn tracked_borrow(tracked &self) -> (tracked result: &GhostSubset<T>)
        ensures
            result.id() == self.id(),
            result@ == self@,
    {
        use_type_invariant(self);
        &self.subset
    }

    /// Consumes this range wrapper and returns its underlying [`GhostSubset`].
    pub proof fn tracked_into_subset(tracked self) -> (tracked result: GhostSubset<T>)
        ensures
            result.id() == self.id(),
            result@ == self@,
    {
        use_type_invariant(&self);
        self.subset
    }
}

} // verus!
