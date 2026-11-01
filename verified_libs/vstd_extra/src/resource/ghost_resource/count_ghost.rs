//! Integer-based counting ghost resources with authority.
use crate::sum::*;
use vstd::map::*;
use vstd::modes::tracked_swap;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::{PCM, Resource};

verus! {

/// A PCM that tracks a resource value, its fraction, and **the authority**.
ghost enum FractionalCarrier<T, const TOTAL: usize> {
    Value { v: T, n: int, auth: bool },
    Empty,
    Invalid,
}

impl<T, const TOTAL: usize> FractionalCarrier<T, TOTAL> {
    spec fn new(v: T) -> Self {
        FractionalCarrier::Value { v, n: TOTAL as int, auth: true }
    }
}

impl<T, const TOTAL: usize> ResourceAlgebra for FractionalCarrier<T, TOTAL> {
    closed spec fn valid(self) -> bool {
        match self {
            FractionalCarrier::Invalid => false,
            FractionalCarrier::Empty => true,
            FractionalCarrier::Value { v: _, n, auth } => (0 < n <= TOTAL) || (n == 0 && auth),
        }
    }

    closed spec fn op(a: Self, b: Self) -> Self {
        match a {
            FractionalCarrier::Invalid => FractionalCarrier::Invalid,
            FractionalCarrier::Empty => b,
            FractionalCarrier::Value { v: sv, n: sn, auth: sa } => match b {
                FractionalCarrier::Invalid => FractionalCarrier::Invalid,
                FractionalCarrier::Empty => a,
                FractionalCarrier::Value { v: ov, n: on, auth: oa } => {
                    if sv != ov {
                        FractionalCarrier::Invalid
                    } else if sa && oa {
                        FractionalCarrier::Invalid
                    } else if sn < 0 || on < 0 || (!sa && sn == 0) || (!oa && on == 0) {
                        FractionalCarrier::Invalid
                    } else {
                        FractionalCarrier::Value { v: sv, n: sn + on, auth: sa || oa }
                    }
                },
            },
        }
    }

    proof fn valid_op(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }
}

impl<T, const TOTAL: usize> PCM for FractionalCarrier<T, TOTAL> {
    closed spec fn unit() -> Self {
        FractionalCarrier::Empty
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

pub tracked struct CountGhost<T, const TOTAL: usize = 2> {
    r: Resource<FractionalCarrier<T, TOTAL>>,
}

impl<T, const TOTAL: usize> CountGhost<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value() is Value
        &&& self.r.value()->n > 0
    }

    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Returns the stored resource value.
    pub closed spec fn view(self) -> T {
        self.r.value()->v
    }

    /// Returns the fraction of the resource.
    pub closed spec fn frac(self) -> int {
        self.r.value()->n
    }

    /// Whether this token carries the authority for updating the resource value.
    pub closed spec fn has_authority(self) -> bool {
        self.r.value()->auth
    }

    pub open spec fn valid(self, id: Loc, frac: int) -> bool {
        &&& self.id() == id
        &&& self.frac() == frac
    }

    /// Allocates a new `CountGhost` with the full fraction, the given value, and the authority.
    pub proof fn alloc(v: T) -> (tracked result: Self)
        requires
            TOTAL > 0,
        ensures
            result.frac() == TOTAL,
            result@ == v,
            result.has_authority(),
    {
        let f = FractionalCarrier::<T, TOTAL>::new(v);
        let tracked r = Resource::alloc(f);
        Self { r }
    }

    /// Two `CountGhost`s with the same id must have the same resource value.
    pub proof fn agree(tracked self: &Self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self@ == other@,
    {
        use_type_invariant(self);
        use_type_invariant(other);
        let tracked joined = self.r.join_shared(&other.r);
        joined.validate()
    }

    /// Splits another fraction `n` from this `CountGhost`, returning a new `CountGhost` with
    /// that fraction.
    pub proof fn split(tracked &mut self, n: int) -> (tracked result: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            result.id() == final(self).id(),
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            result@ == old(self)@,
            final(self).frac() + result.frac() == old(self).frac(),
            result.frac() == n,
            !result.has_authority(),
            final(self).has_authority() == old(self).has_authority(),
    {
        self.bounded();
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        use_type_invariant(&mself);
        let tracked (r1, r2) = mself.r.split(
            FractionalCarrier::Value {
                v: mself.r.value()->v,
                n: mself.r.value()->n - n,
                auth: mself.r.value()->auth,
            },
            FractionalCarrier::Value { v: mself.r.value()->v, n, auth: false },
        );
        self.r = r1;
        Self { r: r2 }
    }

    /// Combines a `CountGhost`.
    pub proof fn combine(tracked &mut self, tracked other: Self)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self)@ == other@,
            final(self).frac() == old(self).frac() + other.frac(),
            final(self).has_authority() == (old(self).has_authority() || other.has_authority()),
    {
        self.bounded();
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        use_type_invariant(&mself);
        use_type_invariant(&other);
        let tracked mut r = mself.r;
        r.validate_2(&other.r);
        *self = Self { r: r.join(other.r) };
    }

    /// Updates the value stored in this `CountGhost`.
    /// The token must be the authority and hold the full fraction.
    pub proof fn update(tracked &mut self, v: T)
        requires
            old(self).has_authority(),
            old(self).frac() == TOTAL,
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == v,
            final(self).frac() == old(self).frac(),
            final(self).has_authority(),
    {
        self.bounded();
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        use_type_invariant(&mself);
        let tracked r = mself.r;
        let f = FractionalCarrier::<T, TOTAL>::Value { v, n: TOTAL as int, auth: true };
        *self = Self { r: r.update(f) };
    }

    /// Updates the value stored in both `CountGhost`s.
    pub proof fn update_with(tracked &mut self, tracked other: &mut Self, v: T)
        requires
            old(self).id() == old(other).id(),
            old(self).frac() + old(other).frac() == TOTAL,
            old(self).has_authority() || old(other).has_authority(),
        ensures
            final(self).id() == old(self).id(),
            final(other).id() == old(other).id(),
            final(self).frac() == old(self).frac(),
            final(other).frac() == old(other).frac(),
            old(self)@ == old(other)@,
            final(self)@ == v,
            final(other)@ == v,
    {
        let ghost other_frac = other.frac();
        other.bounded();
        let tracked mut xother = Self::dummy();
        tracked_swap(other, &mut xother);
        self.bounded();
        self.combine(xother);
        self.update(v);
        let tracked mut xother = self.split(other_frac);
        tracked_swap(other, &mut xother);
    }

    /// The fraction of the resource must be positive and at most `TOTAL`.
    pub proof fn bounded(tracked &self)
        ensures
            0 < self.frac() <= TOTAL,
    {
        use_type_invariant(self);
        self.r.validate()
    }

    pub proof fn dummy() -> (tracked result: Self)
        requires
            TOTAL > 0,
    {
        Self::alloc(arbitrary())
    }
}

/// A struct that stores and dispatches `CountGhost<T>`.
/// Unlike `CountGhost`, it provides an `empty` state: after all fractions have been split out,
/// it still remembers the resource value inside the carrier, mirroring `CountResource`.
pub tracked struct CountGhostResource<T, const TOTAL: usize> {
    tracked r: Resource<FractionalCarrier<T, TOTAL>>,
}

impl<T, const TOTAL: usize> CountGhostResource<T, TOTAL> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.r.value() matches FractionalCarrier::Value { auth: true, .. }
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.type_inv()
    }

    /// Whether this `CountGhostResource` is empty, i.e., has no fraction.
    pub open spec fn is_empty(self) -> bool {
        self.frac() == 0
    }

    /// Whether the fraction stored in this `CountGhostResource` is less than `TOTAL`.
    pub open spec fn not_empty(self) -> bool {
        !self.is_empty()
    }

    /// Whether this `CountGhostResource` has the full fraction, i.e., `TOTAL`.
    pub open spec fn is_full(self) -> bool {
        self.frac() == TOTAL
    }

    /// Returns the value of type `T` stored in this `CountGhostResource`.
    pub closed spec fn view(self) -> T {
        self.r.value()->v
    }

    /// The fractions stored in this `CountGhostResource`.
    pub closed spec fn frac(self) -> int {
        self.r.value()->n
    }

    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Create an arbitrary `CountGhostResource`. Useful as a placeholder.
    pub proof fn arbitrary() -> (tracked res: Self)
        requires
            TOTAL > 0,
    {
        let f = FractionalCarrier::<T, TOTAL>::Value { v: arbitrary(), n: 0, auth: true };
        let tracked r = Resource::alloc(f);
        Self { r }
    }

    /// Allocates a new `CountGhostResource` with the full fraction and the given value.
    pub proof fn alloc(value: T) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.not_empty(),
            res.is_full(),
            res@ == value,
            res.wf(),
    {
        let f = FractionalCarrier::<T, TOTAL>::Value { v: value, n: TOTAL as int, auth: true };
        let tracked r = Resource::alloc(f);
        Self { r }
    }

    /// Splits a `CountGhost` with fraction 1.
    pub proof fn split_one(tracked &mut self) -> (tracked res: CountGhost<T, TOTAL>)
        requires
            old(self).not_empty(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() + 1 == old(self).frac(),
            final(self)@ == old(self)@,
            res.frac() == 1,
            res.id() == final(self).id(),
            res@ == final(self)@,
            !res.has_authority(),
            old(self).frac() == 1 ==> final(self).is_empty(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        self.split(1)
    }

    /// Splits a `CountGhost` with the given fraction.
    pub proof fn split(tracked &mut self, n: int) -> (tracked res: CountGhost<T, TOTAL>)
        requires
            1 <= n <= old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() + n == old(self).frac(),
            final(self)@ == old(self)@,
            res.frac() == n,
            res.id() == final(self).id(),
            res@ == final(self)@,
            !res.has_authority(),
            old(self).frac() == n ==> final(self).is_empty(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        self.r.validate();
        let tracked mut dummy = Self::arbitrary();
        tracked_swap(self, &mut dummy);
        let tracked Self { r } = dummy;
        let p1 = FractionalCarrier::Value { v: r.value()->v, n: r.value()->n - n, auth: true };
        let p2 = FractionalCarrier::Value { v: r.value()->v, n, auth: false };
        let tracked (authority, fraction) = r.split(p1, p2);
        self.r = authority;
        CountGhost { r: fraction }
    }

    /// Combines a `CountGhost`.
    pub proof fn combine(tracked &mut self, tracked other: CountGhost<T, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            old(self).frac() + other.frac() > TOTAL ==> false,
            old(self).frac() + other.frac() <= TOTAL ==> {
                &&& final(self).id() == old(self).id()
                &&& final(self)@ == old(self)@
                &&& final(self)@ == other@
                &&& final(self).frac() == old(self).frac() + other.frac()
                &&& final(self).wf()
            },
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        let tracked mut dummy = Self::arbitrary();
        tracked_swap(self, &mut dummy);
        let tracked Self { r } = dummy;
        let tracked mut r1 = r;
        r1.validate_2(&other.r);
        self.r = r1.join(other.r);
        self.r.validate();
    }

    /// `CountGhostResource` satisfies the type invariant.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(self);
    }

    /// A `CountGhostResource` and a `CountGhost` with the same id agree on the value.
    ///
    /// Unlike `CountGhost::agree`, this works even when the resource is empty (all fractions split out).
    pub proof fn validate_with_frac(tracked &self, tracked frac: &CountGhost<T, TOTAL>)
        requires
            self.id() == frac.id(),
        ensures
            self@ == frac@,
    {
        use_type_invariant(self);
        use_type_invariant(frac);
        let tracked joined = self.r.join_shared(&frac.r);
        joined.validate();
    }

    /// Updates the value stored in this `CountGhostResource`.
    /// The fraction must be full before the update.
    pub proof fn update(tracked &mut self, value: T)
        requires
            old(self).is_full(),
        ensures
            final(self).is_full(),
            final(self)@ == value,
            final(self).id() == old(self).id(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked mut dummy = Self::arbitrary();
        tracked_swap(self, &mut dummy);
        let tracked Self { r } = dummy;
        let f = FractionalCarrier::<T, TOTAL>::Value { v: value, n: TOTAL as int, auth: true };
        self.r = r.update(f);
    }
}

pub type TokenResource<const TOTAL: usize> = CountGhostResource<(), TOTAL>;

pub type Token<const TOTAL: usize> = CountGhost<(), TOTAL>;

} // verus!
