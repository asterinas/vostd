use std::borrow::Borrow;

//！ A wrapper around `vstd::tokens::FracGhost` that stores and dispatches fractional access.
use crate::sum::*;
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::tokens::frac::{Empty, Frac, FracGhost};

verus! {

/// A struct that stores and dispatches `FracGhost<T>`.
/// Unlike `FracGhost`, it provides an `empty` state.
/// It also remembers the value even it is empty.
pub tracked struct FracGhostResource<T, const TOTAL: u64> {
    tracked r: Option<FracGhost<T, TOTAL>>,
    ghost snapshot: T,
    ghost id: Loc,
}

impl<T, const TOTAL: u64> FracGhostResource<T, TOTAL> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.r is Some ==> {
            &&& self.id == self.r->Some_0.id()
            &&& self.view() == self.r->Some_0@
        }
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
    }

    /// Whether this `FracGhostResource` is empty, i.e., has no fraction.
    pub open spec fn is_empty(self) -> bool {
        self.frac() == 0
    }

    /// Whether the fraction stored in this `FracGhostResource` is less than `TOTAL`.
    pub open spec fn not_empty(self) -> bool {
        !self.is_empty()
    }

    /// Whether this `FracGhostResource` has the full fraction, i.e., `TOTAL`.
    pub open spec fn is_full(self) -> bool {
        self.frac() == TOTAL
    }

    /// Returns the `FracGhost<T,TOTAL>` stored in this `FracGhostResource`.
    pub closed spec fn storage(self) -> FracGhost<T, TOTAL> {
        self.r->Some_0
    }

    /// Returns the value of type `T` stored in this `FracGhostResource`.
    pub closed spec fn view(self) -> T {
        self.snapshot
    }

    /// The fractions stored in this `FracGhostResource`.
    pub closed spec fn frac(self) -> int {
        if self.r is None {
            0int
        } else {
            self.storage().frac()
        }
    }

    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.id
    }

    /// Create an arbitrary `FracGhostResource`. Useful as a placeholder.
    pub proof fn arbitrary() -> (tracked res: Self)
        requires
            TOTAL > 0,
    {
        Self { r: None, snapshot: arbitrary(), id: arbitrary() }
    }

    /// Allocates a new `FracGhostResource` with the full fraction and the given value.
    pub proof fn alloc(value: T) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.not_empty(),
            res.is_full(),
            res@ == value,
            res.wf(),
    {
        let tracked r = FracGhost::new(value);
        Self { r: Some(r), snapshot: value, id: r.id() }
    }

    /// Splits a `FracGhost` with fraction 1.
    pub proof fn split_one(tracked &mut self) -> (tracked res: FracGhost<T, TOTAL>)
        requires
            old(self).not_empty(),
        ensures
            self.id() == old(self).id(),
            self.frac() + 1 == old(self).frac(),
            self@ == old(self)@,
            res.frac() == 1,
            res.id() == self.id(),
            res@ == self@,
            old(self).frac() == 1 ==> self.is_empty(),
            self.wf(),
    {
        use_type_invariant(&*self);
        if self.frac() == 1 {
            self.r.tracked_take()
        } else {
            self.r.tracked_borrow().bounded();
            let tracked mut r = self.r.tracked_take();
            let tracked res = r.split(1);
            self.r = Some(r);
            res
        }
    }

    /// Splits a `FracGhost` with the given fraction.
    pub proof fn split(tracked &mut self, n: int) -> (tracked res: FracGhost<T, TOTAL>)
        requires
            1 <= n <= old(self).frac(),
        ensures
            self.id() == old(self).id(),
            self.frac() + n == old(self).frac(),
            self@ == old(self)@,
            res.frac() == n,
            res.id() == self.id(),
            res@ == self@,
            old(self).frac() == n ==> self.is_empty(),
            self.wf(),
    {
        use_type_invariant(&*self);
        self.r.tracked_borrow().bounded();
        if self.frac() == n {
            self.r.tracked_take()
        } else {
            let tracked mut r = self.r.tracked_take();
            let tracked res = r.split(n);
            self.r = Some(r);
            res
        }
    }

    /// Combines a `FracGhost`.
    pub proof fn combine(tracked &mut self, tracked other: FracGhost<T, TOTAL>)
        requires
            old(self).id() == other.id(),
            other@ == old(self)@,
        ensures
            old(self).frac() + other.frac() > TOTAL ==> false,
            old(self).frac() + other.frac() <= TOTAL ==> {
                &&& self.id() == old(self).id()
                &&& self@ == old(self)@
                &&& self.frac() == old(self).frac() + other.frac()
                &&& self.wf()
            },
    {
        if self.is_empty() {
            other.bounded();
            self.r = Some(other);
        } else {
            use_type_invariant(&*self);
            let tracked mut r = self.r.tracked_take();
            r.combine(other);
            r.bounded();
            self.r = Some(r);
        }
    }

    /// `FracGhostResource` satisfies the type invariant.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(self);
    }

    pub proof fn validate_full(tracked &self)
        requires
            self.is_full(),
        ensures
            self.not_empty(),
            self.frac() == TOTAL,
            self.wf(),
    {
        use_type_invariant(self);
        if self.is_empty() {
            assert(self.frac() == 0int);
            assert(TOTAL > 0);
            assert(false);
        }
    }

    /// Updates the value stored in this `FracGhostResource`.
    /// The fraction must be full before the update.
    pub proof fn update(tracked &mut self, value: T)
        requires
            old(self).is_full(),
        ensures
            self.is_full(),
            self@ == value,
            self.id() == old(self).id(),
            self.wf(),
    {
        use_type_invariant(&*self);
        let tracked mut r = self.r.tracked_take();
        r.update(value);
        self.snapshot = value;
        self.r = Some(r);
    }
}

pub type TokenResource<const TOTAL: u64> = FracGhostResource<(), TOTAL>;

pub type Token<const TOTAL: u64> = FracGhost<(), TOTAL>;

/// A struct that stores and dispatches `Frac<T>`.
/// Unlike `Frac`, it provides an `empty` state.
pub tracked struct FracResource<T, const TOTAL: u64> {
    tracked r: Option<Frac<T, TOTAL>>,
    ghost id: Loc,
}

impl<T, const TOTAL: u64> FracResource<T, TOTAL> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& match self.r {
            Some(frac) => self.id == frac.id(),
            None => true,
        }
    }

    /// Returns the `Frac<T,TOTAL>` stored in this `FracResource`.
    pub closed spec fn storage(self) -> Frac<T, TOTAL> {
        self.r->Some_0
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.type_inv()
    }

    /// Whether this `FracResource` is empty, i.e., has no fraction.
    pub open spec fn is_empty(self) -> bool {
        self.frac() == 0
    }

    /// Whether the fraction stored in this `FracResource` is less than `TOTAL`.
    pub open spec fn not_empty(self) -> bool {
        !self.is_empty()
    }

    /// Whether this `FracResource` has the full fraction, i.e., `TOTAL`.
    pub open spec fn is_full(self) -> bool {
        self.frac() == TOTAL
    }

    /// Returns the value of type `T` stored in this `FracResource`.
    pub closed spec fn resource(self) -> T {
        self.storage().resource()
    }

    /// Returns the value of type `T` stored in this `FracResource`. It is an alias of `Self::resource`.
    #[verifier::inline]
    pub open spec fn view(self) -> T {
        self.resource()
    }

    /// The fractions stored in this `FracResource`.
    pub closed spec fn frac(self) -> int {
        if self.r is None {
            0int
        } else {
            self.storage().frac()
        }
    }

    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.id
    }

    /// Create an arbitrary `FracResource`. Useful as a placeholder.
    pub proof fn arbitrary() -> (tracked res: Self)
        requires
            TOTAL > 0,
    {
        Self { r: None, id: arbitrary() }
    }

    /// Allocates a new `FracResource` with the given tracked object.
    pub proof fn alloc(tracked value: T) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.not_empty(),
            res.is_full(),
            res@ == value,
            res.wf(),
    {
        let tracked r = Frac::new(value);
        Self { r: Some(r), id: r.id() }
    }

    /// Allocates a new `FracResource` from an `Empty<T,TOTAL>` with the given tracked object.
    pub proof fn alloc_from_empty(tracked empty: Empty<T, TOTAL>, tracked value: T) -> (tracked res:
        Self)
        requires
            TOTAL > 0,
        ensures
            res.is_full(),
            res.id() == empty.id(),
            res.view() == value,
            res.wf(),
    {
        let tracked r = empty.put_resource(value);
        Self { r: Some(r), id: r.id() }
    }

    /// Splits a `Frac` with fraction 1.
    pub proof fn split_one(tracked &mut self) -> (tracked res: Frac<T, TOTAL>)
        requires
            old(self).not_empty(),
        ensures
            self.id() == old(self).id(),
            self.frac() + 1 == old(self).frac(),
            old(self).frac() > 1 ==> self@ == old(self)@,
            res.frac() == 1,
            res.id() == self.id(),
            res.resource() == old(self)@,
            old(self).frac() == 1 ==> self.is_empty(),
            self.wf(),
    {
        use_type_invariant(&*self);
        if self.frac() == 1 {
            self.r.tracked_take()
        } else {
            self.r.tracked_borrow().bounded();
            let tracked mut r = self.r.tracked_take();
            let tracked res = r.split(1);
            self.r = Some(r);
            res
        }
    }

    /// Splits a `Frac` with the given fraction.
    pub proof fn split(tracked &mut self, n: int) -> (tracked res: Frac<T, TOTAL>)
        requires
            1 <= n <= old(self).frac(),
        ensures
            self.id() == old(self).id(),
            self.frac() + n == old(self).frac(),
            old(self).frac() > n ==> self@ == old(self)@,
            res.frac() == n,
            res.id() == self.id(),
            res.resource() == old(self)@,
            old(self).frac() == n ==> self.is_empty(),
            self.wf(),
    {
        use_type_invariant(&*self);
        self.r.tracked_borrow().bounded();
        if self.frac() == n {
            self.r.tracked_take()
        } else {
            let tracked mut r = self.r.tracked_take();
            let tracked res = r.split(n);
            self.r = Some(r);
            res
        }
    }

    /// Combines a `Frac`.
    pub proof fn combine(tracked &mut self, tracked other: Frac<T, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            old(self).frac() + other.frac() > TOTAL ==> false,
            old(self).frac() + other.frac() <= TOTAL ==> {
                &&& self.id() == old(self).id()
                &&& self.resource() == other.resource()
                &&& self.frac() == old(self).frac() + other.frac()
                &&& self.wf()
                &&& old(self).frac() > 0 ==> self@ == old(self)@
            },
    {
        if self.is_empty() {
            other.bounded();
            self.r = Some(other);
        } else {
            use_type_invariant(&*self);
            self.validate_with_frac(&other);
            let tracked mut r = self.r.tracked_take();
            r.combine(other);
            r.bounded();
            self.r = Some(r);
        }
    }

    /// `FracResource` satisfies the type invariant.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(self);
    }

    pub proof fn validate_full(tracked &self)
        requires
            self.is_full(),
        ensures
            self.not_empty(),
            self.frac() == TOTAL,
            self.wf(),
    {
        use_type_invariant(self);
        if self.is_empty() {
            assert(self.frac() == 0int);
            assert(TOTAL > 0);
            assert(false);
        }
    }

    pub proof fn validate_with_frac(tracked &self, tracked frac: &Frac<T, TOTAL>)
        requires
            self.id() == frac.id(),
            self.frac() > 0,
        ensures
            self.resource() == frac.resource(),
    {
        use_type_invariant(self);
        frac.agree(self.r.tracked_borrow());
    }

    /// Consumes the token and takes out the resource.
    pub proof fn take_resource(tracked self) -> (tracked res: (T, Empty<T, TOTAL>))
        requires
            self.is_full(),
        ensures
            res.0 == self@,
            res.1.id() == self.id(),
    {
        use_type_invariant(&self);
        let tracked r = self.r.tracked_unwrap();
        r.take_resource()
    }

    /// Updates the resource stored in this `FracResource` and retunrs the old resource if it exists.
    /// The fraction must be full before the update.
    pub proof fn update(tracked &mut self, tracked value: T) -> (tracked res: T)
        requires
            old(self).is_full(),
        ensures
            self.is_full(),
            res == old(self)@,
            self.id() == old(self).id(),
            self.wf(),
    {
        use_type_invariant(&*self);
        let tracked mut r = self.r.tracked_take();
        let tracked (res, empty) = r.take_resource();
        let tracked r = empty.put_resource(value);
        self.r = Some(r);
        res
    }
}

} // verus!
