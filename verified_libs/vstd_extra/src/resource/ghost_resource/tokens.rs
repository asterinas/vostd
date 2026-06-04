use crate::resource::ghost_resource::count::*;
use crate::sum::*;
use vstd::map::*;
use vstd::modes::tracked_swap;
use vstd::prelude::*;
use vstd::resource::Loc;

verus! {

broadcast use {vstd::map::group_map_axioms, vstd::set::group_set_axioms};

/// A struct that stores and dispatches `CountGhost<T>`.
/// Unlike `CountGhost`, it provides an `empty` state.
/// It also remembers the value even it is empty.
pub tracked struct CountGhostResource<T, const TOTAL: u64> {
    tracked r: Option<CountGhost<T, TOTAL>>,
    ghost snapshot: T,
    ghost id: Loc,
}

impl<T, const TOTAL: u64> CountGhostResource<T, TOTAL> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.r is Some ==> {
            &&& self.id == self.r->0.id()
            &&& self.view() == self.r->0@
        }
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
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

    /// Returns the `CountGhost<T,TOTAL>` stored in this `CountGhostResource`.
    pub closed spec fn storage(self) -> CountGhost<T, TOTAL> {
        self.r->0
    }

    /// Returns the value of type `T` stored in this `CountGhostResource`.
    pub closed spec fn view(self) -> T {
        self.snapshot
    }

    /// The fractions stored in this `CountGhostResource`.
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

    /// Create an arbitrary `CountGhostResource`. Useful as a placeholder.
    pub proof fn arbitrary() -> (tracked res: Self)
        requires
            TOTAL > 0,
    {
        Self { r: None, snapshot: arbitrary(), id: arbitrary() }
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
        let tracked r = CountGhost::new(value);
        Self { r: Some(r), snapshot: value, id: r.id() }
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
            old(self).frac() == 1 ==> final(self).is_empty(),
            final(self).wf(),
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
            old(self).frac() == n ==> final(self).is_empty(),
            final(self).wf(),
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

    /// Combines a `CountGhost`.
    pub proof fn combine(tracked &mut self, tracked other: CountGhost<T, TOTAL>)
        requires
            old(self).id() == other.id(),
            other@ == old(self)@,
        ensures
            old(self).frac() + other.frac() > TOTAL ==> false,
            old(self).frac() + other.frac() <= TOTAL ==> {
                &&& final(self).id() == old(self).id()
                &&& final(self)@ == old(self)@
                &&& final(self).frac() == old(self).frac() + other.frac()
                &&& final(self).wf()
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

    /// `CountGhostResource` satisfies the type invariant.
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
        let tracked mut r = self.r.tracked_take();
        r.update(value);
        self.snapshot = value;
        self.r = Some(r);
    }
}

pub type TokenResource<const TOTAL: u64> = CountGhostResource<(), TOTAL>;

pub type Token<const TOTAL: u64> = CountGhost<(), TOTAL>;

/// A struct that stores and dispatches `Frac<T>`.
/// Unlike `Frac`, it provides an `empty` state.
pub tracked struct CountResource<T, const TOTAL: u64> {
    tracked r: Option<Count<T, TOTAL>>,
    ghost id: Loc,
}

impl<T, const TOTAL: u64> CountResource<T, TOTAL> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& match self.r {
            Some(frac) => self.id == frac.id(),
            None => true,
        }
    }

    /// Returns the `Count<T,TOTAL>` stored in this `CountResource`.
    pub closed spec fn storage(self) -> Count<T, TOTAL> {
        self.r->0
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.type_inv()
    }

    /// Whether this `CountResource` is empty, i.e., has no fraction.
    pub open spec fn is_empty(self) -> bool {
        self.frac() == 0
    }

    /// Whether the fraction stored in this `CountResource` is less than `TOTAL`.
    pub open spec fn not_empty(self) -> bool {
        !self.is_empty()
    }

    /// Whether this `CountResource` has the full fraction, i.e., `TOTAL`.
    pub open spec fn is_full(self) -> bool {
        self.frac() == TOTAL
    }

    /// Returns the value of type `T` stored in this `CountResource`.
    pub closed spec fn resource(self) -> T {
        self.storage().resource()
    }

    /// Returns the value of type `T` stored in this `CountResource`. It is an alias of `Self::resource`.
    #[verifier::inline]
    pub open spec fn view(self) -> T {
        self.resource()
    }

    /// The fractions stored in this `CountResource`.
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

    /// Create an arbitrary `CountResource`. Useful as a placeholder.
    pub proof fn arbitrary() -> (tracked res: Self)
        requires
            TOTAL > 0,
    {
        Self { r: None, id: arbitrary() }
    }

    /// Allocates a new `CountResource` with the given tracked object.
    pub proof fn alloc(tracked value: T) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.not_empty(),
            res.is_full(),
            res@ == value,
            res.wf(),
    {
        let tracked r = Count::new(value);
        Self { r: Some(r), id: r.id() }
    }

    /// Allocates a new `CountResource` from an `EmptyCount<T,TOTAL>` with the given tracked object.
    pub proof fn alloc_from_empty(
        tracked empty: EmptyCount<T, TOTAL>,
        tracked value: T,
    ) -> (tracked res: Self)
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

    /// Splits a `Count` with fraction 1.
    pub proof fn split_one(tracked &mut self) -> (tracked res: Count<T, TOTAL>)
        requires
            old(self).not_empty(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() + 1 == old(self).frac(),
            old(self).frac() > 1 ==> final(self)@ == old(self)@,
            res.frac() == 1,
            res.id() == final(self).id(),
            res.resource() == old(self)@,
            old(self).frac() == 1 ==> final(self).is_empty(),
            final(self).wf(),
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

    /// Splits a `Count` with the given fraction.
    pub proof fn split(tracked &mut self, n: int) -> (tracked res: Count<T, TOTAL>)
        requires
            1 <= n <= old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() + n == old(self).frac(),
            old(self).frac() > n ==> final(self)@ == old(self)@,
            res.frac() == n,
            res.id() == final(self).id(),
            res.resource() == old(self)@,
            old(self).frac() == n ==> final(self).is_empty(),
            final(self).wf(),
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

    /// Combines a `Count`.
    pub proof fn combine(tracked &mut self, tracked other: Count<T, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            old(self).frac() + other.frac() > TOTAL ==> false,
            old(self).frac() + other.frac() <= TOTAL ==> {
                &&& final(self).id() == old(self).id()
                &&& final(self).resource() == other.resource()
                &&& final(self).frac() == old(self).frac() + other.frac()
                &&& final(self).wf()
                &&& old(self).frac() > 0 ==> final(self)@ == old(self)@
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

    /// `CountResource` satisfies the type invariant.
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

    pub proof fn validate_with_frac(tracked &self, tracked frac: &Count<T, TOTAL>)
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
    pub proof fn take_resource(tracked self) -> (tracked (res, empty): (T, EmptyCount<T, TOTAL>))
        requires
            self.is_full(),
        ensures
            res == self@,
            empty.id() == self.id(),
    {
        use_type_invariant(&self);
        let tracked r = self.r.tracked_unwrap();
        r.take_resource()
    }

    /// Updates the resource stored in this `CountResource` and retunrs the old resource if it exists.
    /// The fraction must be full before the update.
    pub proof fn update(tracked &mut self, tracked value: T) -> (tracked res: T)
        requires
            old(self).is_full(),
        ensures
            final(self).is_full(),
            res == old(self)@,
            final(self).id() == old(self).id(),
            final(self).wf(),
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
