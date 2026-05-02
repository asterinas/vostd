use std::borrow::Borrow;

//！ A wrapper around `vstd::tokens::FracGhost` that stores and dispatches fractional access.
use crate::sum::*;
use vstd::map::*;
use vstd::modes::tracked_swap;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::{Resource, PCM};
use vstd::resource::storage_protocol::{Protocol, StorageResource};
use vstd::resource::Loc;

verus! {

broadcast use {vstd::map::group_map_axioms, vstd::set::group_set_axioms};

// Integer-based fractional ghost tokens kept for code that predates
// vstd::resource::frac's real-valued fractions.
ghost enum FractionalCarrier<T, const TOTAL: u64> {
    Value { v: T, n: int },
    Empty,
    Invalid,
}

impl<T, const TOTAL: u64> FractionalCarrier<T, TOTAL> {
    spec fn new(v: T) -> Self {
        FractionalCarrier::Value { v, n: TOTAL as int }
    }
}

impl<T, const TOTAL: u64> ResourceAlgebra for FractionalCarrier<T, TOTAL> {
    closed spec fn valid(self) -> bool {
        match self {
            FractionalCarrier::Invalid => false,
            FractionalCarrier::Empty => true,
            FractionalCarrier::Value { v: _, n } => 0 < n <= TOTAL,
        }
    }

    closed spec fn op(a: Self, b: Self) -> Self {
        match a {
            FractionalCarrier::Invalid => FractionalCarrier::Invalid,
            FractionalCarrier::Empty => b,
            FractionalCarrier::Value { v: sv, n: sn } => match b {
                FractionalCarrier::Invalid => FractionalCarrier::Invalid,
                FractionalCarrier::Empty => a,
                FractionalCarrier::Value { v: ov, n: on } => {
                    if sv != ov {
                        FractionalCarrier::Invalid
                    } else if sn <= 0 || on <= 0 {
                        FractionalCarrier::Invalid
                    } else {
                        FractionalCarrier::Value { v: sv, n: sn + on }
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

impl<T, const TOTAL: u64> PCM for FractionalCarrier<T, TOTAL> {
    closed spec fn unit() -> Self {
        FractionalCarrier::Empty
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

pub tracked struct FracGhost<T, const TOTAL: u64 = 2> {
    r: Resource<FractionalCarrier<T, TOTAL>>,
}

impl<T, const TOTAL: u64> FracGhost<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.r.value() is Value
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> T {
        self.r.value()->v
    }

    pub closed spec fn frac(self) -> int {
        self.r.value()->n
    }

    pub open spec fn valid(self, id: Loc, frac: int) -> bool {
        &&& self.id() == id
        &&& self.frac() == frac
    }

    pub proof fn new(v: T) -> (tracked result: Self)
        requires
            TOTAL > 0,
        ensures
            result.frac() == TOTAL as int,
            result@ == v,
    {
        let f = FractionalCarrier::<T, TOTAL>::new(v);
        let tracked r = Resource::alloc(f);
        Self { r }
    }

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

    pub proof fn take(tracked &mut self) -> (tracked result: Self)
        ensures
            result == *old(self),
    {
        self.bounded();
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        mself
    }

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
    {
        self.bounded();
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        use_type_invariant(&mself);
        let tracked (r1, r2) = mself.r.split(
            FractionalCarrier::Value { v: mself.r.value()->v, n: mself.r.value()->n - n },
            FractionalCarrier::Value { v: mself.r.value()->v, n },
        );
        self.r = r1;
        Self { r: r2 }
    }

    pub proof fn combine(tracked &mut self, tracked other: Self)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self)@ == other@,
            final(self).frac() == old(self).frac() + other.frac(),
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

    pub proof fn update(tracked &mut self, v: T)
        requires
            old(self).frac() == TOTAL,
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == v,
            final(self).frac() == old(self).frac(),
    {
        self.bounded();
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        use_type_invariant(&mself);
        let tracked r = mself.r;
        let f = FractionalCarrier::<T, TOTAL>::Value { v, n: TOTAL as int };
        *self = Self { r: r.update(f) };
    }

    pub proof fn update_with(tracked &mut self, tracked other: &mut Self, v: T)
        requires
            old(self).id() == old(other).id(),
            old(self).frac() + old(other).frac() == TOTAL,
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
        Self::new(arbitrary())
    }
}

ghost enum FractionalCarrierOpt<T, const TOTAL: u64> {
    Value { v: Option<T>, n: int },
    Empty,
    Invalid,
}

impl<T, const TOTAL: u64> Protocol<(), T> for FractionalCarrierOpt<T, TOTAL> {
    closed spec fn op(self, other: Self) -> Self {
        match self {
            FractionalCarrierOpt::Invalid => FractionalCarrierOpt::Invalid,
            FractionalCarrierOpt::Empty => other,
            FractionalCarrierOpt::Value { v: sv, n: sn } => match other {
                FractionalCarrierOpt::Invalid => FractionalCarrierOpt::Invalid,
                FractionalCarrierOpt::Empty => self,
                FractionalCarrierOpt::Value { v: ov, n: on } => {
                    if sv != ov {
                        FractionalCarrierOpt::Invalid
                    } else if sn <= 0 || on <= 0 {
                        FractionalCarrierOpt::Invalid
                    } else {
                        FractionalCarrierOpt::Value { v: sv, n: sn + on }
                    }
                },
            },
        }
    }

    closed spec fn rel(self, s: Map<(), T>) -> bool {
        match self {
            FractionalCarrierOpt::Value { v, n } => {
                (match v {
                    Some(v0) => s.dom().contains(()) && s[()] == v0,
                    None => s =~= map![],
                }) && n == TOTAL && n != 0
            },
            FractionalCarrierOpt::Empty => false,
            FractionalCarrierOpt::Invalid => false,
        }
    }

    closed spec fn unit() -> Self {
        FractionalCarrierOpt::Empty
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }
}

pub tracked struct Frac<T, const TOTAL: u64 = 2> {
    r: StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
}

pub tracked struct Empty<T, const TOTAL: u64 = 2> {
    r: StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
}

impl<T, const TOTAL: u64> Frac<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.r.value() matches FractionalCarrierOpt::Value { v: Some(_), .. }
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn resource(self) -> T {
        self.r.value()->v.unwrap()
    }

    pub closed spec fn frac(self) -> int {
        self.r.value()->n
    }

    pub open spec fn valid(self, id: Loc, frac: int) -> bool {
        &&& self.id() == id
        &&& self.frac() == frac
    }

    pub proof fn new(tracked v: T) -> (tracked result: Self)
        requires
            TOTAL > 0,
        ensures
            result.frac() == TOTAL as int,
            result.resource() == v,
    {
        let f = FractionalCarrierOpt::<T, TOTAL>::Value { v: Some(v), n: TOTAL as int };
        let tracked mut m = Map::<(), T>::tracked_empty();
        m.tracked_insert((), v);
        let tracked r = StorageResource::alloc(f, m);
        Self { r }
    }

    pub proof fn agree(tracked self: &Self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self.resource() == other.resource(),
    {
        use_type_invariant(self);
        use_type_invariant(other);
        let tracked joined = self.r.join_shared(&other.r);
        joined.validate();
    }

    pub proof fn split(tracked &mut self, n: int) -> (tracked result: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            result.id() == final(self).id(),
            final(self).id() == old(self).id(),
            final(self).resource() == old(self).resource(),
            result.resource() == old(self).resource(),
            final(self).frac() + result.frac() == old(self).frac(),
            result.frac() == n,
    {
        use_type_invariant(&*self);
        Self::split_helper(&mut self.r, n)
    }

    proof fn split_helper(
        tracked r: &mut StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
        n: int,
    ) -> (tracked result: Self)
        requires
            0 < n < old(r).value()->n,
            old(r).value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
        ensures
            result.id() == final(r).loc(),
            final(r).loc() == old(r).loc(),
            final(r).value()->v.unwrap() == old(r).value()->v.unwrap(),
            result.resource() == old(r).value()->v.unwrap(),
            final(r).value()->n + result.frac() == old(r).value()->n,
            result.frac() == n,
            final(r).value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
    {
        r.validate();
        let tracked mut r1 = StorageResource::alloc(
            FractionalCarrierOpt::Value { v: None, n: TOTAL as int },
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut r1);
        let tracked (r1, r2) = r1.split(
            FractionalCarrierOpt::Value { v: r1.value()->v, n: r1.value()->n - n },
            FractionalCarrierOpt::Value { v: r1.value()->v, n },
        );
        *r = r1;
        Self { r: r2 }
    }

    pub proof fn combine(tracked &mut self, tracked other: Self)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).resource() == old(self).resource(),
            final(self).resource() == other.resource(),
            final(self).frac() == old(self).frac() + other.frac(),
    {
        use_type_invariant(&*self);
        Self::combine_helper(&mut self.r, other)
    }

    proof fn combine_helper(
        tracked r: &mut StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
        tracked other: Self,
    )
        requires
            old(r).loc() == other.id(),
            old(r).value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
        ensures
            final(r).loc() == old(r).loc(),
            final(r).value()->v.unwrap() == old(r).value()->v.unwrap(),
            final(r).value()->v.unwrap() == other.resource(),
            final(r).value()->n == old(r).value()->n + other.frac(),
            final(r).value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
    {
        r.validate();
        use_type_invariant(&other);
        let tracked mut r1 = StorageResource::alloc(
            FractionalCarrierOpt::Value { v: None, n: TOTAL as int },
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut r1);
        r1.validate_with_shared(&other.r);
        *r = StorageResource::join(r1, other.r);
    }

    pub proof fn bounded(tracked &self)
        ensures
            0 < self.frac() <= TOTAL,
    {
        use_type_invariant(self);
        let (x, _) = self.r.validate();
    }

    pub proof fn borrow(tracked &self) -> (tracked ret: &T)
        ensures
            ret == self.resource(),
    {
        use_type_invariant(self);
        StorageResource::guard(&self.r, map![() => self.resource()]).tracked_borrow(())
    }

    pub proof fn take_resource(tracked self) -> (tracked pair: (T, Empty<T, TOTAL>))
        requires
            self.frac() == TOTAL,
        ensures
            pair.0 == self.resource(),
            pair.1.id() == self.id(),
    {
        use_type_invariant(&self);
        self.r.validate();
        let p1 = self.r.value();
        let p2 = FractionalCarrierOpt::Value { v: None, n: TOTAL as int };
        let b2 = map![() => self.resource()];
        assert forall|q: FractionalCarrierOpt<T, TOTAL>, t1: Map<(), T>|
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p1, q), t1) implies exists|
            t2: Map<(), T>,
        |
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2) && t2.dom().disjoint(
                b2.dom(),
            ) && t1 =~= t2.union_prefer_right(b2) by {
            let t2 = map![];
            assert(FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2));
            assert(t2.dom().disjoint(b2.dom()));
            assert(t1 =~= t2.union_prefer_right(b2));
        }
        let tracked Self { r } = self;
        let tracked (new_r, mut m) = r.withdraw(p2, b2);
        let tracked emp = Empty { r: new_r };
        let tracked resource = m.tracked_remove(());
        (resource, emp)
    }
}

impl<T, const TOTAL: u64> Empty<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value() matches FractionalCarrierOpt::Value { v: None, n }
        &&& n == TOTAL
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub proof fn new(tracked v: T) -> (tracked result: Self)
        requires
            TOTAL > 0,
    {
        let f = FractionalCarrierOpt::<T, TOTAL>::Value { v: None, n: TOTAL as int };
        let tracked mut m = Map::<(), T>::tracked_empty();
        let tracked r = StorageResource::alloc(f, m);
        Self { r }
    }

    pub proof fn put_resource(tracked self, tracked resource: T) -> (tracked frac: Frac<T, TOTAL>)
        ensures
            frac.id() == self.id(),
            frac.resource() == resource,
            frac.frac() == TOTAL,
    {
        use_type_invariant(&self);
        self.r.validate();
        let p1 = self.r.value();
        let b1 = map![() => resource];
        let p2 = FractionalCarrierOpt::Value { v: Some(resource), n: TOTAL as int };
        assert forall|q: FractionalCarrierOpt<T, TOTAL>, t1: Map<(), T>|
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p1, q), t1) implies exists|
            t2: Map<(), T>,
        |
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2) && t1.dom().disjoint(
                b1.dom(),
            ) && t1.union_prefer_right(b1) =~= t2 by {
            let t2 = map![() => resource];
            assert(FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2)
                && t1.dom().disjoint(b1.dom()) && t1.union_prefer_right(b1) =~= t2);
        }
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), resource);
        let tracked Self { r } = self;
        let tracked new_r = r.deposit(m, p2);
        Frac { r: new_r }
    }
}

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

    /// Splits a `FracGhost` with the given fraction.
    pub proof fn split(tracked &mut self, n: int) -> (tracked res: FracGhost<T, TOTAL>)
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

    /// Combines a `FracGhost`.
    pub proof fn combine(tracked &mut self, tracked other: FracGhost<T, TOTAL>)
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

    /// Splits a `Frac` with the given fraction.
    pub proof fn split(tracked &mut self, n: int) -> (tracked res: Frac<T, TOTAL>)
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

    /// Combines a `Frac`.
    pub proof fn combine(tracked &mut self, tracked other: Frac<T, TOTAL>)
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
    pub proof fn take_resource(tracked self) -> (tracked (res, empty): (T, Empty<T, TOTAL>))
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

    /// Updates the resource stored in this `FracResource` and retunrs the old resource if it exists.
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
