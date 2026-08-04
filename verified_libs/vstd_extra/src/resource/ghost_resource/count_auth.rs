//! Authoritative and integer-based counting storage resources.
use vstd::imap::*;
use vstd::modes::tracked_swap;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::storage_protocol::*;

verus! {

/// A protocol monoid that tracks a resource value, its fraction, and **the authority**.
ghost enum FractionalCarrierOpt<T, const TOTAL: u64> {
    Value { v: Option<T>, n: int, auth: bool },
    Empty,
    Invalid,
}

impl<T, const TOTAL: u64> Protocol<(), T> for FractionalCarrierOpt<T, TOTAL> {
    closed spec fn op(self, other: Self) -> Self {
        match self {
            FractionalCarrierOpt::Invalid => FractionalCarrierOpt::Invalid,
            FractionalCarrierOpt::Empty => other,
            FractionalCarrierOpt::Value { v: sv, n: sn, auth: sa } => match other {
                FractionalCarrierOpt::Invalid => FractionalCarrierOpt::Invalid,
                FractionalCarrierOpt::Empty => self,
                FractionalCarrierOpt::Value { v: ov, n: on, auth: oa } => {
                    if sv != ov {
                        FractionalCarrierOpt::Invalid
                    } else if sa && oa {
                        FractionalCarrierOpt::Invalid
                    } else if sn < 0 || on < 0 || (!sa && sn == 0) || (!oa && on == 0) {
                        FractionalCarrierOpt::Invalid
                    } else {
                        FractionalCarrierOpt::Value { v: sv, n: sn + on, auth: sa || oa }
                    }
                },
            },
        }
    }

    closed spec fn rel(self, s: IMap<(), T>) -> bool {
        match self {
            FractionalCarrierOpt::Value { v, n, auth } => {
                (match v {
                    Some(v0) => s.dom().contains(()) && s[()] == v0,
                    None => s =~= imap![],
                }) && auth && n == TOTAL && n != 0
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

pub tracked struct Count<T, const TOTAL: u64 = 2> {
    r: StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
}

pub tracked struct EmptyCount<T, const TOTAL: u64 = 2> {
    r: StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
}

impl<T, const TOTAL: u64> Count<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value() matches FractionalCarrierOpt::Value { v: Some(_), .. }
        &&& self.r.value()->n > 0
    }

    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Returns the stored resource value.
    pub closed spec fn resource(self) -> T {
        self.r.value()->v->0
    }

    /// Returns the fraction of the resource.
    pub closed spec fn frac(self) -> int {
        self.r.value()->n
    }

    /// Whether this token carries the unique authority for the resource slot.
    pub closed spec fn has_authority(self) -> bool {
        self.r.value()->auth
    }

    pub open spec fn valid(self, id: Loc, frac: int) -> bool {
        &&& self.id() == id
        &&& self.frac() == frac
    }

    /// Allocates a new `Count` with the full fraction and the given resource value.
    pub proof fn alloc(tracked v: T) -> (tracked result: Self)
        requires
            TOTAL > 0,
        ensures
            result.frac() == TOTAL,
            result.resource() == v,
            result.has_authority(),
    {
        let f = FractionalCarrierOpt::<T, TOTAL>::Value { v: Some(v), n: TOTAL as int, auth: true };
        let tracked mut m = IMap::<(), T>::tracked_empty();
        m.tracked_insert((), v);
        let tracked r = StorageResource::alloc(f, m);
        Self { r }
    }

    /// Two `Count`s with the same id must have the same resource value.
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

    /// Splits another fraction `n` from this `Count`, returning a new `Count` with that fraction.
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
            final(self).has_authority() == old(self).has_authority(),
            !result.has_authority(),
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
            final(r).value()->v->0 == old(r).value()->v->0,
            result.resource() == old(r).value()->v->0,
            final(r).value()->n + result.frac() == old(r).value()->n,
            result.frac() == n,
            final(r).value()->auth == old(r).value()->auth,
            !result.has_authority(),
            final(r).value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
    {
        r.validate();
        let tracked mut r1 = StorageResource::alloc(
            FractionalCarrierOpt::Value { v: None, n: TOTAL as int, auth: true },
            IMap::tracked_empty(),
        );
        tracked_swap(r, &mut r1);
        let tracked (r1, r2) = r1.split(
            FractionalCarrierOpt::Value {
                v: r1.value()->v,
                n: r1.value()->n - n,
                auth: r1.value()->auth,
            },
            FractionalCarrierOpt::Value { v: r1.value()->v, n, auth: false },
        );
        *r = r1;
        Self { r: r2 }
    }

    /// Combines another `Count` into this one, consuming the other `Count`.
    pub proof fn combine(tracked &mut self, tracked other: Self)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).resource() == old(self).resource(),
            final(self).resource() == other.resource(),
            final(self).frac() == old(self).frac() + other.frac(),
            final(self).has_authority() == (old(self).has_authority() || other.has_authority()),
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
            old(r).value()->n > 0,
        ensures
            final(r).loc() == old(r).loc(),
            final(r).value()->v->0 == old(r).value()->v->0,
            final(r).value()->v->0 == other.resource(),
            final(r).value()->n == old(r).value()->n + other.frac(),
            final(r).value()->auth == (old(r).value()->auth || other.has_authority()),
            final(r).value()->n > 0,
            final(r).value() matches FractionalCarrierOpt::Value { v: Some(_), .. },
    {
        r.validate();
        use_type_invariant(&other);
        let tracked mut r1 = StorageResource::alloc(
            FractionalCarrierOpt::Value { v: None, n: TOTAL as int, auth: true },
            IMap::tracked_empty(),
        );
        tracked_swap(r, &mut r1);
        r1.validate_with_shared(&other.r);
        *r = StorageResource::join(r1, other.r);
    }

    /// The fraction of the resource must be positive and at most `TOTAL`.
    pub proof fn bounded(tracked &self)
        ensures
            0 < self.frac() <= TOTAL,
    {
        use_type_invariant(self);
        let (x, _) = self.r.validate();
    }

    /// Borrows the resource value.
    pub proof fn tracked_borrow(tracked &self) -> (tracked ret: &T)
        ensures
            ret == self.resource(),
    {
        use_type_invariant(self);
        StorageResource::guard(&self.r, imap![() => self.resource()]).tracked_borrow(())
    }

    /// Consumes the `Count` and returns the resource value and an `EmptyCount` with the same id.
    pub proof fn take_resource(tracked self) -> (tracked pair: (T, EmptyCount<T, TOTAL>))
        requires
            self.frac() == TOTAL,
            self.has_authority(),
        ensures
            pair.0 == self.resource(),
            pair.1.id() == self.id(),
    {
        use_type_invariant(&self);
        self.r.validate();
        let p1 = self.r.value();
        let p2 = FractionalCarrierOpt::Value { v: None, n: TOTAL as int, auth: true };
        let b2 = imap![() => self.resource()];
        assert forall|q: FractionalCarrierOpt<T, TOTAL>, t1: IMap<(), T>|
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p1, q), t1) implies exists|
            t2: IMap<(), T>,
        |
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2) && t2.dom().disjoint(
                b2.dom(),
            ) && t1 == t2.union_prefer_right(b2) by {
            let t2 = imap![];
            assert(FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2));
            assert(t2.dom().disjoint(b2.dom()));
            assert(t1 == t2.union_prefer_right(b2));
        }
        let tracked Self { r } = self;
        let tracked (new_r, mut m) = r.withdraw(p2, b2);
        let tracked emp = EmptyCount { r: new_r };
        let tracked resource = m.tracked_remove(());
        (resource, emp)
    }

    /// Consumes the `Count` and returns the resource value, the id is lost because the `EmptyCount` is not returned.
    pub proof fn into_resource(tracked self) -> (tracked res: T)
        requires
            self.frac() == TOTAL,
            self.has_authority(),
        returns
            self.resource(),
    {
        let tracked (res, _) = self.take_resource();
        res
    }
}

impl<T, const TOTAL: u64> EmptyCount<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value() matches FractionalCarrierOpt::Value { v: None, n, auth: true }
        &&& n == TOTAL
    }

    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Allocates a new `EmptyCount`, the `id` is arbitrary.
    pub proof fn alloc() -> (tracked result: Self)
        requires
            TOTAL > 0,
    {
        let f = FractionalCarrierOpt::<T, TOTAL>::Value { v: None, n: TOTAL as int, auth: true };
        let tracked mut m = IMap::<(), T>::tracked_empty();
        let tracked r = StorageResource::alloc(f, m);
        Self { r }
    }

    /// Puts a resource into the `EmptyCount`, returning a `Count` with the same id and the full fraction.
    pub proof fn put_resource(tracked self, tracked resource: T) -> (tracked frac: Count<T, TOTAL>)
        ensures
            frac.id() == self.id(),
            frac.resource() == resource,
            frac.frac() == TOTAL,
            frac.has_authority(),
    {
        use_type_invariant(&self);
        self.r.validate();
        let p1 = self.r.value();
        let b1 = imap![() => resource];
        let p2 = FractionalCarrierOpt::Value { v: Some(resource), n: TOTAL as int, auth: true };
        assert forall|q: FractionalCarrierOpt<T, TOTAL>, t1: IMap<(), T>|
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p1, q), t1) implies exists|
            t2: IMap<(), T>,
        |
            #![all_triggers]
            FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2) && t1.dom().disjoint(
                b1.dom(),
            ) && t1.union_prefer_right(b1) == t2 by {
            let t2 = imap![() => resource];
            assert(FractionalCarrierOpt::rel(FractionalCarrierOpt::op(p2, q), t2)
                && t1.dom().disjoint(b1.dom()) && t1.union_prefer_right(b1) == t2);
        }
        let tracked mut m = IMap::tracked_empty();
        m.tracked_insert((), resource);
        let tracked Self { r } = self;
        let tracked new_r = r.deposit(m, p2);
        Count { r: new_r }
    }
}

/// An authoritative pool that stores and dispatches counted fractions.
///
/// The authority and every dispatched [`Count`] use the same [`Loc`]. The
/// authority remains present when the pool's fraction reaches zero, retaining
/// agreement on the stored value without a second resource identity.
pub tracked struct CountResource<T, const TOTAL: u64> {
    tracked r: StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
}

impl<T, const TOTAL: u64> CountResource<T, TOTAL> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.is_resource_vacant() ==> self.is_empty()
        &&& self.r.value() matches FractionalCarrierOpt::Value { auth: true, .. }
        &&& match self.r.value()->v {
            Some(_) => 0 <= self.r.value()->n <= TOTAL,
            None => self.r.value()->n == TOTAL,
        }
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.type_inv()
    }

    /// Whether this `CountResource` has no fraction.
    ///
    /// This does not imply [`Self::is_resource_vacant`]: it may have reached fraction zero
    /// because all of its fractions were split out.
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

    /// Whether the associated resource slot is vacant and can accept a new resource.
    ///
    /// This state is produced by [`Self::take_resource`] and owns the underlying empty token
    /// needed by [`Self::put_resource`]. Resource vacancy implies [`Self::is_empty`], but the
    /// converse does not hold when all fractions were removed using [`Self::split`] or
    /// [`Self::split_one`].
    pub closed spec fn is_resource_vacant(self) -> bool {
        self.r.value()->v is None
    }

    /// A resource-vacant `CountResource` has no fraction.
    pub proof fn lemma_resource_vacant_implies_empty(tracked &self)
        requires
            self.is_resource_vacant(),
        ensures
            self.is_empty(),
    {
        use_type_invariant(self);
    }

    /// Returns the value of type `T` stored in this `CountResource`.
    pub closed spec fn resource(self) -> T {
        self.r.value()->v->0
    }

    /// Returns the value of type `T` stored in this `CountResource`. It is an alias of `Self::resource`.
    #[verifier::inline]
    pub open spec fn view(self) -> T {
        self.resource()
    }

    /// The fractions stored in this `CountResource`.
    pub closed spec fn frac(self) -> int {
        if self.is_resource_vacant() {
            0
        } else {
            self.r.value()->n
        }
    }

    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    proof fn vacant() -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.is_resource_vacant(),
            res.is_empty(),
            res.wf(),
    {
        let tracked empty = EmptyCount::alloc();
        use_type_invariant(&empty);
        let tracked EmptyCount { r } = empty;
        Self { r }
    }

    /// Create an arbitrary `CountResource`. Useful as a placeholder.
    pub proof fn arbitrary() -> (tracked res: Self)
        requires
            TOTAL > 0,
    {
        Self::vacant()
    }

    /// Allocates a new `CountResource` with the given tracked object.
    pub proof fn alloc(tracked value: T) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.not_empty(),
            res.is_full(),
            !res.is_resource_vacant(),
            res@ == value,
            res.wf(),
    {
        let tracked count = Count::alloc(value);
        use_type_invariant(&count);
        let tracked Count { r } = count;
        Self { r }
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
            !res.is_resource_vacant(),
            res.id() == empty.id(),
            res.view() == value,
            res.wf(),
    {
        let tracked count = empty.put_resource(value);
        use_type_invariant(&count);
        let tracked Count { r } = count;
        Self { r }
    }

    /// Splits a `Count` with fraction 1.
    pub proof fn split_one(tracked &mut self) -> (tracked res: Count<T, TOTAL>)
        requires
            old(self).not_empty(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() + 1 == old(self).frac(),
            final(self)@ == old(self)@,
            res.frac() == 1,
            res.id() == final(self).id(),
            res.resource() == old(self)@,
            old(self).frac() == 1 ==> final(self).is_empty(),
            !final(self).is_resource_vacant(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        self.split(1)
    }

    /// Splits a `Count` with the given fraction.
    pub proof fn split(tracked &mut self, n: int) -> (tracked res: Count<T, TOTAL>)
        requires
            1 <= n <= old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() + n == old(self).frac(),
            final(self)@ == old(self)@,
            res.frac() == n,
            res.id() == final(self).id(),
            res.resource() == old(self)@,
            old(self).frac() == n ==> final(self).is_empty(),
            !final(self).is_resource_vacant(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        self.r.validate();
        let tracked mut dummy = Self::vacant();
        tracked_swap(self, &mut dummy);
        let tracked Self { r } = dummy;
        let p1 = FractionalCarrierOpt::Value { v: r.value()->v, n: r.value()->n - n, auth: true };
        let p2 = FractionalCarrierOpt::Value { v: r.value()->v, n, auth: false };
        let tracked (authority, fraction) = r.split(p1, p2);
        self.r = authority;
        Count { r: fraction }
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
                &&& !final(self).is_resource_vacant()
                &&& final(self).wf()
                &&& final(self)@ == old(self)@
            },
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        self.r.validate_with_shared(&other.r);
        let tracked mut dummy = Self::vacant();
        tracked_swap(self, &mut dummy);
        let tracked Self { r } = dummy;
        self.r = StorageResource::join(r, other.r);
        self.r.validate();
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
    }

    pub proof fn validate_with_frac(tracked &self, tracked frac: &Count<T, TOTAL>)
        requires
            self.id() == frac.id(),
        ensures
            self.resource() == frac.resource(),
    {
        use_type_invariant(self);
        use_type_invariant(frac);
        let tracked joined = self.r.join_shared(&frac.r);
        joined.validate();
    }

    /// Borrows the resource while this pool retains at least one fraction.
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &T)
        requires
            self.not_empty(),
        ensures
            res == self@,
    {
        use_type_invariant(self);
        StorageResource::guard(&self.r, imap![() => self.resource()]).tracked_borrow(())
    }

    /// Takes the resource out and leaves this token ready to accept a new resource.
    pub proof fn take_resource(tracked &mut self) -> (tracked res: T)
        requires
            self.is_full(),
        ensures
            final(self).is_empty(),
            final(self).is_resource_vacant(),
            final(self).id() == old(self).id(),
            res == old(self)@,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked mut dummy = Self::vacant();
        tracked_swap(self, &mut dummy);
        let tracked Self { r } = dummy;
        let tracked count = Count { r };
        let tracked (res, empty) = count.take_resource();
        use_type_invariant(&empty);
        self.r = empty.r;
        res
    }

    /// Puts a resource into a token returned to the empty state by `take_resource`.
    pub proof fn put_resource(tracked &mut self, tracked value: T)
        requires
            old(self).is_resource_vacant(),
        ensures
            final(self).is_full(),
            !final(self).is_resource_vacant(),
            final(self).id() == old(self).id(),
            final(self)@ == value,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked mut dummy = Self::vacant();
        tracked_swap(self, &mut dummy);
        let tracked Self { r } = dummy;
        let tracked empty = EmptyCount { r };
        let tracked count = empty.put_resource(value);
        use_type_invariant(&count);
        let tracked Count { r } = count;
        self.r = r;
    }

    /// Updates the resource stored in this `CountResource` and retunrs the old resource if it exists.
    /// The fraction must be full before the update.
    pub proof fn update(tracked &mut self, tracked value: T) -> (tracked res: T)
        requires
            old(self).is_full(),
        ensures
            final(self).is_full(),
            !final(self).is_resource_vacant(),
            res == old(self)@,
            final(self).id() == old(self).id(),
            final(self).wf(),
    {
        let tracked res = self.take_resource();
        self.put_resource(value);
        res
    }
}

} // verus!
