//! Integer-based counting ghost resource.
use vstd::map::*;
use vstd::modes::tracked_swap;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::{Resource, PCM};
use vstd::resource::storage_protocol::*;
use vstd::resource::Loc;

verus! {

// Integer-based counting ghost tokens which duplicate the retired int-based fractional resources.
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

pub tracked struct CountGhost<T, const TOTAL: u64 = 2> {
    r: Resource<FractionalCarrier<T, TOTAL>>,
}

impl<T, const TOTAL: u64> CountGhost<T, TOTAL> {
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

pub tracked struct Count<T, const TOTAL: u64 = 2> {
    r: StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
}

pub tracked struct EmptyCount<T, const TOTAL: u64 = 2> {
    r: StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
}

impl<T, const TOTAL: u64> Count<T, TOTAL> {
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

    pub proof fn take_resource(tracked self) -> (tracked pair: (T, EmptyCount<T, TOTAL>))
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
        let tracked emp = EmptyCount { r: new_r };
        let tracked resource = m.tracked_remove(());
        (resource, emp)
    }
}

impl<T, const TOTAL: u64> EmptyCount<T, TOTAL> {
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

    pub proof fn put_resource(tracked self, tracked resource: T) -> (tracked frac: Count<T, TOTAL>)
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
        Count { r: new_r }
    }
}

} // verus!
