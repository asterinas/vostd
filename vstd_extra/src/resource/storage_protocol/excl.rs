//! Exclusive storage protocol resource algebra.
use vstd::modes::tracked_swap;
use vstd::prelude::*;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::storage_protocol::*;
use vstd::resource::Loc;

verus! {

pub ghost enum ExclusiveSP<A> {
    Unit,
    /// Exclusive ownership of a value.
    Exclusive(Option<A>),
    /// Invalid state.
    Invalid,
}

impl<A> Protocol<(), A> for ExclusiveSP<A> {
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (ExclusiveSP::Unit, x) => x,
            (x, ExclusiveSP::Unit) => x,
            _ => ExclusiveSP::Invalid,
        }
    }

    open spec fn rel(self, s: Map<(), A>) -> bool {
        match self {
            ExclusiveSP::Unit => s.is_empty(),
            ExclusiveSP::Exclusive(None) => s.is_empty(),
            ExclusiveSP::Exclusive(Some(x)) => s =~= map![() => x],
            ExclusiveSP::Invalid => false,
        }
    }

    open spec fn unit() -> Self {
        ExclusiveSP::Unit
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }
}

impl<A> ExclusiveSP<A> {
    pub open spec fn value(self) -> A {
        match self {
            ExclusiveSP::Exclusive(Some(x)) => x,
            _ => arbitrary(),
        }
    }

    pub proof fn lemma_deposits(self, value: A)
        requires
            self is Exclusive,
            self->Exclusive_0 is None,
        ensures
            deposits(self, map![() => value], ExclusiveSP::Exclusive(Some(value))),
    {
        let m = map![() => value];
        assert forall|q: Self, s: Map<(), A>|
            #![auto]
            Self::rel(Self::op(self, q), s) implies exists|s1: Map<(), A>|
            #![auto]
            Self::rel(Self::op(ExclusiveSP::Exclusive(Some(value)), q), s1) && s.dom().disjoint(
                m.dom(),
            ) && &&s.union_prefer_right(m) == s1 by {
            assert(s == Map::<(), A>::empty());
            assert(Self::rel(Self::op(ExclusiveSP::Exclusive(Some(value)), q), m));
            assert(s.dom().disjoint(m.dom()));
            assert(s.union_prefer_right(m) == m);
        }
    }
}

/// `Exclusive` is a token that stores a tracked object of type `T` and ensures its exclusive ownership.
/// No two `Exclusive` tokens can have the same id.
/// The owned tracked object can be borrowed, updated, taken out and put back.
pub tracked struct Exclusive<T> {
    tracked r: StorageResource<(), T, ExclusiveSP<T>>,
}

impl<T> Exclusive<T> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Returns the underlying `ExclP<T>` protocol monoid.
    pub closed spec fn protocol_monoid(self) -> ExclusiveSP<T> {
        self.r.value()
    }

    /// Returns the owned resource.
    pub open spec fn resource(self) -> T {
        self.protocol_monoid().value()
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        self.protocol_monoid() is Exclusive
    }

    /// Wether the token stores a resource.
    pub open spec fn has_resource(self) -> bool {
        self.protocol_monoid()->Exclusive_0 is Some
    }

    /// Wether the token does not store any resource.
    pub open spec fn has_no_resource(self) -> bool {
        self.protocol_monoid()->Exclusive_0 is None
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    closed spec fn type_inv_inner(r: ExclusiveSP<T>) -> bool {
        r is Exclusive
    }

    /// The existence of two `Exclusive` tokens ensures that they do not have the same id.
    pub proof fn validate_with_other(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *final(self),
            final(self).wf(),
            final(self).id() != other.id(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.validate_with_shared(&other.r);
        }
    }

    /// Borrows the owned resource.
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &T)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        use_type_invariant(&*self);
        StorageResource::guard(&self.r, map![() => self.resource()]).tracked_borrow(())
    }

    /// Takes out the owned resource.
    pub proof fn take_resource(tracked &mut self) -> (tracked res: T)
        requires
            old(self).has_resource(),
        ensures
            final(self).has_no_resource(),
            res == old(self).resource(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        Self::take_resource_helper(&mut self.r)
    }

    proof fn take_resource_helper(
        tracked r: &mut StorageResource<(), T, ExclusiveSP<T>>,
    ) -> (tracked res: T)
        requires
            Self::type_inv_inner(old(r).value()),
            old(r).value()->Exclusive_0 is Some,
        ensures
            Self::type_inv_inner(final(r).value()),
            final(r).value()->Exclusive_0 is None,
            final(r).loc() == old(r).loc(),
            res == old(r).value()->Exclusive_0->0,
    {
        let tracked mut tmp = StorageResource::<(), T, ExclusiveSP<T>>::alloc(
            ExclusiveSP::Unit,
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut tmp);
        let tracked (mut r1, mut r2) = tmp.withdraw(
            ExclusiveSP::Exclusive(None),
            map![()=> tmp.value().value()],
        );
        tracked_swap(r, &mut r1);
        r2.tracked_remove(())
    }

    /// Puts back the owned resource.
    pub proof fn put_resource(tracked &mut self, tracked value: T)
        requires
            old(self).has_no_resource(),
        ensures
            final(self).has_resource(),
            final(self).resource() == value,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        Self::put_resource_helper(&mut self.r, value)
    }

    proof fn put_resource_helper(
        tracked r: &mut StorageResource<(), T, ExclusiveSP<T>>,
        tracked value: T,
    )
        requires
            Self::type_inv_inner(old(r).value()),
            old(r).value()->Exclusive_0 is None,
        ensures
            Self::type_inv_inner(final(r).value()),
            final(r).value()->Exclusive_0 is Some,
            final(r).loc() == old(r).loc(),
            final(r).value()->Exclusive_0->0 == value,
    {
        let ghost g = value;
        let tracked mut tmp = StorageResource::<(), T, ExclusiveSP<T>>::alloc(
            ExclusiveSP::Unit,
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut tmp);
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), value);
        tmp.value().lemma_deposits(g);
        let tracked mut r1 = tmp.deposit(m, ExclusiveSP::Exclusive(Some(g)));
        tracked_swap(r, &mut r1);
    }

    /// Updates the owned resource and returns the old resource if it exists.
    pub proof fn update(tracked &mut self, tracked value: T) -> (tracked res: Option<T>)
        ensures
            final(self).has_resource(),
            final(self).resource() == value,
            res == if old(self).has_resource() {
                Some(old(self).resource())
            } else {
                None
            },
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked mut res = None;
        if self.has_resource() {
            res = Some(self.take_resource());
        }
        self.put_resource(value);
        res
    }
}

} // verus!
