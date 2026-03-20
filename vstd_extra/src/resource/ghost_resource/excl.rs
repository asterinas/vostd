//！ Exclusive ghost resource.
use vstd::modes::tracked_swap;
use vstd::pcm::*;
use vstd::prelude::*;
use vstd::storage_protocol::StorageResource;

use super::super::pcm::excl::*;
use super::super::storage_protocol::excl::*;

verus! {

pub type UniqueToken = ExclusiveGhost<()>;

/// `ExclusiveGhost` is a token that always provides exclusive access to a ghost value of type `T`.
pub tracked struct ExclusiveGhost<T>(Resource<ExclR<T>>);

impl<T> ExclusiveGhost<T> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.0.loc()
    }

    /// Returns the underlying `ExclR<T>` PCM element.
    pub closed spec fn pcm(self) -> ExclR<T> {
        self.0.value()
    }

    /// Returns the ghost value of type `T`.
    pub open spec fn value(self) -> T {
        self.pcm().value()
    }

    /// Returns the ghost value of type `T`, an alias of `Self::value()`.
    pub open spec fn view(self) -> T {
        self.value()
    }

    /// Type invariant: the PCM element must be `Excl`.
    pub open spec fn wf(self) -> bool {
        self.pcm() is Excl
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    spec fn type_inv_inner(r: ExclR<T>) -> bool {
        r is Excl
    }

    /// Allocates a new `ExclusiveGhost` with the given value。
    pub proof fn alloc(value: T) -> (tracked res: Self)
        ensures
            res.view() == value,
            res.wf(),
    {
        Self(Resource::<ExclR<T>>::alloc(ExclR::Excl(value)))
    }

    /// Updates the ghost value and returns the old value.
    pub proof fn update(tracked &mut self, value: T) -> (res: T)
        ensures
            self.id() == old(self).id(),
            self.view() == value,
            self.wf(),
    {
        use_type_invariant(&*self);
        Self::update_helper(&mut self.0, value)
    }

    proof fn update_helper(tracked r: &mut Resource<ExclR<T>>, value: T) -> (res: T)
        requires
            Self::type_inv_inner(old(r).value()),
            old(r).value() is Excl,
        ensures
            Self::type_inv_inner(r.value()),
            r.value() is Excl,
            r.loc() == old(r).loc(),
            res == old(r).value().value(),
            r.value().value() == value,
    {
        let ghost res = r.value().value();
        let tracked mut tmp = Resource::<ExclR<T>>::alloc(ExclR::Unit);
        tracked_swap(r, &mut tmp);
        let tracked mut r1 = tmp.update(ExclR::Excl(value));
        tracked_swap(r, &mut r1);
        res
    }

    /// The existence of two `ExclusiveGhost` tokens ensures that they do not have the same id.
    pub proof fn validate_with_other(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *self,
            self.id() != other.id(),
            self.wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.0.validate_2(&other.0);
        }
    }

    /// The token always satisfies `Self::wf()`.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(self);
    }
}

/// `ExclusiveResource` is a token that stores and maintains an exclusive tracked object of type `T`.
/// The exclusive ownership of the tracked object can be taken and released by `Exclusive` tokens.
pub tracked struct ExclusiveResource<T> {
    tracked r: StorageResource<(), T, ExclP<T>>,
}

impl<T> ExclusiveResource<T> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Returns the underlying `ExclP<T>` protocol monoid.
    pub closed spec fn protocol_monoid(self) -> ExclP<T> {
        self.r.value()
    }

    /// Whether the resource is currently stored.
    pub open spec fn has_resource(self) -> bool {
        self.protocol_monoid() is Excl
    }

    /// Whether the resource has been taken.
    pub open spec fn has_no_resource(self) -> bool {
        self.protocol_monoid() is Unit
    }

    /// Returns the stored resource, only meaningful if `Self::has_resource()` is true.
    pub open spec fn resource(self) -> T {
        self.protocol_monoid().value()
    }

    pub open spec fn wf(self) -> bool {
        &&& self.has_resource() || self.has_no_resource()
        &&& self.has_resource() <==> !self.has_no_resource()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    closed spec fn type_inv_inner(r: ExclP<T>) -> bool {
        &&& r is Unit || r is Excl
        &&& r is Unit <==> r !is Excl
    }

    /// Allocates a new `ExclusiveResource` with the given resource.
    pub proof fn alloc(tracked resource: T) -> (tracked res: Self)
        ensures
            res.resource() == resource,
            res.has_resource(),
    {
        let ghost g = resource;
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), resource);
        Self { r: StorageResource::<(), T, ExclP<T>>::alloc(ExclP::Excl(g), m) }
    }

    /// Splits another `ExclusiveResource`, giving the exclusive ownership to the new resource token if available.
    pub proof fn split_with_resource(tracked &mut self) -> (tracked res: Self)
        ensures
            self.id() == old(self).id(),
            self.has_no_resource(),
            res.id() == old(self).id(),
            res.has_resource() == old(self).has_resource(),
            res.has_resource() ==> res.resource() == old(self).resource(),
    {
        use_type_invariant(&*self);
        let tracked res = Self::split_with_resource_helper(&mut self.r);
        Self { r: res }
    }

    proof fn split_with_resource_helper(
        tracked r: &mut StorageResource<(), T, ExclP<T>>,
    ) -> (tracked res: StorageResource<(), T, ExclP<T>>)
        requires
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(r.value()),
            Self::type_inv_inner(res.value()),
            r.value() is Unit,
            res.value() is Excl <==> old(r).value() is Excl,
            old(r).loc() == r.loc(),
            old(r).loc() == res.loc(),
            res.value() is Excl ==> res.value().value() == old(r).value().value(),
    {
        let tracked mut tmp = StorageResource::<(), T, ExclP<T>>::alloc(
            ExclP::Unit,
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut tmp);
        let tracked (mut r1, r2) = tmp.split(ExclP::Unit, tmp.value());
        tracked_swap(r, &mut r1);
        r2
    }

    /// Takes the exclusive ownership, returning an `Exclusive` token.
    pub proof fn split_exclusive(tracked &mut self) -> (tracked res: Exclusive<T>)
        requires
            old(self).has_resource(),
        ensures
            self.id() == old(self).id(),
            self.has_no_resource(),
            res.id() == old(self).id(),
            res.resource() == old(self).resource(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_with_resource_helper(&mut self.r);
        Exclusive { r }
    }

    /// Joins an `Exclusive` token back to this `ExclusiveResource`.
    pub proof fn join_exclusive(tracked &mut self, tracked other: Exclusive<T>)
        requires
            old(self).id() == other.id(),
        ensures
            old(self).has_no_resource() ==> {
                &&& self.id() == old(self).id()
                &&& self.resource() == other.resource()
                &&& self.has_resource()
                &&& self.wf()
            },
            old(self).has_resource() ==> false,
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        if self.has_resource() {
            self.validate_with_exclusive(&other)
        } else {
            Self::join_exclusive_helper(&mut self.r, other.r);
        }
    }

    proof fn join_exclusive_helper(
        tracked r1: &mut StorageResource<(), T, ExclP<T>>,
        tracked r2: StorageResource<(), T, ExclP<T>>,
    )
        requires
            Self::type_inv_inner(old(r1).value()),
            Self::type_inv_inner(r2.value()),
            old(r1).value() is Unit,
            r2.value() is Excl,
            old(r1).loc() == r2.loc(),
        ensures
            Self::type_inv_inner(r1.value()),
            r1.value() is Excl,
            r1.loc() == r2.loc(),
            r1.value().value() == r2.value().value(),
    {
        let tracked mut tmp = StorageResource::<(), T, ExclP<T>>::alloc(
            ExclP::Unit,
            Map::tracked_empty(),
        );
        tracked_swap(r1, &mut tmp);
        let tracked mut r = StorageResource::join(tmp, r2);
        tracked_swap(r1, &mut r);
    }

    /// Borrows the resource, requires that the exclusive ownership is available.
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &T)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        use_type_invariant(&*self);
        StorageResource::guard(&self.r, map![() => self.resource()]).tracked_borrow(())
    }

    /// Takes the resource out, requires that the exclusive ownership is available.
    pub proof fn take_resource(tracked &mut self) -> (tracked res: T)
        requires
            old(self).has_resource(),
        ensures
            self.id() == old(self).id(),
            self.has_no_resource(),
            res == old(self).resource(),
    {
        use_type_invariant(&*self);
        Self::take_resource_helper(&mut self.r)
    }

    proof fn take_resource_helper(tracked r: &mut StorageResource<(), T, ExclP<T>>) -> (tracked res:
        T)
        requires
            Self::type_inv_inner(old(r).value()),
            old(r).value() is Excl,
        ensures
            Self::type_inv_inner(r.value()),
            r.value() is Unit,
            r.loc() == old(r).loc(),
            res == old(r).value().value(),
    {
        let tracked mut tmp = StorageResource::<(), T, ExclP<T>>::alloc(
            ExclP::Unit,
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut tmp);
        let tracked (mut r1, mut r2) = tmp.withdraw(ExclP::Unit, map![()=>tmp.value().value()]);
        tracked_swap(r, &mut r1);
        r2.tracked_remove(())
    }

    /// The existence of an `Exclusive` token ensures that either there is no resource in this `ExclusiveResource`,
    /// or they do not have the same id.
    pub proof fn validate_with_exclusive(tracked &mut self, tracked other: &Exclusive<T>)
        ensures
            self.has_resource() ==> self.id() != other.id(),
            *old(self) == *self,
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.has_resource() {
            if self.id() == other.id() {
                self.r.validate_with_shared(&other.r);
            }
        }
    }
}

/// `Exclusive` is a token that always holds the exclusive ownership of a tracked object of type `T`.
/// The owned tracked object can be borrowed or updated, but not taken out.
pub tracked struct Exclusive<T> {
    tracked r: StorageResource<(), T, ExclP<T>>,
}

impl<T> Exclusive<T> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Returns the underlying `ExclP<T>` protocol monoid.
    pub closed spec fn protocol_monoid(self) -> ExclP<T> {
        self.r.value()
    }

    /// Returns the owned resource.
    pub open spec fn resource(self) -> T {
        self.protocol_monoid().value()
    }

    pub open spec fn wf(self) -> bool {
        self.protocol_monoid() is Excl
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    /// The existence of two `Exclusive` tokens ensures that they do not have the same id.
    pub proof fn validate_with_other(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *self,
            self.wf(),
            self.id() != other.id(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.validate_with_shared(&other.r);
        }
    }

    /// Borrowing the owned resource.
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &T)
        ensures
            *res == self.resource(),
    {
        use_type_invariant(&*self);
        StorageResource::guard(&self.r, map![() => self.resource()]).tracked_borrow(())
    }
}

} // verus!
