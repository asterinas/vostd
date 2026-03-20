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
/// No two `ExclusiveGhost` tokens can have the same id.
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

/// `Exclusive` is a token that stores a tracked object of type `T` and ensures its exclusive ownership.
/// No two `Exclusive` tokens can have the same id.
/// The owned tracked object can be borrowed, updated, taken out and put back.
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

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        self.protocol_monoid() is Excl
    }

    /// Wether the token stores a resource.
    pub open spec fn has_resource(self) -> bool {
        self.protocol_monoid()->Excl_0 is Some
    }

    /// Wether the token does not store any resource.
    pub open spec fn has_no_resource(self) -> bool {
        self.protocol_monoid()->Excl_0 is None
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    closed spec fn type_inv_inner(r: ExclP<T>) -> bool {
        r is Excl
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
            self.has_no_resource(),
            res == old(self).resource(),
            self.wf(),
    {
        use_type_invariant(&*self);
        Self::take_resource_helper(&mut self.r)
    }

    proof fn take_resource_helper(tracked r: &mut StorageResource<(), T, ExclP<T>>) -> (tracked res:
        T)
        requires
            Self::type_inv_inner(old(r).value()),
            old(r).value()->Excl_0 is Some,
        ensures
            Self::type_inv_inner(r.value()),
            r.value()->Excl_0 is None,
            r.loc() == old(r).loc(),
            res == old(r).value()->Excl_0->Some_0,
    {
        let tracked mut tmp = StorageResource::<(), T, ExclP<T>>::alloc(
            ExclP::Unit,
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut tmp);
        let tracked (mut r1, mut r2) = tmp.withdraw(
            ExclP::Excl(None),
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
            self.has_resource(),
            self.resource() == value,
            self.wf(),
    {
        use_type_invariant(&*self);
        Self::put_resource_helper(&mut self.r, value)
    }

    proof fn put_resource_helper(tracked r: &mut StorageResource<(), T, ExclP<T>>, tracked value: T)
        requires
            Self::type_inv_inner(old(r).value()),
            old(r).value()->Excl_0 is None,
        ensures
            Self::type_inv_inner(r.value()),
            r.value()->Excl_0 is Some,
            r.loc() == old(r).loc(),
            r.value()->Excl_0->Some_0 == value,
    {
        let ghost g = value;
        let tracked mut tmp = StorageResource::<(), T, ExclP<T>>::alloc(
            ExclP::Unit,
            Map::tracked_empty(),
        );
        tracked_swap(r, &mut tmp);
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), value);
        tmp.value().lemma_deposits(g);
        let tracked mut r1 = tmp.deposit(m, ExclP::Excl(Some(g)));
        tracked_swap(r, &mut r1);
    }

    /// Updates the owned resource and returns the old resource if it exists.
    pub proof fn update(tracked &mut self, tracked value: T) -> (tracked res: Option<T>)
        ensures
            self.has_resource(),
            self.resource() == value,
            res == if old(self).has_resource() {
                Some(old(self).resource())
            } else {
                None
            },
            self.wf(),
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
