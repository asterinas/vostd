//！ Exclusive ghost resource.
use vstd::modes::tracked_swap;
use vstd::pcm::*;
use vstd::prelude::*;

use super::super::pcm::excl::*;

verus! {

pub type UniqueTokenStorage = ExclusiveGhostResource<()>;

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

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.pcm() is Excl
    }

    /// Allocates a new `ExclusiveGhost` with the given value。
    pub proof fn alloc(value: T) -> (tracked res: Self)
        ensures
            res.view() == value,
    {
        Self(Resource::<ExclR<T>>::alloc(ExclR::Excl(value)))
    }

    /// Updates the ghost value and returns the old value.
    pub proof fn update(tracked &mut self, value: T) -> (res: T)
        ensures
            self.id() == old(self).id(),
            self.view() == value,
    {
        use_type_invariant(&*self);
        ExclusiveGhostResource::update_helper(&mut self.0, value)
    }

    /// The existence of two `ExclusiveGhost` tokens ensures that they do not have the same id.
    pub proof fn validate_with_other(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *self,
            self.id() != other.id(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.0.validate_2(&other.0);
        }
    }
}

// `ExclusiveGhostResource` is a token that can split and join `ExclusiveGhost`, it can be empty.
pub tracked struct ExclusiveGhostResource<T>(Resource<ExclR<T>>);

impl<T> ExclusiveGhostResource<T> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.0.loc()
    }

    /// Returns the underlying `ExclR<T>` PCM element.
    pub closed spec fn pcm(self) -> ExclR<T> {
        self.0.value()
    }

    /// Returns the ghost value of type `T`, only meaningful if `Self::is_full()` is true.
    pub open spec fn value(self) -> T {
        self.pcm().value()
    }

    /// Returns the ghost value of type `T`, an alias of `Self::value()`.
    #[verifier::inline]
    pub open spec fn view(self) -> T {
        self.value()
    }

    /// Whether the exclusive ownership has been taken.
    pub open spec fn is_empty(self) -> bool {
        self.pcm() is Unit
    }

    /// Whether the exclusive ownership is available.
    pub open spec fn is_full(self) -> bool {
        self.pcm() is Excl
    }

    pub open spec fn wf(self) -> bool {
        &&& self.is_empty() || self.is_full()
        &&& self.is_empty() <==> !self.is_full()
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    closed spec fn type_inv_inner(r: ExclR<T>) -> bool {
        &&& r is Unit || r is Excl
        &&& r is Unit <==> r !is Excl
    }

    /// Allocates a new `ExclusiveGhostResource` with the given value.
    pub proof fn alloc(value: T) -> (tracked res: Self)
        ensures
            res.view() == value,
            res.is_full(),
            res.wf(),
    {
        Self(Resource::<ExclR<T>>::alloc(ExclR::Excl(value)))
    }

    /// Takes the exclusive ownership, returning an `ExclusiveGhost` token.
    pub proof fn take(tracked &mut self) -> (tracked res: ExclusiveGhost<T>)
        requires
            old(self).is_full(),
        ensures
            self.id() == old(self).id(),
            self.is_empty(),
            res.id() == old(self).id(),
            res.view() == old(self).view(),
            self.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::take_helper(&mut self.0);
        ExclusiveGhost(r)
    }

    proof fn take_helper(tracked r: &mut Resource<ExclR<T>>) -> (tracked res: Resource<ExclR<T>>)
        requires
            Self::type_inv_inner(old(r).value()),
            old(r).value() is Excl,
        ensures
            Self::type_inv_inner(r.value()),
            Self::type_inv_inner(res.value()),
            r.value() is Unit,
            res.value() is Excl,
            old(r).loc() == r.loc(),
            old(r).loc() == res.loc(),
            res.value().value() == old(r).value().value(),
    {
        let tracked mut tmp = Resource::<ExclR<T>>::alloc(ExclR::Unit);
        tracked_swap(r, &mut tmp);
        let tracked (mut r1,r2) = tmp.split(ExclR::Unit, tmp.value());
        tracked_swap(r, &mut r1);
        r2
    }

    /// The existence of an `ExclusiveGhost` token ensures that either there is no resource in this `ExclusiveGhostResource`, 
    /// or they do not have the same id.
    pub proof fn validate_with_exclusive(tracked &mut self, tracked other: &ExclusiveGhost<T>)
        ensures
            self.is_full() ==> self.id() != other.id(),
            *old(self) == *self,
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.is_full() {
            if self.id() == other.id() {
                self.0.validate_2(&other.0);
            }
        }
    }
    
    /// Joins an `ExclusiveGhost` token back to this `ExclusiveGhostResource`.
    pub proof fn join(tracked &mut self, tracked other: ExclusiveGhost<T>)
        requires
            old(self).id() == other.id(),
        ensures
            old(self).is_empty() ==> {
                &&& self.id() == old(self).id()
                &&& self.view() == other.view()
                &&& self.is_full()
                &&& self.wf()
            },
            old(self).is_full() ==> false,
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        if self.is_full() {
            self.validate_with_exclusive(&other)
        } else {
            Self::join_helper(&mut self.0, other.0);
        }
    }

    proof fn join_helper(tracked r1: &mut Resource<ExclR<T>>, tracked r2: Resource<ExclR<T>>)
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
            let tracked mut tmp = Resource::<ExclR<T>>::alloc(ExclR::Unit);
            tracked_swap(r1, &mut tmp);
            let tracked mut r = tmp.join(r2);
            tracked_swap(r1, &mut r);
    }
    
    /// Updates the ghost value and returns the old value, requires that the exclusive ownership is available.
    pub proof fn update(tracked &mut self, value: T) -> (res: T)
        requires
            old(self).is_full(),
        ensures
            res == old(self).view(),
            self.id() == old(self).id(),
            self.view() == value,
            self.is_full(),
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

    /// Validates the internal consistency of this resource token.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        self.0.validate();
    }
}

} // verus!
