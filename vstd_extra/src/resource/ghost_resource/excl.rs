//！ Exclusive ghost resource.
use vstd::modes::tracked_swap;
use vstd::pcm::*;
use vstd::prelude::*;

use super::super::pcm::excl::*;

verus! {

pub type UniqueTokenStorage = ExclusiveGhostStorage<()>;

pub type UniqueToken = ExclusiveGhost<()>;

/// A wrapper around `Resource<ExclR<T>>` that provides (optional) exclusive ownership of a value of type `T`.
/// For actual usage, we recommend `ExclusiveGhostStorage` and `ExclusiveGhost`.
pub tracked struct ExclusiveGhostResource<T> {
    tracked r: Resource<ExclR<T>>,
}

impl<T> ExclusiveGhostResource<T> {
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn value(self) -> T {
        self.r.value().value()
    }

    pub open spec fn view(self) -> T {
        self.value()
    }

    pub closed spec fn pcm(self) -> ExclR<T> {
        self.r.value()
    }

    pub open spec fn is_empty(self) -> bool {
        self.pcm() is Unit
    }

    pub open spec fn is_full(self) -> bool {
        self.pcm() is Excl
    }

    pub proof fn alloc(value: T) -> (tracked res: Self)
        ensures
            res.view() == value,
            res.is_full(),
    {
        Self { r: Resource::<ExclR<T>>::alloc(ExclR::new(value)) }
    }

    pub proof fn validate(tracked &self)
        ensures
            self.is_empty() || self.is_full(),
            self.is_empty() <==> !self.is_full(),
            self.is_full() <==> !self.is_empty(),
    {
        self.r.validate();
    }

    pub proof fn is_exclusive(tracked &mut self, tracked other: &Self)
        ensures
            self.is_full() && other.is_full() ==> self.id() != other.id(),
            *old(self) == *self,
    {
        if self.is_full() && other.is_full() {
            if self.id() == other.id() {
                self.r.validate_2(&other.r);
            }
        }
    }

    pub proof fn take(tracked &mut self) -> (tracked res: Self)
        requires
            old(self).is_full(),
        ensures
            res == *old(self),
            old(self).id() == self.id(),
            self.is_empty(),
    {
        let tracked mut empty = Resource::<ExclR<T>>::create_unit(self.id());
        tracked_swap(&mut self.r, &mut empty);
        Self { r: empty }
    }

    pub proof fn join(tracked &mut self, tracked other: Self)
        requires
            old(self).is_empty(),
            other.is_full(),
            old(self).id() == other.id(),
        ensures
            *self == other,
    {
        let tracked mut other = other;
        tracked_swap(&mut self.r, &mut other.r);
    }

    pub proof fn update(tracked &mut self, value: T)
        requires
            old(self).is_full(),
        ensures
            self.is_full(),
            self.id() == old(self).id(),
            self.view() == value,
    {
        let tracked mut resource = self.take();
        let tracked r = resource.r;
        let tracked r = r.update(ExclR::new(value));
        self.join(Self { r });
    }
}

/// An `ExclusiveGhost` always provides exclusive ownership of a value of type `T`.
pub tracked struct ExclusiveGhost<T>(ExclusiveGhostResource<T>);

impl<T> ExclusiveGhost<T> {
    pub closed spec fn id(self) -> Loc {
        self.0.id()
    }

    pub closed spec fn value(self) -> T {
        self.0.value()
    }

    pub open spec fn view(self) -> T {
        self.value()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.0.is_full()
    }

    pub proof fn alloc(value: T) -> (tracked res: Self)
        ensures
            res.view() == value,
    {
        Self(ExclusiveGhostResource::alloc(value))
    }

    pub proof fn update(tracked &mut self, value: T)
        ensures
            self.id() == old(self).id(),
            self.view() == value,
    {
        use_type_invariant(&*self);
        self.0.update(value);
    }

    proof fn is_exclusive(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *self,
            self.id() != other.id(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.0.is_exclusive(&other.0);
    }
}

// An `ExclusiveGhostStorage` can split and join `ExclusiveGhost`, it can be empty or full.
pub tracked struct ExclusiveGhostStorage<T>(ExclusiveGhostResource<T>);

impl<T> ExclusiveGhostStorage<T> {
    pub closed spec fn id(self) -> Loc {
        self.0.id()
    }

    pub closed spec fn value(self) -> T {
        self.0.value()
    }

    pub open spec fn view(self) -> T {
        self.value()
    }

    pub closed spec fn is_empty(self) -> bool {
        self.0.is_empty()
    }

    pub closed spec fn is_full(self) -> bool {
        self.0.is_full()
    }

    pub open spec fn wf(self) -> bool {
        &&& self.is_empty() || self.is_full()
        &&& self.is_empty() <==> !self.is_full()
        &&& self.is_full() <==> !self.is_empty()
    }

    #[verifier::type_invariant]
    pub open spec fn type_inv(self) -> bool {
        self.wf()
    }

    pub proof fn alloc(value: T) -> (tracked res: Self)
        ensures
            res.view() == value,
            res.is_full(),
            res.wf(),
    {
        Self(ExclusiveGhostResource::alloc(value))
    }

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
        let tracked r = self.0.take();
        ExclusiveGhost(r)
    }

    pub proof fn is_exclusive(tracked &mut self, tracked other: &ExclusiveGhost<T>)
        ensures
            self.is_full() ==> self.id() != other.id(),
            *old(self) == *self,
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.0.is_exclusive(&other.0);
    }

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
        use_type_invariant(&other);
        if self.is_full() {
            self.0.is_exclusive(&other.0);
        } else {
            self.validate();
            self.0.join(other.0);
        }
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        self.0.validate();
    }
}

} // verus!
