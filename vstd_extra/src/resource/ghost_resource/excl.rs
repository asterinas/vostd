//！ Exclusive ghost resource.
use vstd::modes::tracked_swap;
use vstd::prelude::*;
use vstd::resource::algebra::{Resource, ResourceAlgebra};
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::Loc;

verus! {

pub type UniqueToken = ExclusiveGhost<()>;

/// `ExclusiveGhost` is a token that always provides exclusive access to a ghost value of type `T`.
/// No two `ExclusiveGhost` tokens can have the same id.
pub tracked struct ExclusiveGhost<T>(Resource<ExclusiveRA<T>>);

impl<T> ExclusiveGhost<T> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.0.loc()
    }

    /// Returns the underlying upstream exclusive resource-algebra element.
    pub closed spec fn pcm(self) -> ExclusiveRA<T> {
        self.0.value()
    }

    /// Returns the ghost value of type `T`.
    pub open spec fn value(self) -> T {
        self.pcm()->Exclusive_0
    }

    /// Returns the ghost value of type `T`, an alias of `Self::value()`.
    pub open spec fn view(self) -> T {
        self.value()
    }

    /// Type invariant: the PCM element must be `Excl`.
    pub open spec fn wf(self) -> bool {
        self.pcm() is Exclusive
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    spec fn type_inv_inner(r: ExclusiveRA<T>) -> bool {
        r is Exclusive
    }

    /// Allocates a new `ExclusiveGhost` with the given value。
    pub proof fn alloc(value: T) -> (tracked res: Self)
        ensures
            res.view() == value,
            res.wf(),
    {
        Self(Resource::<ExclusiveRA<T>>::alloc(ExclusiveRA::Exclusive(value)))
    }

    /// Updates the ghost value and returns the old value.
    pub proof fn update(tracked &mut self, value: T) -> (res: T)
        ensures
            final(self).id() == old(self).id(),
            final(self).view() == value,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        Self::update_helper(&mut self.0, value)
    }

    proof fn update_helper(tracked r: &mut Resource<ExclusiveRA<T>>, value: T) -> (res: T)
        requires
            Self::type_inv_inner(old(r).value()),
            old(r).value() is Exclusive,
        ensures
            Self::type_inv_inner(final(r).value()),
            final(r).value() is Exclusive,
            final(r).loc() == old(r).loc(),
            res == old(r).value()->Exclusive_0,
            final(r).value()->Exclusive_0 == value,
    {
        let ghost res = r.value()->Exclusive_0;
        let tracked mut tmp = Resource::<ExclusiveRA<T>>::alloc(
            ExclusiveRA::Exclusive(arbitrary()),
        );
        tracked_swap(r, &mut tmp);
        assert forall|frame: ExclusiveRA<T>|
            #![trigger ExclusiveRA::<T>::op(tmp.value(), frame).valid()]
            ExclusiveRA::<T>::op(tmp.value(), frame).valid() implies ExclusiveRA::<T>::op(
            ExclusiveRA::Exclusive(value),
            frame,
        ).valid() by {}
        let tracked mut r1 = tmp.update(ExclusiveRA::Exclusive(value));
        tracked_swap(r, &mut r1);
        res
    }

    /// The existence of two `ExclusiveGhost` tokens ensures that they do not have the same id.
    pub proof fn validate_with_other(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *final(self),
            final(self).id() != other.id(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.0.validate_2(&other.0.as_ref());
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

} // verus!
