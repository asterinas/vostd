use core::{marker::PhantomData, ops::Deref};
use vstd::prelude::*;
use vstd::resource::Loc;

use crate::resource::ghost_resource::excl::ExclusiveGhost;

verus! {

/// A protocol for associating a value with a permission used by its verified
/// drop implementation.
///
/// This trait only defines the shape of the protocol. Implementing it does not
/// by itself guarantee that [`TrackDrop::Obligation`] is linear, unforgeable,
/// or authoritatively tied to [`TrackDrop::State`]. In particular, an
/// implementation may intentionally use a trivial obligation and perform no
/// drop-permission checking.
///
/// Implementations that rely on this protocol for safety are responsible for
/// establishing all of the following properties in their concrete
/// specifications and proofs:
///
/// - an issued obligation is associated with the value for which it was
///   issued;
/// - the obligation cannot be forged or duplicated;
/// - the state records enough authoritative information to detect a lost
///   outstanding obligation; and
/// - [`Drop::drop`] consumes the obligation and performs the corresponding
///   state transition exactly once.
pub trait TrackDrop: Sized {
    /// A ghost state that originally holds the authoritative drop permission.
    type State;

    /// The type of the drop permission.
    ///
    /// This permission does not necessarily represent the full permission to
    /// drop the value, as [`TrackDrop::drop_requires`] still takes a
    /// [`TrackDrop::State`] parameter.
    type Obligation;

    spec fn tracked_redeem_requires(self, s: Self::State) -> bool;

    spec fn tracked_redeem_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool;

    /// Gives the drop permission to the value.
    proof fn tracked_redeem(self, tracked s: &mut Self::State) -> (tracked obl: Self::Obligation)
        requires
            self.tracked_redeem_requires(*old(s)),
        ensures
            self.tracked_redeem_ensures(*old(s), *final(s), obl),
    ;

    /// Precondition of [`Drop::drop`].
    spec fn drop_requires(self, s: Self::State, obl: Self::Obligation) -> bool;

    /// Postcondition of [`Drop::drop`].
    spec fn drop_ensures(self, s0: Self::State, s1: Self::State, obl: Self::Obligation) -> bool;
}

pub trait Drop: TrackDrop {
    fn drop(self, Tracked(s): Tracked<&mut Self::State>, Tracked(obl): Tracked<Self::Obligation>)
        requires
            self.drop_requires(*old(s), obl),
        ensures
            self.drop_ensures(*old(s), *final(s), obl),
    ;
}

pub struct ManuallyDrop<T: TrackDrop> {
    value: T,
    tracked_obligation: Tracked<T::Obligation>,
}

impl<T: TrackDrop> ManuallyDrop<T> {
    pub fn new(t: T, obligaton: Tracked<T::Obligation>) -> (res: Self)
        ensures
            res@ == t,
            res.obligation() == obligaton@,
    {
        Self { value: t, tracked_obligation: obligaton }
    }

    pub fn into_inner(self) -> (res: (T, Tracked<T::Obligation>))
        ensures
            res.0 == self@,
            res.1@ == self.obligation(),
    {
        (self.value, self.tracked_obligation)
    }
}

impl<T: TrackDrop> Deref for ManuallyDrop<T> {
    type Target = T;

    fn deref(&self) -> (res: &Self::Target)
        ensures
            *res == self@,
    {
        &self.value
    }
}

impl<T: TrackDrop> View for ManuallyDrop<T> {
    type V = T;

    closed spec fn view(&self) -> (res: Self::V) {
        self.value
    }
}

impl<T: TrackDrop> ManuallyDrop<T> {
    pub closed spec fn obligation(self) -> T::Obligation {
        self.tracked_obligation@
    }
}

} // verus!
verus! {

#[verifier::reject_recursive_types(R)]
pub tracked struct DropObligation<R> {
    inner: ExclusiveGhost<R>,
}

impl<R> DropObligation<R> {
    pub closed spec fn value(self) -> R {
        self.inner.view()
    }

    /// Unique identifier of this token.
    pub closed spec fn id(self) -> Loc {
        self.inner.id()
    }

    /// Mint a fresh obligation token. S.
    pub proof fn tracked_mint(value: R) -> (tracked res: DropObligation<R>)
        ensures
            res.value() == value,
    {
        DropObligation { inner: ExclusiveGhost::alloc(value) }
    }

    /// Two outstanding obligations have distinct `Loc`s.
    pub proof fn validate_with_other(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *final(self),
            final(self).id() != other.id(),
    {
        self.inner.validate_with_other(&other.inner);
    }
}

} // verus!
