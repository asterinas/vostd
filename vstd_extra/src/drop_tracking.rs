use core::{marker::PhantomData, ops::Deref};
use vstd::prelude::*;

verus! {

pub trait TrackDrop {
    type State;

    spec fn constructor_requires(self, s: Self::State) -> bool;

    spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool;

    #[verifier::returns(proof)]
    proof fn constructor_spec(self, tracked s: &mut Self::State)
        requires
            self.constructor_requires(*old(s)),
        ensures
            self.constructor_ensures(*old(s), *final(s)),
    ;

    spec fn drop_requires(self, s: Self::State) -> bool;

    spec fn drop_ensures(self, s0: Self::State, s1: Self::State) -> bool;

    proof fn drop_tracked(self, tracked s: &mut Self::State)
        requires
            self.drop_requires(*old(s)),
        ensures
            self.drop_ensures(*old(s), *final(s)),
    ;
}

pub trait Drop: TrackDrop {
    fn drop(self, Tracked(s): Tracked<Self::State>) -> (res: Tracked<Self::State>)
        requires
            self.drop_requires(s),
        ensures
            self.drop_ensures(s, res@),
    ;
}

pub struct ManuallyDrop<T: TrackDrop>(pub T);

impl<T: TrackDrop> ManuallyDrop<T> {
    #[verifier::external_body]
    pub fn new(t: T, Tracked(s): Tracked<&mut T::State>) -> (res: Self)
        requires
            t.constructor_requires(*old(s)),
        ensures
            t.constructor_ensures(*old(s), *final(s)),
            res.0 == t,
    {
        proof {
            t.constructor_spec(s);
        }
        Self(t)
    }
}

impl<T: Drop> ManuallyDrop<T> {
    pub fn drop(self, Tracked(s): Tracked<T::State>) -> (res: Tracked<T::State>)
        requires
            self.0.drop_requires(s),
        ensures
            self.0.drop_ensures(s, res@),
    {
        self.0.drop(Tracked(s))
    }
}

impl<T: TrackDrop> Deref for ManuallyDrop<T> {
    type Target = T;

    #[verifier::external_body]
    fn deref(&self) -> (res: &Self::Target)
        ensures
            res == &self.0,
    {
        &self.0
    }
}

impl<T: TrackDrop> View for ManuallyDrop<T> {
    type V = T;

    open spec fn view(&self) -> (res: Self::V) {
        self.0
    }
}

} // verus!
