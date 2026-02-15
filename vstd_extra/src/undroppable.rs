use crate::external::manually_drop::*;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use vstd::prelude::*;

verus! {

pub trait Undroppable {
    type State;

    spec fn constructor_requires(self, s: Self::State) -> bool;

    spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool;

    #[verifier::returns(proof)]
    proof fn constructor_spec(self, tracked s: &mut Self::State)
        requires
            self.constructor_requires(*old(s)),
        ensures
            self.constructor_ensures(*old(s), *s),
    ;
}

pub struct NeverDrop<T: Undroppable>(pub T);

impl<T: Undroppable> NeverDrop<T> {
    #[verifier::external_body]
    pub fn new(t: T, Tracked(s): Tracked<&mut T::State>) -> (res: Self)
        requires
            t.constructor_requires(*old(s)),
        ensures
            t.constructor_ensures(*old(s), *s),
            res.0 == t,
    {
        proof {
            t.constructor_spec(s);
        }
        Self(t)
    }
}

impl<T: Undroppable> Deref for NeverDrop<T> {
    type Target = T;

    #[verifier::external_body]
    fn deref(&self) -> (res: &Self::Target)
        ensures
            res == &self.0,
    {
        &self.0
    }
}

impl<T: Undroppable> View for NeverDrop<T> {
    type V = T;

    open spec fn view(&self) -> (res: Self::V) {
        self.0
    }
}

} // verus!
