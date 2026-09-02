//! Persistent flags for recording that an event has occurred.
use crate::sum::Sum;
use vstd::{
    prelude::*,
    resource::{Loc, set::*},
};

verus! {

/// Unique authority to perform a one-shot transition.
pub tracked struct OneShotPending {
    auth: GhostSetAuth<()>,
}

/// Duplicable knowledge that a one-shot transition has occurred.
pub tracked struct OneShotSet {
    flag: GhostPersistentSingleton<()>,
}

impl OneShotPending {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        !self.auth@.contains(())
    }

    /// Creates a pending one-shot transition at a fresh resource location.
    pub proof fn new() -> (tracked result: Self) {
        let tracked (auth, _) = GhostSetAuth::new(Set::empty());
        Self { auth }
    }

    /// The resource location of this one-shot transition.
    pub closed spec fn id(self) -> Loc {
        self.auth.id()
    }

    /// Consumes the unique pending authority and marks the transition as set.
    pub proof fn set(tracked self) -> (tracked result: OneShotSet)
        ensures
            result.id() == self.id(),
    {
        use_type_invariant(&self);
        let tracked mut auth = self.auth;
        let tracked flag = auth.insert(()).persist();
        OneShotSet { flag }
    }

    /// A pending authority cannot coexist with set knowledge at the same location.
    pub proof fn incompatible(tracked &self, tracked set: &OneShotSet)
        ensures
            self.id() != set.id(),
    {
        if self.id() == set.id() {
            use_type_invariant(self);
            set.flag.agree(&self.auth);
        }
    }
}

impl OneShotSet {
    /// The resource location of this one-shot transition.
    pub closed spec fn id(self) -> Loc {
        self.flag.id()
    }

    /// Duplicates the knowledge that the transition is set.
    pub proof fn duplicate(tracked &self) -> (tracked result: Self)
        ensures
            result.id() == self.id(),
    {
        Self { flag: self.flag.duplicate() }
    }
}

impl Sum<OneShotPending, OneShotSet> {
    /// Ensures that a one-shot sum is set and returns duplicable knowledge of that fact.
    pub proof fn tracked_ensure_set(tracked &mut self) -> (tracked result: OneShotSet)
        ensures
            *final(self) is Right,
            result.id() == final(self)->Right_0.id(),
            match *old(self) {
                Sum::Left(pending) => final(self)->Right_0.id() == pending.id(),
                Sum::Right(set) => final(self)->Right_0.id() == set.id(),
            },
    {
        if *self is Right {
            self.tracked_borrow_right().duplicate()
        } else {
            let tracked replacement = OneShotPending::new();
            let tracked pending = self.tracked_swap_left(replacement);
            let tracked set = pending.set();
            let tracked result = set.duplicate();
            *self = Sum::Right(set);
            result
        }
    }
}

} // verus!
