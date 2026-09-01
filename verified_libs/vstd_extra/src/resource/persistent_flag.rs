//! A persistent flag for recording that an event has occurred.
//!
//! [`GhostFlagAuth`] is the authoritative state of the flag. Once it is set,
//! [`GhostPersistentFlag`] provides duplicable knowledge that it remains set.
use vstd::{
    prelude::*,
    resource::{Loc, set::*},
};

verus! {

/// Authoritative ownership of a monotonic boolean flag.
pub tracked struct GhostFlagAuth {
    auth: GhostSetAuth<()>,
}

/// Duplicable knowledge that the corresponding [`GhostFlagAuth`] is set.
pub tracked struct GhostPersistentFlag {
    flag: GhostPersistentSingleton<()>,
}

impl GhostFlagAuth {
    /// Creates an unset flag at a fresh resource location.
    pub proof fn new() -> (tracked result: Self)
        ensures
            !result.is_set(),
    {
        let tracked (auth, _) = GhostSetAuth::new(Set::empty());
        Self { auth }
    }

    /// The resource location of this flag.
    pub closed spec fn id(self) -> Loc {
        self.auth.id()
    }

    /// Whether the flag has been set.
    pub closed spec fn is_set(self) -> bool {
        self.auth@.contains(())
    }

    /// Sets the flag and returns duplicable knowledge that it is set.
    pub proof fn set(tracked &mut self) -> (tracked result: GhostPersistentFlag)
        requires
            !old(self).is_set(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_set(),
            result.id() == final(self).id(),
    {
        let tracked flag = self.auth.insert(()).persist();
        GhostPersistentFlag { flag }
    }
}

impl GhostPersistentFlag {
    /// The resource location of this flag.
    pub closed spec fn id(self) -> Loc {
        self.flag.id()
    }

    /// Duplicates the persistent flag knowledge.
    pub proof fn duplicate(tracked &self) -> (tracked result: Self)
        ensures
            result.id() == self.id(),
    {
        Self { flag: self.flag.duplicate() }
    }

    /// Establishes that the corresponding authoritative flag is set.
    pub proof fn agree(tracked &self, tracked auth: &GhostFlagAuth)
        requires
            self.id() == auth.id(),
        ensures
            auth.is_set(),
    {
        self.flag.agree(&auth.auth);
    }
}

} // verus!
