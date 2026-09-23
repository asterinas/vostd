// SPDX-License-Identifier: MPL-2.0
//! Typed identity and client resources for an IRC11 root publication history.
//!
//! # Verified Properties
//!
//! The latest non-null publication retains its linear registration and client
//! resource. Every registered allocation also has persistent typed block
//! information, and each non-null history message agrees with that information
//! by full pointer equality, including provenance.
//! Replacing the current publication transfers its previous linear resources to
//! the caller while retaining historical identities. Appended timestamps may
//! have gaps.
//!
//! Resolving a historical message returns identity only. Reader protection and
//! permission to reclaim an allocation belong to the surrounding RCU protocol.
use vstd::{prelude::*, resource::Loc};
use vstd_extra::{
    atomic_irc11::{AtomicHistory, ThreadView},
    ownership::Inv,
};

use super::{
    RcuBlockInfo, RcuRegistration,
    ownership::RcuOwnedObject,
    root::{RcuRootGhost, current_registration_matches, rcu_root_history_inv},
};

verus! {

broadcast use vstd::atomic_weak::group_view_history;

/// Current linear resources and persistent typed identities for one root.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRootOwnedGhost<T, O> {
    root: RcuRootGhost,
    current: Option<RcuOwnedObject<T, O>>,
    infos: Map<nat, RcuBlockInfo<T>>,
}

impl<T, O> Inv for RcuRootOwnedGhost<T, O> {
    open spec fn inv(self) -> bool {
        &&& self.root().domain_auth().inv()
        &&& current_registration_matches(self.root(), self.current_registration())
        &&& self.infos().dom() == self.root().objects().dom()
        &&& forall|obj: nat|
            self.infos().contains_key(obj) ==> {
                let info = #[trigger] self.infos()[obj];
                &&& info.inv()
                &&& info.domain() == self.domain()
                &&& info.obj() == obj
                &&& self.root().objects().contains_pair(obj, info.addr())
            }
        &&& match self.current_owned() {
            Some(owned) => {
                &&& owned.inv()
                &&& self.infos().contains_key(owned.block_info().obj())
                &&& equal(self.infos()[owned.block_info().obj()].ptr(), owned.block_info().ptr())
            },
            None => true,
        }
    }
}

/// Agreement between native history messages and exact registered pointers.
pub open spec fn rcu_owned_root_history_inv<T, O>(
    history: AtomicHistory<*mut T>,
    root: RcuRootOwnedGhost<T, O>,
) -> bool {
    &&& root.inv()
    &&& rcu_root_history_inv(history, root.root())
    &&& forall|ts: nat|
        history.contains_timestamp(ts) ==> {
            match #[trigger] root.root().publications()[ts] {
                Some(obj) => equal(root.infos()[obj].ptr(), history.value(ts)),
                None => true,
            }
        }
}

impl<T, O> RcuRootOwnedGhost<T, O> {
    /// Allocation identity metadata paired with the atomic history.
    pub closed spec fn root(self) -> RcuRootGhost {
        self.root
    }

    /// Protection domain of every retained registration.
    pub open spec fn domain(self) -> Loc {
        self.root().domain()
    }

    /// Persistent typed identities indexed by allocation ID.
    pub closed spec fn infos(self) -> Map<nat, RcuBlockInfo<T>> {
        self.infos
    }

    /// Linear resources of the current non-null publication, if any.
    pub closed spec fn current_owned(self) -> Option<RcuOwnedObject<T, O>> {
        self.current
    }

    /// Registration paired with the current publication.
    pub open spec fn current_registration(self) -> Option<RcuRegistration<T>> {
        match self.current_owned() {
            Some(owned) => Some(owned.registration()),
            None => None,
        }
    }

    /// Client resource paired with the current publication.
    pub open spec fn current_ownership(self) -> Option<O> {
        match self.current_owned() {
            Some(owned) => Some(owned.ownership()),
            None => None,
        }
    }

    /// Initializes a root while retaining its registration and client resource.
    pub proof fn tracked_initial(
        ptr: *mut T,
        tracked ownership: Option<O>,
        history: AtomicHistory<*mut T>,
        timestamp: nat,
        message_view: ThreadView,
    ) -> (tracked res: Self)
        requires
            (ownership is Some) == (ptr.addr() != 0),
            history.is_singleton(timestamp, (ptr, message_view)),
        ensures
            rcu_owned_root_history_inv(history, res),
            res.root().current_timestamp() == timestamp,
            res.current_ownership() == ownership,
            match res.current_owned() {
                Some(owned) => {
                    &&& ptr.addr() != 0
                    &&& equal(owned.block_info().ptr(), ptr)
                    &&& res.infos().dom() == Set::empty().insert(owned.block_info().obj())
                },
                None => {
                    &&& ptr.addr() == 0
                    &&& res.infos().dom() == Set::<nat>::empty()
                },
            },
    {
        let tracked (root, registration) = RcuRootGhost::tracked_initial(
            ptr,
            history,
            timestamp,
            message_view,
        );
        let tracked mut infos = Map::<nat, RcuBlockInfo<T>>::tracked_empty();
        let tracked current = match registration {
            Some(registration) => {
                let ghost obj = registration.0.obj();
                let tracked info = registration.0.tracked_duplicate();
                infos.tracked_insert(obj, info);
                assert forall|registered: nat| infos.contains_key(registered) implies {
                    let saved = #[trigger] infos[registered];
                    &&& saved.inv()
                    &&& saved.domain() == root.domain()
                    &&& saved.obj() == registered
                    &&& root.objects().contains_pair(registered, saved.addr())
                } by {
                    assert(registered == obj);
                };
                Some(RcuOwnedObject::tracked_new(registration, ownership.tracked_unwrap()))
            },
            None => None,
        };
        let tracked res = Self { root, current, infos };
        assert(res.inv());
        assert forall|ts: nat| history.contains_timestamp(ts) implies {
            match #[trigger] res.root().publications()[ts] {
                Some(obj) => equal(res.infos()[obj].ptr(), history.value(ts)),
                None => true,
            }
        } by {
            assert(ts == timestamp);
        };
        res
    }

    /// Appends a fresh registration or null message, returning the previous client resource.
    ///
    /// This transfers bookkeeping resources only. It does not certify that the
    /// previous allocation is detached from every link or safe to reclaim.
    pub proof fn tracked_push_fresh(
        tracked &mut self,
        prev: AtomicHistory<*mut T>,
        next: AtomicHistory<*mut T>,
        new_timestamp: nat,
        value: *mut T,
        message_view: ThreadView,
        tracked ownership: Option<O>,
    ) -> (tracked previous: Option<RcuOwnedObject<T, O>>)
        requires
            rcu_owned_root_history_inv(prev, *old(self)),
            old(self).root().current_timestamp() < new_timestamp,
            next == prev.insert(new_timestamp, value, message_view),
            (ownership is Some) == (value.addr() != 0),
        ensures
            rcu_owned_root_history_inv(next, *final(self)),
            final(self).domain() == old(self).domain(),
            final(self).root().domain_auth().retire_registry() == old(
                self,
            ).root().domain_auth().retire_registry(),
            final(self).root().current_timestamp() == new_timestamp,
            final(self).current_ownership() == ownership,
            final(self).root().publications() == old(self).root().publications().insert(
                new_timestamp,
                match final(self).current_owned() {
                    Some(owned) => Some(owned.block_info().obj()),
                    None => None,
                },
            ),
            forall|obj: nat| #[trigger]
                old(self).infos().contains_key(obj) ==> {
                    &&& final(self).infos().contains_key(obj)
                    &&& final(self).infos()[obj] == old(self).infos()[obj]
                },
            match final(self).current_owned() {
                Some(owned) => {
                    &&& value.addr() != 0
                    &&& equal(owned.block_info().ptr(), value)
                    &&& !old(self).infos().contains_key(owned.block_info().obj())
                    &&& final(self).infos().dom() == old(self).infos().dom().insert(
                        owned.block_info().obj(),
                    )
                },
                None => {
                    &&& value.addr() == 0
                    &&& final(self).infos() == old(self).infos()
                },
            },
        returns
            old(self).current_owned(),
    {
        let tracked previous = if self.current is Some {
            Some(self.current.tracked_take())
        } else {
            None
        };
        let tracked registration = self.root.tracked_push_fresh(
            prev,
            next,
            new_timestamp,
            value,
            message_view,
        );
        let tracked current = match registration {
            Some(registration) => {
                let ghost obj = registration.0.obj();
                let tracked info = registration.0.tracked_duplicate();
                self.infos.tracked_insert(obj, info);
                assert forall|registered: nat| self.infos.contains_key(registered) implies {
                    let saved = #[trigger] self.infos[registered];
                    &&& saved.inv()
                    &&& saved.domain() == self.domain()
                    &&& saved.obj() == registered
                    &&& self.root().objects().contains_pair(registered, saved.addr())
                } by {
                    if registered != obj {
                        assert(old(self).infos().contains_key(registered));
                        assert(self.infos[registered] == old(self).infos()[registered]);
                        assert(old(self).root().objects().contains_pair(
                            registered,
                            self.infos[registered].addr(),
                        ));
                    }
                };
                Some(RcuOwnedObject::tracked_new(registration, ownership.tracked_unwrap()))
            },
            None => None,
        };
        self.current = current;
        assert(self.inv());
        assert forall|ts: nat| next.contains_timestamp(ts) implies {
            match #[trigger] self.root().publications()[ts] {
                Some(obj) => equal(self.infos()[obj].ptr(), next.value(ts)),
                None => true,
            }
        } by {
            if ts != new_timestamp {
                assert(prev.contains_timestamp(ts));
                assert(next.value(ts) == prev.value(ts));
                assert(self.root().publications()[ts] == old(self).root().publications()[ts]);
                match old(self).root().publications()[ts] {
                    Some(obj) => {
                        assert(old(self).infos().contains_key(obj));
                        assert(self.infos()[obj] == old(self).infos()[obj]);
                    },
                    None => {},
                }
            }
        };
        previous
    }

    /// Copies a message's typed allocation identity without borrowing its client resource.
    pub proof fn tracked_info_at(
        tracked &self,
        history: AtomicHistory<*mut T>,
        timestamp: nat,
    ) -> (tracked res: Option<RcuBlockInfo<T>>)
        requires
            rcu_owned_root_history_inv(history, *self),
            history.contains_timestamp(timestamp),
        ensures
            match (self.root().published_at(timestamp), res) {
                (None, None) => history.value(timestamp).addr() == 0,
                (Some(object), Some(info)) => {
                    &&& info.inv()
                    &&& info.domain() == object.domain
                    &&& object.domain == self.domain()
                    &&& info.obj() == object.obj
                    &&& info.addr() == object.addr
                    &&& equal(info.ptr(), history.value(timestamp))
                    &&& self.infos().contains_key(info.obj())
                    &&& equal(info.ptr(), self.infos()[info.obj()].ptr())
                },
                _ => false,
            },
    {
        match self.root.publications()[timestamp] {
            Some(obj) => {
                let tracked info = self.infos.tracked_borrow(obj);
                Some(info.tracked_duplicate())
            },
            None => None,
        }
    }
}

} // verus!
