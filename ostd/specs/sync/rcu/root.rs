// SPDX-License-Identifier: MPL-2.0
//! Allocation identities for a native IRC11 root publication history.
//!
//! # Verified Properties
//!
//! Every non-null message names a registered allocation; null messages have no
//! allocation ID. Initialization creates a fresh registration for a non-null
//! pointer and returns its linear base retire permission to the caller.
//! Native timestamps are independent of allocation IDs.
//!
//! This layer tracks publication identity only. Physical ownership, reader
//! protection, and detachment evidence must be supplied by the RCU protocol.
//! In particular, persistent block information alone does not make a load safe
//! or authorize publishing a previously reclaimed allocation.
use vstd::{prelude::*, resource::Loc};
use vstd_extra::{
    atomic_irc11::{AtomicHistory, ThreadView},
    ownership::Inv,
};

use super::{RcuDomainAuth, RcuRegistration};

verus! {

broadcast use vstd::atomic_weak::group_view_history;

/// Allocation identity attached to a non-null publication.
pub ghost struct RcuPublishedObject {
    pub domain: Loc,
    pub obj: nat,
    pub addr: usize,
}

/// Registration metadata paired with an atomic root's modification history.
pub tracked struct RcuRootGhost {
    domain: RcuDomainAuth,
    ghost publications: Map<nat, Option<nat>>,
    ghost current_timestamp: nat,
}

/// Agreement of persistent identity, linear permission, and publication.
pub open spec fn registration_matches_publication<T>(
    registration: RcuRegistration<T>,
    object: RcuPublishedObject,
) -> bool {
    &&& registration.0.inv()
    &&& registration.1.inv()
    &&& registration.0.domain() == object.domain
    &&& registration.0.obj() == object.obj
    &&& registration.0.addr() == object.addr
    &&& registration.0.obj() == registration.1.obj()
    &&& registration.0.domain() == registration.1.domain()
    &&& registration.0.ptr() == registration.1.ptr()
}

/// The current publication's registration, including its unique permission.
pub open spec fn current_registration_matches<T>(
    root: RcuRootGhost,
    registration: Option<RcuRegistration<T>>,
) -> bool {
    match (root.current(), registration) {
        (None, None) => true,
        (Some(object), Some(registration)) => {
            &&& registration_matches_publication(registration, object)
            &&& registration.1.belongs_to(root.domain_auth())
        },
        _ => false,
    }
}

/// Agreement between a native pointer history and its allocation registry.
pub open spec fn rcu_root_history_inv<T>(
    history: AtomicHistory<*mut T>,
    root: RcuRootGhost,
) -> bool {
    &&& root.domain_auth().inv()
    &&& root.publications().dom() == history.dom()
    &&& history.is_max_timestamp(root.current_timestamp())
    &&& forall|ts: nat|
        history.contains_timestamp(ts) ==> {
            match #[trigger] root.publications()[ts] {
                None => history.value(ts).addr() == 0,
                Some(obj) => {
                    &&& history.value(ts).addr() != 0
                    &&& root.objects().contains_pair(obj, history.value(ts).addr())
                },
            }
        }
}

impl RcuRootGhost {
    /// Domain authority retained by this root's publication registry.
    pub closed spec fn domain_auth(self) -> RcuDomainAuth {
        self.domain
    }

    /// Stable identity of the root's allocation domain.
    pub closed spec fn domain(self) -> Loc {
        self.domain.id()
    }

    /// All allocation registrations, including historical publications.
    pub closed spec fn objects(self) -> Map<nat, usize> {
        self.domain.objects()
    }

    /// Allocation ID recorded for each timestamp, or `None` for a null message.
    pub closed spec fn publications(self) -> Map<nat, Option<nat>> {
        self.publications
    }

    /// Timestamp of the latest publication.
    pub closed spec fn current_timestamp(self) -> nat {
        self.current_timestamp
    }

    /// Resolves a history message to its registered allocation identity.
    pub open spec fn published_at(self, timestamp: nat) -> Option<RcuPublishedObject>
        recommends
            self.publications().contains_key(timestamp),
    {
        match self.publications()[timestamp] {
            Some(obj) => Some(
                RcuPublishedObject { domain: self.domain(), obj, addr: self.objects()[obj] },
            ),
            None => None,
        }
    }

    /// Allocation identity of the latest message.
    pub open spec fn current(self) -> Option<RcuPublishedObject>
        recommends
            self.publications().contains_key(self.current_timestamp()),
    {
        self.published_at(self.current_timestamp())
    }

    /// Initializes publication metadata for a newly created root atomic.
    ///
    /// # Preconditions
    /// The atomic history contains exactly the supplied initial message.
    ///
    /// # Postconditions
    /// History and registration agree. A non-null pointer receives one fresh
    /// registration whose linear permission is returned to the caller.
    pub proof fn tracked_initial<T>(
        ptr: *mut T,
        history: AtomicHistory<*mut T>,
        timestamp: nat,
        message_view: ThreadView,
    ) -> (tracked res: (Self, Option<RcuRegistration<T>>))
        requires
            history.is_singleton(timestamp, (ptr, message_view)),
        ensures
            rcu_root_history_inv(history, res.0),
            res.0.current_timestamp() == timestamp,
            current_registration_matches(res.0, res.1),
            (res.1 is Some) == (ptr.addr() != 0),
            res.1 matches Some(registration) ==> {
                &&& registration.0.ptr() == ptr
                &&& res.0.publications()[timestamp] == Some(registration.0.obj())
            },
            match res.1 {
                Some(registration) => res.0.objects() == Map::empty().insert(
                    registration.0.obj(),
                    ptr.addr(),
                ),
                None => res.0.objects() == Map::empty(),
            },
    {
        let tracked mut domain = RcuDomainAuth::tracked_new();
        assert(history.is_max_timestamp(timestamp));
        assert(history.dom() == Set::empty().insert(timestamp)) by {
            assert forall|ts: nat|
                history.dom().contains(ts) <==> Set::empty().insert(timestamp).contains(ts) by {
                if history.dom().contains(ts) {
                    assert(history.contains_timestamp(ts));
                    assert(ts == timestamp);
                }
            };
        };
        if ptr.addr() == 0 {
            (
                RcuRootGhost {
                    domain,
                    publications: Map::empty().insert(timestamp, None),
                    current_timestamp: timestamp,
                },
                None,
            )
        } else {
            let tracked registration = domain.tracked_register(ptr);
            let ghost obj = registration.0.obj();
            (
                RcuRootGhost {
                    domain,
                    publications: Map::empty().insert(timestamp, Some(obj)),
                    current_timestamp: timestamp,
                },
                Some(registration),
            )
        }
    }
}

} // verus!
