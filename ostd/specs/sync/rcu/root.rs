// SPDX-License-Identifier: MPL-2.0
//! Allocation identities for a native IRC11 root publication history.
//!
//! # Verified Properties
//!
//! Every non-null message names a registered allocation; null messages have no
//! allocation ID. Appending a newly registered allocation preserves earlier
//! messages, while publishing the same registration again preserves its ID.
//! Timestamps may have gaps and are distinct from allocation IDs.
//!
//! This layer tracks publication identity only. Physical ownership, reader
//! protection, and detachment evidence must be supplied by the RCU protocol.
//! In particular, persistent block information alone does not make a load safe
//! or authorize publishing a previously reclaimed allocation.
use vstd::{prelude::*, raw_ptr::ptr_null_mut, resource::Loc};
use vstd_extra::{
    atomic_irc11::{AtomicHistory, ThreadView},
    ownership::Inv,
};

use super::{RcuBlockInfo, RcuDomainAuth, RcuRegistration};

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

    /// Appends a publication with a fresh registration, or a null message.
    ///
    /// # Preconditions
    /// The previous history satisfies the invariant. The new message is appended
    /// after its maximum timestamp; this transition does not cover stores that
    /// insert a message earlier in modification order.
    ///
    /// # Postconditions
    /// Prior messages keep their allocation identities. The returned registration
    /// describes the new current pointer, even if its address appeared before.
    pub proof fn tracked_push_fresh<T>(
        tracked &mut self,
        prev: AtomicHistory<*mut T>,
        next: AtomicHistory<*mut T>,
        new_timestamp: nat,
        value: *mut T,
        message_view: ThreadView,
    ) -> (tracked res: Option<RcuRegistration<T>>)
        requires
            rcu_root_history_inv(prev, *old(self)),
            old(self).current_timestamp() < new_timestamp,
            next == prev.insert(new_timestamp, value, message_view),
        ensures
            rcu_root_history_inv(next, *final(self)),
            final(self).domain() == old(self).domain(),
            final(self).domain_auth().retire_registry() == old(
                self,
            ).domain_auth().retire_registry(),
            final(self).current_timestamp() == new_timestamp,
            current_registration_matches(*final(self), res),
            (res is Some) == (value.addr() != 0),
            res matches Some(registration) ==> {
                &&& registration.0.ptr() == value
                &&& !old(self).objects().contains_key(registration.0.obj())
            },
            final(self).publications() == old(self).publications().insert(
                new_timestamp,
                match res {
                    Some(registration) => Some(registration.0.obj()),
                    None => None,
                },
            ),
            match res {
                Some(registration) => final(self).objects() == old(self).objects().insert(
                    registration.0.obj(),
                    value.addr(),
                ),
                None => final(self).objects() == old(self).objects(),
            },
    {
        let tracked res = if value.addr() == 0 {
            self.publications = self.publications.insert(new_timestamp, None);
            None
        } else {
            let tracked registration = self.domain.tracked_register(value);
            self.publications = self.publications.insert(new_timestamp, Some(registration.0.obj()));
            Some(registration)
        };
        self.current_timestamp = new_timestamp;

        assert forall|ts: nat| next.contains_timestamp(ts) implies {
            match #[trigger] self.publications()[ts] {
                None => next.value(ts).addr() == 0,
                Some(obj) => {
                    &&& next.value(ts).addr() != 0
                    &&& self.objects().contains_pair(obj, next.value(ts).addr())
                },
            }
        } by {
            if ts != new_timestamp {
                assert(prev.contains_timestamp(ts));
                assert(next.value(ts) == prev.value(ts));
                assert(self.publications()[ts] == old(self).publications()[ts]);
            }
        };
        res
    }

    /// Appends another message for an existing registration.
    ///
    /// # Preconditions
    /// The history satisfies the invariant, the timestamp is later than every
    /// existing message, and valid block information binds this exact pointer to
    /// this domain. The caller must separately justify publishing the allocation.
    ///
    /// # Postconditions
    /// The new message carries the same allocation ID. The domain and all earlier
    /// messages are preserved, and no new retire permission is created.
    pub proof fn tracked_push_registered<T>(
        tracked &mut self,
        prev: AtomicHistory<*mut T>,
        next: AtomicHistory<*mut T>,
        new_timestamp: nat,
        value: *mut T,
        message_view: ThreadView,
        tracked info: &RcuBlockInfo<T>,
    )
        requires
            rcu_root_history_inv(prev, *old(self)),
            old(self).current_timestamp() < new_timestamp,
            next == prev.insert(new_timestamp, value, message_view),
            info.domain() == old(self).domain(),
            info.ptr() == value,
            info.inv(),
        ensures
            rcu_root_history_inv(next, *final(self)),
            final(self).domain_auth() == old(self).domain_auth(),
            final(self).domain() == old(self).domain(),
            final(self).objects() == old(self).objects(),
            final(self).current_timestamp() == new_timestamp,
            final(self).publications() == old(self).publications().insert(
                new_timestamp,
                Some(info.obj()),
            ),
    {
        self.domain.lemma_block_info_agree(info);
        info.lemma_address();
        self.publications = self.publications.insert(new_timestamp, Some(info.obj()));
        self.current_timestamp = new_timestamp;

        assert forall|ts: nat| next.contains_timestamp(ts) implies {
            match #[trigger] self.publications()[ts] {
                None => next.value(ts).addr() == 0,
                Some(obj) => {
                    &&& next.value(ts).addr() != 0
                    &&& self.objects().contains_pair(obj, next.value(ts).addr())
                },
            }
        } by {
            if ts != new_timestamp {
                assert(prev.contains_timestamp(ts));
                assert(next.value(ts) == prev.value(ts));
                assert(self.publications()[ts] == old(self).publications()[ts]);
            }
        };
    }
}

/// Proves that republishing an allocation preserves its ID across timestamp gaps.
///
/// # Preconditions
/// The pointer is non-null.
///
/// # Postconditions
/// Messages at timestamps 3 and 8 identify the same registration.
pub proof fn lemma_republication_preserves_allocation_id<T>(ptr: *mut T) -> (tracked res: (
    RcuRootGhost,
    RcuRegistration<T>,
))
    requires
        ptr.addr() != 0,
    ensures
        res.0.publications().dom() == Set::empty().insert(3nat).insert(8nat),
        res.0.publications()[3] == Some(res.1.0.obj()),
        res.0.publications()[8] == Some(res.1.0.obj()),
        current_registration_matches(res.0, Some(res.1)),
{
    let ghost view = ThreadView::empty();
    let ghost initial = AtomicHistory(Map::empty().insert(3nat, (ptr, view)));
    let tracked (mut root, registration) = RcuRootGhost::tracked_initial(ptr, initial, 3, view);
    let tracked registration = registration.tracked_unwrap();
    let ghost next = initial.insert(8, ptr, view);
    root.tracked_push_registered(initial, next, 8, ptr, view, &registration.0);
    (root, registration)
}

/// Proves that a null publication and later address reuse preserve old identities.
///
/// # Preconditions
/// The pointer is non-null.
///
/// # Postconditions
/// The two non-null messages have different allocation IDs at the same address;
/// the intervening null message has no allocation ID.
pub proof fn lemma_history_distinguishes_reused_address<T>(ptr: *mut T) -> (tracked res: (
    RcuRootGhost,
    RcuRegistration<T>,
    RcuRegistration<T>,
))
    requires
        ptr.addr() != 0,
    ensures
        res.0.publications().dom() == Set::empty().insert(3nat).insert(8nat).insert(13nat),
        res.0.publications()[3] == Some(res.1.0.obj()),
        res.0.publications()[8] is None,
        res.0.publications()[13] == Some(res.2.0.obj()),
        res.1.0.obj() != res.2.0.obj(),
        res.1.0.addr() == res.2.0.addr() == ptr.addr(),
        current_registration_matches(res.0, Some(res.2)),
{
    let ghost view = ThreadView::empty();
    let ghost initial = AtomicHistory(Map::empty().insert(3nat, (ptr, view)));
    let tracked (mut root, first) = RcuRootGhost::tracked_initial(ptr, initial, 3, view);
    let tracked first = first.tracked_unwrap();
    let ghost null = ptr_null_mut::<T>();
    let ghost removed = initial.insert(8, null, view);
    let tracked no_registration = root.tracked_push_fresh(initial, removed, 8, null, view);
    assert(no_registration is None);
    let ghost reused = removed.insert(13, ptr, view);
    let tracked second = root.tracked_push_fresh(removed, reused, 13, ptr, view);
    let tracked second = second.tracked_unwrap();
    (root, first, second)
}

} // verus!
