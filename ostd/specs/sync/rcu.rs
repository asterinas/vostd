//! Weak-memory RCU base and traversal specification.
//!
//! This module models the shape of the traversal specification from the RCU
//! relaxed-memory paper:
//!
//! - the base layer provides registration-time allocation IDs, persistent
//!   block information, unique retire permissions, and the
//!   `Inactive(tid) <-> Guard(tid, X, G)` reader protocol;
//! - the traversal layer reasons about link histories (`RcuPointsTo`) and
//!   incoming-link histories (`RcuPointedBy`);
//! - concrete data structures instantiate the traversal trait.
//!
//! Allocation IDs, removed sets, link views, and incoming edges are all keyed
//! by AId, not by physical address. Physical addresses only appear in
//! `BlockInfo` and the guard's `address -> AId` protection map. This distinction
//! is required to handle stale weak-memory messages after address reuse.
//!
//! The module remains proof-only. The executable `Rcu<P>` adapter is a
//! direct-root specialization: replacing its atomic publication detaches the
//! owned `P` handle from that root. This must not be reused as the detach rule
//! for an internal node with arbitrary incoming links; such nodes require the
//! tracked `RcuPointedBy` transition from the traversal layer.
//!
//! The paper-level reclamation chain is connected through persistent reader
//! start snapshots, per-CPU closed-generation resources, physical read leases,
//! and type-erased callback reclaim permits. The linked-list acceptance path
//! additionally connects native internal-link loads and unlink CAS events to
//! AId-keyed traversal authority. Remaining limitations are integration
//! boundaries rather than missing logical steps: the linked-list adapter is
//! still private and acceptance-specific, `read_with()` retains a trusted
//! shared-reference bridge, and implicit Rust `Drop` cannot yet carry the
//! verified consuming transition.
use core::marker::PhantomData;

use crate::specs::mm::cpu::CpuId;

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::map::{GhostMapAuth, GhostPersistentPointsTo, GhostPointsTo};
use vstd::thread_view::Objective;
use vstd_extra::atomic_irc11::{
    AtomicHistory as Irc11History, AtomicId as Irc11AtomicId, AtomicPointsTo,
    ThreadView as Irc11ThreadView,
};

verus! {

broadcast use {vstd::atomic_weak::group_view_history, vstd::thread_view::group_thread_view_axioms};

pub type LinkIndex = nat;

pub type LinkEdge = (nat, LinkIndex);

/// Scheduler identity of the execution context that owns one RCU reader.
///
/// `session` is the fresh preemption-session resource identity created when
/// the scheduler checks a task in on `cpu`. Recording the full tuple prevents
/// an RCU guard from being detached, in the proof, from the preemption guard
/// that keeps its task on that CPU.
pub ghost struct RcuReaderContext {
    pub scheduler: Loc,
    pub task: Loc,
    pub session: Loc,
    pub cpu: CpuId,
    /// Implementation generation in which this reader started.
    ///
    /// For a [`super::rcu_cpu::CpuRcuReadGuardToken`], this is required to
    /// equal the persistent CPU participant generation. The legacy
    /// task-session generation must not be substituted here when the two
    /// authorities have not been connected.
    pub generation: nat,
}

/// Proof summary for a type-erased RCU callback.
///
/// The executable callback may close over any sized Rust value, but the RCU
/// proof only needs to know which logical object it will reclaim and which
/// grace-period generation retired that object. `domain` identifies the RCU
/// protection domain, and `obj` identifies the reclaimed allocation/object
/// inside that domain. `retire_view` is the retiring task's weak-memory view
/// after unlink and before the callback is enqueued; completion must eventually
/// prove that every CPU report has advanced beyond this view.
pub ghost struct RcuCallbackSummary {
    /// Scheduler whose CPU participants must complete the grace period.
    pub scheduler: Loc,
    /// The RCU protection domain whose grace period governs this callback.
    pub domain: Loc,
    /// Logical identity of the retired object inside `domain`.
    pub obj: nat,
    /// Root-atomic removal observation retained from `Retired(a, Q)`.
    pub removal: RcuRemovalObservation,
    /// Authoritative observation map that recorded `removal`.
    pub retire_observation_registry: Loc,
    /// The domain-local epoch in which `obj` was retired.
    pub retire_epoch: nat,
    /// Weak-memory observations that must precede safe reclamation.
    pub retire_view: Irc11ThreadView,
}

/// Persistent identity of one completed base-retirement transition.
///
/// The observation-registry identity is part of the record. A domain-local
/// allocation ID and a numerically equal removal observation are not enough to
/// compare resources unless they also belong to the same authoritative
/// observation map.
pub ghost struct RcuRetiredRecord {
    pub domain: Loc,
    pub obj: nat,
    pub removal: RcuRemovalObservation,
    pub retire_observation_registry: Loc,
}

impl RcuCallbackSummary {
    pub open spec fn retired_record(self) -> RcuRetiredRecord {
        RcuRetiredRecord {
            domain: self.domain,
            obj: self.obj,
            removal: self.removal,
            retire_observation_registry: self.retire_observation_registry,
        }
    }
}

/// The paper's detachment observation `Q` for a root publication.
///
/// A view observes this fact once it has advanced to at least `timestamp` in
/// the root atomic's modification history. The message at `timestamp` is the
/// first publication after the retired object ceased to be the root.
pub ghost struct RcuRemovalObservation {
    pub root: Loc,
    pub timestamp: nat,
    pub message_view: Irc11ThreadView,
}

impl RcuRemovalObservation {
    pub open spec fn observed_by(self, view: Irc11ThreadView) -> bool {
        view.contains(self.message_view)
    }
}

/// Logical identity attached to one non-null publication in an RCU root.
///
/// The paper distinguishes a physical address from an allocation ID because
/// an address may be reused after reclamation. `domain` identifies this RCU
/// registry, while `obj` identifies one registration within that domain. The
/// same address may therefore occur in multiple `RcuPublishedObject` values
/// without introducing an ABA-style identity collision.
pub ghost struct RcuPublishedObject {
    pub domain: Loc,
    pub obj: nat,
    pub addr: usize,
}

/// Resources created by one application of the paper's registration rule.
///
/// `BlockInfo` is persistent and may justify any number of publications. The
/// base retire permission is unique and must survive until traversal proves
/// that the registered allocation has been removed.
pub type RcuRegistration<T> = (RcuBlockInfo<T>, RcuBaseRetirePerm<T>);

/// Complete linear ownership associated with one registered allocation.
///
/// The RCU base protocol treats `ownership` abstractly. The executable OSTD
/// instance uses `P::Permission`, while proof examples may use `()` or another
/// client resource.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuOwnedObject<T, O> {
    registration: RcuRegistration<T>,
    ownership: O,
}

/// Complete ownership of a detached root after the base retire transition.
///
/// The persistent object identity justifies the erased callback summary,
/// `retired` proves that traversal removal happened, and `ownership` is the
/// physical resource consumed by the callback body.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRetiredOwnedObject<T, O> {
    object: RcuObjectId<T>,
    retired: RcuRetired<T>,
    ownership: O,
}

impl<T, O> RcuRetiredOwnedObject<T, O> {
    pub closed spec fn object(self) -> RcuObjectId<T> {
        self.object
    }

    pub closed spec fn retired(self) -> RcuRetired<T> {
        self.retired
    }

    pub closed spec fn ownership(self) -> O {
        self.ownership
    }

    pub closed spec fn domain(self) -> Loc {
        self.object().domain()
    }

    pub closed spec fn obj(self) -> nat {
        self.object().obj()
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.object().ptr()
    }

    pub proof fn tracked_into_parts(tracked self) -> (tracked res: (
        RcuObjectId<T>,
        RcuRetired<T>,
        O,
    ))
        ensures
            res.0 == self.object(),
            res.1 == self.retired(),
            res.2 == self.ownership(),
            res.0.domain() == res.1.domain(),
            res.0.obj() == res.1.obj(),
            res.0.ptr() == res.1.ptr(),
    {
        use_type_invariant(&self);
        (self.object, self.retired, self.ownership)
    }

    pub open spec fn wf(self) -> bool {
        &&& self.object().domain() == self.retired().domain()
        &&& self.object().obj() == self.retired().obj()
        &&& self.object().ptr() == self.retired().ptr()
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

impl<T, O> RcuOwnedObject<T, O> {
    pub closed spec fn registration(self) -> RcuRegistration<T> {
        self.registration
    }

    pub closed spec fn block_info(self) -> RcuBlockInfo<T> {
        self.registration().0
    }

    pub closed spec fn retire_perm(self) -> RcuBaseRetirePerm<T> {
        self.registration().1
    }

    pub closed spec fn ownership(self) -> O {
        self.ownership
    }

    pub proof fn tracked_into_parts(tracked self) -> (tracked res: (RcuRegistration<T>, O))
        ensures
            res.0 == self.registration(),
            res.1 == self.ownership(),
    {
        (self.registration, self.ownership)
    }
}

/// Agreement between one registration resource and publication metadata.
pub open spec fn registration_matches_publication<T>(
    registration: RcuRegistration<T>,
    object: RcuPublishedObject,
) -> bool {
    &&& registration.0.wf()
    &&& registration.1.wf()
    &&& registration.0.domain() == object.domain
    &&& registration.0.obj() == object.obj
    &&& registration.0.addr() == object.addr
    &&& registration.0.obj() == registration.1.obj()
    &&& registration.0.domain() == registration.1.domain()
    &&& registration.0.ptr() == registration.1.ptr()
}

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

/// Publication metadata paired with an RCU root's atomic message history.
///
/// Entry `publications[i]` describes atomic message `i`. A null message has no
/// allocation identity; a non-null message refers to an allocation ID obtained
/// from `RcuDomainAuth::tracked_register`. In particular, the allocation ID is
/// not the history index `i`.
///
/// This state intentionally does not contain the traversal removed set or a
/// grace-period epoch. In the paper, removal of an internal node belongs to
/// `SeenRemoved` and incoming-link histories, while expiration/reclamation
/// belongs to the base RCU protocol. A root store only detaches the directly
/// owned root publication; it cannot prove that an arbitrary internal node is
/// unreachable from every incoming link.
pub tracked struct RcuRootGhost {
    domain: RcuDomainAuth,
    ghost publications: Map<nat, Option<nat>>,
    ghost current_timestamp: nat,
}

impl RcuRootGhost {
    pub closed spec fn domain_auth(self) -> RcuDomainAuth {
        self.domain
    }

    pub closed spec fn domain(self) -> Loc {
        self.domain.id()
    }

    pub closed spec fn objects(self) -> Map<nat, usize> {
        self.domain.objects()
    }

    pub closed spec fn domain_wf(self) -> bool {
        self.domain.wf()
    }

    pub closed spec fn publications(self) -> Map<nat, Option<nat>> {
        self.publications
    }

    pub closed spec fn current_timestamp(self) -> nat {
        self.current_timestamp
    }

    pub open spec fn published_at(self, ts: nat) -> Option<RcuPublishedObject>
        recommends
            self.publications().contains_key(ts),
    {
        match self.publications()[ts] {
            Some(obj) => Some(
                RcuPublishedObject { domain: self.domain(), obj, addr: self.objects()[obj] },
            ),
            None => None,
        }
    }

    /// Allocation identity carried by the latest atomic message.
    pub open spec fn current(self) -> Option<RcuPublishedObject>
        recommends
            self.publications().contains_key(self.current_timestamp()),
    {
        self.published_at(self.current_timestamp())
    }

    /// Allocate a fresh publication registry containing the initial message.
    ///
    /// A non-null initial value is registered exactly once and the registration
    /// resources are returned to the caller. The root history retains only the
    /// allocation ID; it does not consume the unique retire permission.
    pub proof fn tracked_initial<T>(
        ptr: *mut T,
        history: Irc11History<*mut T>,
        timestamp: nat,
        message_view: Irc11ThreadView,
    ) -> (tracked res: (Self, Option<RcuRegistration<T>>))
        requires
            history.is_singleton(timestamp, (ptr, message_view)),
        ensures
            rcu_root_history_inv(history, res.0),
            (res.1 is Some) == (ptr.addr() != 0),
            res.1 is Some ==> res.1->Some_0.0.ptr() == ptr,
            res.1 is Some ==> res.1->Some_0.0.obj() == res.1->Some_0.1.obj(),
            res.1 is Some ==> res.1->Some_0.0.domain() == res.0.domain(),
            res.1 is Some ==> res.0.publications()[timestamp] == Some(res.1->Some_0.0.obj()),
            res.1 is Some ==> res.1->Some_0.0.wf(),
            match res.1 {
                Some(registration) => res.0.objects() == Map::empty().insert(
                    registration.0.obj(),
                    ptr.addr(),
                ),
                None => res.0.objects() == Map::empty(),
            },
            current_registration_matches(res.0, res.1),
            res.0.domain_auth().retired() == Set::<nat>::empty(),
            res.0.domain_auth().retire_observations() == Map::<nat, RcuRemovalObservation>::empty(),
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
            let tracked (block_info, retire_perm) = domain.tracked_register(ptr);
            let ghost obj = block_info.obj();
            assert(domain.objects().contains_pair(obj, ptr.addr()));
            (
                RcuRootGhost {
                    domain,
                    publications: Map::empty().insert(timestamp, Some(obj)),
                    current_timestamp: timestamp,
                },
                Some((block_info, retire_perm)),
            )
        }
    }

    /// Publish a freshly introduced allocation.
    ///
    /// This combines the paper's registration rule with the first publication
    /// of that registration. The returned resources must remain associated
    /// with the allocation; in particular, the retire permission is not part
    /// of the append-only atomic history.
    pub proof fn tracked_push_fresh<T>(
        tracked &mut self,
        prev: Irc11History<*mut T>,
        next: Irc11History<*mut T>,
        old_timestamp: nat,
        new_timestamp: nat,
        value: *mut T,
        message_view: Irc11ThreadView,
    ) -> (tracked res: Option<RcuRegistration<T>>)
        requires
            rcu_root_history_inv(prev, *old(self)),
            prev.is_max_timestamp(old_timestamp),
            new_timestamp == old_timestamp + 1,
            next == prev.insert(new_timestamp, value, message_view),
        ensures
            rcu_root_history_inv(next, *final(self)),
            final(self).domain() == old(self).domain(),
            final(self).domain_auth().retire_registry() == old(
                self,
            ).domain_auth().retire_registry(),
            final(self).domain_auth().reader_registry() == old(
                self,
            ).domain_auth().reader_registry(),
            final(self).domain_auth().retire_observation_registry() == old(
                self,
            ).domain_auth().retire_observation_registry(),
            final(self).domain_auth().retired() == old(self).domain_auth().retired(),
            final(self).domain_auth().retire_observations() == old(
                self,
            ).domain_auth().retire_observations(),
            (res is Some) == (value.addr() != 0),
            res is Some ==> res->Some_0.0.ptr() == value,
            res is Some ==> res->Some_0.0.obj() == res->Some_0.1.obj(),
            res is Some ==> !old(self).objects().contains_key(res->Some_0.0.obj()),
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
            current_registration_matches(*final(self), res),
    {
        let tracked res = if value.addr() == 0 {
            self.publications = self.publications.insert(new_timestamp, None);
            None
        } else {
            let tracked (block_info, retire_perm) = self.domain.tracked_register(value);
            let ghost obj = block_info.obj();
            self.publications = self.publications.insert(new_timestamp, Some(obj));
            Some((block_info, retire_perm))
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
            if ts == new_timestamp {
            } else {
                assert(prev.contains_timestamp(ts));
                assert(next.value(ts) == prev.value(ts));
                assert(self.publications()[ts] == old(self).publications()[ts]);
                match self.publications()[ts] {
                    Some(obj) => {
                        assert(old(self).objects().contains_pair(obj, prev.value(ts).addr()));
                        assert(self.objects().contains_pair(obj, next.value(ts).addr()));
                    },
                    None => {},
                }
            }
        };
        res
    }

    /// Re-publish an allocation that was registered earlier.
    ///
    /// Unlike [`tracked_push_fresh`](Self::tracked_push_fresh), this rule does
    /// not allocate a new AId. Every message published with the same persistent
    /// `BlockInfo` therefore carries the same allocation identity.
    pub proof fn tracked_push_registered<T>(
        tracked &mut self,
        prev: Irc11History<*mut T>,
        next: Irc11History<*mut T>,
        old_timestamp: nat,
        new_timestamp: nat,
        value: *mut T,
        message_view: Irc11ThreadView,
        tracked info: &RcuBlockInfo<T>,
    )
        requires
            rcu_root_history_inv(prev, *old(self)),
            prev.is_max_timestamp(old_timestamp),
            new_timestamp == old_timestamp + 1,
            next == prev.insert(new_timestamp, value, message_view),
            info.domain() == old(self).domain(),
            info.ptr() == value,
            info.wf(),
        ensures
            rcu_root_history_inv(next, *final(self)),
            final(self).domain() == old(self).domain(),
            final(self).domain_auth().retire_registry() == old(
                self,
            ).domain_auth().retire_registry(),
            final(self).domain_auth().reader_registry() == old(
                self,
            ).domain_auth().reader_registry(),
            final(self).domain_auth().retire_observation_registry() == old(
                self,
            ).domain_auth().retire_observation_registry(),
            final(self).domain_auth().retired() == old(self).domain_auth().retired(),
            final(self).domain_auth().retire_observations() == old(
                self,
            ).domain_auth().retire_observations(),
            final(self).objects() == old(self).objects(),
            final(self).publications() == old(self).publications().insert(
                new_timestamp,
                Some(info.obj()),
            ),
    {
        self.domain.lemma_block_info_agree(info);
        self.publications = self.publications.insert(new_timestamp, Some(info.obj()));
        self.current_timestamp = new_timestamp;
        assert(self.objects() == old(self).objects());

        assert forall|ts: nat| next.contains_timestamp(ts) implies {
            match #[trigger] self.publications()[ts] {
                None => next.value(ts).addr() == 0,
                Some(obj) => {
                    &&& next.value(ts).addr() != 0
                    &&& self.objects().contains_pair(obj, next.value(ts).addr())
                },
            }
        } by {
            if ts == new_timestamp {
                assert(info.addr() == value.addr());
                assert(value.addr() != 0);
                assert(self.publications()[ts] == Some(info.obj()));
                assert(self.objects().contains_pair(info.obj(), next.value(ts).addr()));
            } else {
                assert(prev.contains_timestamp(ts));
                assert(next.value(ts) == prev.value(ts));
                assert(self.publications()[ts] == old(self).publications()[ts]);
                match self.publications()[ts] {
                    Some(obj) => {
                        assert(old(self).objects().contains_pair(obj, prev.value(ts).addr()));
                        assert(self.objects().contains_pair(obj, next.value(ts).addr()));
                    },
                    None => {},
                }
            }
        };
    }
}

/// Agreement between the weak-memory message history and RCU allocation IDs.
pub open spec fn rcu_root_history_inv<T>(
    history: Irc11History<*mut T>,
    ghost: RcuRootGhost,
) -> bool {
    &&& ghost.domain_wf()
    &&& ghost.publications().dom() == history.dom()
    &&& history.is_max_timestamp(ghost.current_timestamp())
    &&& forall|ts: nat|
        history.contains_timestamp(ts) ==> {
            match #[trigger] ghost.publications()[ts] {
                None => history.value(ts).addr() == 0,
                Some(obj) => {
                    &&& history.value(ts).addr() != 0
                    &&& ghost.objects().contains_pair(obj, history.value(ts).addr())
                },
            }
        }
}

pub open spec fn rcu_history_inv<T>(nullable: bool, history: Irc11History<*mut T>) -> bool {
    &&& !history.dom().is_empty()
    &&& !nullable ==> forall|ts: nat|
        history.contains_timestamp(ts) ==> #[trigger] history.value(ts).addr() != 0
}

/// Scheduler registry used by the kernel's singleton RCU domain.
///
/// Scheduler integration must establish that every `RunningTaskContext`
/// passed to the global RCU API is checked out from this registry.
pub uninterp spec fn rcu_scheduler() -> Loc;

/// Immutable identity carried by an executable RCU root atomic.
///
/// Besides nullability, the key records the two resource locations needed to
/// associate read-side guard tokens with the same root invariant after the
/// invariant has been closed.
pub ghost struct RcuRootKey {
    pub nullable: bool,
    /// Scheduler registry whose canonical CPU participants protect this root.
    pub scheduler: Loc,
    pub domain: Loc,
    pub reader_registry: Loc,
    pub retire_observation_registry: Loc,
    pub reclaim_registry: Loc,
    pub active_lease_registry: Loc,
}

/// Typed ownership state paired with one executable RCU root atomic.
///
/// `root` owns the append-only publication registry. `current` owns the unique
/// registration resources for the latest non-null root value. Historical
/// messages retain only persistent allocation metadata, so replacing the root
/// can move the old unique retire permission out exactly once.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRootOwnedGhost<T, O = ()> {
    root: RcuRootGhost,
    current: Option<RcuOwnedObject<T, O>>,
    infos: Map<nat, RcuBlockInfo<T>>,
    ghost removals: Map<nat, RcuRemovalObservation>,
}

// The root ghost owns only global resource-algebra state. Its payload remains
// objective exactly when the client ownership stored in it is objective.
unsafe impl<T, O: Objective> Objective for RcuRootOwnedGhost<T, O> {

}

impl<T, O> RcuRootOwnedGhost<T, O> {
    pub closed spec fn root(self) -> RcuRootGhost {
        self.root
    }

    pub closed spec fn domain(self) -> Loc {
        self.root().domain()
    }

    pub closed spec fn publications(self) -> Map<nat, Option<nat>> {
        self.root().publications()
    }

    pub closed spec fn reader_registry(self) -> Loc {
        self.root().domain_auth().reader_registry()
    }

    pub closed spec fn retire_observation_registry(self) -> Loc {
        self.root().domain_auth().retire_observation_registry()
    }

    /// Agrees a persistent callback retirement fact with this root's
    /// authoritative removal map.
    pub proof fn lemma_retired_fact_agrees(tracked &self, tracked fact: &RcuRetiredFact)
        requires
            self.root().domain_wf(),
            self.removals() == self.root().domain_auth().retire_observations(),
            fact.wf(),
            fact.domain() == self.domain(),
            fact.retire_observation_registry() == self.retire_observation_registry(),
        ensures
            self.removals().contains_pair(fact.obj(), fact.removal()),
    {
        fact.lemma_observation_agrees(&self.root.domain);
    }

    pub open spec fn published_at(self, ts: nat) -> Option<RcuPublishedObject>
        recommends
            self.publications().contains_key(ts),
    {
        self.root().published_at(ts)
    }

    pub closed spec fn current_registration(self) -> Option<RcuRegistration<T>> {
        match self.current {
            Some(owned) => Some(owned.registration()),
            None => None,
        }
    }

    pub closed spec fn current_owned(self) -> Option<RcuOwnedObject<T, O>> {
        self.current
    }

    pub closed spec fn current_ownership(self) -> Option<O> {
        match self.current {
            Some(owned) => Some(owned.ownership()),
            None => None,
        }
    }

    pub closed spec fn infos(self) -> Map<nat, RcuBlockInfo<T>> {
        self.infos
    }

    pub closed spec fn removals(self) -> Map<nat, RcuRemovalObservation> {
        self.removals
    }

    pub open spec fn ownership_wf(self) -> bool {
        current_registration_matches(self.root(), self.current_registration())
    }

    /// Every registered allocation retains a persistent typed identity token.
    ///
    /// Entries are append-only. Retiring an object moves its unique ownership
    /// and retire permission out of `current`, but leaves this persistent
    /// `BlockInfo` available to justify stale weak-memory history reads.
    pub open spec fn infos_wf(self) -> bool {
        &&& self.infos().dom() == self.root().objects().dom()
        &&& match self.current_owned() {
            Some(owned) => {
                &&& self.infos().contains_key(owned.block_info().obj())
                &&& equal(self.infos()[owned.block_info().obj()].ptr(), owned.block_info().ptr())
            },
            None => true,
        }
        &&& forall|obj: nat|
            self.infos().contains_key(obj) ==> {
                let info = #[trigger] self.infos()[obj];
                &&& info.wf()
                &&& info.domain() == self.domain()
                &&& info.obj() == obj
                &&& self.root().objects().contains_pair(obj, info.addr())
            }
    }

    /// Root-history interpretation of the paper's detachment observations.
    ///
    /// Once `removals[obj] = ts`, no message at or after `ts` may publish that
    /// allocation ID again. The currently owned registration is therefore
    /// never in the removed domain.
    pub open spec fn removals_wf(self, history: Irc11History<*mut T>) -> bool {
        &&& self.removals().dom().subset_of(self.infos().dom())
        &&& match self.current_registration() {
            Some(registration) => !self.removals().contains_key(registration.0.obj()),
            None => true,
        }
        &&& forall|obj: nat|
            self.removals().contains_key(obj) ==> {
                let ts = (#[trigger] self.removals()[obj]).timestamp;
                &&& history.contains_timestamp(ts)
                &&& forall|later: nat|
                    history.contains_timestamp(later) && ts <= later
                        ==> #[trigger] self.publications()[later] != Some(obj)
            }
    }

    /// Copies the persistent identity corresponding to one published message.
    pub proof fn tracked_info_for(tracked &self, object: RcuPublishedObject) -> (tracked res:
        RcuBlockInfo<T>)
        requires
            self.infos_wf(),
            object.domain == self.domain(),
            self.root().objects().contains_pair(object.obj, object.addr),
        ensures
            res.wf(),
            res.domain() == object.domain,
            res.obj() == object.obj,
            res.addr() == object.addr,
            equal(res.ptr(), self.infos()[object.obj].ptr()),
    {
        let tracked info = self.infos.tracked_borrow(object.obj);
        info.tracked_duplicate()
    }

    /// Resolves one atomic-history timestamp to its persistent typed identity.
    ///
    /// This is the proof interface used by weak atomic loads. It keeps the
    /// root's internal publication and identity maps opaque to the atomic
    /// wrapper while exporting exact pointer provenance, not just an address.
    pub proof fn tracked_info_at(
        tracked &self,
        history: Irc11History<*mut T>,
        ts: nat,
    ) -> (tracked res: Option<RcuBlockInfo<T>>)
        requires
            rcu_owned_root_history_inv(history, *self),
            history.contains_timestamp(ts),
        ensures
            self.publications().contains_key(ts),
            match (self.published_at(ts), res) {
                (None, None) => history.value(ts).addr() == 0,
                (Some(object), Some(info)) => {
                    &&& object.domain == self.domain()
                    &&& object.addr == history.value(ts).addr()
                    &&& self.infos().contains_key(info.obj())
                    &&& info.wf()
                    &&& info.domain() == object.domain
                    &&& info.obj() == object.obj
                    &&& info.addr() == object.addr
                    &&& equal(info.ptr(), history.value(ts))
                    &&& equal(info.ptr(), self.infos()[info.obj()].ptr())
                },
                _ => false,
            },
    {
        assert(self.publications().contains_key(ts));
        match self.publications()[ts] {
            Some(obj) => {
                let ghost object = RcuPublishedObject {
                    domain: self.domain(),
                    obj,
                    addr: self.root().objects()[obj],
                };
                assert(self.published_at(ts) == Some(object));
                let tracked info = self.tracked_info_for(object);
                assert(equal(info.ptr(), history.value(ts)));
                Some(info)
            },
            None => {
                assert(self.published_at(ts) is None);
                None
            },
        }
    }

    /// Extracts the allocation ID stored in a non-null root publication.
    pub proof fn lemma_published_object_id(
        tracked &self,
        history: Irc11History<*mut T>,
        ts: nat,
        object: RcuPublishedObject,
    )
        requires
            rcu_owned_root_history_inv(history, *self),
            history.contains_timestamp(ts),
            self.published_at(ts) == Some(object),
        ensures
            self.publications()[ts] == Some(object.obj),
    {
        match self.publications()[ts] {
            Some(obj) => {
                assert(self.root().objects().contains_pair(obj, history.value(ts).addr()));
                assert(self.published_at(ts) == Some(
                    RcuPublishedObject {
                        domain: self.domain(),
                        obj,
                        addr: self.root().objects()[obj],
                    },
                ));
            },
            None => {
                assert(self.published_at(ts) is None);
            },
        }
    }

    /// Opens the paper's entry-time expired-set membership into the recorded
    /// root-removal observation for that allocation.
    pub proof fn lemma_observed_retired(
        tracked &self,
        history: Irc11History<*mut T>,
        root: Loc,
        view: Irc11ThreadView,
        obj: nat,
    )
        requires
            rcu_owned_root_history_inv(history, *self),
            self.root().domain_auth().observed_retired(root, view).contains(obj),
        ensures
            self.removals().contains_key(obj),
            self.removals()[obj].root == root,
            self.removals()[obj].observed_by(view),
    {
        assert(self.root().domain_auth().wf());
        assert(self.root().domain_auth().retired().contains(obj));
        assert(self.root().domain_auth().retire_observations().dom()
            == self.root().domain_auth().retired());
        assert(self.root().domain_auth().retire_observations().dom().contains(obj));
        assert(self.root().domain_auth().retire_observations().contains_key(obj));
    }

    /// Relates an observed persistent retirement-fact collection to this
    /// root's entry-time expired set.
    pub proof fn lemma_retired_facts_observed(
        tracked &self,
        history: Irc11History<*mut T>,
        tracked facts: &RcuRetiredFacts,
        root: Loc,
        view: Irc11ThreadView,
    )
        requires
            rcu_owned_root_history_inv(history, *self),
            facts.observed_by(view),
        ensures
            forall|record: RcuRetiredRecord| #[trigger]
                facts.records().contains(record) && record.domain == self.domain()
                    && record.retire_observation_registry == self.retire_observation_registry()
                    && record.removal.root == root ==> self.root().domain_auth().observed_retired(
                    root,
                    view,
                ).contains(record.obj),
    {
        facts.lemma_matching_records_observed_retired(&self.root.domain, root, view);
    }

    /// Registers and starts one fresh logical reader instance.
    ///
    /// The paper leaves `TId` abstract. This implementation allocates one
    /// proof-only identity per critical section so nested kernel readers remain
    /// distinguishable. It implements the paper's base specification, but is
    /// not the fixed `LOCALS[tid]` identity used by its concrete epoch
    /// algorithm.
    pub proof fn tracked_start_reader(
        tracked &mut self,
        history: Irc11History<*mut T>,
        root: Loc,
        start_view: Irc11ThreadView,
        reader: RcuReaderContext,
    ) -> (tracked res: RcuBaseGuard)
        requires
            rcu_owned_root_history_inv(history, *old(self)),
        ensures
            rcu_owned_root_history_inv(history, *final(self)),
            final(self).domain() == old(self).domain(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).current_owned() == old(self).current_owned(),
            final(self).current_registration() == old(self).current_registration(),
            final(self).publications() == old(self).publications(),
            final(self).infos() == old(self).infos(),
            final(self).removals() == old(self).removals(),
            final(self).root().domain_auth().retired() == old(self).root().domain_auth().retired(),
            final(self).root().domain_auth().retire_observations() == old(
                self,
            ).root().domain_auth().retire_observations(),
            res.wf(),
            res.domain() == final(self).domain(),
            res.reader_registry() == final(self).reader_registry(),
            res.reader() == reader,
            res.root() == root,
            res.start_view() == start_view,
            res.retire_observation_registry()
                == final(self).root().domain_auth().retire_observation_registry(),
            res.retire_observation_registry() == old(self).retire_observation_registry(),
            res.expired() == final(self).root().domain_auth().observed_retired(root, start_view),
    {
        let tracked inactive = self.root.domain.tracked_register_reader(reader);
        let tracked guard = self.root.domain.tracked_guard_start(inactive, root, start_view);
        assert(current_registration_matches(self.root(), self.current_registration()));
        assert(self.infos_wf());
        guard
    }

    /// Initializes root history and retains the initial registration as the
    /// current unique ownership resource.
    pub proof fn tracked_initial(
        ptr: *mut T,
        tracked ownership: Option<O>,
        history: Irc11History<*mut T>,
        timestamp: nat,
        message_view: Irc11ThreadView,
    ) -> (tracked res: Self)
        requires
            (ownership is Some) == (ptr.addr() != 0),
            history.is_singleton(timestamp, (ptr, message_view)),
        ensures
            rcu_owned_root_history_inv(history, res),
            (res.current_registration() is Some) == (ptr.addr() != 0),
            res.current_registration() is Some ==> res.current_registration()->Some_0.0.ptr()
                == ptr,
            res.current_ownership() == ownership,
            res.removals() == Map::<nat, RcuRemovalObservation>::empty(),
            res.infos().dom() == match res.current_registration() {
                Some(registration) => Set::empty().insert(registration.0.obj()),
                None => Set::empty(),
            },
            match res.current_owned() {
                Some(owned) => {
                    &&& ptr.addr() != 0
                    &&& equal(owned.block_info().ptr(), ptr)
                    &&& ownership == Some(owned.ownership())
                },
                None => {
                    &&& ptr.addr() == 0
                    &&& ownership is None
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
                assert(infos.dom() == root.objects().dom());
                assert forall|registered: nat| infos.contains_key(registered) implies {
                    let saved = #[trigger] infos[registered];
                    &&& saved.wf()
                    &&& saved.domain() == root.domain()
                    &&& saved.obj() == registered
                    &&& root.objects().contains_pair(registered, saved.addr())
                } by {
                    assert(registered == obj);
                };
                Some(RcuOwnedObject { registration, ownership: ownership.tracked_unwrap() })
            },
            None => {
                assert(infos.dom() == root.objects().dom());
                None
            },
        };
        let tracked res = RcuRootOwnedGhost { root, current, infos, removals: Map::empty() };
        assert(res.infos().dom() == match res.current_registration() {
            Some(registration) => Set::empty().insert(registration.0.obj()),
            None => Set::empty(),
        });
        assert(res.infos_wf());
        assert(res.removals_wf(history));
        assert(res.removals() == res.root().domain_auth().retire_observations());
        res
    }

    /// Publishes a fresh allocation and retires the previously current root.
    ///
    /// In this direct-root specialization, replacement is the complete removal
    /// event for the old owned publication: this cell is the only managed edge
    /// for that `P` handle. This rule is not the paper's general
    /// `RcuPointedBy-detach` rule for internal nodes.
    pub proof fn tracked_push_fresh<OwnPred>(
        tracked &mut self,
        prev: Irc11History<*mut T>,
        next: Irc11History<*mut T>,
        old_timestamp: nat,
        new_timestamp: nat,
        value: *mut T,
        message_view: Irc11ThreadView,
        root: Loc,
        tracked ownership: Option<O>,
    ) -> (tracked detached: Option<RcuRetiredOwnedObject<T, O>>) where
        OwnPred: RcuRootOwnershipPredicate<T, O>,

        requires
            rcu_owned_root_history_inv(prev, *old(self)),
            rcu_current_ownership_inv::<T, O, OwnPred>(*old(self)),
            prev.is_max_timestamp(old_timestamp),
            new_timestamp == old_timestamp + 1,
            next == prev.insert(new_timestamp, value, message_view),
            (ownership is Some) == (value.addr() != 0),
        ensures
            rcu_owned_root_history_inv(next, *final(self)),
            final(self).domain() == old(self).domain(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            match detached {
                Some(detached) => {
                    &&& old(self).current_registration() is Some
                    &&& detached.object() == old(self).current_registration()->Some_0.0
                    &&& detached.object().domain() == old(self).domain()
                    &&& detached.obj() == old(self).current_registration()->Some_0.0.obj()
                    &&& equal(detached.ptr(), old(self).infos()[detached.obj()].ptr())
                    &&& detached.retired().domain() == detached.domain()
                    &&& detached.retired().obj() == detached.obj()
                    &&& detached.retired().ptr() == detached.ptr()
                    &&& detached.retired().removal() == (RcuRemovalObservation {
                        root,
                        timestamp: new_timestamp,
                        message_view,
                    })
                    &&& detached.retired().retire_observation_registry() == old(
                        self,
                    ).retire_observation_registry()
                    &&& equal(detached.ptr(), prev.value(old_timestamp))
                    &&& old(self).current_ownership() == Some(detached.ownership())
                    &&& OwnPred::owns(detached.ptr(), detached.ownership())
                },
                None => old(self).current_registration() is None,
            },
            (final(self).current_registration() is Some) == (value.addr() != 0),
            final(self).current_registration() is Some
                ==> final(self).current_registration()->Some_0.0.ptr() == value,
            final(self).current_ownership() == ownership,
            match final(self).current_registration() {
                Some(registration) => {
                    &&& !old(self).infos().contains_key(registration.0.obj())
                    &&& final(self).infos().dom() == old(self).infos().dom().insert(
                        registration.0.obj(),
                    )
                    &&& forall|obj: nat| #[trigger]
                        old(self).infos().contains_key(obj) ==> final(self).infos()[obj] == old(
                            self,
                        ).infos()[obj]
                },
                None => final(self).infos() == old(self).infos(),
            },
            final(self).removals() == match detached {
                Some(detached) => old(self).removals().insert(
                    detached.obj(),
                    detached.retired().removal(),
                ),
                None => old(self).removals(),
            },
            match final(self).current_owned() {
                Some(owned) => {
                    &&& value.addr() != 0
                    &&& equal(owned.block_info().ptr(), value)
                    &&& ownership == Some(owned.ownership())
                },
                None => {
                    &&& value.addr() == 0
                    &&& ownership is None
                },
            },
    {
        assert(current_registration_matches(self.root(), self.current_registration()));
        let ghost removed_obj = match self.current_registration() {
            Some(registration) => Some(registration.0.obj()),
            None => None,
        };
        let tracked old_current = if self.current is Some {
            Some(self.current.tracked_take())
        } else {
            None
        };
        let tracked new_registration = self.root.tracked_push_fresh(
            prev,
            next,
            old_timestamp,
            new_timestamp,
            value,
            message_view,
        );
        let tracked new_current = match new_registration {
            Some(registration) => {
                let ghost obj = registration.0.obj();
                let tracked info = registration.0.tracked_duplicate();
                self.infos.tracked_insert(obj, info);
                assert(self.infos.dom() == self.root.objects().dom());
                assert forall|registered: nat| self.infos.contains_key(registered) implies {
                    let saved = #[trigger] self.infos[registered];
                    &&& saved.wf()
                    &&& saved.domain() == self.root.domain()
                    &&& saved.obj() == registered
                    &&& self.root.objects().contains_pair(registered, saved.addr())
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
                Some(RcuOwnedObject { registration, ownership: ownership.tracked_unwrap() })
            },
            None => {
                assert(self.infos_wf());
                None
            },
        };
        let ghost removal = RcuRemovalObservation { root, timestamp: new_timestamp, message_view };
        let tracked detached = match old_current {
            Some(owned) => {
                let tracked (registration, old_ownership) = owned.tracked_into_parts();
                let tracked (object, base) = registration;
                assert(base.belongs_to(self.root.domain));
                let ghost seen_removed = RcuSeenRemoved {
                    removed: Set::empty().insert(object.obj()),
                    link_view: RcuLinkView::empty(),
                };
                let tracked retire = lift_direct_root_retire_perm(base, seen_removed);
                let tracked retired = self.root.domain.tracked_retire(retire, removal);
                Some(RcuRetiredOwnedObject { object, retired, ownership: old_ownership })
            },
            None => None,
        };
        self.current = new_current;
        assert(match self.current_registration() {
            Some(registration) => {
                &&& !old(self).infos().contains_key(registration.0.obj())
                &&& self.infos().dom() == old(self).infos().dom().insert(registration.0.obj())
            },
            None => self.infos() == old(self).infos(),
        });
        self.removals = match removed_obj {
            Some(obj) => self.removals.insert(obj, removal),
            None => self.removals,
        };
        assert(self.removals() == self.root().domain_auth().retire_observations()) by {
            match removed_obj {
                Some(obj) => {
                    assert(old(self).removals() == old(
                        self,
                    ).root().domain_auth().retire_observations());
                    assert(self.removals() == old(self).removals().insert(obj, removal));
                    assert(self.root().domain_auth().retire_observations() == old(
                        self,
                    ).root().domain_auth().retire_observations().insert(obj, removal));
                },
                None => {
                    assert(old(self).removals() == old(
                        self,
                    ).root().domain_auth().retire_observations());
                    assert(self.removals() == old(self).removals());
                    assert(self.root().domain_auth().retire_observations() == old(
                        self,
                    ).root().domain_auth().retire_observations());
                },
            }
        };
        assert(self.removals() == match detached {
            Some(detached) => old(self).removals().insert(
                detached.obj(),
                detached.retired().removal(),
            ),
            None => old(self).removals(),
        });
        assert(current_registration_matches(self.root(), self.current_registration()));
        assert(self.infos_wf());
        assert(self.removals_wf(next)) by {
            assert forall|obj: nat| self.removals().contains_key(obj) implies {
                let ts = (#[trigger] self.removals()[obj]).timestamp;
                &&& next.contains_timestamp(ts)
                &&& forall|later: nat|
                    next.contains_timestamp(later) && ts <= later
                        ==> #[trigger] self.publications()[later] != Some(obj)
            } by {
                if removed_obj == Some(obj) {
                    assert(self.removals()[obj] == removal);
                    assert(self.removals()[obj].timestamp == new_timestamp);
                    assert(self.publications()[new_timestamp] == match new_registration {
                        Some(registration) => Some(registration.0.obj()),
                        None => None,
                    });
                    if new_registration is Some {
                        assert(!old(self).root().objects().contains_key(
                            new_registration->Some_0.0.obj(),
                        ));
                        assert(old(self).infos().contains_key(obj));
                    }
                } else {
                    assert(old(self).removals().contains_key(obj));
                    assert(self.removals()[obj] == old(self).removals()[obj]);
                    assert forall|later: nat|
                        next.contains_timestamp(later) && self.removals()[obj].timestamp
                            <= later implies #[trigger] self.publications()[later] != Some(obj) by {
                        if later != new_timestamp {
                            assert(prev.contains_timestamp(later));
                            assert(self.publications()[later] == old(self).publications()[later]);
                        } else {
                            if new_registration is Some {
                                assert(!old(self).root().objects().contains_key(
                                    new_registration->Some_0.0.obj(),
                                ));
                                assert(old(self).infos().contains_key(obj));
                            }
                        }
                    };
                }
            };
        }
        detached
    }

    /// Re-publishes the currently owned registration without changing its AId
    /// or releasing its unique retire permission.
    pub proof fn tracked_republish_current(
        tracked &mut self,
        prev: Irc11History<*mut T>,
        next: Irc11History<*mut T>,
        old_timestamp: nat,
        new_timestamp: nat,
        value: *mut T,
        message_view: Irc11ThreadView,
    )
        requires
            rcu_owned_root_history_inv(prev, *old(self)),
            prev.is_max_timestamp(old_timestamp),
            new_timestamp == old_timestamp + 1,
            next == prev.insert(new_timestamp, value, message_view),
            old(self).current_registration() is Some,
            old(self).current_registration()->Some_0.0.ptr() == value,
        ensures
            rcu_owned_root_history_inv(next, *final(self)),
            final(self).domain() == old(self).domain(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).current_registration() == old(self).current_registration(),
    {
        let tracked owned = self.current.tracked_take();
        self.root.tracked_push_registered(
            prev,
            next,
            old_timestamp,
            new_timestamp,
            value,
            message_view,
            &owned.registration.0,
        );
        self.current = Some(owned);
        assert(current_registration_matches(self.root(), self.current_registration()));
        assert(self.removals() == self.root().domain_auth().retire_observations());
        assert(self.removals_wf(next)) by {
            assert forall|obj: nat| self.removals().contains_key(obj) implies {
                let ts = (#[trigger] self.removals()[obj]).timestamp;
                &&& next.contains_timestamp(ts)
                &&& forall|later: nat|
                    next.contains_timestamp(later) && ts <= later
                        ==> #[trigger] self.publications()[later] != Some(obj)
            } by {
                assert(old(self).removals().contains_key(obj));
                assert(!old(self).removals().contains_key(owned.registration.0.obj()));
                assert(obj != owned.registration.0.obj());
                assert forall|later: nat|
                    next.contains_timestamp(later) && self.removals()[obj].timestamp
                        <= later implies #[trigger] self.publications()[later] != Some(obj) by {
                    if later != new_timestamp {
                        assert(prev.contains_timestamp(later));
                        assert(self.publications()[later] == old(self).publications()[later]);
                    } else {
                        assert(self.publications()[later] == Some(owned.registration.0.obj()));
                    }
                };
            };
        }
    }
}

/// The current ownership resource agrees with the latest publication, while
/// older history entries need only agree with persistent registration metadata.
pub open spec fn rcu_owned_root_history_inv<T, O>(
    history: Irc11History<*mut T>,
    ghost: RcuRootOwnedGhost<T, O>,
) -> bool {
    &&& rcu_root_history_inv(history, ghost.root())
    &&& ghost.ownership_wf()
    &&& ghost.infos_wf()
    &&& ghost.removals_wf(history)
    &&& ghost.removals() == ghost.root().domain_auth().retire_observations()
    &&& forall|ts: nat|
        history.contains_timestamp(ts) ==> {
            match #[trigger] ghost.publications()[ts] {
                Some(obj) => equal(ghost.infos()[obj].ptr(), history.value(ts)),
                None => true,
            }
        }
    &&& match ghost.current_registration() {
        Some(registration) => equal(
            registration.0.ptr(),
            history.value(ghost.root().current_timestamp()),
        ),
        None => history.value(ghost.root().current_timestamp()).addr() == 0,
    }
}

/// Client relation between a pointer and its physical ownership resource.
pub trait RcuRootOwnershipPredicate<T, O> {
    spec fn owns(ptr: *mut T, ownership: O) -> bool;
}

/// Trivial ownership relation used by proof-only examples carrying `()`.
pub struct UnitRcuRootOwnership;

impl<T> RcuRootOwnershipPredicate<T, ()> for UnitRcuRootOwnership {
    open spec fn owns(_ptr: *mut T, _ownership: ()) -> bool {
        true
    }
}

pub open spec fn rcu_current_ownership_inv<T, O, OwnPred>(
    ghost: RcuRootOwnedGhost<T, O>,
) -> bool where OwnPred: RcuRootOwnershipPredicate<T, O> {
    match ghost.current_owned() {
        Some(owned) => OwnPred::owns(owned.block_info().ptr(), owned.ownership()),
        None => true,
    }
}

/// Opens the structural current-ownership relation for atomic clients.
pub proof fn lemma_current_owned_resources<T, O, OwnPred>(
    history: Irc11History<*mut T>,
    tracked ghost: &RcuRootOwnedGhost<T, O>,
) where OwnPred: RcuRootOwnershipPredicate<T, O>
    requires
        rcu_owned_root_history_inv(history, *ghost),
        rcu_current_ownership_inv::<T, O, OwnPred>(*ghost),
    ensures
        match ghost.current_owned() {
            Some(owned) => {
                &&& owned.block_info().wf()
                &&& equal(owned.block_info().ptr(), history.value(ghost.root().current_timestamp()))
                &&& OwnPred::owns(owned.block_info().ptr(), owned.ownership())
            },
            None => history.value(ghost.root().current_timestamp()).addr() == 0,
        },
{
    match ghost.current_owned() {
        Some(owned) => {
            assert(ghost.current_registration() == Some(owned.registration()));
        },
        None => {},
    }
}

/// RCU weak-atomic invariant with typed ownership for the current root value.
pub struct RcuOwnedWeakAtomicInv<OwnPred> {
    _marker: PhantomData<OwnPred>,
}

impl<T, O: Objective, OwnPred> InvariantPredicate<
    (RcuRootKey, Irc11AtomicId),
    (AtomicPointsTo<*mut T>, RcuRootOwnedGhost<T, O>),
> for RcuOwnedWeakAtomicInv<OwnPred> where OwnPred: RcuRootOwnershipPredicate<T, O> {
    open spec fn inv(
        key_loc: (RcuRootKey, Irc11AtomicId),
        pair: (AtomicPointsTo<*mut T>, RcuRootOwnedGhost<T, O>),
    ) -> bool {
        let (key, loc) = key_loc;
        let (points_to, g) = pair;
        &&& points_to.loc() == loc
        &&& key.domain == g.domain()
        &&& key.reader_registry == g.reader_registry()
        &&& key.retire_observation_registry == g.retire_observation_registry()
        &&& rcu_history_inv(key.nullable, points_to.hist())
        &&& rcu_owned_root_history_inv(points_to.hist(), g)
        &&& rcu_current_ownership_inv::<T, O, OwnPred>(g)
        &&& forall|obj: nat|
            g.removals().contains_key(obj) ==> {
                let removal = #[trigger] g.removals()[obj];
                points_to.get_timestamp(removal.message_view) == Some(removal.timestamp)
            }
    }
}

/// Proof-facing summary of one grace period.
///
/// `epoch` is assigned by the monitor, not by callback producers. Every
/// callback in a batch carries exactly this epoch, so completion of an older
/// grace period cannot authorize a callback queued for a later one.
pub ghost struct GracePeriodView {
    pub epoch: nat,
    pub callbacks: Seq<RcuCallbackSummary>,
    pub is_complete: bool,
}

impl GracePeriodView {
    /// The state of the grace period when the monitor is created: complete,
    /// with no callbacks attached.
    pub open spec fn initial() -> Self {
        GracePeriodView { epoch: 0, callbacks: Seq::empty(), is_complete: true }
    }

    pub open spec fn has_pending_work(self) -> bool {
        !self.is_complete || self.callbacks.len() > 0
    }

    /// Lock-protected well-formedness: a completed grace period has already
    /// had its callbacks taken. The monitor may break this transiently inside
    /// a critical section (between completing a grace period and taking its
    /// callbacks), but it must hold whenever the monitor lock is released.
    pub open spec fn wf(self) -> bool {
        &&& self.is_complete ==> self.callbacks.len() == 0
        &&& forall|i: int|
            0 <= i < self.callbacks.len() ==> (#[trigger] self.callbacks[i]).retire_epoch
                == self.epoch
    }
}

/// Proof-facing summary of the monitor state protected by the RCU monitor's
/// lock.
pub ghost struct MonitorStateView {
    pub current_gp: GracePeriodView,
    pub next_callbacks: Seq<RcuCallbackSummary>,
}

impl MonitorStateView {
    /// The monitor state at creation: a complete grace period and no queued
    /// callbacks.
    pub open spec fn initial() -> Self {
        MonitorStateView { current_gp: GracePeriodView::initial(), next_callbacks: Seq::empty() }
    }

    /// All callback summaries the monitor is still responsible for.
    pub open spec fn pending_summaries(self) -> Seq<RcuCallbackSummary> {
        self.current_gp.callbacks.add(self.next_callbacks)
    }

    pub open spec fn has_pending_work(self) -> bool {
        self.current_gp.has_pending_work() || self.next_callbacks.len() > 0
    }

    pub open spec fn no_pending_work(self) -> bool {
        !self.has_pending_work()
    }

    /// Lock-protected well-formedness: when the current grace period is
    /// complete, the monitor has either restarted it with the queued callbacks
    /// or stopped monitoring, so both callback lists are empty.
    pub open spec fn wf(self) -> bool {
        &&& self.current_gp.wf()
        &&& self.current_gp.is_complete ==> self.next_callbacks.len() == 0
        &&& forall|i: int|
            0 <= i < self.next_callbacks.len() ==> (#[trigger] self.next_callbacks[i]).retire_epoch
                == self.current_gp.epoch + 1
    }
}

/// Under the lock-protected invariant, "has pending work" collapses to "the
/// current grace period is incomplete": a complete grace period implies both
/// callback lists are empty.
pub proof fn monitor_state_pending_iff_incomplete(state: MonitorStateView)
    requires
        state.wf(),
    ensures
        state.has_pending_work() <==> !state.current_gp.is_complete,
        state.no_pending_work() <==> state.current_gp.is_complete,
{
}

/// `no_pending_work` certifies that the pending-summary sequence is empty.
pub proof fn monitor_state_no_pending_no_summaries(state: MonitorStateView)
    requires
        state.no_pending_work(),
    ensures
        state.pending_summaries() == Seq::<RcuCallbackSummary>::empty(),
{
}

/// Ghost summary paired with the RCU monitor's `is_monitoring` flag.
///
/// `states[ts]` summarizes the lock-protected monitor state stored with flag
/// message timestamp `ts`. This is intentionally a summary: the concrete
/// callback vectors live in the monitor state protected by its lock, and the
/// agreement between `states[ts]` and that state is established by the writer,
/// which performs every flag store while holding the monitor lock.
pub tracked struct RcuMonitorFlagGhost {
    pub ghost states: Map<nat, MonitorStateView>,
}

unsafe impl Objective for RcuMonitorFlagGhost {

}

impl RcuMonitorFlagGhost {
    pub open spec fn initial(timestamp: nat) -> Self {
        RcuMonitorFlagGhost { states: Map::empty().insert(timestamp, MonitorStateView::initial()) }
    }

    /// Proof-mode constructor for the tracked ghost state stored inside the
    /// monitor flag's weak atomic invariant.
    pub proof fn tracked_initial(timestamp: nat) -> (tracked res: Self)
        ensures
            res == Self::initial(timestamp),
    {
        RcuMonitorFlagGhost { states: Map::empty().insert(timestamp, MonitorStateView::initial()) }
    }

    pub open spec fn insert(self, timestamp: nat, state: MonitorStateView) -> Self {
        RcuMonitorFlagGhost { states: self.states.insert(timestamp, state) }
    }

    pub proof fn tracked_insert(
        tracked self,
        timestamp: nat,
        state: MonitorStateView,
    ) -> (tracked res: Self)
        ensures
            res == self.insert(timestamp, state),
    {
        RcuMonitorFlagGhost { states: self.states.insert(timestamp, state) }
    }

    /// Whether the state recorded at flag message `timestamp` had work pending.
    pub open spec fn pending_at(self, timestamp: nat) -> bool
        recommends
            self.states.contains_key(timestamp),
    {
        self.states[timestamp].has_pending_work()
    }
}

/// Weak-memory invariant for the monitor's fast-path flag.
///
/// Every flag message carries a well-formed snapshot of the monitor state, and
/// the invariant is deliberately one-way: a `false` flag message certifies that
/// the state recorded at that message had no pending monitor work. A `true`
/// flag is conservative and may over-approximate pending work.
///
/// Note the weak-memory reading: a relaxed load may observe a stale message,
/// so a `false` read only certifies "no pending work as of that message", not
/// "no pending work now". That is exactly what the monitor fast path needs:
/// callbacks enqueued after that message were published together with a `true`
/// flag message, so skipping the slow path can only delay their grace period,
/// never lose them.
pub open spec fn rcu_monitor_flag_history_inv(
    history: Irc11History<bool>,
    ghost: RcuMonitorFlagGhost,
) -> bool {
    &&& !history.dom().is_empty()
    &&& ghost.states.dom() == history.dom()
    &&& forall|timestamp: nat|
        history.contains_timestamp(timestamp) ==> (#[trigger] ghost.states[timestamp]).wf()
    &&& forall|timestamp: nat|
        history.contains_timestamp(timestamp) ==> {
            !(#[trigger] history.value(timestamp)) ==> ghost.states[timestamp].no_pending_work()
        }
}

pub struct RcuMonitorFlagInv;

impl InvariantPredicate<
    Irc11AtomicId,
    (AtomicPointsTo<bool>, RcuMonitorFlagGhost),
> for RcuMonitorFlagInv {
    open spec fn inv(
        loc: Irc11AtomicId,
        pair: (AtomicPointsTo<bool>, RcuMonitorFlagGhost),
    ) -> bool {
        &&& pair.0.loc() == loc
        &&& rcu_monitor_flag_history_inv(pair.0.hist(), pair.1)
    }
}

pub proof fn rcu_monitor_flag_initial_inv(
    history: Irc11History<bool>,
    timestamp: nat,
    message_view: Irc11ThreadView,
)
    requires
        history.is_singleton(timestamp, (false, message_view)),
    ensures
        rcu_monitor_flag_history_inv(history, RcuMonitorFlagGhost::initial(timestamp)),
{
    assert(history.dom() == Set::empty().insert(timestamp)) by {
        assert forall|ts: nat|
            history.dom().contains(ts) <==> Set::empty().insert(timestamp).contains(ts) by {
            if history.dom().contains(ts) {
                assert(history.contains_timestamp(ts));
                assert(ts == timestamp);
            }
        };
    };
}

/// Inserting one flag message preserves the history invariant, provided the
/// writer records a well-formed state snapshot and only writes `false` when
/// that snapshot has no pending work.
///
/// This is the proof obligation discharged by `set_monitoring`: it
/// stores the flag while holding the monitor lock, so it can supply the
/// lock-protected state view as the snapshot.
pub proof fn preserve_rcu_monitor_flag_inv_on_insert(
    prev: Irc11History<bool>,
    next: Irc11History<bool>,
    timestamp: nat,
    value: bool,
    message_view: Irc11ThreadView,
    prev_ghost: RcuMonitorFlagGhost,
    next_ghost: RcuMonitorFlagGhost,
    state: MonitorStateView,
)
    requires
        rcu_monitor_flag_history_inv(prev, prev_ghost),
        !prev.contains_timestamp(timestamp),
        next == prev.insert(timestamp, value, message_view),
        next_ghost == prev_ghost.insert(timestamp, state),
        state.wf(),
        !value ==> state.no_pending_work(),
    ensures
        rcu_monitor_flag_history_inv(next, next_ghost),
{
    assert(next_ghost.states.dom() == next.dom());
    assert forall|ts: nat| next.contains_timestamp(ts) implies (
    #[trigger] next_ghost.states[ts]).wf() by {
        if ts == timestamp {
            assert(next_ghost.states[ts] == state);
        } else {
            assert(prev.contains_timestamp(ts));
            assert(next_ghost.states[ts] == prev_ghost.states[ts]);
        }
    };
    assert forall|ts: nat| next.contains_timestamp(ts) implies {
        !(#[trigger] next.value(ts)) ==> next_ghost.states[ts].no_pending_work()
    } by {
        if ts == timestamp {
            assert(next.value(ts) == value);
            assert(next_ghost.states[ts] == state);
        } else {
            assert(prev.contains_timestamp(ts));
            assert(next.value(ts) == prev.value(ts));
            assert(next_ghost.states[ts] == prev_ghost.states[ts]);
        }
    };
}

/// The key safety fact behind the monitor fast path: observing a `false` flag
/// message certifies that the monitor state recorded at that message had no
/// queued callbacks and no incomplete grace period.
pub proof fn rcu_monitor_flag_false_has_no_pending(
    history: Irc11History<bool>,
    ghost: RcuMonitorFlagGhost,
    ts: nat,
)
    requires
        rcu_monitor_flag_history_inv(history, ghost),
        history.contains_timestamp(ts),
        !history.value(ts),
    ensures
        ghost.states[ts].no_pending_work(),
        ghost.states[ts].pending_summaries() == Seq::<RcuCallbackSummary>::empty(),
        ghost.states[ts].current_gp.is_complete,
{
    monitor_state_pending_iff_incomplete(ghost.states[ts]);
    monitor_state_no_pending_no_summaries(ghost.states[ts]);
}

pub proof fn preserve_rcu_history_inv_on_push<T>(
    nullable: bool,
    prev: Irc11History<*mut T>,
    next: Irc11History<*mut T>,
    timestamp: nat,
    value: *mut T,
    message_view: Irc11ThreadView,
)
    requires
        rcu_history_inv(nullable, prev),
        !prev.contains_timestamp(timestamp),
        next == prev.insert(timestamp, value, message_view),
        nullable || value.addr() != 0,
    ensures
        rcu_history_inv(nullable, next),
{
    assert(!next.dom().is_empty());
    if !nullable {
        assert forall|ts: nat| next.contains_timestamp(ts) implies #[trigger] next.value(ts).addr()
            != 0 by {
            if ts == timestamp {
                assert(next.value(ts) == value);
            } else {
                assert(prev.contains_timestamp(ts));
                assert(next.value(ts) == prev.value(ts));
            }
        };
    }
}

pub proof fn rcu_history_inv_read_nonnull<T>(history: Irc11History<*mut T>, ts: nat)
    requires
        rcu_history_inv(false, history),
        history.contains_timestamp(ts),
    ensures
        history.value(ts).addr() != 0,
        !history.value(ts).is_null(),
{
    assert(history.value(ts).addr() != 0);
}

/// Link view carried by an RCU read-side guard.
///
/// `seen_at(a) = n` means the guard has observed link-history events for source
/// AId `a` up to at least `n`. Following a loaded link at index `k` is allowed
/// only when `seen_at(a) <= k`; otherwise the pointer may be too stale.
#[verifier::reject_recursive_types(T)]
pub ghost struct RcuLinkView<T> {
    pub seen: Map<nat, LinkIndex>,
    pub marker: Option<*mut T>,
}

impl<T> RcuLinkView<T> {
    pub open spec fn empty() -> Self {
        RcuLinkView { seen: Map::empty(), marker: None }
    }

    pub open spec fn seen_at(self, obj: nat) -> LinkIndex {
        if self.seen.contains_key(obj) {
            self.seen[obj]
        } else {
            0nat
        }
    }

    pub open spec fn observe(self, obj: nat, n: LinkIndex) -> Self {
        RcuLinkView {
            seen: self.seen.insert(
                obj,
                if self.seen_at(obj) <= n {
                    n
                } else {
                    self.seen_at(obj)
                },
            ),
            marker: self.marker,
        }
    }

    /// Observing one source never moves any source's traversal position
    /// backwards.
    pub proof fn lemma_observe_monotonic(self, obj: nat, n: LinkIndex, other: nat)
        ensures
            self.seen_at(other) <= self.observe(obj, n).seen_at(other),
            self.seen_at(obj) <= n ==> self.observe(obj, n).seen_at(obj) == n,
    {
    }
}

/// Paper-style `SeenRemoved(D, LV)`.
///
/// `removed` is the set `D` observed by the guard; `link_view` is `LV`.
/// A dead incoming edge is either from a removed predecessor AId or overwritten
/// by a later observed link event.
#[verifier::reject_recursive_types(T)]
pub ghost struct RcuSeenRemoved<T> {
    pub removed: Set<nat>,
    pub link_view: RcuLinkView<T>,
}

impl<T> RcuSeenRemoved<T> {
    pub open spec fn empty() -> Self {
        RcuSeenRemoved { removed: Set::empty(), link_view: RcuLinkView::empty() }
    }

    pub open spec fn seen_at(self, obj: nat) -> LinkIndex {
        self.link_view.seen_at(obj)
    }

    pub open spec fn dead_edge(self, edge: LinkEdge) -> bool {
        self.removed.contains(edge.0) || self.seen_at(edge.0) > edge.1
    }
}

/// Authoritative ghost handle for one RCU protection domain.
///
/// The concrete implementation owns this token in its invariant. We keep the
/// fields private so clients cannot manufacture domain authority. `readers`
/// only registers fresh logical reader-instance identities. Active/inactive
/// phase is represented linearly by [`RcuInactive`] and [`RcuBaseGuard`], so
/// ending a critical section does not need this authority.
pub tracked struct RcuDomainAuth {
    objects: GhostMapAuth<nat, usize>,
    retire_perms: GhostMapAuth<nat, usize>,
    retire_observation_cells: GhostMapAuth<nat, Option<RcuRemovalObservation>>,
    readers: GhostMapAuth<nat, bool>,
    ghost next_obj: nat,
    ghost next_reader: nat,
    ghost retired: Set<nat>,
    ghost retire_observations: Map<nat, RcuRemovalObservation>,
}

impl RcuDomainAuth {
    /// The paper's RCU location `l` is the identity of the allocation registry.
    /// Every object registered through this authority belongs to this domain.
    pub closed spec fn id(self) -> Loc {
        self.objects.id()
    }

    pub closed spec fn objects(self) -> Map<nat, usize> {
        self.objects@
    }

    pub closed spec fn next_obj(self) -> nat {
        self.next_obj
    }

    pub closed spec fn retired(self) -> Set<nat> {
        self.retired
    }

    /// Physical detachment observation recorded for each retired allocation.
    ///
    /// A guard's implementation-specific expired set `X` is derived from this
    /// map at critical-section entry: it contains exactly the retired
    /// allocations whose detachment observation is already covered by the
    /// entering thread's weak-memory view.
    pub closed spec fn retire_observations(self) -> Map<nat, RcuRemovalObservation> {
        self.retire_observations
    }

    pub open spec fn observed_retired(self, root: Loc, view: Irc11ThreadView) -> Set<nat> {
        self.retired().filter(
            |obj: nat|
                self.retire_observations()[obj].root == root
                    && self.retire_observations()[obj].observed_by(view),
        )
    }

    pub closed spec fn reader_registry(self) -> Loc {
        self.readers.id()
    }

    pub closed spec fn retire_registry(self) -> Loc {
        self.retire_perms.id()
    }

    /// Resource registry that agrees every retired object with its unique
    /// detachment observation.
    pub closed spec fn retire_observation_registry(self) -> Loc {
        self.retire_observation_cells.id()
    }

    pub closed spec fn next_reader(self) -> nat {
        self.next_reader
    }

    /// Internal consistency of the resource algebras used by the base RCU
    /// model.
    pub closed spec fn wf(self) -> bool {
        &&& self.objects@ == self.retire_perms@
        &&& self.retire_observation_cells@.dom() == self.objects@.dom()
        &&& forall|obj: nat| #[trigger]
            self.objects@.contains_key(obj) ==> {
                match self.retire_observation_cells@[obj] {
                    Some(removal) => self.retire_observations().contains_pair(obj, removal),
                    None => !self.retire_observations().contains_key(obj),
                }
            }
        &&& forall|obj: nat| #[trigger] self.objects@.contains_key(obj) ==> obj < self.next_obj()
        &&& forall|tid: nat| #[trigger] self.readers@.contains_key(tid) ==> tid < self.next_reader()
        &&& forall|tid: nat| #[trigger] self.readers@.contains_key(tid) ==> !self.readers@[tid]
        &&& self.retired().subset_of(self.objects().dom())
        &&& self.retire_observations().dom() == self.retired()
    }

    /// Allocates a fresh RCU protection domain.
    pub proof fn tracked_new() -> (tracked res: Self)
        ensures
            res.wf(),
            res.objects() == Map::<nat, usize>::empty(),
            res.next_obj() == 0,
            res.retired() == Set::<nat>::empty(),
            res.retire_observations() == Map::<nat, RcuRemovalObservation>::empty(),
    {
        let tracked (objects, _objects_entries) = GhostMapAuth::new(Map::empty());
        let tracked (retire_perms, _retire_entries) = GhostMapAuth::new(Map::empty());
        let tracked (retire_observation_cells, _retire_observation_entries) = GhostMapAuth::new(
            Map::empty(),
        );
        let tracked (readers, _reader_entries) = GhostMapAuth::new(Map::empty());
        RcuDomainAuth {
            objects,
            retire_perms,
            retire_observation_cells,
            readers,
            next_obj: 0,
            next_reader: 0,
            retired: Set::empty(),
            retire_observations: Map::empty(),
        }
    }

    /// Implements the paper's `rcu-register` rule.
    ///
    /// The allocation ID is chosen here, once per registration. It is not an
    /// atomic-history timestamp. Registration returns both persistent block
    /// information and the unique base retire permission for the allocation.
    pub proof fn tracked_register<T>(tracked &mut self, ptr: *mut T) -> (tracked res: (
        RcuBlockInfo<T>,
        RcuBaseRetirePerm<T>,
    ))
        requires
            old(self).wf(),
            ptr.addr() != 0,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).retire_registry() == old(self).retire_registry(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).next_obj() == old(self).next_obj() + 1,
            final(self).retired() == old(self).retired(),
            final(self).retire_observations() == old(self).retire_observations(),
            final(self).objects() == old(self).objects().insert(old(self).next_obj(), ptr.addr()),
            res.0.domain() == final(self).id(),
            res.0.obj() == old(self).next_obj(),
            res.0.ptr() == ptr,
            res.0.addr() == ptr.addr(),
            res.0.wf(),
            res.1.domain() == final(self).id(),
            res.1.obj() == res.0.obj(),
            res.1.ptr() == ptr,
            res.1.wf(),
            res.1.belongs_to(*final(self)),
    {
        let ghost obj = self.next_obj;
        assert(!self.objects@.contains_key(obj));
        assert(!self.retire_perms@.contains_key(obj));

        let tracked object = self.objects.insert(obj, ptr.addr());
        let tracked block_info = object.persist();
        let tracked retire_perm = self.retire_perms.insert(obj, ptr.addr());
        let tracked retire_observation = self.retire_observation_cells.insert(obj, None);
        self.next_obj = self.next_obj + 1;

        assert forall|registered: nat| #[trigger]
            self.objects@.contains_key(registered) implies registered < self.next_obj by {
            if registered != obj {
                assert(old(self).objects().contains_key(registered));
            }
        };

        (
            RcuBlockInfo { info: block_info, ptr },
            RcuBaseRetirePerm {
                domain: self.id(),
                perm: retire_perm,
                observation: retire_observation,
                ptr,
            },
        )
    }

    /// Establishes agreement between domain authority and persistent block
    /// information supplied by a client or an atomic-history invariant.
    pub proof fn lemma_block_info_agree<T>(tracked &self, tracked info: &RcuBlockInfo<T>)
        requires
            self.wf(),
            info.domain() == self.id(),
        ensures
            self.objects().contains_pair(info.obj(), info.addr()),
    {
        info.info.agree(&self.objects);
    }

    /// Registers one reader slot and returns the paper's `Inactive(tid)`
    /// resource for it.
    pub proof fn tracked_register_reader(
        tracked &mut self,
        reader: RcuReaderContext,
    ) -> (tracked res: RcuInactive)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).retire_registry() == old(self).retire_registry(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).objects() == old(self).objects(),
            final(self).retired() == old(self).retired(),
            final(self).retire_observations() == old(self).retire_observations(),
            res.domain() == final(self).id(),
            res.tid() == old(self).next_reader(),
            res.reader() == reader,
            res.belongs_to(*final(self)),
            res.wf(),
    {
        let ghost tid = self.next_reader;
        assert(!self.readers@.contains_key(tid));
        let tracked state = self.readers.insert(tid, false);
        self.next_reader = self.next_reader + 1;
        assert forall|registered: nat| #[trigger]
            self.readers@.contains_key(registered) implies registered < self.next_reader by {
            if registered != tid {
                assert(old(self).readers@.contains_key(registered));
            }
        };
        assert forall|registered: nat| #[trigger]
            self.readers@.contains_key(registered) implies !self.readers@[registered] by {
            if registered != tid {
                assert(old(self).readers@.contains_key(registered));
            }
        };
        RcuInactive { domain: self.id(), state, reader }
    }

    /// Starts a read-side critical section, snapshotting the set `X` of AIds
    /// whose root-removal observation is covered by the entering thread's
    /// weak-memory view.
    ///
    /// The paper only requires `X` to be a subset of all retired allocations.
    /// Using `retired` itself here would be too strong: a reader may safely
    /// observe a newly retired stale pointer while that retirement's grace
    /// period is still in progress.
    pub proof fn tracked_guard_start(
        tracked &self,
        tracked inactive: RcuInactive,
        root: Loc,
        start_view: Irc11ThreadView,
    ) -> (tracked res: RcuBaseGuard)
        requires
            self.wf(),
            inactive.belongs_to(*self),
            inactive.wf(),
        ensures
            res.belongs_to(*self),
            res.tid() == inactive.tid(),
            res.reader() == inactive.reader(),
            res.root() == root,
            res.start_view() == start_view,
            res.retire_observation_registry() == self.retire_observation_registry(),
            res.expired() == self.observed_retired(root, start_view),
            res.protected() == Map::<usize, nat>::empty(),
            res.wf(),
    {
        let ghost tid = inactive.tid();
        inactive.state.agree(&self.readers);
        assert(self.readers@.contains_key(tid));
        RcuBaseGuard {
            domain: self.id(),
            state: inactive.state,
            reader: inactive.reader,
            root,
            start_view,
            retire_observation_registry: self.retire_observation_registry(),
            expired: self.observed_retired(root, start_view),
            protected: Map::empty(),
        }
    }

    /// Implements the base `rcu-retire` transition by adding the detached AId
    /// to `RcuState.R` and consuming its unique traversal retire permission.
    pub proof fn tracked_retire<T>(
        tracked &mut self,
        tracked retire: RcuRetirePerm<T>,
        removal: RcuRemovalObservation,
    ) -> (tracked res: RcuRetired<T>)
        requires
            old(self).wf(),
            retire.belongs_to(*old(self)),
            retire.wf(),
            retire.ready_to_retire(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).retire_registry() == old(self).retire_registry(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).objects() == old(self).objects(),
            final(self).retired() == old(self).retired().insert(retire.obj()),
            final(self).retire_observations() == old(self).retire_observations().insert(
                retire.obj(),
                removal,
            ),
            res.domain() == final(self).id(),
            res.obj() == retire.obj(),
            res.ptr() == retire.ptr(),
            res.removal() == removal,
            res.retire_observation_registry() == final(self).retire_observation_registry(),
            res.wf(),
    {
        let ghost domain = retire.domain();
        let ghost obj = retire.obj();
        let ghost ptr = retire.ptr();
        retire.base.perm.agree(&self.retire_perms);
        retire.base.observation.agree(&self.retire_observation_cells);
        assert(self.objects().contains_key(obj));
        let tracked mut observation = retire.base.observation;
        observation.update(&mut self.retire_observation_cells, Some(removal));
        let tracked observation = observation.persist();
        self.retired = self.retired.insert(obj);
        self.retire_observations = self.retire_observations.insert(obj, removal);
        assert(self.objects@ == old(self).objects@);
        assert(self.retire_perms@ == old(self).retire_perms@);
        assert(self.readers@ == old(self).readers@);
        assert(self.next_obj() == old(self).next_obj());
        assert(self.next_reader() == old(self).next_reader());
        assert(self.retire_observation_cells@ == old(self).retire_observation_cells@.insert(
            obj,
            Some(removal),
        ));
        assert(self.retire_observation_cells@.dom() == old(self).retire_observation_cells@.dom());
        assert(self.retire_observation_cells@.dom() == self.objects@.dom());
        assert forall|registered: nat| #[trigger] self.objects@.contains_key(registered) implies {
            match self.retire_observation_cells@[registered] {
                Some(recorded) => self.retire_observations().contains_pair(registered, recorded),
                None => !self.retire_observations().contains_key(registered),
            }
        } by {
            if registered == obj {
                assert(self.retire_observation_cells@[registered] == Some(removal));
                assert(self.retire_observations().contains_pair(registered, removal));
            } else {
                assert(self.retire_observation_cells@[registered] == old(
                    self,
                ).retire_observation_cells@[registered]);
                assert(self.retire_observations().contains_key(registered) == old(
                    self,
                ).retire_observations().contains_key(registered));
            }
        };
        assert(self.retired().subset_of(self.objects().dom()));
        assert(self.retire_observations().dom() == self.retired());
        let tracked fact = retire.base.perm.persist();
        RcuRetired { fact: RcuRetiredFact { domain, fact, observation }, ptr }
    }
}

/// The paper's unique `Inactive(tid)` reader resource.
pub tracked struct RcuInactive {
    ghost domain: Loc,
    state: GhostPointsTo<nat, bool>,
    ghost reader: RcuReaderContext,
}

impl RcuInactive {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn tid(self) -> nat {
        self.state.key()
    }

    pub closed spec fn reader(self) -> RcuReaderContext {
        self.reader
    }

    pub closed spec fn reader_registry(self) -> Loc {
        self.state.id()
    }

    pub closed spec fn wf(self) -> bool {
        true
    }

    pub closed spec fn belongs_to(self, domain: RcuDomainAuth) -> bool {
        &&& self.domain() == domain.id()
        &&& self.state.id() == domain.reader_registry()
    }
}

/// The base paper guard `Guard(tid, X, G)`.
///
/// `expired` is the start-time snapshot `X`. `protected[addr] = a` is the
/// mutable protection map `G` populated by successful protect operations.
/// `root` and `start_view` are implementation-refinement metadata: they are
/// not additional assumptions in the paper's abstract `Guard(tid, X, G)`, but
/// retain the witness from which `X` was computed.
pub tracked struct RcuBaseGuard {
    ghost domain: Loc,
    state: GhostPointsTo<nat, bool>,
    ghost reader: RcuReaderContext,
    ghost root: Loc,
    ghost start_view: Irc11ThreadView,
    ghost retire_observation_registry: Loc,
    ghost expired: Set<nat>,
    ghost protected: Map<usize, nat>,
}

impl RcuBaseGuard {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn tid(self) -> nat {
        self.state.key()
    }

    pub closed spec fn reader_registry(self) -> Loc {
        self.state.id()
    }

    pub closed spec fn reader(self) -> RcuReaderContext {
        self.reader
    }

    /// Root atomic whose removal history determined this guard's expired set.
    pub closed spec fn root(self) -> Loc {
        self.root
    }

    /// Weak-memory view captured when this read-side critical section began.
    pub closed spec fn start_view(self) -> Irc11ThreadView {
        self.start_view
    }

    /// Registry that issued persistent retirement facts for this domain.
    pub closed spec fn retire_observation_registry(self) -> Loc {
        self.retire_observation_registry
    }

    pub closed spec fn expired(self) -> Set<nat> {
        self.expired
    }

    pub closed spec fn protected(self) -> Map<usize, nat> {
        self.protected
    }

    pub closed spec fn wf(self) -> bool {
        &&& !self.state.value()
        &&& forall|addr: usize| #[trigger]
            self.protected().dom().contains(addr) ==> !self.expired().contains(
                self.protected()[addr],
            )
    }

    pub closed spec fn belongs_to(self, domain: RcuDomainAuth) -> bool {
        &&& self.domain() == domain.id()
        &&& self.state.id() == domain.reader_registry()
        &&& self.retire_observation_registry() == domain.retire_observation_registry()
    }

    pub closed spec fn protects(self, addr: usize, obj: nat) -> bool {
        self.protected().contains_pair(addr, obj)
    }

    /// Implements the paper's local `Guard -> Inactive` unlock rule.
    ///
    /// The domain registry only certifies the reader-instance identity; it
    /// does not track critical-section phase. Consequently this transition
    /// consumes the linear guard without opening `RcuState` or the root atomic
    /// invariant.
    pub proof fn tracked_stop(tracked self) -> (tracked res: RcuInactive)
        requires
            self.wf(),
        ensures
            res.domain() == self.domain(),
            res.tid() == self.tid(),
            res.reader() == self.reader(),
            res.wf(),
            res.reader_registry() == self.reader_registry(),
    {
        RcuInactive { domain: self.domain, state: self.state, reader: self.reader }
    }

    /// Implements the base `Guard-protect` update. An object already in the
    /// guard's start snapshot `X` cannot be newly protected by this guard.
    pub proof fn tracked_protect<T>(tracked &mut self, tracked info: &RcuBlockInfo<T>)
        requires
            old(self).wf(),
            info.wf(),
            info.domain() == old(self).domain(),
            !old(self).expired().contains(info.obj()),
        ensures
            final(self).wf(),
            final(self).domain() == old(self).domain(),
            final(self).tid() == old(self).tid(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).reader() == old(self).reader(),
            final(self).root() == old(self).root(),
            final(self).start_view() == old(self).start_view(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).expired() == old(self).expired(),
            final(self).protected() == old(self).protected().insert(info.addr(), info.obj()),
            final(self).protects(info.addr(), info.obj()),
    {
        self.protected = self.protected.insert(info.addr(), info.obj());
        assert forall|addr: usize| #[trigger]
            self.protected().dom().contains(addr) implies !self.expired().contains(
            self.protected()[addr],
        ) by {
            if addr == info.addr() {
                assert(self.protected()[addr] == info.obj());
            } else {
                assert(old(self).protected().dom().contains(addr));
                assert(self.protected()[addr] == old(self).protected()[addr]);
            }
        };
    }
}

/// Persistent `BlockInfo(l, a, P)` for one RCU-managed allocation.
///
/// The current Verus cut records the allocation's typed pointer and physical
/// address; the client-owned block predicate `P` remains represented by the
/// corresponding `P::Permission` at the executable boundary. The resource
/// token is persistent and can therefore be copied into every weak-memory
/// history entry that publishes this allocation.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuBlockInfo<T> {
    info: GhostPersistentPointsTo<nat, usize>,
    ghost ptr: *mut T,
}

impl<T> RcuBlockInfo<T> {
    pub closed spec fn domain(self) -> Loc {
        self.info.id()
    }

    pub closed spec fn obj(self) -> nat {
        self.info.key()
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.ptr
    }

    pub closed spec fn addr(self) -> usize {
        self.info.value()
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.addr() == self.ptr().addr()
        &&& self.ptr().addr() != 0
    }

    /// Opens the address facts hidden by the block-info abstraction.
    pub proof fn lemma_wf_facts(tracked &self)
        requires
            self.wf(),
        ensures
            self.addr() == self.ptr().addr(),
            self.ptr().addr() != 0,
    {
    }

    /// Persistent block information can be retained by both the client and
    /// every historical atomic message that mentions the allocation.
    pub proof fn tracked_duplicate(tracked &self) -> (tracked res: Self)
        ensures
            res.domain() == self.domain(),
            res.obj() == self.obj(),
            res.ptr() == self.ptr(),
            res.addr() == self.addr(),
            res.wf() == self.wf(),
    {
        let tracked info = self.info.duplicate();
        RcuBlockInfo { info, ptr: self.ptr }
    }
}

/// Compatibility name used by the callback/traversal boundary.
pub type RcuObjectId<T> = RcuBlockInfo<T>;

/// Regression proof for the allocation-ID discipline required by relaxed
/// memory RCU.
///
/// `res.0` and `res.1` are two persistent copies of one registration, so they
/// carry the same AId. `res.2` is a second registration at the same physical
/// address, so it carries a fresh AId. This is the distinction that rules out
/// identifying stale weak-memory messages by address alone.
pub proof fn registration_distinguishes_reused_address<T>(ptr: *mut T) -> (tracked res: (
    RcuBlockInfo<T>,
    RcuBlockInfo<T>,
    RcuBlockInfo<T>,
))
    requires
        ptr.addr() != 0,
    ensures
        res.0.domain() == res.1.domain(),
        res.0.domain() == res.2.domain(),
        res.0.obj() == res.1.obj(),
        res.0.obj() != res.2.obj(),
        res.0.addr() == ptr.addr(),
        res.1.addr() == ptr.addr(),
        res.2.addr() == ptr.addr(),
{
    let tracked mut domain = RcuDomainAuth::tracked_new();
    let tracked (first, _first_retire) = domain.tracked_register(ptr);
    let tracked first_history_copy = first.tracked_duplicate();
    let tracked (second, _second_retire) = domain.tracked_register(ptr);
    assert(first.obj() < second.obj());
    (first, first_history_copy, second)
}

/// Regression proof for registration-time identity across re-publication.
///
/// Both history entries are justified by the same persistent `BlockInfo`, so
/// they contain the same AId even though they have different atomic
/// timestamps. This is the paper's required separation between allocation
/// identity and modification-order position.
pub proof fn registered_republication_preserves_allocation_id<T>(ptr: *mut T) -> (tracked res: (
    RcuRootGhost,
    RcuRegistration<T>,
))
    requires
        ptr.addr() != 0,
    ensures
        res.0.publications().dom() == Set::empty().insert(0nat).insert(1nat),
        res.0.publications()[0] == Some(res.1.0.obj()),
        res.0.publications()[1] == Some(res.1.0.obj()),
        res.1.0.domain() == res.0.domain(),
        res.1.0.obj() == res.1.1.obj(),
{
    let ghost view = Irc11ThreadView::empty();
    let ghost initial = Irc11History(Map::empty().insert(0nat, (ptr, view)));
    let tracked (mut root, registration_opt) = RcuRootGhost::tracked_initial(ptr, initial, 0, view);
    let tracked registration = registration_opt.tracked_unwrap();
    let ghost next = initial.insert(1, ptr, view);
    root.tracked_push_registered(initial, next, 0, 1, ptr, view, &registration.0);
    (root, registration)
}

/// Regression proof for ownership transfer on root replacement.
///
/// The old registration leaves the atomic ownership state exactly once, while
/// the fresh registration for `next_ptr` becomes current. This is the resource
/// handoff that later feeds traversal retirement and callback construction.
pub proof fn owned_root_replacement_retires_previous_registration<T>(
    first_ptr: *mut T,
    next_ptr: *mut T,
) -> (tracked res: (RcuRootOwnedGhost<T>, RcuRetiredOwnedObject<T, ()>))
    requires
        first_ptr.addr() != 0,
        next_ptr.addr() != 0,
    ensures
        res.1.ptr() == first_ptr,
        res.1.object().obj() == res.1.retired().obj(),
        res.0.current_registration() is Some,
        res.0.current_registration()->Some_0.0.ptr() == next_ptr,
        res.0.current_registration()->Some_0.0.obj()
            == res.0.current_registration()->Some_0.1.obj(),
        res.1.domain() == res.0.domain(),
{
    let ghost view = Irc11ThreadView::empty();
    let ghost initial = Irc11History(Map::empty().insert(0nat, (first_ptr, view)));
    let tracked mut root = RcuRootOwnedGhost::tracked_initial(
        first_ptr,
        Some(()),
        initial,
        0,
        view,
    );
    let ghost next_history = initial.insert(1, next_ptr, view);
    let tracked detached = root.tracked_push_fresh::<UnitRcuRootOwnership>(
        initial,
        next_history,
        0,
        1,
        next_ptr,
        view,
        root.domain(),
        Some(()),
    );
    let tracked detached = detached.tracked_unwrap();
    (root, detached)
}

/// Low-level base retire permission.
///
/// This is the paper's unique `BaseRetirePerm(l, a)`. The embedded owning
/// points-to resource makes duplication impossible. By itself it is not enough
/// to retire or reclaim an object; traversal must first establish that every
/// relevant incoming edge has been removed.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuBaseRetirePerm<T> {
    ghost domain: Loc,
    perm: GhostPointsTo<nat, usize>,
    observation: GhostPointsTo<nat, Option<RcuRemovalObservation>>,
    ghost ptr: *mut T,
}

impl<T> RcuBaseRetirePerm<T> {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.ptr
    }

    pub closed spec fn obj(self) -> nat {
        self.perm.key()
    }

    pub closed spec fn addr(self) -> usize {
        self.perm.value()
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.addr() == self.ptr().addr()
        &&& self.observation.key() == self.obj()
        &&& self.observation.value() is None
    }

    pub closed spec fn belongs_to(self, domain: RcuDomainAuth) -> bool {
        &&& self.domain() == domain.id()
        &&& self.perm.id() == domain.retire_registry()
        &&& self.observation.id() == domain.retire_observation_registry()
    }
}

/// High-level retire permission.
///
/// This corresponds to `RetirePerm(l, a) = BaseRetirePerm(l, a) *
/// exists D LV. SeenRemoved(D, LV) * a in D`.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRetirePerm<T> {
    base: RcuBaseRetirePerm<T>,
    ghost seen_removed: RcuSeenRemoved<T>,
}

impl<T> RcuRetirePerm<T> {
    pub closed spec fn base(self) -> RcuBaseRetirePerm<T> {
        self.base
    }

    pub closed spec fn domain(self) -> Loc {
        self.base.domain()
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.base.ptr()
    }

    pub closed spec fn obj(self) -> nat {
        self.base.obj()
    }

    pub closed spec fn seen_removed(self) -> RcuSeenRemoved<T> {
        self.seen_removed
    }

    pub open spec fn wf(self) -> bool {
        self.base().wf()
    }

    /// The traversal layer has established that this object may be retired.
    /// Reclamation still requires a completed base-RCU grace period.
    pub open spec fn ready_to_retire(self) -> bool {
        self.seen_removed().removed.contains(self.obj())
    }

    pub closed spec fn belongs_to(self, domain: RcuDomainAuth) -> bool {
        self.base.belongs_to(domain)
    }
}

/// Internal bridge for the directly owned root-pointer specialization.
///
/// This is deliberately not a public traversal rule. `RcuSeenRemoved` is only
/// a logical view and can be constructed freely, so exposing this function
/// would let a client claim detachment without owning the paper's
/// `RcuPointedBy`/incoming-link authority. The executable `Rcu<P>` root uses
/// this bridge only while replacing its directly owned root publication. A
/// general linked structure must instead obtain a retire permission from a
/// future tracked traversal-state transition.
proof fn lift_direct_root_retire_perm<T>(
    tracked base: RcuBaseRetirePerm<T>,
    seen_removed: RcuSeenRemoved<T>,
) -> (tracked perm: RcuRetirePerm<T>)
    requires
        base.wf(),
        seen_removed.removed.contains(base.obj()),
    ensures
        perm.base() == base,
        perm.domain() == base.domain(),
        perm.ptr() == base.ptr(),
        perm.obj() == base.obj(),
        perm.seen_removed() == seen_removed,
        perm.wf(),
        perm.ready_to_retire(),
{
    RcuRetirePerm { base, seen_removed }
}

/// Persistent, type-erased evidence that one allocation passed the base
/// `rcu-retire` transition.
///
/// `fact` comes from consuming the allocation's unique `BaseRetirePerm`.
/// `observation` comes from updating that permission's domain-owned
/// observation cell from `None` to `Some(removal)`. Their keys agree, so
/// clients cannot attach an unrelated detachment observation to a registered
/// object. Both facts are persistent and remain duplicable after callback type
/// erasure.
pub tracked struct RcuRetiredFact {
    ghost domain: Loc,
    fact: GhostPersistentPointsTo<nat, usize>,
    observation: GhostPersistentPointsTo<nat, Option<RcuRemovalObservation>>,
}

impl RcuRetiredFact {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn obj(self) -> nat {
        self.fact.key()
    }

    pub closed spec fn addr(self) -> usize {
        self.fact.value()
    }

    pub closed spec fn removal(self) -> RcuRemovalObservation {
        self.observation.value()->Some_0
    }

    pub closed spec fn retire_observation_registry(self) -> Loc {
        self.observation.id()
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.fact.key() == self.observation.key()
        &&& self.observation.value() is Some
    }

    pub open spec fn record(self) -> RcuRetiredRecord {
        RcuRetiredRecord {
            domain: self.domain(),
            obj: self.obj(),
            retire_observation_registry: self.retire_observation_registry(),
            removal: self.removal(),
        }
    }

    pub closed spec fn matches(self, summary: RcuCallbackSummary) -> bool {
        &&& summary.domain == self.domain()
        &&& summary.obj == self.obj()
        &&& summary.removal == self.removal()
        &&& summary.retire_observation_registry == self.retire_observation_registry()
    }

    pub proof fn tracked_duplicate(tracked &self) -> (tracked res: Self)
        requires
            self.wf(),
        ensures
            res.wf(),
            res.record() == self.record(),
            res.domain() == self.domain(),
            res.obj() == self.obj(),
            res.addr() == self.addr(),
            res.removal() == self.removal(),
            res.retire_observation_registry() == self.retire_observation_registry(),
    {
        let tracked fact = self.fact.duplicate();
        let tracked observation = self.observation.duplicate();
        RcuRetiredFact { domain: self.domain, fact, observation }
    }

    /// Establishes that this callback fact contains the observation recorded by
    /// the corresponding domain authority.
    pub proof fn lemma_observation_agrees(tracked &self, tracked domain: &RcuDomainAuth)
        requires
            self.wf(),
            domain.wf(),
            self.domain() == domain.id(),
            self.retire_observation_registry() == domain.retire_observation_registry(),
        ensures
            domain.retired().contains(self.obj()),
            domain.retire_observations().contains_pair(self.obj(), self.removal()),
    {
        self.observation.agree(&domain.retire_observation_cells);
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

/// A finite collection of persistent retirement facts.
///
/// The map key is the complete retirement record, rather than just an AId.
/// This lets CPU-generation state accumulate facts from independent RCU
/// domains without assuming that domain IDs determine observation-registry
/// identities by pure equality alone.
pub tracked struct RcuRetiredFacts {
    facts: Map<RcuRetiredRecord, RcuRetiredFact>,
}

impl RcuRetiredFacts {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        forall|record: RcuRetiredRecord| #[trigger]
            self.facts.contains_key(record) ==> {
                &&& self.facts[record].wf()
                &&& self.facts[record].record() == record
            }
    }

    /// Complete set of certified retirement records in this collection.
    pub closed spec fn records(self) -> Set<RcuRetiredRecord> {
        self.facts.dom()
    }

    pub closed spec fn contains(self, record: RcuRetiredRecord) -> bool {
        self.facts.contains_key(record)
    }

    /// Every retained detachment observation is covered by `view`.
    ///
    /// The retirement facts themselves are persistent, but this predicate is
    /// the separate weak-memory premise needed before a CPU report may publish
    /// them to readers in a later quiescent generation.
    pub open spec fn observed_by(self, view: Irc11ThreadView) -> bool {
        forall|record: RcuRetiredRecord| #[trigger]
            self.records().contains(record) ==> record.removal.observed_by(view)
    }

    proof fn lemma_matching_subset_observed_retired(
        tracked &self,
        tracked domain: &RcuDomainAuth,
        root: Loc,
        view: Irc11ThreadView,
        records: Set<RcuRetiredRecord>,
    )
        requires
            domain.wf(),
            self.observed_by(view),
            records.subset_of(self.records()),
        ensures
            forall|record: RcuRetiredRecord| #[trigger]
                records.contains(record) && record.domain == domain.id()
                    && record.retire_observation_registry == domain.retire_observation_registry()
                    && record.removal.root == root ==> domain.observed_retired(root, view).contains(
                    record.obj,
                ),
        decreases records.len(),
    {
        if !records.is_empty() {
            let ghost record = records.choose();
            let ghost rest = records.remove(record);
            let tracked fact = self.tracked_borrow(record);
            assert(self.records().contains(record));
            assert(record.removal.observed_by(view));
            if record.domain == domain.id() && record.retire_observation_registry
                == domain.retire_observation_registry() && record.removal.root == root {
                fact.lemma_observation_agrees(domain);
                assert(domain.retired().contains(record.obj));
                assert(domain.retire_observations().contains_pair(record.obj, record.removal));
            }
            Self::lemma_matching_subset_observed_retired(self, domain, root, view, rest);
            assert forall|candidate: RcuRetiredRecord| #[trigger]
                records.contains(candidate) && candidate.domain == domain.id()
                    && candidate.retire_observation_registry == domain.retire_observation_registry()
                    && candidate.removal.root == root implies domain.observed_retired(
                root,
                view,
            ).contains(candidate.obj) by {
                if candidate == record {
                } else {
                    assert(rest.contains(candidate));
                }
            };
        }
    }

    /// Converts persistent retirement facts whose detachments have been
    /// observed into membership in the domain's entry-time expired set.
    ///
    /// This is the paper's `Retired(a, Q)` plus observation-of-`Q` step. The
    /// retirement fact alone is deliberately insufficient.
    pub proof fn lemma_matching_records_observed_retired(
        tracked &self,
        tracked domain: &RcuDomainAuth,
        root: Loc,
        view: Irc11ThreadView,
    )
        requires
            domain.wf(),
            self.observed_by(view),
        ensures
            forall|record: RcuRetiredRecord| #[trigger]
                self.records().contains(record) && record.domain == domain.id()
                    && record.retire_observation_registry == domain.retire_observation_registry()
                    && record.removal.root == root ==> domain.observed_retired(root, view).contains(
                    record.obj,
                ),
    {
        Self::lemma_matching_subset_observed_retired(self, domain, root, view, self.records());
    }

    /// Creates an empty retirement-fact collection.
    pub proof fn empty() -> (tracked res: Self)
        ensures
            res.records() == Set::<RcuRetiredRecord>::empty(),
    {
        RcuRetiredFacts { facts: Map::tracked_empty() }
    }

    /// Borrows the persistent fact for one record.
    pub proof fn tracked_borrow(tracked &self, record: RcuRetiredRecord) -> (tracked res:
        &RcuRetiredFact)
        requires
            self.records().contains(record),
        ensures
            res.wf(),
            res.record() == record,
    {
        use_type_invariant(self);
        let tracked res = self.facts.tracked_borrow(record);
        res
    }

    /// Inserts a persistent copy of `fact`.
    pub proof fn tracked_insert(tracked &mut self, tracked fact: &RcuRetiredFact)
        requires
            fact.wf(),
        ensures
            final(self).records() == old(self).records().insert(fact.record()),
            final(self).contains(fact.record()),
    {
        use_type_invariant(&*self);
        use_type_invariant(fact);
        let ghost record = fact.record();
        let ghost old_records = self.facts.dom();
        if !self.contains(record) {
            let tracked duplicate = fact.tracked_duplicate();
            self.facts.tracked_insert(record, duplicate);
            assert forall|saved: RcuRetiredRecord| #[trigger]
                self.facts.contains_key(saved) implies {
                &&& self.facts[saved].wf()
                &&& self.facts[saved].record() == saved
            } by {
                if saved == record {
                } else {
                    assert(old_records.contains(saved));
                }
            };
        }
    }

    proof fn tracked_duplicate_keys(
        tracked source: &Map<RcuRetiredRecord, RcuRetiredFact>,
        keys: Set<RcuRetiredRecord>,
    ) -> (tracked duplicates: Map<RcuRetiredRecord, RcuRetiredFact>)
        requires
            keys.subset_of(source.dom()),
            forall|record: RcuRetiredRecord| #[trigger]
                source.dom().contains(record) ==> {
                    &&& source[record].wf()
                    &&& source[record].record() == record
                },
        ensures
            duplicates.dom() == keys,
            forall|record: RcuRetiredRecord| #[trigger]
                keys.contains(record) ==> {
                    &&& duplicates[record].wf()
                    &&& duplicates[record].record() == record
                },
        decreases keys.len(),
    {
        if keys.is_empty() {
            Map::tracked_empty()
        } else {
            let ghost record = keys.choose();
            let ghost rest = keys.remove(record);
            let tracked mut duplicates = Self::tracked_duplicate_keys(source, rest);
            let tracked fact = source.tracked_borrow(record);
            let tracked duplicate = fact.tracked_duplicate();
            duplicates.tracked_insert(record, duplicate);
            assert(keys == rest.insert(record));
            assert forall|saved: RcuRetiredRecord| #[trigger] keys.contains(saved) implies {
                &&& duplicates[saved].wf()
                &&& duplicates[saved].record() == saved
            } by {
                if saved == record {
                } else {
                    assert(rest.contains(saved));
                }
            };
            duplicates
        }
    }

    /// Duplicates this persistent fact collection.
    pub proof fn tracked_duplicate(tracked &self) -> (tracked res: Self)
        ensures
            res.records() == self.records(),
    {
        use_type_invariant(self);
        let tracked facts = Self::tracked_duplicate_keys(&self.facts, self.facts.dom());
        RcuRetiredFacts { facts }
    }

    proof fn tracked_merge_keys(
        tracked target: &mut RcuRetiredFacts,
        tracked source: &RcuRetiredFacts,
        keys: Set<RcuRetiredRecord>,
    )
        requires
            keys.subset_of(source.records()),
        ensures
            final(target).records() == old(target).records().union(keys),
        decreases keys.len(),
    {
        if !keys.is_empty() {
            let ghost record = keys.choose();
            let ghost rest = keys.remove(record);
            let tracked fact = source.tracked_borrow(record);
            target.tracked_insert(fact);
            Self::tracked_merge_keys(target, source, rest);
            assert(keys == rest.insert(record));
        }
    }

    /// Adds persistent copies of all facts in `other`.
    pub proof fn tracked_merge(tracked &mut self, tracked other: &RcuRetiredFacts)
        ensures
            final(self).records() == old(self).records().union(other.records()),
    {
        Self::tracked_merge_keys(self, other, other.records());
    }
}

/// Typed objective record that an allocation has passed the base
/// `rcu-retire` transition. It is safe to enqueue its callback, but not yet
/// safe to execute it; execution additionally needs monitor grace-period
/// completion.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRetired<T> {
    fact: RcuRetiredFact,
    ghost ptr: *mut T,
}

impl<T> RcuRetired<T> {
    pub closed spec fn domain(self) -> Loc {
        self.fact.domain()
    }

    pub closed spec fn obj(self) -> nat {
        self.fact.obj()
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.ptr
    }

    pub closed spec fn addr(self) -> usize {
        self.fact.addr()
    }

    pub closed spec fn removal(self) -> RcuRemovalObservation {
        self.fact.removal()
    }

    /// Authoritative observation registry that issued this retirement fact.
    pub closed spec fn retire_observation_registry(self) -> Loc {
        self.fact.retire_observation_registry()
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.fact.wf()
        &&& self.addr() == self.ptr().addr()
    }

    proof fn tracked_into_fact(tracked self) -> (tracked res: RcuRetiredFact)
        requires
            self.wf(),
        ensures
            res.domain() == self.domain(),
            res.obj() == self.obj(),
            res.addr() == self.ptr().addr(),
            res.removal() == self.removal(),
            res.retire_observation_registry() == self.retire_observation_registry(),
    {
        self.fact
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

/// Regression proof for the distinction between retirement and expiration.
///
/// Even a reader registered after `retire` may protect the object while no
/// grace period has expired it. This is the stale-read case required by the
/// paper's relaxed-memory base specification.
pub proof fn retired_but_unexpired_object_remains_protectable<T>(ptr: *mut T) -> (tracked res: (
    RcuBaseGuard,
    RcuBlockInfo<T>,
))
    requires
        ptr.addr() != 0,
    ensures
        res.1.ptr() == ptr,
        res.0.domain() == res.1.domain(),
        res.0.expired() == Set::<nat>::empty(),
        res.0.protects(res.1.addr(), res.1.obj()),
{
    let tracked mut domain = RcuDomainAuth::tracked_new();
    let tracked (info, base) = domain.tracked_register(ptr);
    let ghost reader = arbitrary();
    let tracked inactive = domain.tracked_register_reader(reader);
    let tracked mut guard = domain.tracked_guard_start(
        inactive,
        domain.id(),
        Irc11ThreadView::empty(),
    );
    let ghost seen_removed = RcuSeenRemoved {
        removed: Set::empty().insert(info.obj()),
        link_view: RcuLinkView::empty(),
    };
    let tracked retire = lift_direct_root_retire_perm(base, seen_removed);
    let ghost removal = RcuRemovalObservation {
        root: domain.id(),
        timestamp: 1,
        message_view: Irc11ThreadView::empty(),
    };
    let tracked _retired = domain.tracked_retire(retire, removal);
    assert(guard.expired() == Set::<nat>::empty());
    assert(!guard.expired().contains(info.obj()));
    guard.tracked_protect(&info);
    (guard, info)
}

/// Regression proof that observing a retirement makes it expired for a new
/// guard.
///
/// Timestamp zero is covered by an empty weak-memory view. Consequently the
/// retired allocation enters the new guard's `X` snapshot and cannot be added
/// to its protection map.
pub proof fn observed_retired_object_enters_guard_expired<T>(ptr: *mut T) -> (tracked res: (
    RcuBaseGuard,
    RcuBlockInfo<T>,
))
    requires
        ptr.addr() != 0,
    ensures
        res.1.ptr() == ptr,
        res.0.domain() == res.1.domain(),
        res.0.expired().contains(res.1.obj()),
{
    let tracked mut domain = RcuDomainAuth::tracked_new();
    let tracked (info, base) = domain.tracked_register(ptr);
    let ghost seen_removed = RcuSeenRemoved {
        removed: Set::empty().insert(info.obj()),
        link_view: RcuLinkView::empty(),
    };
    let tracked retire = lift_direct_root_retire_perm(base, seen_removed);
    let ghost removal = RcuRemovalObservation {
        root: domain.id(),
        timestamp: 0,
        message_view: Irc11ThreadView::empty(),
    };
    let tracked _retired = domain.tracked_retire(retire, removal);

    let ghost reader = arbitrary();
    let tracked inactive = domain.tracked_register_reader(reader);
    let tracked guard = domain.tracked_guard_start(inactive, domain.id(), Irc11ThreadView::empty());
    assert(removal.observed_by(Irc11ThreadView::empty()));
    assert(guard.expired().contains(info.obj()));
    (guard, info)
}

/// Non-generic proof certificate carried across the type-erasure boundary.
///
/// A certificate can only be produced from a typed traversal retire permission,
/// but after that point the monitor only needs the erased callback summary.
pub tracked struct RcuCallbackSafety {
    retired: RcuRetiredFact,
}

impl RcuCallbackSafety {
    pub closed spec fn domain(self) -> Loc {
        self.retired.domain()
    }

    pub closed spec fn obj(self) -> nat {
        self.retired.obj()
    }

    pub closed spec fn removal(self) -> RcuRemovalObservation {
        self.retired.removal()
    }

    pub closed spec fn retire_observation_registry(self) -> Loc {
        self.retired.retire_observation_registry()
    }

    /// The monitor may assign any future batch generation, but it cannot
    /// change the retired object's domain or allocation identity.
    pub closed spec fn matches(self, summary: RcuCallbackSummary) -> bool {
        self.retired.matches(summary)
    }

    /// Establishes the abstract matching predicate without exposing the
    /// persistent retirement resource to callback-monitor clients.
    pub proof fn lemma_matches(tracked &self, summary: RcuCallbackSummary)
        requires
            summary.domain == self.domain(),
            summary.obj == self.obj(),
            summary.removal == self.removal(),
            summary.retire_observation_registry == self.retire_observation_registry(),
        ensures
            self.matches(summary),
    {
    }

    /// Duplicates the persistent base-retirement fact for an object-level
    /// reclaim permit.
    pub proof fn tracked_retired_fact(tracked &self, summary: RcuCallbackSummary) -> (tracked res:
        RcuRetiredFact)
        requires
            self.matches(summary),
        ensures
            res.wf(),
            res.domain() == self.domain(),
            res.obj() == self.obj(),
            res.removal() == self.removal(),
            res.retire_observation_registry() == self.retire_observation_registry(),
            res.matches(summary),
            res.record() == summary.retired_record(),
    {
        use_type_invariant(&self.retired);
        self.retired.tracked_duplicate()
    }
}

pub open spec fn callback_safety_from_traversal<T>(
    cert: RcuCallbackSafety,
    object: RcuObjectId<T>,
) -> bool {
    &&& cert.domain() == object.domain()
    &&& cert.obj() == object.obj()
}

/// Consume a typed traversal retire permission and compress it into the
/// non-generic summary needed by the type-erased callback monitor.
pub proof fn certify_callback_from_retired<T>(
    tracked object: &RcuObjectId<T>,
    tracked retired: RcuRetired<T>,
) -> (tracked cert: RcuCallbackSafety)
    requires
        object.domain() == retired.domain(),
        object.obj() == retired.obj(),
        object.ptr() == retired.ptr(),
    ensures
        cert.domain() == retired.domain(),
        cert.obj() == object.obj(),
        cert.removal() == retired.removal(),
        cert.retire_observation_registry() == retired.retire_observation_registry(),
        callback_safety_from_traversal(cert, *object),
{
    use_type_invariant(&retired);
    let tracked fact = retired.tracked_into_fact();
    RcuCallbackSafety { retired: fact }
}

/// Read-side guard token for one critical section.
///
/// This is the traversal-level guard: it includes the base guard protection and
/// the `SeenRemoved(D, LV)` observation used to rule out stale links.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuReadGuardToken<T> {
    base: RcuBaseGuard,
    ghost seen_removed: RcuSeenRemoved<T>,
}

impl<T> RcuReadGuardToken<T> {
    pub closed spec fn domain(self) -> Loc {
        self.base.domain()
    }

    pub closed spec fn tid(self) -> nat {
        self.base.tid()
    }

    pub closed spec fn reader_registry(self) -> Loc {
        self.base.reader_registry()
    }

    pub closed spec fn reader(self) -> RcuReaderContext {
        self.base.reader()
    }

    pub closed spec fn root(self) -> Loc {
        self.base.root()
    }

    pub closed spec fn start_view(self) -> Irc11ThreadView {
        self.base.start_view()
    }

    pub closed spec fn retire_observation_registry(self) -> Loc {
        self.base.retire_observation_registry()
    }

    pub closed spec fn expired(self) -> Set<nat> {
        self.base.expired()
    }

    pub closed spec fn protected(self) -> Map<usize, nat> {
        self.base.protected()
    }

    pub closed spec fn protects(self, addr: usize, obj: nat) -> bool {
        self.base.protects(addr, obj)
    }

    pub closed spec fn seen_removed(self) -> RcuSeenRemoved<T> {
        self.seen_removed
    }

    pub closed spec fn link_view(self) -> RcuLinkView<T> {
        self.seen_removed().link_view
    }

    pub open spec fn seen_at(self, obj: nat) -> LinkIndex {
        self.seen_removed().seen_at(obj)
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.base.wf()
        &&& self.expired().subset_of(self.seen_removed().removed)
    }

    pub closed spec fn is_for(self, domain: RcuDomainAuth) -> bool {
        self.base.belongs_to(domain)
    }

    /// Exposes the traversal-side consequence of a well-formed guard without
    /// opening the guard representation in client modules.
    pub proof fn lemma_expired_is_removed(tracked &self)
        requires
            self.wf(),
        ensures
            self.expired().subset_of(self.seen_removed().removed),
    {
    }

    pub proof fn lemma_protected_not_expired(tracked &self, addr: usize, obj: nat)
        requires
            self.wf(),
            self.protects(addr, obj),
        ensures
            !self.expired().contains(obj),
    {
    }

    /// Preconditions of the paper's base `Guard-protect` rule.
    ///
    /// This deliberately says only that the allocation was not already
    /// expired when the critical section started. Whether a stale traversal
    /// may still reach the allocation is proved separately from
    /// `SeenRemoved` and the link history.
    pub open spec fn can_base_protect(self, info: RcuBlockInfo<T>) -> bool {
        &&& self.wf()
        &&& info.wf()
        &&& info.domain() == self.domain()
        &&& !self.expired().contains(info.obj())
    }

    /// A base-protectable allocation that traversal has also proved is not in
    /// the guard's observed removed set.
    pub open spec fn can_protect(self, info: RcuBlockInfo<T>) -> bool {
        &&& self.can_base_protect(info)
        &&& !self.seen_removed().removed.contains(info.obj())
    }

    /// Combines the paper's base guard with traversal `SeenRemoved(D, LV)`.
    pub proof fn tracked_new(
        tracked base: RcuBaseGuard,
        seen_removed: RcuSeenRemoved<T>,
    ) -> (tracked res: Self)
        requires
            base.wf(),
            base.expired().subset_of(seen_removed.removed),
        ensures
            res.wf(),
            res.domain() == base.domain(),
            res.tid() == base.tid(),
            res.reader_registry() == base.reader_registry(),
            res.reader() == base.reader(),
            res.root() == base.root(),
            res.start_view() == base.start_view(),
            res.retire_observation_registry() == base.retire_observation_registry(),
            res.expired() == base.expired(),
            res.protected() == base.protected(),
            res.seen_removed() == seen_removed,
    {
        RcuReadGuardToken { base, seen_removed }
    }

    /// Lift a base guard using its start-time expired set as the initial
    /// traversal observation.
    pub proof fn tracked_from_base(tracked base: RcuBaseGuard) -> (tracked res: Self)
        requires
            base.wf(),
        ensures
            res.wf(),
            res.domain() == base.domain(),
            res.tid() == base.tid(),
            res.reader_registry() == base.reader_registry(),
            res.reader() == base.reader(),
            res.root() == base.root(),
            res.start_view() == base.start_view(),
            res.retire_observation_registry() == base.retire_observation_registry(),
            res.expired() == base.expired(),
            res.seen_removed().removed == base.expired(),
            res.link_view() == RcuLinkView::<T>::empty(),
    {
        let ghost seen_removed = RcuSeenRemoved {
            removed: base.expired(),
            link_view: RcuLinkView::empty(),
        };
        RcuReadGuardToken::tracked_new(base, seen_removed)
    }

    /// Consume the traversal wrapper when ending the read-side critical
    /// section.
    pub proof fn tracked_into_base(tracked self) -> (tracked res: RcuBaseGuard)
        requires
            self.wf(),
        ensures
            res.wf(),
            res.domain() == self.domain(),
            res.tid() == self.tid(),
            res.reader_registry() == self.reader_registry(),
            res.reader() == self.reader(),
            res.root() == self.root(),
            res.start_view() == self.start_view(),
            res.retire_observation_registry() == self.retire_observation_registry(),
            res.expired() == self.expired(),
            res.protected() == self.protected(),
    {
        self.base
    }

    /// Records one successful base `Guard-protect` operation in `G`.
    pub proof fn tracked_protect(tracked &mut self, tracked info: &RcuBlockInfo<T>)
        requires
            old(self).can_protect(*info),
        ensures
            final(self).wf(),
            final(self).domain() == old(self).domain(),
            final(self).tid() == old(self).tid(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).reader() == old(self).reader(),
            final(self).root() == old(self).root(),
            final(self).start_view() == old(self).start_view(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).expired() == old(self).expired(),
            final(self).seen_removed() == old(self).seen_removed(),
            final(self).protected() == old(self).protected().insert(info.addr(), info.obj()),
            final(self).protects(info.addr(), info.obj()),
    {
        self.base.tracked_protect(info);
    }

    /// Records a coherent observation of the next link event from an already
    /// protected source. The returned source witness is refreshed to carry the
    /// guard's advanced link-view snapshot.
    pub proof fn tracked_observe_link(
        tracked &mut self,
        tracked from: RcuProtectedPtr<T>,
        n: LinkIndex,
    ) -> (tracked res: RcuProtectedPtr<T>)
        requires
            old(self).wf(),
            from.protected_by(*old(self)),
            old(self).seen_at(from.obj()) <= n,
        ensures
            final(self).wf(),
            final(self).domain() == old(self).domain(),
            final(self).tid() == old(self).tid(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).reader() == old(self).reader(),
            final(self).root() == old(self).root(),
            final(self).start_view() == old(self).start_view(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).expired() == old(self).expired(),
            final(self).protected() == old(self).protected(),
            final(self).seen_removed().removed == old(self).seen_removed().removed,
            final(self).link_view() == old(self).link_view().observe(from.obj(), n),
            final(self).seen_at(from.obj()) == n,
            res.domain() == from.domain(),
            res.obj() == from.obj(),
            res.ptr() == from.ptr(),
            res.protected_by(*final(self)),
    {
        let ghost old_expired = self.expired();
        let ghost old_removed = self.seen_removed.removed;
        let ghost seen_removed = RcuSeenRemoved {
            removed: old_removed,
            link_view: self.seen_removed.link_view.observe(from.obj(), n),
        };
        self.seen_removed = seen_removed;
        assert(self.expired() == old_expired);
        assert(self.seen_removed.removed == old_removed);
        assert(self.expired().subset_of(self.seen_removed.removed));
        assert(self.wf());
        RcuProtectedPtr { domain: from.domain(), obj: from.obj(), ptr: from.ptr(), seen_removed }
    }

    /// In-place form of [`tracked_observe_link`](Self::tracked_observe_link).
    /// This is convenient for atomic loads, which must advance the guard and
    /// its source protection witness to the same traversal snapshot.
    pub proof fn tracked_observe_link_in_place(
        tracked &mut self,
        tracked from: &mut RcuProtectedPtr<T>,
        n: LinkIndex,
    )
        requires
            old(self).wf(),
            old(from).protected_by(*old(self)),
            old(self).seen_at(old(from).obj()) <= n,
        ensures
            final(self).wf(),
            final(self).domain() == old(self).domain(),
            final(self).tid() == old(self).tid(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).reader() == old(self).reader(),
            final(self).root() == old(self).root(),
            final(self).start_view() == old(self).start_view(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).expired() == old(self).expired(),
            final(self).protected() == old(self).protected(),
            final(self).seen_removed().removed == old(self).seen_removed().removed,
            final(self).link_view() == old(self).link_view().observe(old(from).obj(), n),
            final(self).seen_at(old(from).obj()) == n,
            final(from).domain() == old(from).domain(),
            final(from).obj() == old(from).obj(),
            final(from).ptr() == old(from).ptr(),
            final(from).protected_by(*final(self)),
    {
        let ghost seen_removed = RcuSeenRemoved {
            removed: self.seen_removed.removed,
            link_view: self.seen_removed.link_view.observe(from.obj(), n),
        };
        self.seen_removed = seen_removed;
        from.seen_removed = seen_removed;
        assert(self.wf());
        assert(from.protected_by(*self));
    }
}

/// A pointer protected by a live read-side guard.
///
/// It records the same `SeenRemoved` snapshot as the guard. This lets traversal
/// proofs preserve the fact that the protected pointer is not in the guard's
/// removed set.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuProtectedPtr<T> {
    ghost domain: Loc,
    ghost obj: nat,
    ghost ptr: *mut T,
    ghost seen_removed: RcuSeenRemoved<T>,
}

impl<T> RcuProtectedPtr<T> {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.ptr
    }

    pub closed spec fn obj(self) -> nat {
        self.obj
    }

    pub closed spec fn seen_removed(self) -> RcuSeenRemoved<T> {
        self.seen_removed
    }

    /// Duplicates the persistent fact that this pointer is protected by its
    /// recorded guard snapshot.
    ///
    /// The witness contains only ghost identities and observations; it owns
    /// no linear physical resource.  Traversal can therefore retain one copy
    /// while another is recorded in a physical read lease.
    pub proof fn tracked_duplicate(tracked &self) -> (tracked res: Self)
        ensures
            res == *self,
    {
        RcuProtectedPtr {
            domain: self.domain,
            obj: self.obj,
            ptr: self.ptr,
            seen_removed: self.seen_removed,
        }
    }

    pub open spec fn protected_by(self, guard: RcuReadGuardToken<T>) -> bool {
        &&& self.domain() == guard.domain()
        &&& self.seen_removed() == guard.seen_removed()
        &&& !self.seen_removed().removed.contains(self.obj())
        &&& guard.protects(self.ptr().addr(), self.obj())
    }

    /// Materializes the linear protection witness for a pointer already
    /// installed in a direct-root guard's protection map.
    ///
    /// Generic traversal clients should normally use [`protect_root`] or
    /// [`protect_next`]. This constructor is for the executable `Rcu<P>`
    /// adapter, whose guarded atomic load performs the root protection
    /// transition before returning to the caller.
    pub proof fn tracked_from_guard(
        tracked guard: &RcuReadGuardToken<T>,
        tracked info: &RcuBlockInfo<T>,
    ) -> (tracked res: Self)
        requires
            guard.wf(),
            info.wf(),
            info.domain() == guard.domain(),
            guard.protects(info.addr(), info.obj()),
            !guard.seen_removed().removed.contains(info.obj()),
        ensures
            res.domain() == info.domain(),
            res.obj() == info.obj(),
            res.ptr() == info.ptr(),
            res.protected_by(*guard),
    {
        RcuProtectedPtr {
            domain: info.domain(),
            obj: info.obj(),
            ptr: info.ptr(),
            seen_removed: guard.seen_removed(),
        }
    }
}

/// Traversal specification for an RCU-protected data structure.
///
/// `link_inv(from, n, to, g)` is the client-facing analogue of a
/// `RcuPointsTo(from, ...)` snapshot containing the `n`th link event from
/// `from` to `to`. `seen_removed_sound` is the client-facing analogue of the
/// `RcuPointedBy`/`SeenRemoved` invariant for partially ordered link histories.
pub trait RcuTraversalSafety: Sized {
    type Node;

    type Ghost;

    spec fn root_inv(p: *mut Self::Node, obj: nat, g: Self::Ghost) -> bool;

    spec fn node_inv(p: *mut Self::Node, obj: nat, g: Self::Ghost) -> bool;

    spec fn link_inv(
        from: *mut Self::Node,
        from_obj: nat,
        n: LinkIndex,
        to: *mut Self::Node,
        to_obj: nat,
        g: Self::Ghost,
    ) -> bool;

    spec fn seen_removed_sound(seen_removed: RcuSeenRemoved<Self::Node>, g: Self::Ghost) -> bool;

    proof fn root_is_node_inv(p: *mut Self::Node, obj: nat, g: Self::Ghost)
        requires
            Self::root_inv(p, obj, g),
        ensures
            Self::node_inv(p, obj, g),
    ;

    proof fn link_preserves_protection(
        from: *mut Self::Node,
        from_obj: nat,
        n: LinkIndex,
        to: *mut Self::Node,
        to_obj: nat,
        seen_removed: RcuSeenRemoved<Self::Node>,
        g: Self::Ghost,
    )
        requires
            Self::node_inv(from, from_obj, g),
            Self::link_inv(from, from_obj, n, to, to_obj, g),
            Self::seen_removed_sound(seen_removed, g),
            !seen_removed.removed.contains(from_obj),
            seen_removed.seen_at(from_obj) <= n,
        ensures
            Self::node_inv(to, to_obj, g),
            !seen_removed.removed.contains(to_obj),
    ;
}

/// Protect a freshly acquired root pointer.
pub proof fn protect_root<S: RcuTraversalSafety>(
    tracked guard: &mut RcuReadGuardToken<S::Node>,
    tracked info: &RcuBlockInfo<S::Node>,
    p: *mut S::Node,
    g: S::Ghost,
) -> (tracked root: RcuProtectedPtr<S::Node>)
    requires
        old(guard).can_protect(*info),
        info.ptr() == p,
        S::root_inv(p, info.obj(), g),
    ensures
        root.ptr() == p,
        root.obj() == info.obj(),
        root.domain() == old(guard).domain(),
        root.protected_by(*final(guard)),
        final(guard).wf(),
        final(guard).domain() == old(guard).domain(),
        final(guard).expired() == old(guard).expired(),
        final(guard).seen_removed() == old(guard).seen_removed(),
        S::node_inv(p, info.obj(), g),
{
    S::root_is_node_inv(p, info.obj(), g);
    guard.tracked_protect(info);
    RcuProtectedPtr {
        domain: guard.domain(),
        obj: info.obj(),
        ptr: p,
        seen_removed: guard.seen_removed(),
    }
}

/// Protect a child reached by following a non-stale link-history event.
pub proof fn protect_link<S: RcuTraversalSafety>(
    tracked guard: &mut RcuReadGuardToken<S::Node>,
    tracked from: &RcuProtectedPtr<S::Node>,
    tracked to_info: &RcuBlockInfo<S::Node>,
    n: LinkIndex,
    to: *mut S::Node,
    g: S::Ghost,
) -> (tracked to_protected: RcuProtectedPtr<S::Node>)
    requires
        from.protected_by(*old(guard)),
        old(guard).can_base_protect(*to_info),
        to_info.ptr() == to,
        S::node_inv(from.ptr(), from.obj(), g),
        S::link_inv(from.ptr(), from.obj(), n, to, to_info.obj(), g),
        S::seen_removed_sound(guard.seen_removed(), g),
        guard.seen_at(from.obj()) <= n,
    ensures
        to_protected.ptr() == to,
        to_protected.obj() == to_info.obj(),
        to_protected.domain() == from.domain(),
        to_protected.protected_by(*final(guard)),
        final(guard).wf(),
        final(guard).domain() == old(guard).domain(),
        final(guard).tid() == old(guard).tid(),
        final(guard).reader_registry() == old(guard).reader_registry(),
        final(guard).reader() == old(guard).reader(),
        final(guard).root() == old(guard).root(),
        final(guard).start_view() == old(guard).start_view(),
        final(guard).retire_observation_registry() == old(guard).retire_observation_registry(),
        final(guard).expired() == old(guard).expired(),
        final(guard).seen_removed() == old(guard).seen_removed(),
        S::node_inv(to, to_info.obj(), g),
{
    S::link_preserves_protection(
        from.ptr(),
        from.obj(),
        n,
        to,
        to_info.obj(),
        guard.seen_removed(),
        g,
    );
    assert(old(guard).can_protect(*to_info));
    guard.tracked_protect(to_info);
    RcuProtectedPtr {
        domain: from.domain(),
        obj: to_info.obj(),
        ptr: to,
        seen_removed: guard.seen_removed(),
    }
}

/// Minimal ghost-only node used to demonstrate the traversal contract.
pub struct LinkedListNode;

/// Paper-style ghost state for a linked list.
///
/// `successors[p]` is the successor history for `p`, corresponding to
/// `RcuPointsTo(p, s)`. A non-null event records both the pointer and its AId;
/// retaining the AId prevents an old history event from being reinterpreted as
/// a different allocation after address reuse.
///
/// `incoming_all[p]` is the set of all incoming edges that have ever pointed to
/// `p`, corresponding to the authoritative incoming set in `RcuPointedBy(p, B)`.
///
pub ghost struct LinkedListGhost {
    pub root: *mut LinkedListNode,
    pub root_obj: nat,
    /// Historical allocation registry, keyed by AId rather than address.
    /// Distinct reclaimed and newly registered objects may therefore retain
    /// the same pointer without collapsing their identities.
    pub objects: Map<nat, *mut LinkedListNode>,
    /// Per-allocation link histories. An address is not a valid history key:
    /// after reuse, the old and new allocations must have disjoint histories.
    pub successors: Map<nat, Seq<Option<(*mut LinkedListNode, nat)>>>,
    pub incoming_all: Map<nat, Set<LinkEdge>>,
}

impl LinkedListGhost {
    /// Current `RcuPointedBy` set, derived from the latest event of every
    /// source. Keeping it derived avoids a second mutable representation of
    /// the same link relation.
    pub open spec fn current_incoming(self, to_obj: nat) -> Set<LinkEdge> {
        if self.incoming_all.contains_key(to_obj) {
            self.incoming_all[to_obj].filter(
                |edge: LinkEdge|
                    self.objects.contains_key(edge.0) && self.successors.contains_key(edge.0)
                        && self.successors[edge.0].len() > 0 && edge.1
                        == self.successors[edge.0].len() - 1
                        && self.successors[edge.0].last() is Some
                        && self.successors[edge.0].last()->Some_0.1 == to_obj,
            )
        } else {
            Set::empty()
        }
    }

    /// Every recorded history event names a registered allocation and appears
    /// in that allocation's authoritative incoming-edge history.
    pub open spec fn wf(self) -> bool {
        &&& self.objects.contains_pair(self.root_obj, self.root)
        &&& self.successors.dom() == self.objects.dom()
        &&& self.incoming_all.dom() == self.objects.dom()
        &&& forall|from_obj: nat, n: LinkIndex|
            #![trigger self.objects.contains_key(from_obj), self.successors[from_obj][n as int]]
            self.objects.contains_key(from_obj) && n < self.successors[from_obj].len()
                && self.successors[from_obj][n as int] is Some ==> {
                let event = self.successors[from_obj][n as int]->Some_0;
                &&& self.objects.contains_pair(event.1, event.0)
                &&& self.incoming_all[event.1].contains((from_obj, n))
            }
    }

    /// A link view cannot claim an event newer than the source's history.
    pub open spec fn bounds(self, view: RcuLinkView<LinkedListNode>) -> bool {
        forall|from_obj: nat| #[trigger]
            self.objects.contains_key(from_obj) && view.seen.contains_key(from_obj) ==> {
                &&& self.successors[from_obj].len() > 0
                &&& view.seen_at(from_obj) < self.successors[from_obj].len()
            }
    }
}

/// Linear writer authority for the linked-list traversal history.
///
/// Clients can inspect [`LinkedListGhost`] snapshots, but only this tracked
/// authority can append link events and turn a node's unique base permission
/// into [`RcuRetirePerm`]. This is the proof-only analogue of owning all
/// `RcuPointsTo`/`RcuPointedBy` resources for one list.
pub tracked struct LinkedListTraversalAuth {
    ghost domain: Loc,
    ghost state: LinkedListGhost,
    ghost removed: Set<nat>,
    infos: Map<nat, RcuBlockInfo<LinkedListNode>>,
    retire_perms: Map<nat, RcuBaseRetirePerm<LinkedListNode>>,
}

impl LinkedListTraversalAuth {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn state(self) -> LinkedListGhost {
        self.state
    }

    /// Objects whose removal has already been certified by this authority.
    pub closed spec fn removed(self) -> Set<nat> {
        self.removed
    }

    pub closed spec fn has_retire_perm(self, obj: nat) -> bool {
        self.retire_perms.contains_key(obj)
    }

    pub closed spec fn has_info(self, obj: nat) -> bool {
        self.infos.contains_key(obj)
    }

    pub closed spec fn info(self, obj: nat) -> RcuBlockInfo<LinkedListNode>
        recommends
            self.has_info(obj),
    {
        self.infos[obj]
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.state().wf()
        &&& self.infos.dom() == self.state().incoming_all.dom()
        &&& forall|obj: nat| #[trigger]
            self.infos.contains_key(obj) ==> {
                let info = self.infos[obj];
                &&& info.wf()
                &&& info.domain() == self.domain()
                &&& info.obj() == obj
                &&& self.state().objects.contains_pair(obj, info.ptr())
            }
        &&& forall|obj: nat| #[trigger]
            self.retire_perms.contains_key(obj) ==> {
                let perm = self.retire_perms[obj];
                &&& perm.wf()
                &&& perm.domain() == self.domain()
                &&& self.state().objects.contains_pair(obj, perm.ptr())
                &&& perm.obj() == obj
            }
    }

    /// Starts an authoritative list with one registered root allocation.
    pub proof fn tracked_new(
        tracked root_info: &RcuBlockInfo<LinkedListNode>,
        tracked root_retire: RcuBaseRetirePerm<LinkedListNode>,
    ) -> (tracked res: Self)
        requires
            root_info.wf(),
            root_retire.wf(),
            root_retire.domain() == root_info.domain(),
            root_retire.obj() == root_info.obj(),
            root_retire.ptr() == root_info.ptr(),
        ensures
            res.wf(),
            res.domain() == root_info.domain(),
            res.state().root == root_info.ptr(),
            res.state().root_obj == root_info.obj(),
            res.state().objects == Map::empty().insert(root_info.obj(), root_info.ptr()),
            res.state().successors == Map::empty().insert(root_info.obj(), Seq::empty()),
            res.state().incoming_all == Map::empty().insert(root_info.obj(), Set::empty()),
            res.removed() == Set::empty(),
            res.has_info(root_info.obj()),
            res.info(root_info.obj()).ptr() == root_info.ptr(),
            res.has_retire_perm(root_info.obj()),
            forall|obj: nat| #[trigger] res.has_retire_perm(obj) <==> obj == root_info.obj(),
    {
        let ghost state = LinkedListGhost {
            root: root_info.ptr(),
            root_obj: root_info.obj(),
            objects: Map::empty().insert(root_info.obj(), root_info.ptr()),
            successors: Map::empty().insert(root_info.obj(), Seq::empty()),
            incoming_all: Map::empty().insert(root_info.obj(), Set::empty()),
        };
        let tracked mut infos = Map::tracked_empty();
        let tracked saved_root_info = root_info.tracked_duplicate();
        infos.tracked_insert(root_info.obj(), saved_root_info);
        let tracked mut retire_perms = Map::tracked_empty();
        retire_perms.tracked_insert(root_info.obj(), root_retire);
        LinkedListTraversalAuth {
            domain: root_info.domain(),
            state,
            removed: Set::empty(),
            infos,
            retire_perms,
        }
    }

    /// Adds a separately registered allocation to this list's traversal
    /// authority. Registration alone does not publish an incoming link.
    pub proof fn tracked_register_node(
        tracked &mut self,
        tracked info: &RcuBlockInfo<LinkedListNode>,
        tracked retire: RcuBaseRetirePerm<LinkedListNode>,
    )
        requires
            old(self).wf(),
            info.wf(),
            retire.wf(),
            info.domain() == old(self).domain(),
            retire.domain() == old(self).domain(),
            retire.obj() == info.obj(),
            retire.ptr() == info.ptr(),
            !old(self).state().objects.contains_key(info.obj()),
            !old(self).state().incoming_all.contains_key(info.obj()),
            !old(self).has_retire_perm(info.obj()),
        ensures
            final(self).wf(),
            final(self).domain() == old(self).domain(),
            final(self).state().root == old(self).state().root,
            final(self).state().root_obj == old(self).state().root_obj,
            final(self).state().objects == old(self).state().objects.insert(info.obj(), info.ptr()),
            final(self).state().successors == old(self).state().successors.insert(
                info.obj(),
                Seq::empty(),
            ),
            final(self).state().incoming_all == old(self).state().incoming_all.insert(
                info.obj(),
                Set::empty(),
            ),
            final(self).removed() == old(self).removed(),
            final(self).has_info(info.obj()),
            final(self).info(info.obj()).ptr() == info.ptr(),
            final(self).has_retire_perm(info.obj()),
    {
        let ghost old_state = self.state;
        self.state = LinkedListGhost {
            root: self.state.root,
            root_obj: self.state.root_obj,
            objects: self.state.objects.insert(info.obj(), info.ptr()),
            successors: self.state.successors.insert(info.obj(), Seq::empty()),
            incoming_all: self.state.incoming_all.insert(info.obj(), Set::empty()),
        };
        let tracked saved_info = info.tracked_duplicate();
        self.infos.tracked_insert(info.obj(), saved_info);
        self.retire_perms.tracked_insert(info.obj(), retire);
        assert(self.state.successors.dom() == self.state.objects.dom());
        assert(self.state.incoming_all.dom() == self.state.objects.dom());
        assert forall|from_obj: nat, n: LinkIndex|
            #![trigger self.state.objects.contains_key(from_obj), self.state.successors[from_obj][n as int]]
            self.state.objects.contains_key(from_obj) && n < self.state.successors[from_obj].len()
                && self.state.successors[from_obj][n as int] is Some implies {
            let event = self.state.successors[from_obj][n as int]->Some_0;
            &&& self.state.objects.contains_pair(event.1, event.0)
            &&& self.state.incoming_all[event.1].contains((from_obj, n))
        } by {
            assert(from_obj != info.obj());
            assert(old_state.objects.contains_key(from_obj));
            assert(old_state.successors[from_obj] == self.state.successors[from_obj]);
        };
        assert(self.state.wf());
        assert(self.infos.dom() == self.state.incoming_all.dom());
        assert forall|obj: nat| #[trigger] self.infos.contains_key(obj) implies {
            let saved = self.infos[obj];
            &&& saved.wf()
            &&& saved.domain() == self.domain()
            &&& saved.obj() == obj
            &&& self.state.objects.contains_pair(obj, saved.ptr())
        } by {
            if obj != info.obj() {
                assert(old(self).infos.contains_key(obj));
            }
        };
        assert forall|obj: nat| #[trigger] self.retire_perms.contains_key(obj) implies {
            let perm = self.retire_perms[obj];
            &&& perm.wf()
            &&& perm.domain() == self.domain()
            &&& self.state.objects.contains_pair(obj, perm.ptr())
            &&& perm.obj() == obj
        } by {
            if obj != info.obj() {
                assert(old(self).retire_perms.contains_key(obj));
            }
        };
    }

    /// Copies the persistent allocation identity used by an atomic link
    /// message without exposing the authority's internal registry.
    pub proof fn tracked_info_for(tracked &self, obj: nat) -> (tracked res: RcuBlockInfo<
        LinkedListNode,
    >)
        requires
            self.wf(),
            self.has_info(obj),
        ensures
            res.wf(),
            res.domain() == self.domain(),
            res.obj() == obj,
            res.ptr() == self.info(obj).ptr(),
            self.state().objects.contains_pair(obj, res.ptr()),
    {
        let tracked info = self.infos.tracked_borrow(obj);
        info.tracked_duplicate()
    }

    /// Opens the registry-domain consequence needed by traversal adapters.
    pub proof fn lemma_has_info_for_object(tracked &self, obj: nat)
        requires
            self.wf(),
            self.state().incoming_all.contains_key(obj),
        ensures
            self.has_info(obj),
    {
        assert(self.infos.dom() == self.state().incoming_all.dom());
    }

    /// Installs the initial null event for a newly created atomic link.
    /// Subsequent changes to this source must use the publish/unlink rules.
    pub proof fn tracked_initialize_null(
        tracked &mut self,
        from: *mut LinkedListNode,
        from_obj: nat,
    ) -> (n: LinkIndex)
        requires
            old(self).wf(),
            old(self).state().objects.contains_pair(from_obj, from),
            old(self).state().successors[from_obj].len() == 0,
            !old(self).removed().contains(from_obj),
        ensures
            n == 0,
            final(self).wf(),
            final(self).domain() == old(self).domain(),
            final(self).state().root == old(self).state().root,
            final(self).state().root_obj == old(self).state().root_obj,
            final(self).state().objects == old(self).state().objects,
            final(self).state().successors == old(self).state().successors.insert(
                from_obj,
                old(self).state().successors[from_obj].push(None),
            ),
            final(self).state().incoming_all == old(self).state().incoming_all,
            final(self).removed() == old(self).removed(),
            forall|obj: nat| #[trigger]
                final(self).has_retire_perm(obj) == old(self).has_retire_perm(obj),
    {
        let ghost old_state = self.state;
        self.state = LinkedListGhost {
            root: old_state.root,
            root_obj: old_state.root_obj,
            objects: old_state.objects,
            successors: old_state.successors.insert(
                from_obj,
                old_state.successors[from_obj].push(None),
            ),
            incoming_all: old_state.incoming_all,
        };
        assert(old_state.successors.contains_key(from_obj));
        assert(self.state.objects.contains_pair(self.state.root_obj, self.state.root));
        assert(self.state.successors.dom() == self.state.objects.dom());
        assert forall|source: *mut LinkedListNode, source_obj: nat, i: LinkIndex|
            #![trigger self.state.objects.contains_pair(source_obj, source), self.state.successors[source_obj][i as int]]
            self.state.objects.contains_pair(source_obj, source)
                && self.state.successors.contains_key(source_obj) && i
                < self.state.successors[source_obj].len()
                && self.state.successors[source_obj][i as int] is Some implies {
            let event = self.state.successors[source_obj][i as int]->Some_0;
            &&& self.state.objects.contains_pair(event.1, event.0)
            &&& self.state.incoming_all[event.1].contains((source_obj, i))
        } by {
            if source_obj == from_obj {
                assert(i == 0);
                assert(self.state.successors[source_obj][i as int] is None);
                assert(false);
            }
            assert(old_state.objects.contains_pair(source_obj, source));
            assert(old_state.successors[source_obj] == self.state.successors[source_obj]);
        };
        assert(self.state.wf());
        assert(self.infos.dom() == self.state.incoming_all.dom());
        0
    }

    /// Publishes (or replaces with) a non-null successor and returns the new
    /// source-history index.
    pub proof fn tracked_publish_link(
        tracked &mut self,
        from: *mut LinkedListNode,
        from_obj: nat,
        to: *mut LinkedListNode,
        to_obj: nat,
    ) -> (n: LinkIndex)
        requires
            old(self).wf(),
            old(self).state().objects.contains_pair(from_obj, from),
            old(self).state().objects.contains_pair(to_obj, to),
            !old(self).removed().contains(from_obj),
            !old(self).removed().contains(to_obj),
        ensures
            n == old(self).state().successors[from_obj].len(),
            final(self).wf(),
            final(self).domain() == old(self).domain(),
            final(self).state().root == old(self).state().root,
            final(self).state().root_obj == old(self).state().root_obj,
            final(self).state().objects == old(self).state().objects,
            final(self).state().successors == old(self).state().successors.insert(
                from_obj,
                old(self).state().successors[from_obj].push(Some((to, to_obj))),
            ),
            final(self).state().incoming_all == old(self).state().incoming_all.insert(
                to_obj,
                old(self).state().incoming_all[to_obj].insert((from_obj, n)),
            ),
            final(self).removed() == old(self).removed(),
            forall|obj: nat| #[trigger]
                final(self).has_retire_perm(obj) == old(self).has_retire_perm(obj),
            LinkedListTraversalSpec::link_inv(from, from_obj, n, to, to_obj, final(self).state()),
    {
        let ghost old_state = self.state;
        let n = old_state.successors[from_obj].len();
        self.state = LinkedListGhost {
            root: old_state.root,
            root_obj: old_state.root_obj,
            objects: old_state.objects,
            successors: old_state.successors.insert(
                from_obj,
                old_state.successors[from_obj].push(Some((to, to_obj))),
            ),
            incoming_all: old_state.incoming_all.insert(
                to_obj,
                old_state.incoming_all[to_obj].insert((from_obj, n)),
            ),
        };
        assert(old_state.successors.contains_key(from_obj));
        assert(old_state.incoming_all.contains_key(to_obj));
        assert(self.state.objects.contains_pair(self.state.root_obj, self.state.root));
        assert(self.state.successors.dom() == self.state.objects.dom());
        assert(self.state.incoming_all.dom() == self.state.objects.dom());
        assert forall|source: *mut LinkedListNode, source_obj: nat, i: LinkIndex|
            #![trigger self.state.objects.contains_pair(source_obj, source), self.state.successors[source_obj][i as int]]
            self.state.objects.contains_pair(source_obj, source)
                && self.state.successors.contains_key(source_obj) && i
                < self.state.successors[source_obj].len()
                && self.state.successors[source_obj][i as int] is Some implies {
            let event = self.state.successors[source_obj][i as int]->Some_0;
            &&& self.state.objects.contains_pair(event.1, event.0)
            &&& self.state.incoming_all[event.1].contains((source_obj, i))
        } by {
            if source_obj == from_obj && i == n {
                assert(self.state.successors[source_obj][i as int] == Some((to, to_obj)));
            } else {
                assert(i < old_state.successors[source_obj].len());
                assert(self.state.successors[source_obj][i as int]
                    == old_state.successors[source_obj][i as int]);
                let event = old_state.successors[source_obj][i as int]->Some_0;
                assert(old_state.incoming_all[event.1].contains((source_obj, i)));
                assert(self.state.incoming_all[event.1].contains((source_obj, i)));
            }
        };
        assert(self.state.wf());
        assert(self.infos.dom() == self.state.incoming_all.dom());
        assert forall|obj: nat| #[trigger] self.infos.contains_key(obj) implies {
            let info = self.infos[obj];
            &&& info.wf()
            &&& info.domain() == self.domain()
            &&& info.obj() == obj
            &&& self.state.objects.contains_pair(obj, info.ptr())
        } by {
            let ghost saved = self.infos[obj];
            assert(old_state.objects.contains_pair(obj, saved.ptr()));
        };
        n
    }

    /// Appends a null event after the expected current successor. The old
    /// incoming edge remains in `incoming_all`, but is no longer current.
    pub proof fn tracked_unlink(
        tracked &mut self,
        from: *mut LinkedListNode,
        from_obj: nat,
        to: *mut LinkedListNode,
        to_obj: nat,
    ) -> (n: LinkIndex)
        requires
            old(self).wf(),
            old(self).state().objects.contains_pair(from_obj, from),
            old(self).state().objects.contains_pair(to_obj, to),
            !old(self).removed().contains(from_obj),
            old(self).state().successors[from_obj].len() > 0,
            old(self).state().successors[from_obj].last() == Some((to, to_obj)),
        ensures
            n == old(self).state().successors[from_obj].len(),
            final(self).wf(),
            final(self).domain() == old(self).domain(),
            final(self).state().root == old(self).state().root,
            final(self).state().root_obj == old(self).state().root_obj,
            final(self).state().objects == old(self).state().objects,
            final(self).state().successors == old(self).state().successors.insert(
                from_obj,
                old(self).state().successors[from_obj].push(None),
            ),
            final(self).state().incoming_all == old(self).state().incoming_all,
            final(self).removed() == old(self).removed(),
            forall|obj: nat| #[trigger]
                final(self).has_retire_perm(obj) == old(self).has_retire_perm(obj),
            !final(self).state().current_incoming(to_obj).contains((from_obj, (n - 1) as nat)),
    {
        let ghost old_state = self.state;
        let n = old_state.successors[from_obj].len();
        self.state = LinkedListGhost {
            root: old_state.root,
            root_obj: old_state.root_obj,
            objects: old_state.objects,
            successors: old_state.successors.insert(
                from_obj,
                old_state.successors[from_obj].push(None),
            ),
            incoming_all: old_state.incoming_all,
        };
        assert(old_state.successors.contains_key(from_obj));
        assert(self.state.objects.contains_pair(self.state.root_obj, self.state.root));
        assert(self.state.successors.dom() == self.state.objects.dom());
        assert forall|source: *mut LinkedListNode, source_obj: nat, i: LinkIndex|
            #![trigger self.state.objects.contains_pair(source_obj, source), self.state.successors[source_obj][i as int]]
            self.state.objects.contains_pair(source_obj, source)
                && self.state.successors.contains_key(source_obj) && i
                < self.state.successors[source_obj].len()
                && self.state.successors[source_obj][i as int] is Some implies {
            let event = self.state.successors[source_obj][i as int]->Some_0;
            &&& self.state.objects.contains_pair(event.1, event.0)
            &&& self.state.incoming_all[event.1].contains((source_obj, i))
        } by {
            if source_obj == from_obj && i == n {
                assert(self.state.successors[source_obj][i as int] is None);
                assert(false);
            }
            assert(i < old_state.successors[source_obj].len());
            assert(self.state.successors[source_obj][i as int]
                == old_state.successors[source_obj][i as int]);
        };
        assert(self.state.wf());
        n
    }

    /// Applies the paper's traversal retire rule. The prior observation must
    /// already cover every historical incoming edge; this authority is the
    /// only public producer of the resulting high-level retire permission.
    pub proof fn tracked_retire_node(
        tracked &mut self,
        obj: nat,
        prior: RcuSeenRemoved<LinkedListNode>,
    ) -> (tracked res: RcuRetirePerm<LinkedListNode>)
        requires
            old(self).wf(),
            old(self).has_retire_perm(obj),
            old(self).has_info(obj),
            obj != old(self).state().root_obj,
            old(self).state().incoming_all[obj].len() > 0,
            prior.removed == old(self).removed(),
            old(self).state().bounds(prior.link_view),
            LinkedListTraversalSpec::seen_removed_sound(prior, old(self).state()),
            forall|edge: LinkEdge| #[trigger]
                old(self).state().incoming_all[obj].contains(edge) ==> prior.dead_edge(edge),
        ensures
            final(self).wf(),
            final(self).domain() == old(self).domain(),
            final(self).state() == old(self).state(),
            final(self).removed() == old(self).removed().insert(obj),
            !final(self).has_retire_perm(obj),
            final(self).has_info(obj),
            final(self).info(obj) == old(self).info(obj),
            res.wf(),
            res.ready_to_retire(),
            res.domain() == old(self).domain(),
            res.obj() == obj,
            old(self).state().objects.contains_pair(obj, res.ptr()),
            res.seen_removed().removed == prior.removed.insert(obj),
            res.seen_removed().link_view == prior.link_view,
            LinkedListTraversalSpec::seen_removed_sound(res.seen_removed(), final(self).state()),
    {
        assert(self.state().objects.contains_pair(obj, self.retire_perms[obj].ptr()));
        let tracked base = self.retire_perms.tracked_remove(obj);
        let ghost seen_removed = RcuSeenRemoved {
            removed: prior.removed.insert(obj),
            link_view: prior.link_view,
        };
        self.removed = self.removed.insert(obj);
        assert forall|to_obj: nat| #[trigger] seen_removed.removed.contains(to_obj) implies {
            &&& self.state.incoming_all.contains_key(to_obj)
            &&& forall|edge: LinkEdge| #[trigger]
                self.state.incoming_all[to_obj].contains(edge) ==> seen_removed.dead_edge(edge)
        } by {
            if to_obj == obj {
                assert(self.state.incoming_all.contains_key(obj));
            } else {
                assert(prior.removed.contains(to_obj));
            }
        };
        RcuRetirePerm { base, seen_removed }
    }
}

/// Native IRC11 timestamp metadata for one linked-list atomic link.
///
/// Native histories use abstract timestamps, whereas the traversal proof uses
/// dense per-source event indices. This linear ghost state records their
/// explicit correspondence; no equality between the two namespaces is
/// assumed.
pub tracked struct LinkedListLinkObservation {
    fact: GhostPersistentPointsTo<nat, LinkIndex>,
    native_fact: GhostPersistentPointsTo<nat, (Irc11AtomicId, Irc11ThreadView, nat)>,
}

impl LinkedListLinkObservation {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        self.native_fact.value().2 == self.timestamp()
    }

    /// Persistent registry that certifies this timestamp/index pair.
    pub closed spec fn registry(self) -> Loc {
        self.fact.id()
    }

    /// Persistent registry that certifies the native view observation.
    pub closed spec fn native_registry(self) -> Loc {
        self.native_fact.id()
    }

    /// Fresh identifier allocated for this native load observation.
    pub closed spec fn native_observation_id(self) -> nat {
        self.native_fact.key()
    }

    /// Native IRC11 timestamp observed by the load.
    pub closed spec fn timestamp(self) -> nat {
        self.fact.key()
    }

    /// Dense traversal-history index corresponding to [`Self::timestamp`].
    pub closed spec fn index(self) -> LinkIndex {
        self.fact.value()
    }

    /// Native atomic location whose timestamp was observed.
    pub closed spec fn loc(self) -> Irc11AtomicId {
        self.native_fact.value().0
    }

    /// Subjective view immediately after the load that minted this token.
    pub closed spec fn view(self) -> Irc11ThreadView {
        self.native_fact.value().1
    }

    /// Duplicates the persistent timestamp/index observation.
    pub proof fn tracked_duplicate(tracked &self) -> (tracked res: Self)
        ensures
            res.registry() == self.registry(),
            res.native_registry() == self.native_registry(),
            res.timestamp() == self.timestamp(),
            res.index() == self.index(),
            res.loc() == self.loc(),
            res.view() == self.view(),
    {
        use_type_invariant(self);
        LinkedListLinkObservation {
            fact: self.fact.duplicate(),
            native_fact: self.native_fact.duplicate(),
        }
    }
}

pub tracked struct LinkedListAtomicLinkGhost {
    ghost source: *mut LinkedListNode,
    ghost source_obj: nat,
    ghost timestamp_to_index: Map<nat, LinkIndex>,
    timestamp_registry: GhostMapAuth<nat, LinkIndex>,
    timestamp_facts: Map<nat, GhostPersistentPointsTo<nat, LinkIndex>>,
    native_observation_registry: GhostMapAuth<nat, (Irc11AtomicId, Irc11ThreadView, nat)>,
    ghost next_observation: nat,
    ghost current_timestamp: nat,
}

impl LinkedListAtomicLinkGhost {
    pub closed spec fn source(self) -> *mut LinkedListNode {
        self.source
    }

    pub closed spec fn source_obj(self) -> nat {
        self.source_obj
    }

    pub closed spec fn timestamps(self) -> Map<nat, LinkIndex> {
        self.timestamp_to_index
    }

    /// Append-only registry used to issue persistent load observations.
    pub closed spec fn timestamp_registry(self) -> Loc {
        self.timestamp_registry.id()
    }

    pub closed spec fn certified_timestamps(self) -> Map<nat, LinkIndex> {
        self.timestamp_registry@
    }

    pub closed spec fn observation_facts(self) -> Map<
        nat,
        GhostPersistentPointsTo<nat, LinkIndex>,
    > {
        self.timestamp_facts
    }

    /// Append-only registry of native `(location, view, timestamp)` load facts.
    pub closed spec fn native_observation_registry(self) -> Loc {
        self.native_observation_registry.id()
    }

    pub closed spec fn native_observations(self) -> Map<
        nat,
        (Irc11AtomicId, Irc11ThreadView, nat),
    > {
        self.native_observation_registry@
    }

    pub closed spec fn next_observation(self) -> nat {
        self.next_observation
    }

    pub closed spec fn current_timestamp(self) -> nat {
        self.current_timestamp
    }

    pub open spec fn index_at(self, timestamp: nat) -> LinkIndex
        recommends
            self.timestamps().contains_key(timestamp),
    {
        self.timestamps()[timestamp]
    }

    /// Agreement among the native atomic history, dense traversal history,
    /// and persistent allocation identities retained by the list authority.
    pub open spec fn wf(
        self,
        history: Irc11History<*mut LinkedListNode>,
        auth: LinkedListTraversalAuth,
    ) -> bool {
        &&& auth.wf()
        &&& auth.state().objects.contains_pair(self.source_obj(), self.source())
        &&& !auth.removed().contains(self.source_obj())
        &&& history.is_max_timestamp(self.current_timestamp())
        &&& self.timestamps().dom() == history.dom()
        &&& self.certified_timestamps() == self.timestamps()
        &&& self.observation_facts().dom() == self.timestamps().dom()
        &&& forall|timestamp: nat| #[trigger]
            self.observation_facts().contains_key(timestamp) ==> {
                let fact = self.observation_facts()[timestamp];
                &&& fact.id() == self.timestamp_registry()
                &&& fact.key() == timestamp
                &&& fact.value() == self.timestamps()[timestamp]
            }
        &&& forall|observation_id: nat| #[trigger]
            self.native_observations().contains_key(observation_id) ==> observation_id
                < self.next_observation()
        &&& auth.state().successors[self.source_obj()].len() > 0
        &&& self.index_at(self.current_timestamp()) + 1
            == auth.state().successors[self.source_obj()].len()
        &&& forall|timestamp: nat|
            history.contains_timestamp(timestamp) ==> {
                let n = #[trigger] self.timestamps()[timestamp];
                &&& n < auth.state().successors[self.source_obj()].len()
                &&& match auth.state().successors[self.source_obj()][n as int] {
                    None => history.value(timestamp).addr() == 0,
                    Some((ptr, obj)) => {
                        &&& history.value(timestamp).addr() != 0
                        &&& equal(ptr, history.value(timestamp))
                        &&& auth.has_info(obj)
                        &&& auth.info(obj).ptr() == ptr
                    },
                }
            }
        &&& forall|earlier: nat, later: nat|
            #![trigger self.timestamps()[earlier], self.timestamps()[later]]
            history.contains_timestamp(earlier) && history.contains_timestamp(later) ==> (earlier
                < later <==> self.index_at(earlier) < self.index_at(later))
    }

    /// Every issued native observation remains valid for the current
    /// append-only atomic points-to resource.
    pub open spec fn native_observations_wf(
        self,
        points_to: AtomicPointsTo<*mut LinkedListNode>,
    ) -> bool {
        forall|observation_id: nat| #[trigger]
            self.native_observations().contains_key(observation_id) ==> {
                let observation = self.native_observations()[observation_id];
                &&& observation.0 == points_to.loc()
                &&& points_to.get_timestamp(observation.1) == Some(observation.2)
            }
    }

    /// Creates the timestamp mapping for an atomic link initialized to null.
    pub proof fn tracked_initial_null(
        history: Irc11History<*mut LinkedListNode>,
        timestamp: nat,
        message_view: Irc11ThreadView,
        tracked auth: &LinkedListTraversalAuth,
        source: *mut LinkedListNode,
        source_obj: nat,
    ) -> (tracked res: Self)
        requires
            auth.wf(),
            auth.state().objects.contains_pair(source_obj, source),
            !auth.removed().contains(source_obj),
            auth.state().successors[source_obj] == Seq::empty().push(None),
            history.is_singleton(timestamp, (core::ptr::null_mut(), message_view)),
        ensures
            res.wf(history, *auth),
            res.source() == source,
            res.source_obj() == source_obj,
            res.timestamps() == Map::empty().insert(timestamp, 0),
            res.native_observations() == Map::empty(),
            res.next_observation() == 0,
            res.current_timestamp() == timestamp,
    {
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
        let tracked (mut timestamp_registry, _timestamp_entries) = GhostMapAuth::new(Map::empty());
        let tracked initial_fact = timestamp_registry.insert(timestamp, 0).persist();
        let tracked mut timestamp_facts = Map::tracked_empty();
        timestamp_facts.tracked_insert(timestamp, initial_fact);
        let tracked (native_observation_registry, _native_observations) = GhostMapAuth::new(
            Map::empty(),
        );
        let tracked res = LinkedListAtomicLinkGhost {
            source,
            source_obj,
            timestamp_to_index: Map::empty().insert(timestamp, 0),
            timestamp_registry,
            timestamp_facts,
            native_observation_registry,
            next_observation: 0,
            current_timestamp: timestamp,
        };
        assert forall|ts: nat| history.contains_timestamp(ts) implies {
            let n = #[trigger] res.timestamps()[ts];
            &&& n < auth.state().successors[source_obj].len()
            &&& match auth.state().successors[source_obj][n as int] {
                None => history.value(ts).addr() == 0,
                Some((ptr, obj)) => {
                    &&& history.value(ts).addr() != 0
                    &&& equal(ptr, history.value(ts))
                    &&& auth.has_info(obj)
                    &&& auth.info(obj).ptr() == ptr
                },
            }
        } by {
            assert(ts == timestamp);
        };
        assert forall|earlier: nat, later: nat|
            #![trigger res.timestamps()[earlier], res.timestamps()[later]]
            history.contains_timestamp(earlier) && history.contains_timestamp(later) implies (
        earlier < later <==> res.index_at(earlier) < res.index_at(later)) by {
            assert(earlier == timestamp);
            assert(later == timestamp);
        };
        res
    }

    /// Issues persistent evidence for one native timestamp's dense index.
    pub proof fn tracked_observation_at(
        tracked &mut self,
        tracked points_to: &AtomicPointsTo<*mut LinkedListNode>,
        tracked auth: &LinkedListTraversalAuth,
        timestamp: nat,
        view: Irc11ThreadView,
    ) -> (tracked res: LinkedListLinkObservation)
        requires
            old(self).wf(points_to.hist(), *auth),
            old(self).native_observations_wf(*points_to),
            points_to.hist().contains_timestamp(timestamp),
            points_to.get_timestamp(view) == Some(timestamp),
        ensures
            final(self).wf(points_to.hist(), *auth),
            final(self).native_observations_wf(*points_to),
            final(self).source() == old(self).source(),
            final(self).source_obj() == old(self).source_obj(),
            final(self).timestamp_registry() == old(self).timestamp_registry(),
            final(self).native_observation_registry() == old(self).native_observation_registry(),
            final(self).timestamps() == old(self).timestamps(),
            final(self).current_timestamp() == old(self).current_timestamp(),
            res.registry() == final(self).timestamp_registry(),
            res.native_registry() == final(self).native_observation_registry(),
            res.timestamp() == timestamp,
            res.index() == final(self).index_at(timestamp),
            res.loc() == points_to.loc(),
            res.view() == view,
    {
        let ghost old_native_observations = self.native_observations();
        let ghost observation_id = self.next_observation;
        assert(!old_native_observations.contains_key(observation_id)) by {
            if old_native_observations.contains_key(observation_id) {
                assert(observation_id < self.next_observation);
                assert(false);
            }
        };
        let tracked native_fact = self.native_observation_registry.insert(
            observation_id,
            (points_to.loc(), view, timestamp),
        ).persist();
        self.next_observation = observation_id + 1;
        let tracked fact = self.timestamp_facts.tracked_borrow(timestamp).duplicate();
        let tracked res = LinkedListLinkObservation { fact, native_fact };
        assert forall|id: nat| #[trigger] self.native_observations().contains_key(id) implies id
            < self.next_observation by {
            if id == observation_id {
            } else {
                assert(old_native_observations.contains_key(id));
                assert(old_native_observations[id] == self.native_observations()[id]);
            }
        };
        assert forall|id: nat| #[trigger] self.native_observations().contains_key(id) implies {
            let observation = self.native_observations()[id];
            &&& observation.0 == points_to.loc()
            &&& points_to.get_timestamp(observation.1) == Some(observation.2)
        } by {
            if id == observation_id {
            } else {
                assert(old_native_observations.contains_key(id));
                assert(old_native_observations[id] == self.native_observations()[id]);
            }
        };
        res
    }

    /// Agrees a prior persistent observation with the current append-only
    /// timestamp map. This remains valid after later CAS updates.
    pub proof fn lemma_observation_agrees(
        tracked &self,
        tracked observation: &LinkedListLinkObservation,
    )
        requires
            observation.registry() == self.timestamp_registry(),
            self.certified_timestamps() == self.timestamps(),
        ensures
            self.timestamps().contains_pair(observation.timestamp(), observation.index()),
    {
        observation.fact.agree(&self.timestamp_registry);
    }

    /// Agrees a prior persistent native observation with the current
    /// append-only observation registry.
    pub proof fn lemma_native_observation_agrees(
        tracked &self,
        tracked observation: &LinkedListLinkObservation,
    )
        requires
            observation.native_registry() == self.native_observation_registry(),
        ensures
            self.native_observations().contains_pair(
                observation.native_observation_id(),
                (observation.loc(), observation.view(), observation.timestamp()),
            ),
    {
        use_type_invariant(observation);
        observation.native_fact.agree(&self.native_observation_registry);
    }

    /// Records a successful native CAS that publishes a non-null successor.
    ///
    /// `load_timestamp` and `store_timestamp` are supplied by the native
    /// [`UpdateData`](vstd::atomic_weak::UpdateData). The traversal index is
    /// allocated independently by [`LinkedListTraversalAuth`].
    pub proof fn tracked_cas_publish(
        tracked &mut self,
        tracked auth: &mut LinkedListTraversalAuth,
        prev: Irc11History<*mut LinkedListNode>,
        next: Irc11History<*mut LinkedListNode>,
        load_timestamp: nat,
        store_timestamp: nat,
        to: *mut LinkedListNode,
        to_obj: nat,
        message_view: Irc11ThreadView,
    ) -> (n: LinkIndex)
        requires
            old(self).wf(prev, *old(auth)),
            prev.is_max_timestamp(load_timestamp),
            store_timestamp == load_timestamp + 1,
            next == prev.insert(store_timestamp, to, message_view),
            to.addr() != 0,
            old(auth).state().objects.contains_pair(to_obj, to),
            !old(auth).removed().contains(to_obj),
        ensures
            n == old(auth).state().successors[old(self).source_obj()].len(),
            final(self).wf(next, *final(auth)),
            final(self).source() == old(self).source(),
            final(self).source_obj() == old(self).source_obj(),
            final(self).timestamp_registry() == old(self).timestamp_registry(),
            final(self).native_observation_registry() == old(self).native_observation_registry(),
            final(self).native_observations() == old(self).native_observations(),
            final(self).next_observation() == old(self).next_observation(),
            final(self).timestamps() == old(self).timestamps().insert(store_timestamp, n),
            final(self).current_timestamp() == store_timestamp,
            final(auth).domain() == old(auth).domain(),
            final(auth).state().root == old(auth).state().root,
            final(auth).state().root_obj == old(auth).state().root_obj,
            final(auth).state().objects == old(auth).state().objects,
            final(auth).state().successors == old(auth).state().successors.insert(
                old(self).source_obj(),
                old(auth).state().successors[old(self).source_obj()].push(Some((to, to_obj))),
            ),
            final(auth).state().incoming_all == old(auth).state().incoming_all.insert(
                to_obj,
                old(auth).state().incoming_all[to_obj].insert((old(self).source_obj(), n)),
            ),
            final(auth).removed() == old(auth).removed(),
            forall|obj: nat| #[trigger]
                final(auth).has_retire_perm(obj) == old(auth).has_retire_perm(obj),
            LinkedListTraversalSpec::link_inv(
                final(self).source(),
                final(self).source_obj(),
                n,
                to,
                to_obj,
                final(auth).state(),
            ),
    {
        let ghost source = self.source;
        let ghost source_obj = self.source_obj;
        let ghost old_timestamps = self.timestamp_to_index;
        let ghost old_native_observations = self.native_observations();
        let ghost old_next_observation = self.next_observation();
        let ghost old_state = auth.state();
        let ghost old_current = self.current_timestamp;

        assert(prev.contains_timestamp(old_current));
        assert(prev.contains_timestamp(load_timestamp));
        assert(load_timestamp <= old_current);
        assert(old_current <= load_timestamp);
        assert(load_timestamp == old_current);
        assert(!prev.contains_timestamp(store_timestamp));

        let n = auth.tracked_publish_link(source, source_obj, to, to_obj);
        self.timestamp_to_index = old_timestamps.insert(store_timestamp, n);
        let tracked fact = self.timestamp_registry.insert(store_timestamp, n).persist();
        self.timestamp_facts.tracked_insert(store_timestamp, fact);
        self.current_timestamp = store_timestamp;

        assert(next.is_max_timestamp(store_timestamp)) by {
            assert forall|timestamp: nat| next.contains_timestamp(timestamp) implies timestamp
                <= store_timestamp by {
                if timestamp != store_timestamp {
                    assert(prev.contains_timestamp(timestamp));
                    assert(timestamp <= load_timestamp);
                }
            };
        };
        assert(self.timestamps().dom() == next.dom());
        assert(self.native_observations() == old_native_observations);
        assert(self.next_observation() == old_next_observation);
        assert forall|observation_id: nat| #[trigger]
            self.native_observations().contains_key(observation_id) implies observation_id
            < self.next_observation() by {};
        assert(self.index_at(store_timestamp) == n);
        assert(n + 1 == auth.state().successors[source_obj].len());
        assert forall|timestamp: nat| next.contains_timestamp(timestamp) implies {
            let index = #[trigger] self.timestamps()[timestamp];
            &&& index < auth.state().successors[source_obj].len()
            &&& match auth.state().successors[source_obj][index as int] {
                None => next.value(timestamp).addr() == 0,
                Some((ptr, obj)) => {
                    &&& next.value(timestamp).addr() != 0
                    &&& equal(ptr, next.value(timestamp))
                    &&& auth.has_info(obj)
                    &&& auth.info(obj).ptr() == ptr
                },
            }
        } by {
            if timestamp == store_timestamp {
                assert(auth.state().successors[source_obj][n as int] == Some((to, to_obj)));
                assert(auth.has_info(to_obj));
                assert(auth.info(to_obj).ptr() == to);
            } else {
                assert(prev.contains_timestamp(timestamp));
                let ghost index = old_timestamps[timestamp];
                assert(index < old_state.successors[source_obj].len());
                assert(auth.state().successors[source_obj][index as int]
                    == old_state.successors[source_obj][index as int]);
                assert(next.value(timestamp) == prev.value(timestamp));
                match old_state.successors[source_obj][index as int] {
                    None => {},
                    Some((ptr, obj)) => {
                        assert(old(auth).has_info(obj));
                        assert(auth.has_info(obj));
                        assert(auth.info(obj).ptr() == ptr);
                    },
                }
            }
        };
        assert forall|earlier: nat, later: nat|
            #![trigger self.timestamps()[earlier], self.timestamps()[later]]
            next.contains_timestamp(earlier) && next.contains_timestamp(later) implies (earlier
            < later <==> self.index_at(earlier) < self.index_at(later)) by {
            if earlier == store_timestamp {
                if later != store_timestamp {
                    assert(prev.contains_timestamp(later));
                    assert(later <= load_timestamp);
                    assert(old_timestamps[later] < old_state.successors[source_obj].len());
                    assert(self.index_at(later) < n);
                }
            } else if later == store_timestamp {
                assert(prev.contains_timestamp(earlier));
                assert(earlier <= load_timestamp);
                assert(old_timestamps[earlier] < old_state.successors[source_obj].len());
                assert(self.index_at(earlier) < n);
            } else {
                assert(prev.contains_timestamp(earlier));
                assert(prev.contains_timestamp(later));
            }
        };
        n
    }

    /// Records a successful native CAS that replaces the current successor
    /// with null. The detached edge remains in the append-only traversal
    /// history and can subsequently be discharged by a reader observation.
    pub proof fn tracked_cas_unlink(
        tracked &mut self,
        tracked auth: &mut LinkedListTraversalAuth,
        prev: Irc11History<*mut LinkedListNode>,
        next: Irc11History<*mut LinkedListNode>,
        load_timestamp: nat,
        store_timestamp: nat,
        to: *mut LinkedListNode,
        to_obj: nat,
        message_view: Irc11ThreadView,
    ) -> (n: LinkIndex)
        requires
            old(self).wf(prev, *old(auth)),
            prev.is_max_timestamp(load_timestamp),
            store_timestamp == load_timestamp + 1,
            next == prev.insert(store_timestamp, core::ptr::null_mut(), message_view),
            old(auth).state().successors[old(self).source_obj()].last() == Some((to, to_obj)),
        ensures
            n == old(auth).state().successors[old(self).source_obj()].len(),
            final(self).wf(next, *final(auth)),
            final(self).source() == old(self).source(),
            final(self).source_obj() == old(self).source_obj(),
            final(self).timestamp_registry() == old(self).timestamp_registry(),
            final(self).native_observation_registry() == old(self).native_observation_registry(),
            final(self).native_observations() == old(self).native_observations(),
            final(self).next_observation() == old(self).next_observation(),
            final(self).timestamps() == old(self).timestamps().insert(store_timestamp, n),
            final(self).current_timestamp() == store_timestamp,
            final(auth).domain() == old(auth).domain(),
            final(auth).state().root == old(auth).state().root,
            final(auth).state().root_obj == old(auth).state().root_obj,
            final(auth).state().objects == old(auth).state().objects,
            final(auth).state().successors == old(auth).state().successors.insert(
                old(self).source_obj(),
                old(auth).state().successors[old(self).source_obj()].push(None),
            ),
            final(auth).state().incoming_all == old(auth).state().incoming_all,
            final(auth).removed() == old(auth).removed(),
            forall|obj: nat| #[trigger]
                final(auth).has_retire_perm(obj) == old(auth).has_retire_perm(obj),
            final(auth).state().successors[final(self).source_obj()][n as int] is None,
            !final(auth).state().current_incoming(to_obj).contains(
                (final(self).source_obj(), (n - 1) as nat),
            ),
    {
        let ghost source = self.source;
        let ghost source_obj = self.source_obj;
        let ghost old_timestamps = self.timestamp_to_index;
        let ghost old_native_observations = self.native_observations();
        let ghost old_next_observation = self.next_observation();
        let ghost old_state = auth.state();
        let ghost old_current = self.current_timestamp;

        assert(prev.contains_timestamp(old_current));
        assert(prev.contains_timestamp(load_timestamp));
        assert(load_timestamp <= old_current);
        assert(old_current <= load_timestamp);
        assert(load_timestamp == old_current);
        assert(!prev.contains_timestamp(store_timestamp));

        let n = auth.tracked_unlink(source, source_obj, to, to_obj);
        self.timestamp_to_index = old_timestamps.insert(store_timestamp, n);
        let tracked fact = self.timestamp_registry.insert(store_timestamp, n).persist();
        self.timestamp_facts.tracked_insert(store_timestamp, fact);
        self.current_timestamp = store_timestamp;

        assert(next.is_max_timestamp(store_timestamp)) by {
            assert forall|timestamp: nat| next.contains_timestamp(timestamp) implies timestamp
                <= store_timestamp by {
                if timestamp != store_timestamp {
                    assert(prev.contains_timestamp(timestamp));
                    assert(timestamp <= load_timestamp);
                }
            };
        };
        assert(self.timestamps().dom() == next.dom());
        assert(self.native_observations() == old_native_observations);
        assert(self.next_observation() == old_next_observation);
        assert forall|observation_id: nat| #[trigger]
            self.native_observations().contains_key(observation_id) implies observation_id
            < self.next_observation() by {};
        assert(self.index_at(store_timestamp) == n);
        assert(n + 1 == auth.state().successors[source_obj].len());
        assert forall|timestamp: nat| next.contains_timestamp(timestamp) implies {
            let index = #[trigger] self.timestamps()[timestamp];
            &&& index < auth.state().successors[source_obj].len()
            &&& match auth.state().successors[source_obj][index as int] {
                None => next.value(timestamp).addr() == 0,
                Some((ptr, obj)) => {
                    &&& next.value(timestamp).addr() != 0
                    &&& equal(ptr, next.value(timestamp))
                    &&& auth.has_info(obj)
                    &&& auth.info(obj).ptr() == ptr
                },
            }
        } by {
            if timestamp == store_timestamp {
                assert(auth.state().successors[source_obj][n as int] is None);
            } else {
                assert(prev.contains_timestamp(timestamp));
                let ghost index = old_timestamps[timestamp];
                assert(index < old_state.successors[source_obj].len());
                assert(auth.state().successors[source_obj][index as int]
                    == old_state.successors[source_obj][index as int]);
                assert(next.value(timestamp) == prev.value(timestamp));
                match old_state.successors[source_obj][index as int] {
                    None => {},
                    Some((ptr, obj)) => {
                        assert(old(auth).has_info(obj));
                        assert(auth.has_info(obj));
                        assert(auth.info(obj).ptr() == ptr);
                    },
                }
            }
        };
        assert forall|earlier: nat, later: nat|
            #![trigger self.timestamps()[earlier], self.timestamps()[later]]
            next.contains_timestamp(earlier) && next.contains_timestamp(later) implies (earlier
            < later <==> self.index_at(earlier) < self.index_at(later)) by {
            if earlier == store_timestamp {
                if later != store_timestamp {
                    assert(prev.contains_timestamp(later));
                    assert(later <= load_timestamp);
                    assert(old_timestamps[later] < old_state.successors[source_obj].len());
                    assert(self.index_at(later) < n);
                }
            } else if later == store_timestamp {
                assert(prev.contains_timestamp(earlier));
                assert(earlier <= load_timestamp);
                assert(old_timestamps[earlier] < old_state.successors[source_obj].len());
                assert(self.index_at(earlier) < n);
            } else {
                assert(prev.contains_timestamp(earlier));
                assert(prev.contains_timestamp(later));
            }
        };
        n
    }

    /// Resolves an observed native atomic message to its traversal event and
    /// persistent child identity.
    pub proof fn tracked_info_at(
        tracked &self,
        history: Irc11History<*mut LinkedListNode>,
        tracked auth: &LinkedListTraversalAuth,
        timestamp: nat,
    ) -> (tracked res: Option<RcuBlockInfo<LinkedListNode>>)
        requires
            self.wf(history, *auth),
            history.contains_timestamp(timestamp),
        ensures
            self.index_at(timestamp) < auth.state().successors[self.source_obj()].len(),
            match res {
                None => {
                    &&& history.value(timestamp).addr() == 0
                    &&& auth.state().successors[self.source_obj()][self.index_at(
                        timestamp,
                    ) as int] is None
                },
                Some(info) => {
                    &&& history.value(timestamp).addr() != 0
                    &&& info.wf()
                    &&& info.domain() == auth.domain()
                    &&& equal(info.ptr(), history.value(timestamp))
                    &&& LinkedListTraversalSpec::link_inv(
                        self.source(),
                        self.source_obj(),
                        self.index_at(timestamp),
                        info.ptr(),
                        info.obj(),
                        auth.state(),
                    )
                },
            },
    {
        let ghost n = self.index_at(timestamp);
        match auth.state().successors[self.source_obj()][n as int] {
            None => None,
            Some((ptr, obj)) => {
                let tracked info = auth.tracked_info_for(obj);
                assert(equal(info.ptr(), history.value(timestamp)));
                Some(info)
            },
        }
    }

    /// Connects a native atomic load to the paper's guarded traversal rule.
    ///
    /// The source witness is refreshed in place with the observed link index.
    /// A non-null message additionally installs the loaded allocation in the
    /// guard's protection map and returns its protected witness.
    pub proof fn tracked_load_and_protect(
        tracked &self,
        history: Irc11History<*mut LinkedListNode>,
        tracked auth: &LinkedListTraversalAuth,
        tracked guard: &mut RcuReadGuardToken<LinkedListNode>,
        tracked from: &mut RcuProtectedPtr<LinkedListNode>,
        timestamp: nat,
    ) -> (tracked res: Option<RcuProtectedPtr<LinkedListNode>>)
        requires
            self.wf(history, *auth),
            history.contains_timestamp(timestamp),
            old(guard).wf(),
            old(guard).domain() == auth.domain(),
            old(from).protected_by(*old(guard)),
            old(from).ptr() == self.source(),
            old(from).obj() == self.source_obj(),
            old(guard).seen_at(old(from).obj()) <= self.index_at(timestamp),
            LinkedListTraversalSpec::seen_removed_sound(old(guard).seen_removed(), auth.state()),
        ensures
            final(guard).wf(),
            final(guard).domain() == old(guard).domain(),
            final(guard).tid() == old(guard).tid(),
            final(guard).reader_registry() == old(guard).reader_registry(),
            final(guard).reader() == old(guard).reader(),
            final(guard).root() == old(guard).root(),
            final(guard).start_view() == old(guard).start_view(),
            final(guard).retire_observation_registry() == old(guard).retire_observation_registry(),
            final(guard).expired() == old(guard).expired(),
            final(guard).seen_removed().removed == old(guard).seen_removed().removed,
            final(guard).seen_at(self.source_obj()) == self.index_at(timestamp),
            LinkedListTraversalSpec::seen_removed_sound(final(guard).seen_removed(), auth.state()),
            final(from).ptr() == self.source(),
            final(from).obj() == self.source_obj(),
            final(from).domain() == final(guard).domain(),
            final(from).seen_removed() == final(guard).seen_removed(),
            !final(from).seen_removed().removed.contains(final(from).obj()),
            res is None ==> final(guard).protected() == old(guard).protected(),
            (res is Some) == (history.value(timestamp).addr() != 0),
            match res {
                None => history.value(timestamp).addr() == 0,
                Some(child) => {
                    &&& equal(child.ptr(), history.value(timestamp))
                    &&& child.domain() == auth.domain()
                    &&& child.protected_by(*final(guard))
                    &&& LinkedListTraversalSpec::node_inv(child.ptr(), child.obj(), auth.state())
                },
            },
    {
        let ghost n = self.index_at(timestamp);
        let tracked info = self.tracked_info_at(history, auth, timestamp);
        let ghost old_seen_removed = guard.seen_removed();
        let ghost old_domain = guard.domain();
        let ghost old_tid = guard.tid();
        let ghost old_reader_registry = guard.reader_registry();
        let ghost old_reader = guard.reader();
        let ghost old_root = guard.root();
        let ghost old_start_view = guard.start_view();
        let ghost old_retire_observation_registry = guard.retire_observation_registry();
        let ghost old_expired = guard.expired();
        let ghost old_protected = guard.protected();
        assert(old_domain == old(guard).domain());
        assert(old_tid == old(guard).tid());
        assert(old_reader_registry == old(guard).reader_registry());
        assert(old_reader == old(guard).reader());
        assert(old_root == old(guard).root());
        assert(old_start_view == old(guard).start_view());
        assert(old_retire_observation_registry == old(guard).retire_observation_registry());
        assert(old_expired == old(guard).expired());
        assert(old_protected == old(guard).protected());
        guard.tracked_observe_link_in_place(from, n);
        linked_list_observe_preserves_seen_removed_sound(
            old_seen_removed,
            auth.state(),
            self.source_obj(),
            n,
        );
        assert(from.protected_by(*guard));
        assert(guard.domain() == old_domain);
        assert(guard.tid() == old_tid);
        assert(guard.reader_registry() == old_reader_registry);
        assert(guard.reader() == old_reader);
        assert(guard.root() == old_root);
        assert(guard.start_view() == old_start_view);
        assert(guard.retire_observation_registry() == old_retire_observation_registry);
        assert(guard.expired() == old_expired);
        assert(guard.protected() == old_protected);
        let tracked res;
        match info {
            None => {
                assert(guard.domain() == old(guard).domain());
                assert(guard.tid() == old(guard).tid());
                assert(guard.reader_registry() == old(guard).reader_registry());
                assert(guard.reader() == old(guard).reader());
                assert(guard.root() == old(guard).root());
                assert(guard.start_view() == old(guard).start_view());
                assert(guard.retire_observation_registry() == old(
                    guard,
                ).retire_observation_registry());
                assert(guard.expired() == old(guard).expired());
                assert(guard.protected() == old(guard).protected());
                res = None;
            },
            Some(info) => {
                assert(LinkedListTraversalSpec::node_inv(from.ptr(), from.obj(), auth.state()));
                let tracked child = protect_link::<LinkedListTraversalSpec>(
                    guard,
                    from,
                    &info,
                    n,
                    info.ptr(),
                    auth.state(),
                );
                res = Some(child);
            },
        }
        assert(guard.domain() == old(guard).domain());
        assert(guard.tid() == old(guard).tid());
        assert(guard.reader_registry() == old(guard).reader_registry());
        assert(guard.reader() == old(guard).reader());
        assert(guard.root() == old(guard).root());
        assert(guard.start_view() == old(guard).start_view());
        assert(guard.retire_observation_registry() == old(guard).retire_observation_registry());
        assert(guard.expired() == old(guard).expired());
        res
    }
}

pub struct LinkedListTraversalSpec;

impl RcuTraversalSafety for LinkedListTraversalSpec {
    type Node = LinkedListNode;

    type Ghost = LinkedListGhost;

    open spec fn root_inv(p: *mut LinkedListNode, obj: nat, g: LinkedListGhost) -> bool {
        &&& p == g.root
        &&& obj == g.root_obj
        &&& g.objects.contains_pair(obj, p)
        &&& g.successors.contains_key(obj)
        &&& g.incoming_all.contains_key(obj)
    }

    open spec fn node_inv(p: *mut LinkedListNode, obj: nat, g: LinkedListGhost) -> bool {
        &&& g.objects.contains_pair(obj, p)
        &&& g.successors.contains_key(obj)
        &&& g.incoming_all.contains_key(obj)
    }

    open spec fn link_inv(
        from: *mut LinkedListNode,
        from_obj: nat,
        n: LinkIndex,
        to: *mut LinkedListNode,
        to_obj: nat,
        g: LinkedListGhost,
    ) -> bool {
        &&& g.objects.contains_pair(from_obj, from)
        &&& g.objects.contains_pair(to_obj, to)
        &&& g.successors.contains_key(from_obj)
        &&& n < g.successors[from_obj].len()
        &&& g.successors[from_obj][n as int] == Some((to, to_obj))
        &&& g.successors.contains_key(to_obj)
        &&& g.incoming_all.contains_key(to_obj)
        &&& g.incoming_all[to_obj].contains((from_obj, n))
    }

    open spec fn seen_removed_sound(
        seen_removed: RcuSeenRemoved<LinkedListNode>,
        g: LinkedListGhost,
    ) -> bool {
        forall|to_obj: nat| #[trigger]
            seen_removed.removed.contains(to_obj) ==> {
                &&& g.incoming_all.contains_key(to_obj)
                &&& forall|edge: LinkEdge| #[trigger]
                    g.incoming_all[to_obj].contains(edge) ==> seen_removed.dead_edge(edge)
            }
    }

    proof fn root_is_node_inv(p: *mut LinkedListNode, obj: nat, g: LinkedListGhost) {
    }

    proof fn link_preserves_protection(
        from: *mut LinkedListNode,
        from_obj: nat,
        n: LinkIndex,
        to: *mut LinkedListNode,
        to_obj: nat,
        seen_removed: RcuSeenRemoved<LinkedListNode>,
        g: LinkedListGhost,
    ) {
        if seen_removed.removed.contains(to_obj) {
            assert(g.incoming_all[to_obj].contains((from_obj, n)));
            assert(seen_removed.dead_edge((from_obj, n)));
            assert(false);
        }
    }
}

/// Advancing one source observation preserves every previously established
/// dead-edge fact in a linked-list `SeenRemoved` snapshot.
pub proof fn linked_list_observe_preserves_seen_removed_sound(
    seen_removed: RcuSeenRemoved<LinkedListNode>,
    g: LinkedListGhost,
    source_obj: nat,
    n: LinkIndex,
)
    requires
        LinkedListTraversalSpec::seen_removed_sound(seen_removed, g),
    ensures
        LinkedListTraversalSpec::seen_removed_sound(
            RcuSeenRemoved {
                removed: seen_removed.removed,
                link_view: seen_removed.link_view.observe(source_obj, n),
            },
            g,
        ),
{
    let ghost observed = RcuSeenRemoved {
        removed: seen_removed.removed,
        link_view: seen_removed.link_view.observe(source_obj, n),
    };
    assert forall|to_obj: nat| #[trigger] observed.removed.contains(to_obj) implies {
        &&& g.incoming_all.contains_key(to_obj)
        &&& forall|edge: LinkEdge| #[trigger]
            g.incoming_all[to_obj].contains(edge) ==> observed.dead_edge(edge)
    } by {
        assert(seen_removed.removed.contains(to_obj));
        assert(g.incoming_all.contains_key(to_obj));
        assert forall|edge: LinkEdge| #[trigger]
            g.incoming_all[to_obj].contains(edge) implies observed.dead_edge(edge) by {
            assert(seen_removed.dead_edge(edge));
            if !seen_removed.removed.contains(edge.0) {
                seen_removed.link_view.lemma_observe_monotonic(source_obj, n, edge.0);
                assert(observed.seen_at(edge.0) >= seen_removed.seen_at(edge.0));
            }
        };
    };
}

/// A latest link from a predecessor not already in `D` cannot be dead in a
/// bounded link view. Consequently the traversal retire rule cannot be
/// applied while that incoming edge remains live.
pub proof fn linked_list_live_edge_blocks_retire(
    g: LinkedListGhost,
    seen_removed: RcuSeenRemoved<LinkedListNode>,
    from: *mut LinkedListNode,
    from_obj: nat,
    n: LinkIndex,
    to: *mut LinkedListNode,
    to_obj: nat,
)
    requires
        g.wf(),
        g.bounds(seen_removed.link_view),
        LinkedListTraversalSpec::link_inv(from, from_obj, n, to, to_obj, g),
        g.successors[from_obj].len() == n + 1,
        !seen_removed.removed.contains(from_obj),
    ensures
        g.current_incoming(to_obj).contains((from_obj, n)),
        !seen_removed.dead_edge((from_obj, n)),
        !(forall|edge: LinkEdge| #[trigger]
            g.incoming_all[to_obj].contains(edge) ==> seen_removed.dead_edge(edge)),
{
    if seen_removed.link_view.seen.contains_key(from_obj) {
        assert(seen_removed.seen_at(from_obj) < g.successors[from_obj].len());
    } else {
        assert(seen_removed.seen_at(from_obj) == 0);
    }
    assert(seen_removed.seen_at(from_obj) <= n);
    assert(g.successors[from_obj].last() == Some((to, to_obj)));
    assert(g.current_incoming(to_obj).contains((from_obj, n))) by {
        assert(g.objects.contains_key(from_obj));
        assert(g.successors.contains_key(from_obj));
    }
}

/// End-to-end ghost example for an internal list node. Publishing creates the
/// historical incoming edge at index 0; unlinking appends a newer null event;
/// observing index 1 then lets the authority consume the child's unique base
/// permission and produce the traversal-level retire permission.
pub proof fn linked_list_unlink_enables_retire(
    tracked root_info: &RcuBlockInfo<LinkedListNode>,
    tracked root_retire: RcuBaseRetirePerm<LinkedListNode>,
    tracked child_info: &RcuBlockInfo<LinkedListNode>,
    tracked child_retire: RcuBaseRetirePerm<LinkedListNode>,
) -> (tracked retired: RcuRetirePerm<LinkedListNode>)
    requires
        root_info.wf(),
        root_retire.wf(),
        root_retire.domain() == root_info.domain(),
        root_retire.obj() == root_info.obj(),
        root_retire.ptr() == root_info.ptr(),
        child_info.wf(),
        child_retire.wf(),
        child_info.domain() == root_info.domain(),
        child_retire.domain() == root_info.domain(),
        child_retire.obj() == child_info.obj(),
        child_retire.ptr() == child_info.ptr(),
        child_info.ptr() != root_info.ptr(),
        child_info.obj() != root_info.obj(),
    ensures
        retired.wf(),
        retired.ready_to_retire(),
        retired.domain() == root_info.domain(),
        retired.obj() == child_info.obj(),
        LinkedListTraversalSpec::seen_removed_sound(
            retired.seen_removed(),
            LinkedListGhost {
                root: root_info.ptr(),
                root_obj: root_info.obj(),
                objects: Map::empty().insert(root_info.obj(), root_info.ptr()).insert(
                    child_info.obj(),
                    child_info.ptr(),
                ),
                successors: Map::empty().insert(root_info.obj(), Seq::empty()).insert(
                    child_info.obj(),
                    Seq::empty(),
                ).insert(
                    root_info.obj(),
                    Seq::empty().push(Some((child_info.ptr(), child_info.obj()))).push(None),
                ),
                incoming_all: Map::empty().insert(root_info.obj(), Set::empty()).insert(
                    child_info.obj(),
                    Set::empty().insert((root_info.obj(), 0)),
                ),
            },
        ),
{
    let tracked mut auth = LinkedListTraversalAuth::tracked_new(root_info, root_retire);
    auth.tracked_register_node(child_info, child_retire);
    let n = auth.tracked_publish_link(
        root_info.ptr(),
        root_info.obj(),
        child_info.ptr(),
        child_info.obj(),
    );
    assert(n == 0);
    let observed = auth.tracked_unlink(
        root_info.ptr(),
        root_info.obj(),
        child_info.ptr(),
        child_info.obj(),
    );
    assert(observed == 1);
    let ghost prior = RcuSeenRemoved {
        removed: Set::empty(),
        link_view: RcuLinkView::empty().observe(root_info.obj(), observed),
    };
    assert(auth.state().bounds(prior.link_view)) by {
        assert forall|from: *mut LinkedListNode, from_obj: nat| #[trigger]
            auth.state().objects.contains_pair(from_obj, from) && prior.link_view.seen.contains_key(
                from_obj,
            ) implies {
            &&& auth.state().successors[from_obj].len() > 0
            &&& prior.link_view.seen_at(from_obj) < auth.state().successors[from_obj].len()
        } by {
            assert(from == root_info.ptr());
            assert(from_obj == root_info.obj());
        };
    }
    assert(LinkedListTraversalSpec::seen_removed_sound(prior, auth.state()));
    assert forall|edge: LinkEdge| #[trigger]
        auth.state().incoming_all[child_info.obj()].contains(edge) implies prior.dead_edge(
        edge,
    ) by {
        assert(edge == (root_info.obj(), 0));
        assert(prior.seen_at(root_info.obj()) == observed);
    };
    auth.tracked_retire_node(child_info.obj(), prior)
}

/// Regression proof for the fully dynamic traversal authority.
///
/// The old allocation is reachable from two distinct predecessors. Both
/// incoming edges must be unlinked and observed before retirement. A fresh
/// AId is then registered at exactly the same address, published, unlinked,
/// and published again. The old history entries continue naming `old_obj`,
/// while both publications of the reused allocation name `reused_obj`.
pub proof fn linked_list_multiple_predecessors_republish_reused_address(
    tracked root_info: &RcuBlockInfo<LinkedListNode>,
    tracked root_retire: RcuBaseRetirePerm<LinkedListNode>,
    tracked left_info: &RcuBlockInfo<LinkedListNode>,
    tracked left_retire: RcuBaseRetirePerm<LinkedListNode>,
    tracked right_info: &RcuBlockInfo<LinkedListNode>,
    tracked right_retire: RcuBaseRetirePerm<LinkedListNode>,
    tracked old_info: &RcuBlockInfo<LinkedListNode>,
    tracked old_retire: RcuBaseRetirePerm<LinkedListNode>,
    tracked reused_info: &RcuBlockInfo<LinkedListNode>,
    tracked reused_retire: RcuBaseRetirePerm<LinkedListNode>,
) -> (tracked res: (LinkedListTraversalAuth, RcuRetirePerm<LinkedListNode>))
    requires
        root_info.wf(),
        root_retire.wf(),
        root_retire.domain() == root_info.domain(),
        root_retire.obj() == root_info.obj(),
        root_retire.ptr() == root_info.ptr(),
        left_info.wf(),
        left_retire.wf(),
        left_info.domain() == root_info.domain(),
        left_retire.domain() == root_info.domain(),
        left_retire.obj() == left_info.obj(),
        left_retire.ptr() == left_info.ptr(),
        right_info.wf(),
        right_retire.wf(),
        right_info.domain() == root_info.domain(),
        right_retire.domain() == root_info.domain(),
        right_retire.obj() == right_info.obj(),
        right_retire.ptr() == right_info.ptr(),
        old_info.wf(),
        old_retire.wf(),
        old_info.domain() == root_info.domain(),
        old_retire.domain() == root_info.domain(),
        old_retire.obj() == old_info.obj(),
        old_retire.ptr() == old_info.ptr(),
        reused_info.wf(),
        reused_retire.wf(),
        reused_info.domain() == root_info.domain(),
        reused_retire.domain() == root_info.domain(),
        reused_retire.obj() == reused_info.obj(),
        reused_retire.ptr() == reused_info.ptr(),
        old_info.ptr() == reused_info.ptr(),
        root_info.obj() != left_info.obj(),
        root_info.obj() != right_info.obj(),
        root_info.obj() != old_info.obj(),
        root_info.obj() != reused_info.obj(),
        left_info.obj() != right_info.obj(),
        left_info.obj() != old_info.obj(),
        left_info.obj() != reused_info.obj(),
        right_info.obj() != old_info.obj(),
        right_info.obj() != reused_info.obj(),
        old_info.obj() != reused_info.obj(),
    ensures
        res.0.wf(),
        res.0.removed().contains(old_info.obj()),
        res.0.has_retire_perm(reused_info.obj()),
        res.0.state().objects.contains_pair(old_info.obj(), old_info.ptr()),
        res.0.state().objects.contains_pair(reused_info.obj(), old_info.ptr()),
        res.0.state().successors[left_info.obj()][0] == Some((old_info.ptr(), old_info.obj())),
        res.0.state().successors[left_info.obj()][2] == Some(
            (reused_info.ptr(), reused_info.obj()),
        ),
        res.0.state().successors[left_info.obj()][4] == Some(
            (reused_info.ptr(), reused_info.obj()),
        ),
        res.0.state().incoming_all[old_info.obj()].contains((left_info.obj(), 0)),
        res.0.state().incoming_all[old_info.obj()].contains((right_info.obj(), 0)),
        res.0.state().incoming_all[reused_info.obj()].contains((left_info.obj(), 2)),
        res.0.state().incoming_all[reused_info.obj()].contains((left_info.obj(), 4)),
        res.0.state().current_incoming(reused_info.obj()).contains((left_info.obj(), 4)),
        res.1.wf(),
        res.1.ready_to_retire(),
        res.1.obj() == old_info.obj(),
        res.1.ptr() == old_info.ptr(),
{
    let tracked mut auth = LinkedListTraversalAuth::tracked_new(root_info, root_retire);
    auth.tracked_register_node(left_info, left_retire);
    auth.tracked_register_node(right_info, right_retire);
    auth.tracked_register_node(old_info, old_retire);

    let root_left = auth.tracked_publish_link(
        root_info.ptr(),
        root_info.obj(),
        left_info.ptr(),
        left_info.obj(),
    );
    let left_old = auth.tracked_publish_link(
        left_info.ptr(),
        left_info.obj(),
        old_info.ptr(),
        old_info.obj(),
    );
    let root_right = auth.tracked_publish_link(
        root_info.ptr(),
        root_info.obj(),
        right_info.ptr(),
        right_info.obj(),
    );
    let right_old = auth.tracked_publish_link(
        right_info.ptr(),
        right_info.obj(),
        old_info.ptr(),
        old_info.obj(),
    );
    assert(root_left == 0);
    assert(left_old == 0);
    assert(root_right == 1);
    assert(right_old == 0);
    assert(auth.state().current_incoming(old_info.obj()).contains((left_info.obj(), left_old)));
    assert(auth.state().current_incoming(old_info.obj()).contains((right_info.obj(), right_old)));

    let left_unlink = auth.tracked_unlink(
        left_info.ptr(),
        left_info.obj(),
        old_info.ptr(),
        old_info.obj(),
    );
    let right_unlink = auth.tracked_unlink(
        right_info.ptr(),
        right_info.obj(),
        old_info.ptr(),
        old_info.obj(),
    );
    assert(left_unlink == 1);
    assert(right_unlink == 1);
    let ghost prior = RcuSeenRemoved {
        removed: Set::empty(),
        link_view: RcuLinkView::empty().observe(left_info.obj(), left_unlink).observe(
            right_info.obj(),
            right_unlink,
        ),
    };
    assert(auth.state().bounds(prior.link_view)) by {
        assert forall|from_obj: nat| #[trigger]
            auth.state().objects.contains_key(from_obj) && prior.link_view.seen.contains_key(
                from_obj,
            ) implies {
            &&& auth.state().successors[from_obj].len() > 0
            &&& prior.seen_at(from_obj) < auth.state().successors[from_obj].len()
        } by {
            if from_obj == left_info.obj() {
                assert(prior.seen_at(from_obj) == left_unlink);
            } else {
                assert(from_obj == right_info.obj());
                assert(prior.seen_at(from_obj) == right_unlink);
            }
        };
    }
    assert(LinkedListTraversalSpec::seen_removed_sound(prior, auth.state()));
    assert forall|edge: LinkEdge| #[trigger]
        auth.state().incoming_all[old_info.obj()].contains(edge) implies prior.dead_edge(edge) by {
        if edge.0 == left_info.obj() {
            assert(edge == (left_info.obj(), left_old));
            assert(prior.seen_at(left_info.obj()) == left_unlink);
        } else {
            assert(edge == (right_info.obj(), right_old));
            assert(prior.seen_at(right_info.obj()) == right_unlink);
        }
    };
    let tracked retired = auth.tracked_retire_node(old_info.obj(), prior);

    auth.tracked_register_node(reused_info, reused_retire);
    let first_republication = auth.tracked_publish_link(
        left_info.ptr(),
        left_info.obj(),
        reused_info.ptr(),
        reused_info.obj(),
    );
    assert(first_republication == 2);
    let reused_unlink = auth.tracked_unlink(
        left_info.ptr(),
        left_info.obj(),
        reused_info.ptr(),
        reused_info.obj(),
    );
    assert(reused_unlink == 3);
    let second_republication = auth.tracked_publish_link(
        left_info.ptr(),
        left_info.obj(),
        reused_info.ptr(),
        reused_info.obj(),
    );
    assert(second_republication == 4);
    assert(auth.state().objects[old_info.obj()] == old_info.ptr());
    assert(auth.state().objects[reused_info.obj()] == reused_info.ptr());
    assert(old_info.ptr() == reused_info.ptr());
    (auth, retired)
}

/// End-to-end writer example connecting successful native IRC11 CAS updates
/// to the traversal retire rule.
///
/// Native timestamps are kept abstract. The proof relies only on the CAS
/// contract's successor timestamps and on `LinkedListAtomicLinkGhost`'s
/// explicit timestamp-to-index correspondence.
pub proof fn linked_list_native_cas_unlink_enables_retire(
    tracked root_info: &RcuBlockInfo<LinkedListNode>,
    tracked root_retire: RcuBaseRetirePerm<LinkedListNode>,
    tracked child_info: &RcuBlockInfo<LinkedListNode>,
    tracked child_retire: RcuBaseRetirePerm<LinkedListNode>,
    initial_history: Irc11History<*mut LinkedListNode>,
    published_history: Irc11History<*mut LinkedListNode>,
    unlinked_history: Irc11History<*mut LinkedListNode>,
    initial_timestamp: nat,
    published_timestamp: nat,
    unlinked_timestamp: nat,
    initial_view: Irc11ThreadView,
    published_view: Irc11ThreadView,
    unlinked_view: Irc11ThreadView,
) -> (tracked retired: RcuRetirePerm<LinkedListNode>)
    requires
        root_info.wf(),
        root_retire.wf(),
        root_retire.domain() == root_info.domain(),
        root_retire.obj() == root_info.obj(),
        root_retire.ptr() == root_info.ptr(),
        child_info.wf(),
        child_retire.wf(),
        child_info.domain() == root_info.domain(),
        child_retire.domain() == root_info.domain(),
        child_retire.obj() == child_info.obj(),
        child_retire.ptr() == child_info.ptr(),
        child_info.ptr().addr() != 0,
        child_info.ptr() != root_info.ptr(),
        child_info.obj() != root_info.obj(),
        initial_history.is_singleton(initial_timestamp, (core::ptr::null_mut(), initial_view)),
        published_timestamp == initial_timestamp + 1,
        published_history == initial_history.insert(
            published_timestamp,
            child_info.ptr(),
            published_view,
        ),
        unlinked_timestamp == published_timestamp + 1,
        unlinked_history == published_history.insert(
            unlinked_timestamp,
            core::ptr::null_mut(),
            unlinked_view,
        ),
    ensures
        retired.wf(),
        retired.ready_to_retire(),
        retired.domain() == root_info.domain(),
        retired.obj() == child_info.obj(),
{
    let tracked mut auth = LinkedListTraversalAuth::tracked_new(root_info, root_retire);
    auth.tracked_register_node(child_info, child_retire);
    let initial_index = auth.tracked_initialize_null(root_info.ptr(), root_info.obj());
    assert(initial_index == 0);
    let tracked mut link = LinkedListAtomicLinkGhost::tracked_initial_null(
        initial_history,
        initial_timestamp,
        initial_view,
        &auth,
        root_info.ptr(),
        root_info.obj(),
    );

    let published_index = link.tracked_cas_publish(
        &mut auth,
        initial_history,
        published_history,
        initial_timestamp,
        published_timestamp,
        child_info.ptr(),
        child_info.obj(),
        published_view,
    );
    assert(published_index == 1);
    let unlinked_index = link.tracked_cas_unlink(
        &mut auth,
        published_history,
        unlinked_history,
        published_timestamp,
        unlinked_timestamp,
        child_info.ptr(),
        child_info.obj(),
        unlinked_view,
    );
    assert(unlinked_index == 2);

    let ghost prior = RcuSeenRemoved {
        removed: Set::empty(),
        link_view: RcuLinkView::empty().observe(root_info.obj(), unlinked_index),
    };
    assert(auth.state().bounds(prior.link_view)) by {
        assert forall|from: *mut LinkedListNode, from_obj: nat| #[trigger]
            auth.state().objects.contains_pair(from_obj, from) && prior.link_view.seen.contains_key(
                from_obj,
            ) implies {
            &&& auth.state().successors[from_obj].len() > 0
            &&& prior.link_view.seen_at(from_obj) < auth.state().successors[from_obj].len()
        } by {
            assert(from == root_info.ptr());
            assert(from_obj == root_info.obj());
        };
    }
    assert(LinkedListTraversalSpec::seen_removed_sound(prior, auth.state()));
    assert forall|edge: LinkEdge| #[trigger]
        auth.state().incoming_all[child_info.obj()].contains(edge) implies prior.dead_edge(
        edge,
    ) by {
        assert(edge == (root_info.obj(), published_index));
        assert(prior.seen_at(root_info.obj()) == unlinked_index);
    };
    auth.tracked_retire_node(child_info.obj(), prior)
}

/// Uses an authoritative history snapshot to discharge the structural
/// premises of [`protect_link`]. The remaining `seen_removed_sound` premise is
/// the reader-side observation carried by the live guard.
pub proof fn linked_list_authorized_protect_next(
    tracked auth: &LinkedListTraversalAuth,
    tracked guard: &mut RcuReadGuardToken<LinkedListNode>,
    tracked root_info: &RcuBlockInfo<LinkedListNode>,
    tracked next_info: &RcuBlockInfo<LinkedListNode>,
    n: LinkIndex,
) -> (tracked next_protected: RcuProtectedPtr<LinkedListNode>)
    requires
        auth.wf(),
        old(guard).can_protect(*root_info),
        old(guard).can_base_protect(*next_info),
        root_info.domain() == auth.domain(),
        next_info.domain() == auth.domain(),
        root_info.ptr() == auth.state().root,
        root_info.obj() == auth.state().root_obj,
        auth.state().objects.contains_pair(next_info.obj(), next_info.ptr()),
        n < auth.state().successors[root_info.obj()].len(),
        auth.state().successors[root_info.obj()][n as int] == Some(
            (next_info.ptr(), next_info.obj()),
        ),
        LinkedListTraversalSpec::seen_removed_sound(old(guard).seen_removed(), auth.state()),
        old(guard).seen_at(root_info.obj()) <= n,
    ensures
        next_protected.ptr() == next_info.ptr(),
        next_protected.obj() == next_info.obj(),
        next_protected.domain() == auth.domain(),
        next_protected.protected_by(*final(guard)),
        final(guard).wf(),
        LinkedListTraversalSpec::node_inv(next_info.ptr(), next_info.obj(), auth.state()),
{
    assert(LinkedListTraversalSpec::root_inv(root_info.ptr(), root_info.obj(), auth.state()));
    assert(LinkedListTraversalSpec::link_inv(
        root_info.ptr(),
        root_info.obj(),
        n,
        next_info.ptr(),
        next_info.obj(),
        auth.state(),
    ));
    linked_list_protect_next_example(
        guard,
        root_info,
        next_info,
        root_info.ptr(),
        n,
        next_info.ptr(),
        auth.state(),
    )
}

/// Example: after protecting the root, following a non-stale successor-history
/// event protects the next node under the same guard.
pub proof fn linked_list_protect_next_example(
    tracked guard: &mut RcuReadGuardToken<LinkedListNode>,
    tracked root_info: &RcuBlockInfo<LinkedListNode>,
    tracked next_info: &RcuBlockInfo<LinkedListNode>,
    root: *mut LinkedListNode,
    n: LinkIndex,
    next: *mut LinkedListNode,
    g: LinkedListGhost,
) -> (tracked next_protected: RcuProtectedPtr<LinkedListNode>)
    requires
        old(guard).can_protect(*root_info),
        old(guard).can_base_protect(*next_info),
        root_info.ptr() == root,
        next_info.ptr() == next,
        LinkedListTraversalSpec::root_inv(root, root_info.obj(), g),
        LinkedListTraversalSpec::link_inv(root, root_info.obj(), n, next, next_info.obj(), g),
        LinkedListTraversalSpec::seen_removed_sound(old(guard).seen_removed(), g),
        old(guard).seen_at(root_info.obj()) <= n,
    ensures
        next_protected.ptr() == next,
        next_protected.obj() == next_info.obj(),
        next_protected.domain() == old(guard).domain(),
        next_protected.protected_by(*final(guard)),
        final(guard).wf(),
        LinkedListTraversalSpec::node_inv(next, next_info.obj(), g),
{
    let tracked root_protected = protect_root::<LinkedListTraversalSpec>(guard, root_info, root, g);
    protect_link::<LinkedListTraversalSpec>(guard, &root_protected, next_info, n, next, g)
}

} // verus!
