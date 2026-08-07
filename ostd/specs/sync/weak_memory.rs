// SPDX-License-Identifier: MPL-2.0
//! OSTD-specific adapters for Verus' native IRC11 weak-memory atomics.
//!
//! This module contains only transitions coupled to the RCU root and monitor
//! ghost state. Generic native primitives are re-exported by
//! [`vstd_extra::atomic_irc11`].
use core::{marker::PhantomData, sync::atomic::Ordering};

use super::rcu::RcuTraversalSafety;
use super::{rcu as rcu_spec, rcu_cpu as rcu_cpu_spec};
use crate::specs::mm::cpu::online_cpus;
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::modes::tracked_static_ref;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::ghost_var::{GhostVar, GhostVarAuth};
use vstd::thread_view::Objective;
use vstd_extra::atomic_irc11::{
    AtomicId as Irc11AtomicId, AtomicPointsTo, PAtomicWeakBool as Irc11AtomicBool, PAtomicWeakPtr,
    ReleaseViewSeen, ThreadView as Irc11ThreadView, ThreadViewOrder as Irc11ThreadViewOrder,
    Timestamp, ViewSeen,
};

verus! {

broadcast use {vstd::atomic_weak::group_view_history, vstd::thread_view::group_thread_view_axioms};

/// Complete ghost state protected by one RCU root atomic invariant.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRootAtomicState<T, O> {
    pub(crate) points_to: AtomicPointsTo<*mut T>,
    pub(crate) root: rcu_spec::RcuRootOwnedGhost<T, ()>,
    pub(crate) permissions: rcu_cpu_spec::RcuRootPermissionState<T, O>,
}

unsafe impl<T, O: Objective> Objective for RcuRootAtomicState<T, O> {

}

impl<T, O> RcuRootAtomicState<T, O> {
    pub closed spec fn points_to(self) -> AtomicPointsTo<*mut T> {
        self.points_to
    }

    pub closed spec fn root(self) -> rcu_spec::RcuRootOwnedGhost<T, ()> {
        self.root
    }

    pub closed spec fn permissions(self) -> rcu_cpu_spec::RcuRootPermissionState<T, O> {
        self.permissions
    }
}

/// Invariant tying native IRC11 history to paper identities and physical
/// permissions for every allocation that has not yet been reclaimed.
pub struct RcuRootAtomicInv<OwnPred> {
    _marker: PhantomData<OwnPred>,
}

impl<T, O: Objective, OwnPred> InvariantPredicate<
    (rcu_spec::RcuRootKey, Irc11AtomicId),
    RcuRootAtomicState<T, O>,
> for RcuRootAtomicInv<OwnPred> where OwnPred: rcu_spec::RcuRootOwnershipPredicate<T, O> {
    open spec fn inv(
        key_loc: (rcu_spec::RcuRootKey, Irc11AtomicId),
        state: RcuRootAtomicState<T, O>,
    ) -> bool {
        let (key, loc) = key_loc;
        let g = state.root();
        let permissions = state.permissions();
        &&& rcu_spec::RcuOwnedWeakAtomicInv::<rcu_spec::UnitRcuRootOwnership>::inv(
            key_loc,
            (state.points_to(), g),
        )
        &&& permissions.wf()
        &&& permissions.scheduler() == key.scheduler
        &&& permissions.domain() == key.domain
        &&& permissions.root() == key.domain
        &&& permissions.retire_observation_registry() == key.retire_observation_registry
        &&& permissions.reclaim_registry() == key.reclaim_registry
        &&& permissions.active_lease_registry() == key.active_lease_registry
        &&& permissions.allocations() == g.infos().dom()
        &&& forall|obj: nat| #[trigger]
            permissions.keys().contains(obj) ==> {
                &&& permissions.contains(obj)
                &&& permissions.allocations().contains(obj)
                &&& permissions.reclaim_states().dom().contains(obj)
                &&& g.infos().contains_key(obj)
                &&& permissions.reclaim_states()[obj] is Some
                &&& permissions.reclaim_states()[obj]->Some_0 == g.infos()[obj].ptr()
                &&& OwnPred::owns(
                    permissions.reclaim_states()[obj]->Some_0,
                    permissions.ownership(obj),
                )
            }
        &&& permissions.unretired_claims().dom() == match g.current_registration() {
            Some(registration) => Set::empty().insert(registration.0.obj()),
            None => Set::empty(),
        }
        &&& forall|obj: nat| #[trigger]
            g.removals().contains_key(obj) ==> !permissions.has_unretired_claim(obj)
        &&& forall|obj: nat| #[trigger]
            permissions.reclaimed().contains_key(obj) ==> {
                &&& g.removals().contains_key(obj)
                &&& permissions.reclaimed()[obj].record().removal == g.removals()[obj]
            }
    }
}

pub type RcuRootAtomicInvariant<T, O, OwnPred> = AtomicInvariant<
    (rcu_spec::RcuRootKey, Irc11AtomicId),
    RcuRootAtomicState<T, O>,
    RcuRootAtomicInv<OwnPred>,
>;

/// Exposes the permission-state facts carried by the RCU root invariant.
///
/// Keeping this unfolding lemma beside [`RcuRootAtomicInv`] avoids making
/// executable callback code depend on the invariant's concrete conjunction.
pub(crate) proof fn lemma_root_atomic_permission_facts<T, O: Objective, OwnPred>(
    key_loc: (rcu_spec::RcuRootKey, Irc11AtomicId),
    tracked state: &RcuRootAtomicState<T, O>,
) where OwnPred: rcu_spec::RcuRootOwnershipPredicate<T, O>
    requires
        RcuRootAtomicInv::<OwnPred>::inv(key_loc, *state),
    ensures
        rcu_spec::RcuOwnedWeakAtomicInv::<rcu_spec::UnitRcuRootOwnership>::inv(
            key_loc,
            (state.points_to, state.root),
        ),
        state.root.root().domain_wf(),
        state.root.domain() == key_loc.0.domain,
        state.root.retire_observation_registry() == key_loc.0.retire_observation_registry,
        state.root.removals() == state.root.root().domain_auth().retire_observations(),
        state.permissions.wf(),
        state.permissions.scheduler() == key_loc.0.scheduler,
        state.permissions.domain() == key_loc.0.domain,
        state.permissions.root() == key_loc.0.domain,
        state.permissions.retire_observation_registry() == key_loc.0.retire_observation_registry,
        state.permissions.reclaim_registry() == key_loc.0.reclaim_registry,
        state.permissions.active_lease_registry() == key_loc.0.active_lease_registry,
        state.permissions.allocations() == state.root.infos().dom(),
        state.permissions.unretired_claims().dom() == match state.root.current_registration() {
            Some(registration) => Set::empty().insert(registration.0.obj()),
            None => Set::empty(),
        },
        forall|obj: nat| #[trigger]
            state.permissions.keys().contains(obj) ==> {
                &&& state.root.infos().contains_key(obj)
                &&& state.permissions.reclaim_states().dom().contains(obj)
                &&& state.permissions.reclaim_states()[obj] is Some
                &&& state.permissions.reclaim_states()[obj]->Some_0 == state.root.infos()[obj].ptr()
                &&& OwnPred::owns(
                    state.permissions.reclaim_states()[obj]->Some_0,
                    state.permissions.ownership(obj),
                )
            },
        forall|obj: nat| #[trigger]
            state.root.removals().contains_key(obj) ==> !state.permissions.has_unretired_claim(obj),
        forall|obj: nat| #[trigger]
            state.permissions.reclaimed().contains_key(obj) ==> {
                &&& state.root.removals().contains_key(obj)
                &&& state.permissions.reclaimed()[obj].record().removal
                    == state.root.removals()[obj]
            },
{
}

/// Re-folds the root invariant after a proof-only permission-state update.
pub(crate) proof fn lemma_build_root_atomic_inv<T, O: Objective, OwnPred>(
    key_loc: (rcu_spec::RcuRootKey, Irc11AtomicId),
    tracked state: &RcuRootAtomicState<T, O>,
) where OwnPred: rcu_spec::RcuRootOwnershipPredicate<T, O>
    requires
        rcu_spec::RcuOwnedWeakAtomicInv::<rcu_spec::UnitRcuRootOwnership>::inv(
            key_loc,
            (state.points_to, state.root),
        ),
        state.permissions.wf(),
        state.permissions.scheduler() == key_loc.0.scheduler,
        state.permissions.domain() == key_loc.0.domain,
        state.permissions.root() == key_loc.0.domain,
        state.permissions.retire_observation_registry() == key_loc.0.retire_observation_registry,
        state.permissions.reclaim_registry() == key_loc.0.reclaim_registry,
        state.permissions.active_lease_registry() == key_loc.0.active_lease_registry,
        state.permissions.allocations() == state.root.infos().dom(),
        forall|obj: nat| #[trigger]
            state.permissions.keys().contains(obj) ==> {
                &&& state.permissions.contains(obj)
                &&& state.permissions.allocations().contains(obj)
                &&& state.permissions.reclaim_states().dom().contains(obj)
                &&& state.root.infos().contains_key(obj)
                &&& state.permissions.reclaim_states()[obj] is Some
                &&& state.permissions.reclaim_states()[obj]->Some_0 == state.root.infos()[obj].ptr()
                &&& OwnPred::owns(
                    state.permissions.reclaim_states()[obj]->Some_0,
                    state.permissions.ownership(obj),
                )
            },
        state.permissions.unretired_claims().dom() == match state.root.current_registration() {
            Some(registration) => Set::empty().insert(registration.0.obj()),
            None => Set::empty(),
        },
        forall|obj: nat| #[trigger]
            state.root.removals().contains_key(obj) ==> !state.permissions.has_unretired_claim(obj),
        forall|obj: nat| #[trigger]
            state.permissions.reclaimed().contains_key(obj) ==> {
                &&& state.root.removals().contains_key(obj)
                &&& state.permissions.reclaimed()[obj].record().removal
                    == state.root.removals()[obj]
            },
    ensures
        RcuRootAtomicInv::<OwnPred>::inv(key_loc, *state),
{
}

/// Retired root metadata paired with the unique claim for its permission pool.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRetiredRootObject<T> {
    detached: rcu_spec::RcuRetiredOwnedObject<T, ()>,
    claim: rcu_cpu_spec::RcuReclaimClaim<T>,
}

impl<T> RcuRetiredRootObject<T> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& self.detached.object().wf()
        &&& self.claim.obj() == self.detached.object().obj()
        &&& self.claim.is_pending()
        &&& equal(self.claim.ptr(), self.detached.object().ptr())
    }

    pub closed spec fn object(self) -> rcu_spec::RcuObjectId<T> {
        self.detached.object()
    }

    pub closed spec fn retired(self) -> rcu_spec::RcuRetired<T> {
        self.detached.retired()
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.detached.ptr()
    }

    pub closed spec fn obj(self) -> nat {
        self.detached.obj()
    }

    pub closed spec fn claim(self) -> rcu_cpu_spec::RcuReclaimClaim<T> {
        self.claim
    }

    pub proof fn tracked_into_parts(tracked self) -> (tracked res: (
        rcu_spec::RcuObjectId<T>,
        rcu_spec::RcuRetired<T>,
        rcu_cpu_spec::RcuReclaimClaim<T>,
    ))
        ensures
            res.0 == self.object(),
            res.1 == self.retired(),
            res.2 == self.claim(),
            res.0.domain() == res.1.domain(),
            res.0.obj() == res.1.obj(),
            res.0.ptr() == res.1.ptr(),
            equal(res.0.ptr(), self.object().ptr()),
            res.0.obj() == res.2.obj(),
            res.0.wf(),
            res.2.is_pending(),
            equal(res.2.ptr(), res.0.ptr()),
    {
        use_type_invariant(&self);
        assert(self.claim.obj() == self.detached.object().obj());
        let tracked (object, retired, _unit) = self.detached.tracked_into_parts();
        assert(object == self.detached.object());
        assert(self.claim.obj() == object.obj());
        (object, retired, self.claim)
    }
}

/// Writer resources obtained after the traversal proof has certified that the
/// fixed child has no live incoming edge.
///
/// This is the handoff between the linked-list layer and base RCU: `retire`
/// authorizes the paper's `rcu-retire` transition, while `claim` is the unique
/// right to recover the physical ownership after a completed grace period.
pub tracked struct LinkedListDetachedChild {
    object: rcu_spec::RcuObjectId<rcu_spec::LinkedListNode>,
    retire: rcu_spec::RcuRetirePerm<rcu_spec::LinkedListNode>,
    claim: rcu_cpu_spec::RcuReclaimClaim<rcu_spec::LinkedListNode>,
    ghost removal: rcu_spec::RcuRemovalObservation,
}

impl LinkedListDetachedChild {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& self.object().wf()
        &&& self.retire().wf()
        &&& self.retire().ready_to_retire()
        &&& self.object().domain() == self.retire().domain()
        &&& self.object().obj() == self.retire().obj()
        &&& self.object().ptr() == self.retire().ptr()
        &&& self.claim().obj() == self.object().obj()
        &&& self.claim().is_pending()
        &&& equal(self.claim().ptr(), self.object().ptr())
    }

    pub closed spec fn object(self) -> rcu_spec::RcuObjectId<rcu_spec::LinkedListNode> {
        self.object
    }

    pub closed spec fn retire(self) -> rcu_spec::RcuRetirePerm<rcu_spec::LinkedListNode> {
        self.retire
    }

    pub closed spec fn claim(self) -> rcu_cpu_spec::RcuReclaimClaim<rcu_spec::LinkedListNode> {
        self.claim
    }

    pub closed spec fn removal(self) -> rcu_spec::RcuRemovalObservation {
        self.removal
    }

    /// Performs the base-RCU retirement transition after traversal retirement.
    pub proof fn tracked_retire(
        tracked self,
        tracked domain: &mut rcu_spec::RcuDomainAuth,
    ) -> (tracked res: LinkedListRetiredChild)
        requires
            old(domain).wf(),
            self.retire().belongs_to(*old(domain)),
            self.object().domain() == old(domain).id(),
        ensures
            final(domain).wf(),
            final(domain).id() == old(domain).id(),
            res.object() == self.object(),
            res.claim() == self.claim(),
            res.retired().domain() == self.object().domain(),
            res.retired().obj() == self.object().obj(),
            res.retired().ptr() == self.object().ptr(),
            res.retired().removal() == self.removal(),
    {
        use_type_invariant(&self);
        let ghost object_value = self.object();
        let ghost claim_value = self.claim();
        assert(self.object().domain() == old(domain).id());
        let tracked LinkedListDetachedChild { object, retire, claim, removal } = self;
        let tracked retired = domain.tracked_retire(retire, removal);
        assert(object == object_value);
        assert(claim == claim_value);
        assert(object.wf());
        assert(retired.wf());
        assert(retired.domain() == old(domain).id());
        assert(object.domain() == retired.domain());
        assert(object.obj() == retired.obj());
        assert(object.ptr() == retired.ptr());
        assert(claim.obj() == object.obj());
        assert(claim.is_pending());
        assert(equal(claim.ptr(), object.ptr()));
        LinkedListRetiredChild { object, retired, claim }
    }
}

/// A retired linked-list child paired with the claim that will eventually
/// recover its physical ownership.
pub tracked struct LinkedListRetiredChild {
    object: rcu_spec::RcuObjectId<rcu_spec::LinkedListNode>,
    retired: rcu_spec::RcuRetired<rcu_spec::LinkedListNode>,
    claim: rcu_cpu_spec::RcuReclaimClaim<rcu_spec::LinkedListNode>,
}

impl LinkedListRetiredChild {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& self.object().wf()
        &&& self.retired().wf()
        &&& self.object().domain() == self.retired().domain()
        &&& self.object().obj() == self.retired().obj()
        &&& self.object().ptr() == self.retired().ptr()
        &&& self.claim().obj() == self.object().obj()
        &&& self.claim().is_pending()
        &&& equal(self.claim().ptr(), self.object().ptr())
    }

    pub closed spec fn object(self) -> rcu_spec::RcuObjectId<rcu_spec::LinkedListNode> {
        self.object
    }

    pub closed spec fn retired(self) -> rcu_spec::RcuRetired<rcu_spec::LinkedListNode> {
        self.retired
    }

    pub closed spec fn claim(self) -> rcu_cpu_spec::RcuReclaimClaim<rcu_spec::LinkedListNode> {
        self.claim
    }

    /// Compresses the typed traversal retirement into the type-erased safety
    /// certificate consumed by the existing callback monitor.
    pub proof fn tracked_certify_callback(tracked self) -> (tracked res: (
        rcu_spec::RcuObjectId<rcu_spec::LinkedListNode>,
        rcu_spec::RcuCallbackSafety,
        rcu_cpu_spec::RcuReclaimClaim<rcu_spec::LinkedListNode>,
    ))
        ensures
            res.0 == self.object(),
            res.2 == self.claim(),
            res.1.domain() == res.0.domain(),
            res.1.obj() == res.0.obj(),
            res.1.removal() == self.retired().removal(),
            res.1.retire_observation_registry() == self.retired().retire_observation_registry(),
            rcu_spec::callback_safety_from_traversal(res.1, res.0),
    {
        use_type_invariant(&self);
        let tracked LinkedListRetiredChild { object, retired, claim } = self;
        let tracked cert = rcu_spec::certify_callback_from_retired(&object, retired);
        (object, cert, claim)
    }
}

/// Immutable identities carried by the native atomic invariant for the
/// two-node linked-list traversal example.
pub ghost struct LinkedListAtomicKey {
    pub scheduler: Loc,
    pub domain: Loc,
    pub root: Loc,
    pub retire_observation_registry: Loc,
    pub reclaim_registry: Loc,
    pub active_lease_registry: Loc,
    pub lifecycle: Loc,
    pub timestamp_registry: Loc,
    pub source: *mut rcu_spec::LinkedListNode,
    pub source_obj: nat,
    pub child: *mut rcu_spec::LinkedListNode,
    pub child_obj: nat,
}

/// Writer-visible lifecycle of the fixed child managed by one concrete link.
///
/// The two halves of a [`GhostVar`] keep this phase synchronized between the
/// executable wrapper and its atomic invariant.  In particular, a writer that
/// has moved the child to `Retired` can no longer call the publication rule,
/// while stale readers may continue returning leases until `Reclaimed`.
pub ghost enum LinkedListChildPhase {
    /// The child is registered but has never been published by this link.
    Unpublished,
    /// The child is the latest value of the link.
    Linked { index: rcu_spec::LinkIndex, timestamp: Timestamp },
    /// The child was removed by the recorded native atomic message.
    Unlinked { index: rcu_spec::LinkIndex, removal: rcu_spec::RcuRemovalObservation },
    /// Traversal retirement and the physical reclaim claim left the invariant.
    Retired { index: rcu_spec::LinkIndex, removal: rcu_spec::RcuRemovalObservation },
    /// Grace-period completion recovered the physical ownership resource.
    Reclaimed { index: rcu_spec::LinkIndex, removal: rcu_spec::RcuRemovalObservation },
}

impl LinkedListChildPhase {
    pub open spec fn is_reclaimed(self) -> bool {
        self is Reclaimed
    }

    pub open spec fn is_unpublished(self) -> bool {
        self is Unpublished
    }

    pub open spec fn is_linked(self) -> bool {
        self is Linked
    }

    pub open spec fn is_unlinked(self) -> bool {
        self is Unlinked
    }

    pub open spec fn is_retired(self) -> bool {
        self is Retired
    }
}

/// Complete state protected by one native linked-list link invariant.
pub tracked struct LinkedListAtomicState<O> {
    pub(crate) points_to: AtomicPointsTo<*mut rcu_spec::LinkedListNode>,
    pub(crate) link: rcu_spec::LinkedListAtomicLinkGhost,
    pub(crate) auth: rcu_spec::LinkedListTraversalAuth,
    pub(crate) permissions: rcu_cpu_spec::RcuRootPermissionState<rcu_spec::LinkedListNode, O>,
    pub(crate) lifecycle: GhostVarAuth<LinkedListChildPhase>,
}

unsafe impl<O: Objective> Objective for LinkedListAtomicState<O> {

}

impl<O> LinkedListAtomicState<O> {
    pub closed spec fn points_to(self) -> AtomicPointsTo<*mut rcu_spec::LinkedListNode> {
        self.points_to
    }

    pub closed spec fn link(self) -> rcu_spec::LinkedListAtomicLinkGhost {
        self.link
    }

    pub closed spec fn auth(self) -> rcu_spec::LinkedListTraversalAuth {
        self.auth
    }

    pub closed spec fn permissions(self) -> rcu_cpu_spec::RcuRootPermissionState<
        rcu_spec::LinkedListNode,
        O,
    > {
        self.permissions
    }

    pub closed spec fn lifecycle(self) -> GhostVarAuth<LinkedListChildPhase> {
        self.lifecycle
    }
}

/// Native IRC11 invariant for a link whose only non-null value is one
/// pre-registered child.
///
/// Restricting the first executable-style wrapper to two nodes keeps the
/// atomic protocol closed while the general node-registration and physical
/// permission pools are still being designed.
pub struct LinkedListAtomicInv<OwnPred> {
    _marker: PhantomData<OwnPred>,
}

impl<O: Objective, OwnPred> InvariantPredicate<
    (LinkedListAtomicKey, Irc11AtomicId),
    LinkedListAtomicState<O>,
> for LinkedListAtomicInv<OwnPred> where
    OwnPred: rcu_spec::RcuRootOwnershipPredicate<rcu_spec::LinkedListNode, O>,
 {
    open spec fn inv(
        key_loc: (LinkedListAtomicKey, Irc11AtomicId),
        state: LinkedListAtomicState<O>,
    ) -> bool {
        let (key, loc) = key_loc;
        let permissions = state.permissions();
        &&& state.points_to().loc() == loc
        &&& key.source.addr() != 0
        &&& key.child.addr() != 0
        &&& key.source.addr() != key.child.addr()
        &&& key.source_obj != key.child_obj
        &&& state.auth().wf()
        &&& state.auth().domain() == key.domain
        &&& state.auth().state().root == key.source
        &&& state.auth().state().root_obj == key.source_obj
        &&& state.auth().state().objects == Map::empty().insert(key.source_obj, key.source).insert(
            key.child_obj,
            key.child,
        )
        &&& state.auth().state().incoming_all.contains_key(key.child_obj)
        &&& state.auth().state().successors.contains_key(key.source_obj)
        &&& permissions.wf()
        &&& permissions.scheduler() == key.scheduler
        &&& permissions.domain() == key.domain
        &&& permissions.root() == key.root
        &&& permissions.retire_observation_registry() == key.retire_observation_registry
        &&& permissions.reclaim_registry() == key.reclaim_registry
        &&& permissions.active_lease_registry() == key.active_lease_registry
        &&& permissions.allocations() == Set::empty().insert(key.child_obj)
        &&& state.lifecycle().id() == key.lifecycle
        &&& state.link().source() == key.source
        &&& state.link().source_obj() == key.source_obj
        &&& state.link().timestamp_registry() == key.timestamp_registry
        &&& state.link().wf(state.points_to().hist(), state.auth())
        &&& forall|n: rcu_spec::LinkIndex|
            n < state.auth().state().successors[key.source_obj].len()
                && state.auth().state().successors[key.source_obj][n as int] is Some
                ==> #[trigger] state.auth().state().successors[key.source_obj][n as int] == Some(
                (key.child, key.child_obj),
            )
        &&& match state.lifecycle()@ {
            LinkedListChildPhase::Unpublished => {
                &&& state.auth().removed() == Set::<nat>::empty()
                &&& state.auth().has_retire_perm(key.child_obj)
                &&& permissions.keys() == Set::empty().insert(key.child_obj)
                &&& permissions.contains(key.child_obj)
                &&& permissions.reclaim_states()[key.child_obj] == Some(key.child)
                &&& permissions.has_unretired_claim(key.child_obj)
                &&& OwnPred::owns(key.child, permissions.ownership(key.child_obj))
                &&& state.auth().state().successors[key.source_obj].len() == 1
                &&& state.auth().state().successors[key.source_obj].last() is None
                &&& state.auth().state().incoming_all[key.child_obj] == Set::<
                    rcu_spec::LinkEdge,
                >::empty()
            },
            LinkedListChildPhase::Linked { index, timestamp } => {
                &&& state.auth().removed() == Set::<nat>::empty()
                &&& state.auth().has_retire_perm(key.child_obj)
                &&& permissions.keys() == Set::empty().insert(key.child_obj)
                &&& permissions.contains(key.child_obj)
                &&& permissions.reclaim_states()[key.child_obj] == Some(key.child)
                &&& permissions.has_unretired_claim(key.child_obj)
                &&& OwnPred::owns(key.child, permissions.ownership(key.child_obj))
                &&& state.link().current_timestamp() == timestamp
                &&& state.link().index_at(timestamp) == index
                &&& index + 1 == state.auth().state().successors[key.source_obj].len()
                &&& state.auth().state().successors[key.source_obj].last() == Some(
                    (key.child, key.child_obj),
                )
                &&& state.auth().state().incoming_all[key.child_obj] == Set::empty().insert(
                    (key.source_obj, index),
                )
            },
            LinkedListChildPhase::Unlinked { index, removal } => {
                &&& state.auth().removed() == Set::<nat>::empty()
                &&& state.auth().has_retire_perm(key.child_obj)
                &&& permissions.keys() == Set::empty().insert(key.child_obj)
                &&& permissions.contains(key.child_obj)
                &&& permissions.reclaim_states()[key.child_obj] == Some(key.child)
                &&& permissions.has_unretired_claim(key.child_obj)
                &&& OwnPred::owns(key.child, permissions.ownership(key.child_obj))
                &&& removal.root == key.root
                &&& state.link().current_timestamp() == removal.timestamp
                &&& state.link().index_at(removal.timestamp) == index
                &&& state.points_to().hist().thread_view(removal.timestamp) == removal.message_view
                &&& index + 1 == state.auth().state().successors[key.source_obj].len()
                &&& state.auth().state().successors[key.source_obj].last() is None
                &&& index > 0
                &&& state.auth().state().incoming_all[key.child_obj] == Set::empty().insert(
                    (key.source_obj, (index - 1) as nat),
                )
            },
            LinkedListChildPhase::Retired { index, removal } => {
                &&& state.auth().removed() == Set::<nat>::empty().insert(key.child_obj)
                &&& !state.auth().has_retire_perm(key.child_obj)
                &&& permissions.keys() == Set::empty().insert(key.child_obj)
                &&& permissions.contains(key.child_obj)
                &&& permissions.reclaim_states()[key.child_obj] == Some(key.child)
                &&& !permissions.has_unretired_claim(key.child_obj)
                &&& OwnPred::owns(key.child, permissions.ownership(key.child_obj))
                &&& removal.root == key.root
                &&& state.link().current_timestamp() == removal.timestamp
                &&& state.points_to().hist().thread_view(removal.timestamp) == removal.message_view
                &&& state.auth().state().successors[key.source_obj].last() is None
                &&& index > 0
                &&& state.link().index_at(removal.timestamp) == index
                &&& state.auth().state().incoming_all[key.child_obj] == Set::empty().insert(
                    (key.source_obj, (index - 1) as nat),
                )
            },
            LinkedListChildPhase::Reclaimed { index, removal } => {
                &&& state.auth().removed() == Set::<nat>::empty().insert(key.child_obj)
                &&& !state.auth().has_retire_perm(key.child_obj)
                &&& permissions.keys() == Set::<nat>::empty()
                &&& !permissions.contains(key.child_obj)
                &&& permissions.reclaim_states()[key.child_obj] is None
                &&& !permissions.has_unretired_claim(key.child_obj)
                &&& permissions.reclaimed().contains_key(key.child_obj)
                &&& permissions.reclaimed()[key.child_obj].record().removal == removal
                &&& removal.root == key.root
                &&& state.link().current_timestamp() == removal.timestamp
                &&& state.points_to().hist().thread_view(removal.timestamp) == removal.message_view
                &&& state.auth().state().successors[key.source_obj].last() is None
                &&& index > 0
                &&& state.link().index_at(removal.timestamp) == index
                &&& state.auth().state().incoming_all[key.child_obj] == Set::empty().insert(
                    (key.source_obj, (index - 1) as nat),
                )
            },
        }
    }
}

pub type LinkedListAtomicInvariant<O, OwnPred> = AtomicInvariant<
    (LinkedListAtomicKey, Irc11AtomicId),
    LinkedListAtomicState<O>,
    LinkedListAtomicInv<OwnPred>,
>;

/// Executable-style native weak atomic used to close the linked-list
/// traversal invariant before generalizing it to arbitrary data structures.
pub struct LinkedListWeakAtomicLink<O: Objective + 'static, OwnPred: 'static> {
    atomic: PAtomicWeakPtr<rcu_spec::LinkedListNode>,
    child: *mut rcu_spec::LinkedListNode,
    tracked_atomic_inv: Tracked<&'static LinkedListAtomicInvariant<O, OwnPred>>,
    tracked_child_phase: Tracked<GhostVar<LinkedListChildPhase>>,
}

impl<O: Objective + 'static, OwnPred: 'static> LinkedListWeakAtomicLink<O, OwnPred> {
    pub closed spec fn constant(&self) -> LinkedListAtomicKey {
        self.tracked_atomic_inv@.constant().0
    }

    pub closed spec fn native_loc(&self) -> Irc11AtomicId {
        self.atomic.loc()
    }

    /// Namespace of the atomic invariant owned by this wrapper.
    pub closed spec fn invariant_namespace(&self) -> int {
        self.tracked_atomic_inv@.namespace()
    }

    pub closed spec fn child_ptr(&self) -> *mut rcu_spec::LinkedListNode {
        self.child
    }

    /// Runtime child pointer retained by this one-link wrapper.
    #[inline(always)]
    pub(crate) fn child_raw(&self) -> (res: *mut rcu_spec::LinkedListNode)
        ensures
            equal(res, self.child_ptr()),
    {
        self.child
    }

    pub closed spec fn child_phase(&self) -> LinkedListChildPhase {
        self.tracked_child_phase@.view()
    }

    pub closed spec fn well_formed(&self) -> bool {
        &&& self.tracked_atomic_inv@.constant().1 == self.native_loc()
        &&& self.child_ptr() == self.constant().child
        &&& self.child_ptr().addr() != 0
        &&& self.tracked_child_phase@.id() == self.constant().lifecycle
    }

    /// Exposes the structural consequences of the closed wrapper invariant to
    /// executable adapters without exposing its proof-resource representation.
    pub proof fn lemma_well_formed_facts(&self)
        requires
            self.well_formed(),
        ensures
            self.child_ptr() == self.constant().child,
            self.child_ptr().addr() != 0,
    {
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(&self) -> bool {
        self.well_formed()
    }
}

impl<O: Objective + 'static, OwnPred: 'static> LinkedListWeakAtomicLink<O, OwnPred> where
    OwnPred: rcu_spec::RcuRootOwnershipPredicate<rcu_spec::LinkedListNode, O>,
 {
    /// Creates a null link with a pre-registered source and child.
    pub const fn new(
        Ghost(scheduler): Ghost<Loc>,
        Ghost(root): Ghost<Loc>,
        Ghost(retire_observation_registry): Ghost<Loc>,
        child: *mut rcu_spec::LinkedListNode,
        Tracked(source_info): Tracked<&rcu_spec::RcuBlockInfo<rcu_spec::LinkedListNode>>,
        Tracked(source_retire): Tracked<rcu_spec::RcuBaseRetirePerm<rcu_spec::LinkedListNode>>,
        Tracked(child_info): Tracked<&rcu_spec::RcuBlockInfo<rcu_spec::LinkedListNode>>,
        Tracked(child_retire): Tracked<rcu_spec::RcuBaseRetirePerm<rcu_spec::LinkedListNode>>,
        Tracked(child_ownership): Tracked<O>,
    ) -> (res: Self)
        requires
            source_info.wf(),
            source_retire.wf(),
            source_retire.domain() == source_info.domain(),
            source_retire.obj() == source_info.obj(),
            source_retire.ptr() == source_info.ptr(),
            child_info.wf(),
            child_retire.wf(),
            child_info.domain() == source_info.domain(),
            child_retire.domain() == source_info.domain(),
            child_retire.obj() == child_info.obj(),
            child_retire.ptr() == child_info.ptr(),
            child == child_info.ptr(),
            source_info.addr() != 0,
            child_info.addr() != 0,
            source_info.addr() != child_info.addr(),
            source_info.ptr() != child_info.ptr(),
            source_info.obj() != child_info.obj(),
            OwnPred::owns(child, child_ownership),
        ensures
            res.well_formed(),
            res.constant().scheduler == scheduler,
            res.constant().domain == source_info.domain(),
            res.constant().root == root,
            res.constant().retire_observation_registry == retire_observation_registry,
            res.constant().source == source_info.ptr(),
            res.constant().source_obj == source_info.obj(),
            res.constant().child == child_info.ptr(),
            res.constant().child_obj == child_info.obj(),
            res.child_ptr() == child,
            res.child_phase() is Unpublished,
    {
        let (atomic, Tracked(points_to), Tracked(initial_view), Ghost(timestamp)) =
            PAtomicWeakPtr::new(core::ptr::null_mut());
        let tracked mut auth = rcu_spec::LinkedListTraversalAuth::tracked_new(
            source_info,
            source_retire,
        );
        proof {
            assert(auth.has_retire_perm(source_info.obj()));
            assert(!auth.has_retire_perm(child_info.obj()));
            auth.tracked_register_node(child_info, child_retire);
        }
        let ghost initial_index = auth.tracked_initialize_null(
            source_info.ptr(),
            source_info.obj(),
        );
        let tracked link = rcu_spec::LinkedListAtomicLinkGhost::tracked_initial_null(
            points_to.hist(),
            timestamp,
            initial_view@,
            &auth,
            source_info.ptr(),
            source_info.obj(),
        );
        proof_decl! {
            let tracked mut permissions:
                rcu_cpu_spec::RcuRootPermissionState<rcu_spec::LinkedListNode, O>;
            let ghost reclaim_registry: Loc;
            let ghost active_lease_registry: Loc;
            let ghost child_ownership_value: O;
        }
        proof {
            permissions =
            rcu_cpu_spec::RcuRootPermissionState::empty(
                scheduler,
                source_info.domain(),
                root,
                retire_observation_registry,
            );
            reclaim_registry = permissions.reclaim_registry();
            active_lease_registry = permissions.active_lease_registry();
            child_ownership_value = child_ownership;
            assert(permissions.allocations() == Set::<nat>::empty());
            permissions.tracked_insert(child_info, child_ownership);
        }
        let tracked (lifecycle, lifecycle_peer) = GhostVarAuth::new(
            LinkedListChildPhase::Unpublished,
        );
        let tracked state = LinkedListAtomicState { points_to, link, auth, permissions, lifecycle };
        let ghost key = LinkedListAtomicKey {
            scheduler,
            domain: source_info.domain(),
            root,
            retire_observation_registry,
            reclaim_registry,
            active_lease_registry,
            lifecycle: state.lifecycle().id(),
            timestamp_registry: state.link().timestamp_registry(),
            source: source_info.ptr(),
            source_obj: source_info.obj(),
            child: child_info.ptr(),
            child_obj: child_info.obj(),
        };
        proof {
            source_info.lemma_wf_facts();
            child_info.lemma_wf_facts();
            assert(initial_index == 0);
            assert(state.points_to().loc() == atomic.loc());
            assert(key.source.addr() == source_info.addr());
            assert(key.child.addr() == child_info.addr());
            assert(state.auth().wf());
            assert(state.auth().domain() == key.domain);
            assert(state.auth().removed() == Set::<nat>::empty());
            assert(state.auth().state().root == key.source);
            assert(state.auth().state().root_obj == key.source_obj);
            assert(state.auth().state().objects == Map::empty().insert(
                key.source_obj,
                key.source,
            ).insert(key.child_obj, key.child));
            assert(state.permissions().wf());
            assert(state.permissions().scheduler() == key.scheduler);
            assert(state.permissions().domain() == key.domain);
            assert(state.permissions().root() == key.root);
            assert(state.permissions().retire_observation_registry()
                == key.retire_observation_registry);
            assert(state.permissions().reclaim_registry() == key.reclaim_registry);
            assert(state.permissions().active_lease_registry() == key.active_lease_registry);
            assert(state.permissions().allocations() == Set::empty().insert(key.child_obj));
            assert(state.permissions().keys() == Set::empty().insert(key.child_obj));
            assert(state.permissions().contains(key.child_obj));
            assert(state.permissions().reclaim_states()[key.child_obj] == Some(key.child));
            assert(state.permissions().has_unretired_claim(key.child_obj));
            assert(state.permissions().ownership(key.child_obj) == child_ownership_value);
            assert(OwnPred::owns(key.child, state.permissions().ownership(key.child_obj)));
            assert(state.lifecycle()@ is Unpublished);
            assert(state.link().source() == key.source);
            assert(state.link().source_obj() == key.source_obj);
            assert(state.link().wf(state.points_to().hist(), state.auth()));
            assert forall|n: rcu_spec::LinkIndex|
                n < state.auth().state().successors[key.source_obj].len()
                    && state.auth().state().successors[key.source_obj][n as int] is Some implies #[trigger] state.auth().state().successors[key.source_obj][n as int]
                == Some((key.child, key.child_obj)) by {
                assert(n == 0);
                assert(state.auth().state().successors[key.source_obj][n as int] is None);
                assert(false);
            };
            assert(LinkedListAtomicInv::<OwnPred>::inv((key, atomic.loc()), state));
        }
        let tracked atomic_inv = AtomicInvariant::new((key, atomic.loc()), state, 0);
        let tracked atomic_inv = tracked_static_ref(atomic_inv);
        LinkedListWeakAtomicLink {
            atomic,
            child,
            tracked_atomic_inv: Tracked(atomic_inv),
            tracked_child_phase: Tracked(lifecycle_peer),
        }
    }

    fn raw_atomic(&self) -> (res: &PAtomicWeakPtr<rcu_spec::LinkedListNode>)
        requires
            self.well_formed(),
        ensures
            res.loc() == self.native_loc(),
        opens_invariants none
        no_unwind
    {
        &self.atomic
    }

    pub proof fn tracked_atomic_inv(tracked &self) -> (tracked res:
        &'static LinkedListAtomicInvariant<O, OwnPred>)
        requires
            self.well_formed(),
        ensures
            res.constant() == (self.constant(), self.native_loc()),
    {
        self.tracked_atomic_inv.get()
    }

    /// Acquire-loads the native link and applies the paper's guarded traversal
    /// rule in the same atomic-invariant opening.
    ///
    /// `previous` is absent for the first observation and otherwise carries
    /// the persistent timestamp/index fact returned by the preceding load.
    /// Its native view lower bound prevents a later load from moving the
    /// guard's dense traversal position backwards.
    #[inline(always)]
    pub fn load_acquire_and_protect(
        &self,
        Tracked(guard): Tracked<&mut rcu_spec::RcuReadGuardToken<rcu_spec::LinkedListNode>>,
        Tracked(from): Tracked<&mut rcu_spec::RcuProtectedPtr<rcu_spec::LinkedListNode>>,
        Tracked(previous): Tracked<Option<&rcu_spec::LinkedListLinkObservation>>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: (
        *mut rcu_spec::LinkedListNode,
        Ghost<Timestamp>,
        Ghost<rcu_spec::LinkIndex>,
        Tracked<Option<rcu_spec::RcuProtectedPtr<rcu_spec::LinkedListNode>>>,
        Tracked<rcu_spec::LinkedListLinkObservation>,
    ))
        requires
            self.well_formed(),
            !self.child_phase().is_reclaimed(),
            old(guard).wf(),
            old(guard).domain() == self.constant().domain,
            old(guard).seen_removed().removed == Set::<nat>::empty(),
            match previous {
                None => old(guard).seen_at(self.constant().source_obj) == 0,
                Some(observation) => {
                    &&& observation.registry() == self.constant().timestamp_registry
                    &&& observation.loc() == self.native_loc()
                    &&& old(tv)@.contains(observation.view())
                    &&& old(guard).seen_at(self.constant().source_obj) == observation.index()
                },
            },
            old(from).protected_by(*old(guard)),
            old(from).ptr() == self.constant().source,
            old(from).obj() == self.constant().source_obj,
        ensures
            old(tv)@.spec_le(final(tv)@),
            final(guard).wf(),
            final(guard).domain() == old(guard).domain(),
            final(guard).seen_removed().removed == old(guard).seen_removed().removed,
            final(guard).seen_at(self.constant().source_obj) == res.2@,
            final(from).ptr() == self.constant().source,
            final(from).obj() == self.constant().source_obj,
            res.4@.registry() == self.constant().timestamp_registry,
            res.4@.loc() == self.native_loc(),
            res.4@.timestamp() == res.1@,
            res.4@.index() == res.2@,
            res.4@.view() == final(tv)@,
            (res.3@ is Some) == (res.0.addr() != 0),
            match res.3@ {
                None => res.0.addr() == 0,
                Some(child) => {
                    &&& equal(child.ptr(), res.0)
                    &&& child.ptr() == self.constant().child
                    &&& child.obj() == self.constant().child_obj
                    &&& child.domain() == self.constant().domain
                    &&& child.protected_by(*final(guard))
                },
            },
        no_unwind
    {
        let result;
        let ghost view_before = tv@;
        proof {
            use_type_invariant(&*self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => state => {
            proof {
                state.lifecycle.agree(self.tracked_child_phase.borrow());
                assert(LinkedListAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
                assert(state.lifecycle@ == self.child_phase());
                match state.lifecycle@ {
                    LinkedListChildPhase::Reclaimed { index: _, removal: _ } => assert(false),
                    _ => {},
                }
                assert(state.permissions.contains(self.constant().child_obj));
                assert(OwnPred::owns(
                    self.constant().child,
                    state.permissions.ownership(self.constant().child_obj),
                ));
                assert(state.points_to.loc() == self.native_loc());
                match previous {
                    None => {
                        assert(guard.seen_at(from.obj()) == 0);
                    },
                    Some(observation) => {
                        use_type_invariant(observation);
                        observation.lemma_view_timestamp();
                        assert(vstd_extra::atomic_irc11::timestamp_in_view(
                            observation.loc(),
                            observation.view(),
                        ) == Some(observation.timestamp()));
                        assert(observation.loc() == self.native_loc());
                        state.link.lemma_observation_agrees(observation);
                        assert(state.link.index_at(observation.timestamp())
                            == observation.index());
                        assert(state.points_to.hist().contains_timestamp(
                            observation.timestamp(),
                        ));
                        vstd_extra::atomic_irc11::axiom_get_timestamp_is_location_projection(
                            &state.points_to,
                            observation.view(),
                        );
                        assert(vstd_extra::atomic_irc11::timestamp_in_view(
                            self.native_loc(),
                            observation.view(),
                        ) == Some(observation.timestamp()));
                        assert(state.points_to.get_timestamp(observation.view())
                            == Some(observation.timestamp()));
                        state.points_to.get_timestamp_monotonic(
                            view_before,
                            observation.view(),
                        );
                    },
                }
            }
            let loaded = raw_atomic.load(
                Ordering::Acquire,
                Tracked(tv),
                Tracked(&state.points_to),
            );
            let ghost timestamp = loaded.2@.timestamp;
            let ghost index = state.link.index_at(timestamp);
            proof {
                assert(state.points_to.hist().contains_timestamp(timestamp));
                match previous {
                    None => {
                        assert(guard.seen_at(from.obj()) == 0);
                    },
                    Some(observation) => {
                        assert(state.points_to.get_timestamp(view_before).is_some());
                        assert(observation.timestamp()
                            <= state.points_to.get_timestamp(view_before).unwrap());
                        assert(state.points_to.get_timestamp(view_before).unwrap() <= timestamp);
                        assert(observation.timestamp() <= timestamp);
                        assert(state.link.index_at(observation.timestamp())
                            == observation.index());
                        assert(observation.index() <= index);
                        assert(guard.seen_at(from.obj()) == observation.index());
                    },
                }
                assert(guard.seen_at(from.obj()) <= index);
                assert(rcu_spec::LinkedListTraversalSpec::seen_removed_sound(
                    old(guard).seen_removed(),
                    state.auth.state(),
                )) by {
                    assert forall|obj: nat| #[trigger]
                        old(guard).seen_removed().removed.contains(obj) implies {
                            &&& state.auth.state().incoming_all.contains_key(obj)
                            &&& forall|edge: rcu_spec::LinkEdge| #[trigger]
                                state.auth.state().incoming_all[obj].contains(edge)
                                    ==> old(guard).seen_removed().dead_edge(edge)
                        } by {};
                };
            }
            proof_decl! {
                let tracked protected = state.link.tracked_load_and_protect(
                    state.points_to.hist(),
                    &state.auth,
                    guard,
                    from,
                    timestamp,
                );
                let tracked observation;
            }
            proof {
                vstd_extra::atomic_irc11::axiom_get_timestamp_is_location_projection(
                    &state.points_to,
                    tv@,
                );
                assert(vstd_extra::atomic_irc11::timestamp_in_view(
                    self.native_loc(),
                    tv@,
                ) == Some(timestamp));
                observation = state.link.tracked_observation_at(
                    state.points_to.hist(),
                    &state.auth,
                    timestamp,
                    self.native_loc(),
                    tv@,
                );
                assert(equal(state.points_to.hist().value(timestamp), loaded.0));
                match &protected {
                    None => {
                        assert(loaded.0.addr() == 0);
                    },
                    Some(child) => {
                        assert(state.auth.state().successors[self.constant().source_obj][index as int]
                            is Some);
                        assert(state.auth.state().successors[self.constant().source_obj][index as int]
                            == Some((self.constant().child, self.constant().child_obj)));
                        assert(child.ptr() == self.constant().child);
                        assert(child.obj() == self.constant().child_obj);
                    },
                }
                assert(LinkedListAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
            result = (
                loaded.0,
                Ghost(timestamp),
                Ghost(index),
                Tracked(protected),
                Tracked(observation),
            );
        });
        result
    }

    /// Acquire-loads an internal link, applies the paper traversal rule, and
    /// splits a physical read lease for the observed child in one atomic
    /// invariant opening.
    ///
    /// A non-null result retains the child protection witness for subsequent
    /// traversal while the lease supplies the physical ownership resource
    /// used to derive a concrete `RefPermission`.  A null result leaves the
    /// CPU reader fraction unchanged.
    #[inline(always)]
    pub fn load_acquire_and_lease_cpu(
        &self,
        Tracked(guard): Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<rcu_spec::LinkedListNode>>,
        Tracked(from): Tracked<&mut rcu_spec::RcuProtectedPtr<rcu_spec::LinkedListNode>>,
        Tracked(previous): Tracked<Option<&rcu_spec::LinkedListLinkObservation>>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: (
        *mut rcu_spec::LinkedListNode,
        Ghost<Timestamp>,
        Ghost<rcu_spec::LinkIndex>,
        Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<rcu_spec::LinkedListNode>>,
        Tracked<Option<rcu_spec::RcuProtectedPtr<rcu_spec::LinkedListNode>>>,
        Tracked<Option<rcu_cpu_spec::RcuRootReadLease<O>>>,
        Tracked<rcu_spec::LinkedListLinkObservation>,
    ))
        requires
            self.well_formed(),
            !self.child_phase().is_reclaimed(),
            guard.wf(),
            guard.scheduler() == self.constant().scheduler,
            guard.domain() == self.constant().domain,
            guard.root() == self.constant().root,
            guard.retire_observation_registry() == self.constant().retire_observation_registry,
            online_cpus().contains(guard.cpu()),
            guard.seen_removed().removed == Set::<nat>::empty(),
            match previous {
                None => guard.paper_guard().seen_at(self.constant().source_obj) == 0,
                Some(observation) => {
                    &&& observation.registry() == self.constant().timestamp_registry
                    &&& observation.loc() == self.native_loc()
                    &&& old(tv)@.contains(observation.view())
                    &&& guard.paper_guard().seen_at(self.constant().source_obj)
                        == observation.index()
                },
            },
            old(from).protected_by(guard.paper_guard()),
            old(from).ptr() == self.constant().source,
            old(from).obj() == self.constant().source_obj,
        ensures
            old(tv)@.spec_le(final(tv)@),
            res.3@.wf(),
            res.3@.binding() == guard.binding(),
            res.3@.participant_id() == guard.participant_id(),
            res.3@.cpu() == guard.cpu(),
            res.3@.generation() == guard.generation(),
            res.3@.participant_view() == guard.participant_view(),
            res.3@.known_retired() == guard.known_retired(),
            res.3@.scheduler() == guard.scheduler(),
            res.3@.domain() == guard.domain(),
            res.3@.root() == guard.root(),
            res.3@.reader_registry() == guard.reader_registry(),
            res.3@.retire_observation_registry() == guard.retire_observation_registry(),
            res.3@.reader_context() == guard.reader_context(),
            res.3@.start_view() == guard.start_view(),
            res.3@.expired() == guard.expired(),
            res.3@.seen_removed().removed == guard.seen_removed().removed,
            res.3@.paper_guard().seen_at(self.constant().source_obj) == res.2@,
            final(from).ptr() == self.constant().source,
            final(from).obj() == self.constant().source_obj,
            res.6@.registry() == self.constant().timestamp_registry,
            res.6@.loc() == self.native_loc(),
            res.6@.timestamp() == res.1@,
            res.6@.index() == res.2@,
            res.6@.view() == final(tv)@,
            (res.4@ is Some) == (res.0.addr() != 0),
            (res.5@ is Some) == (res.0.addr() != 0),
            match (res.4@, res.5@) {
                (None, None) => {
                    &&& res.0.addr() == 0
                    &&& res.3@.reader_fragment() == guard.reader_fragment()
                },
                (Some(child), Some(lease)) => {
                    &&& equal(child.ptr(), res.0)
                    &&& child.ptr() == self.constant().child
                    &&& child.obj() == self.constant().child_obj
                    &&& child.domain() == self.constant().domain
                    &&& child.protected_by(res.3@.paper_guard())
                    &&& res.3@.reader_fragment().fraction() == guard.reader_fragment().fraction()
                        / 2real
                    &&& lease.key() == child.obj()
                    &&& lease.active_registry() == self.constant().active_lease_registry
                    &&& lease.participant_id() == res.3@.participant_id()
                    &&& lease.reader_fraction() == res.3@.reader_fragment().fraction()
                    &&& lease.domain() == res.3@.domain()
                    &&& lease.root() == res.3@.root()
                    &&& lease.reader_context() == res.3@.reader_context()
                    &&& lease.start_view() == res.3@.start_view()
                    &&& lease.protected_addr() == child.ptr().addr()
                    &&& OwnPred::owns(child.ptr(), lease.resource())
                },
                _ => false,
            },
        no_unwind
    {
        let result;
        let ghost view_before = tv@;
        proof {
            use_type_invariant(self);
        }
        proof_decl! {
            let tracked (mut paper_guard, cpu_reader, binding) = guard.tracked_into_parts();
        }
        proof {
            assert(paper_guard == guard.paper_guard());
            assert(cpu_reader == guard.reader_fragment());
            assert(binding == guard.binding());
            assert(paper_guard.domain() == self.constant().domain);
            assert(paper_guard.seen_removed().removed == Set::<nat>::empty());
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => state => {
            let ghost permissions_before = state.permissions;
            proof {
                state.lifecycle.agree(self.tracked_child_phase.borrow());
                assert(LinkedListAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
                assert(state.lifecycle@ == self.child_phase());
                match state.lifecycle@ {
                    LinkedListChildPhase::Reclaimed { index: _, removal: _ } => assert(false),
                    _ => {},
                }
                assert(state.permissions.contains(self.constant().child_obj));
                assert(OwnPred::owns(
                    self.constant().child,
                    state.permissions.ownership(self.constant().child_obj),
                ));
                assert(state.points_to.loc() == self.native_loc());
                match previous {
                    None => {
                        assert(paper_guard.seen_at(from.obj()) == 0);
                    },
                    Some(observation) => {
                        use_type_invariant(observation);
                        observation.lemma_view_timestamp();
                        assert(vstd_extra::atomic_irc11::timestamp_in_view(
                            observation.loc(),
                            observation.view(),
                        ) == Some(observation.timestamp()));
                        assert(observation.loc() == self.native_loc());
                        state.link.lemma_observation_agrees(observation);
                        assert(state.link.index_at(observation.timestamp())
                            == observation.index());
                        assert(state.points_to.hist().contains_timestamp(
                            observation.timestamp(),
                        ));
                        vstd_extra::atomic_irc11::axiom_get_timestamp_is_location_projection(
                            &state.points_to,
                            observation.view(),
                        );
                        assert(vstd_extra::atomic_irc11::timestamp_in_view(
                            self.native_loc(),
                            observation.view(),
                        ) == Some(observation.timestamp()));
                        assert(state.points_to.get_timestamp(observation.view())
                            == Some(observation.timestamp()));
                        state.points_to.get_timestamp_monotonic(
                            view_before,
                            observation.view(),
                        );
                    },
                }
            }
            let loaded = raw_atomic.load(
                Ordering::Acquire,
                Tracked(tv),
                Tracked(&state.points_to),
            );
            let ghost timestamp = loaded.2@.timestamp;
            let ghost index = state.link.index_at(timestamp);
            proof {
                assert(state.points_to.hist().contains_timestamp(timestamp));
                match previous {
                    None => {
                        assert(paper_guard.seen_at(from.obj()) == 0);
                    },
                    Some(observation) => {
                        assert(state.points_to.get_timestamp(view_before).is_some());
                        assert(observation.timestamp()
                            <= state.points_to.get_timestamp(view_before).unwrap());
                        assert(state.points_to.get_timestamp(view_before).unwrap() <= timestamp);
                        assert(observation.timestamp() <= timestamp);
                        assert(state.link.index_at(observation.timestamp())
                            == observation.index());
                        assert(observation.index() <= index);
                        assert(paper_guard.seen_at(from.obj()) == observation.index());
                    },
                }
                assert(paper_guard.seen_at(from.obj()) <= index);
                assert(paper_guard.domain() == state.auth.domain());
                assert(state.auth.state().successors.contains_key(self.constant().source_obj));
                assert(rcu_spec::LinkedListTraversalSpec::seen_removed_sound(
                    paper_guard.seen_removed(),
                    state.auth.state(),
                )) by {
                    assert forall|obj: nat| #[trigger]
                        paper_guard.seen_removed().removed.contains(obj) implies {
                            &&& state.auth.state().incoming_all.contains_key(obj)
                            &&& forall|edge: rcu_spec::LinkEdge| #[trigger]
                                state.auth.state().incoming_all[obj].contains(edge)
                                    ==> paper_guard.seen_removed().dead_edge(edge)
                        } by {};
                };
            }
            proof_decl! {
                let tracked protected = state.link.tracked_load_and_protect(
                    state.points_to.hist(),
                    &state.auth,
                    &mut paper_guard,
                    from,
                    timestamp,
                );
                let tracked cpu_guard = rcu_cpu_spec::CpuRcuReadGuardToken::tracked_new(
                    paper_guard,
                    cpu_reader,
                    binding,
                );
                let tracked final_guard;
                let tracked lease;
                let tracked observation;
            }
            proof {
                vstd_extra::atomic_irc11::axiom_get_timestamp_is_location_projection(
                    &state.points_to,
                    tv@,
                );
                assert(vstd_extra::atomic_irc11::timestamp_in_view(
                    self.native_loc(),
                    tv@,
                ) == Some(timestamp));
                observation = state.link.tracked_observation_at(
                    state.points_to.hist(),
                    &state.auth,
                    timestamp,
                    self.native_loc(),
                    tv@,
                );
                assert(equal(state.points_to.hist().value(timestamp), loaded.0));
                match &protected {
                    None => {
                        assert(loaded.0.addr() == 0);
                        final_guard = cpu_guard;
                        lease = None;
                    },
                    Some(child) => {
                        assert(state.auth.state().successors[
                            self.constant().source_obj
                        ][index as int] is Some);
                        assert(state.auth.state().successors[
                            self.constant().source_obj
                        ][index as int] == Some((
                            self.constant().child,
                            self.constant().child_obj,
                        )));
                        assert(child.ptr() == self.constant().child);
                        assert(child.obj() == self.constant().child_obj);
                        assert(state.permissions.contains(child.obj()));
                        let ghost child_ownership = state.permissions.ownership(child.obj());
                        assert(OwnPred::owns(child.ptr(), child_ownership));
                        let tracked split = state.permissions.tracked_split_protected(
                            cpu_guard,
                            child,
                        );
                        final_guard = split.0;
                        lease = Some(split.1);
                        assert(split.1.resource() == child_ownership);
                        assert(OwnPred::owns(child.ptr(), split.1.resource()));
                        assert(state.permissions.ownership(child.obj()) == child_ownership);
                        assert(OwnPred::owns(
                            self.constant().child,
                            state.permissions.ownership(self.constant().child_obj),
                        ));
                    },
                }
                assert(state.permissions.wf());
                assert(state.permissions.scheduler() == permissions_before.scheduler());
                assert(state.permissions.domain() == permissions_before.domain());
                assert(state.permissions.root() == permissions_before.root());
                assert(state.permissions.retire_observation_registry()
                    == permissions_before.retire_observation_registry());
                assert(state.permissions.reclaim_registry()
                    == permissions_before.reclaim_registry());
                assert(state.permissions.active_lease_registry()
                    == permissions_before.active_lease_registry());
                assert(state.permissions.allocations() == permissions_before.allocations());
                assert(state.permissions.keys() == permissions_before.keys());
                assert(state.permissions.reclaim_states()
                    == permissions_before.reclaim_states());
                assert(state.permissions.unretired_claims()
                    == permissions_before.unretired_claims());
                state.permissions.lemma_contains_iff_key(self.constant().child_obj);
                assert(state.permissions.contains(self.constant().child_obj));
                assert(state.permissions.reclaim_states()[self.constant().child_obj]
                    == Some(self.constant().child));
                match state.lifecycle@ {
                    LinkedListChildPhase::Unpublished
                    | LinkedListChildPhase::Linked { index: _, timestamp: _ }
                    | LinkedListChildPhase::Unlinked { index: _, removal: _ } => {
                        assert(state.permissions.has_unretired_claim(self.constant().child_obj));
                    },
                    LinkedListChildPhase::Retired { index: _, removal: _ } => {
                        assert(!state.permissions.has_unretired_claim(self.constant().child_obj));
                    },
                    LinkedListChildPhase::Reclaimed { index: _, removal: _ } => assert(false),
                }
                assert(OwnPred::owns(
                    self.constant().child,
                    permissions_before.ownership(self.constant().child_obj),
                ));
                assert(state.permissions.ownership(self.constant().child_obj)
                    == permissions_before.ownership(self.constant().child_obj));
                assert(OwnPred::owns(
                    self.constant().child,
                    state.permissions.ownership(self.constant().child_obj),
                ));
                assert(LinkedListAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
            result = (
                loaded.0,
                Ghost(timestamp),
                Ghost(index),
                Tracked(final_guard),
                Tracked(protected),
                Tracked(lease),
                Tracked(observation),
            );
        });
        result
    }

    /// Returns a child traversal lease and rejoins its saved CPU reader
    /// fraction with the live guard.
    #[verifier::atomic]
    pub fn return_child_lease_cpu(
        &self,
        Tracked(lease): Tracked<Option<rcu_cpu_spec::RcuRootReadLease<O>>>,
        Tracked(guard): Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<rcu_spec::LinkedListNode>>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<rcu_spec::LinkedListNode>>)
        requires
            self.well_formed(),
            !self.child_phase().is_reclaimed(),
            match lease {
                None => true,
                Some(lease) => {
                    &&& lease.active_registry() == self.constant().active_lease_registry
                    &&& lease.participant_id() == guard.participant_id()
                    &&& lease.reader_fraction() == guard.reader_fragment().fraction()
                    &&& lease.domain() == guard.domain()
                    &&& lease.root() == guard.root()
                    &&& lease.reader_context() == guard.reader_context()
                    &&& lease.start_view() == guard.start_view()
                    &&& guard.protects(lease.protected_addr(), lease.key())
                },
            },
            guard.wf(),
            guard.scheduler() == self.constant().scheduler,
            guard.domain() == self.constant().domain,
            guard.root() == self.constant().root,
            guard.retire_observation_registry() == self.constant().retire_observation_registry,
        ensures
            old(tv)@.spec_le(final(tv)@),
            res@.wf(),
            res@.paper_guard() == guard.paper_guard(),
            res@.binding() == guard.binding(),
            res@.participant_id() == guard.participant_id(),
            res@.cpu() == guard.cpu(),
            res@.generation() == guard.generation(),
            res@.participant_view() == guard.participant_view(),
            res@.known_retired() == guard.known_retired(),
            res@.domain() == guard.domain(),
            res@.root() == guard.root(),
            res@.reader_registry() == guard.reader_registry(),
            res@.retire_observation_registry() == guard.retire_observation_registry(),
            res@.reader_context() == guard.reader_context(),
            res@.start_view() == guard.start_view(),
            res@.expired() == guard.expired(),
            res@.seen_removed() == guard.seen_removed(),
            res@.protected() == guard.protected(),
            res@.reader_fragment().fraction() == match lease {
                None => guard.reader_fragment().fraction(),
                Some(_) => guard.reader_fragment().fraction() * 2real,
            },
        no_unwind
    {
        let raw_atomic = &self.atomic;
        proof_decl! {
            let tracked final_guard;
        }
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => state => {
            let ghost permissions_before = state.permissions;
            let _loaded = raw_atomic.load(
                Ordering::Relaxed,
                Tracked(tv),
                Tracked(&state.points_to),
            );
            proof {
                state.lifecycle.agree(self.tracked_child_phase.borrow());
                assert(LinkedListAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
                assert(state.lifecycle@ == self.child_phase());
                match state.lifecycle@ {
                    LinkedListChildPhase::Reclaimed { index: _, removal: _ } => assert(false),
                    _ => {},
                }
                match lease {
                    None => {
                        final_guard = guard;
                    },
                    Some(lease) => {
                        final_guard = state.permissions.tracked_return_loaded(lease, guard);
                    },
                }
                assert(state.permissions.wf());
                assert(state.permissions.scheduler() == permissions_before.scheduler());
                assert(state.permissions.domain() == permissions_before.domain());
                assert(state.permissions.root() == permissions_before.root());
                assert(state.permissions.retire_observation_registry()
                    == permissions_before.retire_observation_registry());
                assert(state.permissions.reclaim_registry()
                    == permissions_before.reclaim_registry());
                assert(state.permissions.active_lease_registry()
                    == permissions_before.active_lease_registry());
                assert(state.permissions.allocations() == permissions_before.allocations());
                assert(state.permissions.keys() == permissions_before.keys());
                assert(state.permissions.reclaim_states()
                    == permissions_before.reclaim_states());
                assert(state.permissions.unretired_claims()
                    == permissions_before.unretired_claims());
                state.permissions.lemma_contains_iff_key(self.constant().child_obj);
                assert(state.permissions.contains(self.constant().child_obj));
                assert(state.permissions.reclaim_states()[self.constant().child_obj]
                    == Some(self.constant().child));
                match state.lifecycle@ {
                    LinkedListChildPhase::Unpublished
                    | LinkedListChildPhase::Linked { index: _, timestamp: _ }
                    | LinkedListChildPhase::Unlinked { index: _, removal: _ } => {
                        assert(state.permissions.has_unretired_claim(self.constant().child_obj));
                    },
                    LinkedListChildPhase::Retired { index: _, removal: _ } => {
                        assert(!state.permissions.has_unretired_claim(self.constant().child_obj));
                    },
                    LinkedListChildPhase::Reclaimed { index: _, removal: _ } => assert(false),
                }
                assert(OwnPred::owns(
                    self.constant().child,
                    permissions_before.ownership(self.constant().child_obj),
                ));
                assert(state.permissions.ownership(self.constant().child_obj)
                    == permissions_before.ownership(self.constant().child_obj));
                assert(OwnPred::owns(
                    self.constant().child,
                    state.permissions.ownership(self.constant().child_obj),
                ));
                assert(LinkedListAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
        });
        Tracked(final_guard)
    }

    /// Publishes the pre-registered child with a native AcqRel/Acquire CAS.
    /// The successful branch appends the matching traversal event before the
    /// atomic invariant is closed.
    #[inline(always)]
    pub fn compare_exchange_publish_child(&mut self, Tracked(tv): Tracked<&mut ViewSeen>) -> (res: (
        Result<*mut rcu_spec::LinkedListNode, *mut rcu_spec::LinkedListNode>,
        Ghost<Option<rcu_spec::LinkIndex>>,
    ))
        requires
            old(self).well_formed(),
            old(self).child_phase().is_unpublished(),
        ensures
            old(tv)@.spec_le(final(tv)@),
            final(self).well_formed(),
            final(self).constant() == old(self).constant(),
            final(self).native_loc() == old(self).native_loc(),
            (res.0 is Ok) == (res.1@ is Some),
            res.0 is Ok ==> res.0->Ok_0.addr() == 0,
            res.0 is Ok ==> final(self).child_phase() is Linked,
            res.0 is Ok ==> final(self).child_phase()->Linked_index == res.1@->Some_0,
            res.0 is Err ==> final(self).child_phase() is Unpublished,
        no_unwind
    {
        let result;
        proof {
            use_type_invariant(&*self);
        }
        let raw_atomic = &self.atomic;
        let child = self.child;
        let null = core::ptr::null_mut();
        proof_decl! {
            let ghost key = self.constant();
            let ghost native_loc = self.native_loc();
            let tracked atomic_inv = self.tracked_atomic_inv.get();
            let tracked release_view = ReleaseViewSeen::new();
        }
        vstd::invariant::open_atomic_invariant!(atomic_inv => state => {
            proof {
                state.lifecycle.agree(self.tracked_child_phase.borrow());
                assert(LinkedListAtomicInv::<OwnPred>::inv(
                    (key, native_loc),
                    state,
                ));
                assert(state.lifecycle@ is Unpublished);
                assert(state.points_to.loc() == native_loc);
            }
            let ghost prev = state.points_to.hist();
            let ghost old_successors = state.auth.state().successors[key.source_obj];
            let cas = raw_atomic.compare_exchange(
                null,
                child,
                Ordering::AcqRel,
                Ordering::Acquire,
                Tracked(tv),
                Tracked(release_view),
                Tracked(&mut state.points_to),
            );
            let ghost update = cas.2@;
            let ghost next = state.points_to.hist();
            proof_decl! {
                let ghost published_index: Option<rcu_spec::LinkIndex>;
            }
            proof {
                match cas.0 {
                    Result::Ok(_) => {
                        assert(next == prev.insert(
                            update.load_timestamp + 1,
                            child,
                            update.store_message_view,
                        ));
                        let index = state.link.tracked_cas_publish(
                            &mut state.auth,
                            prev,
                            next,
                            update.load_timestamp,
                            update.load_timestamp + 1,
                            child,
                            key.child_obj,
                            update.store_message_view,
                        );
                        published_index = Some(index);
                        state.lifecycle.update(
                            self.tracked_child_phase.borrow_mut(),
                            LinkedListChildPhase::Linked {
                                index,
                                timestamp: update.load_timestamp + 1,
                            },
                        );
                        assert(state.auth.state().incoming_all[key.child_obj].contains((
                            key.source_obj,
                            index,
                        )));
                        assert(state.auth.state().incoming_all[key.child_obj].len() > 0);
                        assert(state.auth.removed() == Set::<nat>::empty());
                        assert forall|n: rcu_spec::LinkIndex|
                            n < state.auth.state().successors[key.source_obj].len()
                                && state.auth.state().successors[key.source_obj][n as int] is Some implies
                                #[trigger] state.auth.state().successors[key.source_obj][n as int] == Some((
                                    key.child,
                                    key.child_obj,
                                )) by {
                            if n == index {
                            } else {
                                assert(n < old_successors.len());
                                assert(state.auth.state().successors[key.source_obj][n as int] == old_successors[n as int]);
                            }
                        };
                    },
                    Result::Err(_) => {
                        published_index = None;
                    },
                }
                assert(LinkedListAtomicInv::<OwnPred>::inv(
                    (key, native_loc),
                    state,
                ));
            }
            result = (cas.0, Ghost(published_index));
        });
        result
    }

    /// Unlinks the pre-registered child with a native AcqRel/Acquire CAS.
    /// A successful address comparison is resolved through the invariant to
    /// the child's persistent object identity before the null traversal event
    /// is appended.
    #[inline(always)]
    pub fn compare_exchange_unlink_child(&mut self, Tracked(tv): Tracked<&mut ViewSeen>) -> (res: (
        Result<*mut rcu_spec::LinkedListNode, *mut rcu_spec::LinkedListNode>,
        Ghost<Option<rcu_spec::LinkIndex>>,
    ))
        requires
            old(self).well_formed(),
            old(self).child_phase().is_linked(),
        ensures
            old(tv)@.spec_le(final(tv)@),
            final(self).well_formed(),
            final(self).constant() == old(self).constant(),
            final(self).native_loc() == old(self).native_loc(),
            (res.0 is Ok) == (res.1@ is Some),
            res.0 is Ok ==> res.0->Ok_0.addr() == final(self).child_ptr().addr(),
            res.0 is Ok ==> final(self).child_phase() is Unlinked,
            res.0 is Ok ==> final(self).child_phase()->Unlinked_index == res.1@->Some_0,
            res.0 is Ok ==> final(self).child_phase()->Unlinked_removal.root
                == final(self).constant().root,
            res.0 is Ok ==> final(self).child_phase()->Unlinked_removal.observed_by(final(tv)@),
            res.0 is Err ==> final(self).child_phase() is Linked,
        no_unwind
    {
        let result;
        proof {
            use_type_invariant(&*self);
        }
        let raw_atomic = &self.atomic;
        let child = self.child;
        let null = core::ptr::null_mut();
        proof_decl! {
            let ghost key = self.constant();
            let ghost native_loc = self.native_loc();
            let tracked atomic_inv = self.tracked_atomic_inv.get();
            let tracked release_view = ReleaseViewSeen::new();
        }
        vstd::invariant::open_atomic_invariant!(atomic_inv => state => {
            proof {
                state.lifecycle.agree(self.tracked_child_phase.borrow());
                assert(LinkedListAtomicInv::<OwnPred>::inv(
                    (key, native_loc),
                    state,
                ));
                assert(state.lifecycle@ is Linked);
                assert(state.points_to.loc() == native_loc);
            }
            let ghost prev = state.points_to.hist();
            let ghost old_successors = state.auth.state().successors[key.source_obj];
            let cas = raw_atomic.compare_exchange(
                child,
                null,
                Ordering::AcqRel,
                Ordering::Acquire,
                Tracked(tv),
                Tracked(release_view),
                Tracked(&mut state.points_to),
            );
            let ghost update = cas.2@;
            let ghost next = state.points_to.hist();
            proof_decl! {
                let ghost unlinked_index: Option<rcu_spec::LinkIndex>;
            }
            proof {
                match cas.0 {
                    Result::Ok(value) => {
                        let ghost current_timestamp = state.link.current_timestamp();
                        let ghost current_index = state.link.index_at(current_timestamp);
                        assert(prev.is_max_timestamp(update.load_timestamp));
                        assert(prev.contains_timestamp(current_timestamp));
                        assert(prev.contains_timestamp(update.load_timestamp));
                        assert(update.load_timestamp <= current_timestamp);
                        assert(current_timestamp <= update.load_timestamp);
                        assert(current_timestamp == update.load_timestamp);
                        assert(state.lifecycle@->Linked_timestamp == current_timestamp);
                        assert(state.lifecycle@->Linked_index == current_index);
                        assert(equal(prev.value(update.load_timestamp), value));
                        assert(value.addr() == child.addr());
                        assert(prev.value(current_timestamp).addr() == child.addr());
                        assert(current_index + 1 == old_successors.len());
                        assert(old_successors[current_index as int] is Some) by {
                            if old_successors[current_index as int] is None {
                                assert(prev.value(current_timestamp).addr() == 0);
                                assert(false);
                            }
                        };
                        assert(old_successors[current_index as int] == Some((
                            key.child,
                            key.child_obj,
                        )));
                        assert(old_successors.last() == Some((
                            key.child,
                            key.child_obj,
                        )));
                        assert(state.auth.state().objects.contains_pair(
                            key.source_obj,
                            key.source,
                        ));
                        assert(state.auth.state().objects.contains_pair(
                            key.child_obj,
                            key.child,
                        ));
                        assert(state.auth.state().incoming_all.contains_key(key.child_obj));
                        assert(current_index < old_successors.len());
                        assert(state.auth.state().successors[key.source_obj][current_index as int]
                            == Some((key.child, key.child_obj)));
                        assert(state.auth.state().incoming_all[key.child_obj].len() > 0);
                        assert(next == prev.insert(
                            update.load_timestamp + 1,
                            null,
                            update.store_message_view,
                        ));
                        let index = state.link.tracked_cas_unlink(
                            &mut state.auth,
                            prev,
                            next,
                            update.load_timestamp,
                            update.load_timestamp + 1,
                            key.child,
                            key.child_obj,
                            update.store_message_view,
                        );
                        unlinked_index = Some(index);
                        let ghost removal = rcu_spec::RcuRemovalObservation {
                            root: key.root,
                            timestamp: update.load_timestamp + 1,
                            message_view: update.store_message_view,
                        };
                        state.lifecycle.update(
                            self.tracked_child_phase.borrow_mut(),
                            LinkedListChildPhase::Unlinked { index, removal },
                        );
                        assert(state.auth.removed() == Set::<nat>::empty());
                        assert forall|n: rcu_spec::LinkIndex|
                            n < state.auth.state().successors[key.source_obj].len()
                                && state.auth.state().successors[key.source_obj][n as int] is Some implies
                                #[trigger] state.auth.state().successors[key.source_obj][n as int] == Some((
                                    key.child,
                                    key.child_obj,
                                )) by {
                            assert(n < old_successors.len());
                            assert(state.auth.state().successors[key.source_obj][n as int] == old_successors[n as int]);
                        };
                        assert(state.lifecycle@ is Unlinked);
                        assert(state.link.current_timestamp() == removal.timestamp);
                        assert(state.link.index_at(removal.timestamp) == index);
                        assert(state.points_to.hist().thread_view(removal.timestamp)
                            == removal.message_view);
                        assert(index + 1
                            == state.auth.state().successors[key.source_obj].len());
                        assert(state.auth.state().successors[key.source_obj].last() is None);
                        assert(state.auth.state().incoming_all[key.child_obj].len() > 0);
                    },
                    Result::Err(_) => {
                        unlinked_index = None;
                    },
                }
                assert(LinkedListAtomicInv::<OwnPred>::inv(
                    (key, native_loc),
                    state,
                ));
            }
            result = (cas.0, Ghost(unlinked_index));
        });
        result
    }

    /// Converts a successfully unlinked child into the writer resources
    /// required by base RCU and by eventual physical reclamation.
    ///
    /// The traversal observation records the unlink event itself. Since the
    /// only historical incoming edge is the immediately preceding publish,
    /// this proves that every incoming edge is dead and consumes the child's
    /// unique traversal retire permission.
    #[verifier::atomic]
    pub fn retire_unlinked_child(&mut self, Tracked(tv): Tracked<&mut ViewSeen>) -> (res: Tracked<
        LinkedListDetachedChild,
    >)
        requires
            old(self).well_formed(),
            old(self).child_phase().is_unlinked(),
        ensures
            old(tv)@.spec_le(final(tv)@),
            final(self).well_formed(),
            final(self).constant() == old(self).constant(),
            final(self).native_loc() == old(self).native_loc(),
            final(self).child_phase() is Retired,
            final(self).child_phase()->Retired_index == old(self).child_phase()->Unlinked_index,
            final(self).child_phase()->Retired_removal == old(self).child_phase()->Unlinked_removal,
            final(self).child_phase()->Retired_removal.root == final(self).constant().root,
            res@.object().wf(),
            res@.object().domain() == final(self).constant().domain,
            res@.object().obj() == final(self).constant().child_obj,
            res@.object().ptr() == final(self).constant().child,
            res@.retire().wf(),
            res@.retire().ready_to_retire(),
            res@.retire().domain() == final(self).constant().domain,
            res@.retire().obj() == final(self).constant().child_obj,
            res@.retire().ptr() == final(self).constant().child,
            res@.claim().registry() == final(self).constant().reclaim_registry,
            res@.claim().obj() == final(self).constant().child_obj,
            res@.claim().is_pending(),
            res@.claim().ptr() == final(self).constant().child,
            res@.removal() == final(self).child_phase()->Retired_removal,
            res@.removal().root == final(self).constant().root,
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }
        let raw_atomic = &self.atomic;
        proof_decl! {
            let ghost key = self.constant();
            let ghost native_loc = self.native_loc();
            let tracked atomic_inv = self.tracked_atomic_inv.get();
            let tracked detached;
        }
        vstd::invariant::open_atomic_invariant!(atomic_inv => state => {
            let _loaded = raw_atomic.load(
                Ordering::Relaxed,
                Tracked(tv),
                Tracked(&state.points_to),
            );
            proof {
                state.lifecycle.agree(self.tracked_child_phase.borrow());
                assert(LinkedListAtomicInv::<OwnPred>::inv((key, native_loc), state));
                assert(state.lifecycle@ is Unlinked);
                let ghost index = state.lifecycle@->Unlinked_index;
                let ghost removal = state.lifecycle@->Unlinked_removal;
                let ghost prior = rcu_spec::RcuSeenRemoved {
                    removed: Set::empty(),
                    link_view: rcu_spec::RcuLinkView::empty().observe(key.source_obj, index),
                };
                assert(state.auth.state().bounds(prior.link_view)) by {
                    assert forall|from: *mut rcu_spec::LinkedListNode, from_obj: nat| #[trigger]
                        state.auth.state().objects.contains_pair(from_obj, from)
                            && prior.link_view.seen.contains_key(from_obj) implies {
                        &&& state.auth.state().successors[from_obj].len() > 0
                        &&& prior.link_view.seen_at(from_obj)
                            < state.auth.state().successors[from_obj].len()
                    } by {
                        assert(from_obj == key.source_obj);
                        assert(from == key.source);
                        assert(prior.link_view.seen_at(from_obj) == index);
                        assert(index + 1 == state.auth.state().successors[from_obj].len());
                    };
                }
                assert(rcu_spec::LinkedListTraversalSpec::seen_removed_sound(
                    prior,
                    state.auth.state(),
                ));
                assert forall|edge: rcu_spec::LinkEdge| #[trigger]
                    state.auth.state().incoming_all[key.child_obj].contains(edge) implies
                        prior.dead_edge(edge) by {
                    assert(edge == (key.source_obj, (index - 1) as nat));
                    assert(prior.seen_at(key.source_obj) == index);
                };
                state.auth.lemma_has_info_for_object(key.child_obj);
                assert(state.auth.has_info(key.child_obj));
                assert(state.permissions.contains(key.child_obj));
                let ghost auth_before = state.auth;
                let ghost permissions_before = state.permissions;
                let ghost child_ownership = state.permissions.ownership(key.child_obj);
                let tracked object = state.auth.tracked_info_for(key.child_obj);
                let tracked retire = state.auth.tracked_retire_node(key.child_obj, prior);
                assert(auth_before.state().objects.contains_pair(key.child_obj, retire.ptr()));
                assert(retire.ptr() == key.child);
                let tracked claim = state.permissions.tracked_retire(key.child_obj);
                assert(claim.ptr() == key.child);
                state.lifecycle.update(
                    self.tracked_child_phase.borrow_mut(),
                    LinkedListChildPhase::Retired { index, removal },
                );
                assert(state.auth.removed() == Set::<nat>::empty().insert(key.child_obj));
                assert(!state.auth.has_retire_perm(key.child_obj));
                assert(state.permissions.keys() == Set::empty().insert(key.child_obj));
                state.permissions.lemma_contains_iff_key(key.child_obj);
                assert(state.permissions.contains(key.child_obj));
                assert(state.permissions.allocations().contains(key.child_obj));
                assert(state.permissions.reclaim_states()[key.child_obj] == Some(key.child));
                assert(!state.permissions.has_unretired_claim(key.child_obj));
                assert(state.permissions.ownership(key.child_obj) == child_ownership);
                assert(OwnPred::owns(
                    key.child,
                    state.permissions.ownership(key.child_obj),
                ));
                assert(LinkedListAtomicInv::<OwnPred>::inv((key, native_loc), state));
                assert(object.ptr() == key.child);
                assert(retire.ptr() == key.child);
                assert(claim.ptr() == key.child);
                detached = LinkedListDetachedChild { object, retire, claim, removal };
            }
        });
        Tracked(detached)
    }

    /// Reclaims the retired child's physical ownership after the existing RCU
    /// monitor has produced a completed grace-period witness.
    #[verifier::atomic]
    pub fn reclaim_retired_child(
        &mut self,
        Tracked(claim): Tracked<rcu_cpu_spec::RcuReclaimClaim<rcu_spec::LinkedListNode>>,
        Tracked(completed): Tracked<rcu_cpu_spec::RcuReclaimedWitness>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: Tracked<O>)
        requires
            old(self).well_formed(),
            old(self).child_phase().is_retired(),
            claim.registry() == old(self).constant().reclaim_registry,
            claim.obj() == old(self).constant().child_obj,
            claim.is_pending(),
            claim.ptr() == old(self).constant().child,
            completed.wf(),
            completed.scheduler() == old(self).constant().scheduler,
            completed.record().domain == old(self).constant().domain,
            completed.record().obj == old(self).constant().child_obj,
            completed.record().retire_observation_registry == old(
                self,
            ).constant().retire_observation_registry,
            completed.record().removal == old(self).child_phase()->Retired_removal,
        ensures
            old(tv)@.spec_le(final(tv)@),
            final(self).well_formed(),
            final(self).constant() == old(self).constant(),
            final(self).native_loc() == old(self).native_loc(),
            final(self).child_phase() is Reclaimed,
            final(self).child_phase()->Reclaimed_index == old(self).child_phase()->Retired_index,
            final(self).child_phase()->Reclaimed_removal == old(
                self,
            ).child_phase()->Retired_removal,
            OwnPred::owns(final(self).constant().child, res@),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }
        let raw_atomic = &self.atomic;
        proof_decl! {
            let ghost key = self.constant();
            let ghost native_loc = self.native_loc();
            let tracked atomic_inv = self.tracked_atomic_inv.get();
            let tracked ownership;
        }
        vstd::invariant::open_atomic_invariant!(atomic_inv => state => {
            let _loaded = raw_atomic.load(
                Ordering::Relaxed,
                Tracked(tv),
                Tracked(&state.points_to),
            );
            proof {
                state.lifecycle.agree(self.tracked_child_phase.borrow());
                assert(LinkedListAtomicInv::<OwnPred>::inv((key, native_loc), state));
                assert(state.lifecycle@ is Retired);
                let ghost index = state.lifecycle@->Retired_index;
                let ghost removal = state.lifecycle@->Retired_removal;
                assert(completed.record().removal == removal);
                assert(completed.record().removal.root == key.root);
                state.permissions.lemma_completed_excludes_active(
                    &completed,
                    key.child_obj,
                );
                assert(!state.permissions.has_active(key.child_obj));
                ownership = state.permissions.tracked_reclaim(claim, completed);
                state.lifecycle.update(
                    self.tracked_child_phase.borrow_mut(),
                    LinkedListChildPhase::Reclaimed { index, removal },
                );
                assert(state.permissions.keys() == Set::<nat>::empty());
                state.permissions.lemma_contains_iff_key(key.child_obj);
                assert(!state.permissions.contains(key.child_obj));
                assert(state.permissions.allocations().contains(key.child_obj));
                assert(state.permissions.reclaim_states()[key.child_obj] is None);
                assert(!state.permissions.has_unretired_claim(key.child_obj));
                assert(state.permissions.reclaimed().contains_key(key.child_obj));
                assert(state.permissions.reclaimed()[key.child_obj].record().removal == removal);
                assert(LinkedListAtomicInv::<OwnPred>::inv((key, native_loc), state));
                assert(OwnPred::owns(key.child, ownership));
            }
        });
        Tracked(ownership)
    }

    /// Proof-mode form used by a type-erased callback after its executable
    /// monitor has supplied an open-invariant credit and a completed grace
    /// period.  No additional atomic access is needed at runtime: the callback
    /// owns this link and only consumes proof resources before deallocating the
    /// recovered smart pointer.
    pub proof fn tracked_reclaim_retired_child(
        tracked &mut self,
        tracked claim: rcu_cpu_spec::RcuReclaimClaim<rcu_spec::LinkedListNode>,
        tracked completed: rcu_cpu_spec::RcuReclaimedWitness,
        tracked credit: vstd::invariant::OpenInvariantCredit,
    ) -> (tracked ownership: O)
        requires
            old(self).well_formed(),
            old(self).child_phase().is_retired(),
            claim.registry() == old(self).constant().reclaim_registry,
            claim.obj() == old(self).constant().child_obj,
            claim.is_pending(),
            claim.ptr() == old(self).constant().child,
            completed.wf(),
            completed.scheduler() == old(self).constant().scheduler,
            completed.record().domain == old(self).constant().domain,
            completed.record().obj == old(self).constant().child_obj,
            completed.record().retire_observation_registry == old(
                self,
            ).constant().retire_observation_registry,
            completed.record().removal == old(self).child_phase()->Retired_removal,
        ensures
            final(self).well_formed(),
            final(self).constant() == old(self).constant(),
            final(self).native_loc() == old(self).native_loc(),
            final(self).child_phase() is Reclaimed,
            final(self).child_phase()->Reclaimed_index == old(self).child_phase()->Retired_index,
            final(self).child_phase()->Reclaimed_removal == old(
                self,
            ).child_phase()->Retired_removal,
            OwnPred::owns(final(self).constant().child, ownership),
        opens_invariants [ self.invariant_namespace() ]
    {
        use_type_invariant(&*self);
        let ghost key = self.constant();
        let ghost native_loc = self.native_loc();
        let tracked atomic_inv = self.tracked_atomic_inv.get();
        let tracked mut recovered;
        vstd::invariant::open_atomic_invariant_in_proof!(credit => atomic_inv => state => {
            state.lifecycle.agree(self.tracked_child_phase.borrow());
            assert(LinkedListAtomicInv::<OwnPred>::inv((key, native_loc), state));
            assert(state.lifecycle@ is Retired);
            let ghost index = state.lifecycle@->Retired_index;
            let ghost removal = state.lifecycle@->Retired_removal;
            assert(completed.record().removal == removal);
            assert(completed.record().removal.root == key.root);
            state.permissions.lemma_completed_excludes_active(
                &completed,
                key.child_obj,
            );
            assert(!state.permissions.has_active(key.child_obj));
            recovered = state.permissions.tracked_reclaim(claim, completed);
            state.lifecycle.update(
                self.tracked_child_phase.borrow_mut(),
                LinkedListChildPhase::Reclaimed { index, removal },
            );
            assert(state.permissions.keys() == Set::<nat>::empty());
            state.permissions.lemma_contains_iff_key(key.child_obj);
            assert(!state.permissions.contains(key.child_obj));
            assert(state.permissions.allocations().contains(key.child_obj));
            state.permissions.lemma_allocation_has_reclaim_state(key.child_obj);
            assert(state.permissions.reclaim_states()[key.child_obj] is None);
            assert(!state.permissions.has_unretired_claim(key.child_obj));
            assert(state.permissions.reclaimed().contains_key(key.child_obj));
            assert(state.permissions.reclaimed()[key.child_obj].record().removal == removal);
            assert(LinkedListAtomicInv::<OwnPred>::inv((key, native_loc), state));
            assert(OwnPred::owns(key.child, recovered));
        });
        recovered
    }
}

/// OSTD's RCU-specific specialization of the generic weak pointer atomic.
///
/// This is an RCU client of Verus' native IRC11 protocol. The only local TCB
/// component is `PAtomicWeakPtr`, needed because upstream does not yet expose
/// a native weak-memory `AtomicPtr`.
#[verifier::reject_recursive_types(T)]
pub struct RcuWeakAtomicPtr<T: 'static, O: Objective + 'static, OwnPred: 'static> {
    atomic: PAtomicWeakPtr<T>,
    tracked_atomic_inv: Tracked<&'static RcuRootAtomicInvariant<T, O, OwnPred>>,
}

impl<T: 'static, O: Objective + 'static, OwnPred: 'static> RcuWeakAtomicPtr<T, O, OwnPred> {
    pub closed spec fn constant(&self) -> rcu_spec::RcuRootKey {
        self.tracked_atomic_inv@.constant().0
    }

    pub closed spec fn id(&self) -> Loc {
        self.constant().domain
    }

    pub closed spec fn native_loc(&self) -> Irc11AtomicId {
        self.atomic.loc()
    }

    pub closed spec fn well_formed(&self) -> bool {
        self.tracked_atomic_inv@.constant().1 == self.native_loc()
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(&self) -> bool {
        self.well_formed()
    }
}

impl<T: 'static, O: Objective + 'static, OwnPred: 'static> RcuWeakAtomicPtr<T, O, OwnPred> where
    OwnPred: rcu_spec::RcuRootOwnershipPredicate<T, O>,
 {
    pub const fn new(
        Ghost(nullable): Ghost<bool>,
        Ghost(scheduler): Ghost<Loc>,
        init: *mut T,
        Tracked(ownership): Tracked<Option<O>>,
    ) -> (res: Self)
        requires
            nullable || !init.is_null(),
            (ownership is Some) == !init.is_null(),
            ownership is Some ==> OwnPred::owns(init, ownership->Some_0),
        ensures
            res.well_formed(),
            res.constant().nullable == nullable,
            res.constant().scheduler == scheduler,
    {
        let (atomic, Tracked(points_to), Tracked(initial_view), Ghost(timestamp)) =
            PAtomicWeakPtr::new(init);
        proof_decl! {
            let tracked unit_ownership: Option<()>;
            let tracked physical_ownership: Option<O>;
        }
        proof {
            match ownership {
                Some(ownership) => {
                    unit_ownership = Some(());
                    physical_ownership = Some(ownership);
                },
                None => {
                    unit_ownership = None;
                    physical_ownership = None;
                },
            }
        }
        let tracked g = rcu_spec::RcuRootOwnedGhost::tracked_initial(
            init,
            unit_ownership,
            points_to.hist(),
            timestamp,
            initial_view@,
        );
        proof_decl! {
            let tracked state: RcuRootAtomicState<T, O>;
        }
        proof {
            let tracked mut permissions = rcu_cpu_spec::RcuRootPermissionState::empty(
                scheduler,
                g.domain(),
                g.domain(),
                g.retire_observation_registry(),
            );
            assert(permissions.allocations() == Set::<nat>::empty());
            if physical_ownership is Some {
                let tracked info = g.tracked_info_at(points_to.hist(), timestamp).tracked_unwrap();
                let ghost initial_obj = info.obj();
                let ghost initial_ownership = physical_ownership->Some_0;
                assert(!permissions.allocations().contains(info.obj()));
                permissions.tracked_insert(&info, physical_ownership.tracked_unwrap());
                assert(g.current_registration() is Some);
                assert(info.obj() == g.current_registration()->Some_0.0.obj());
                assert(permissions.has_unretired_claim(info.obj()));
                assert(permissions.keys() == Set::<nat>::empty().insert(initial_obj));
                assert(equal(info.ptr(), init));
                assert(OwnPred::owns(info.ptr(), initial_ownership));
                permissions.lemma_live_reclaim_state(initial_obj);
                assert forall|obj: nat| #[trigger] permissions.keys().contains(obj) implies {
                    &&& g.infos().contains_key(obj)
                    &&& permissions.reclaim_states()[obj] is Some
                    &&& permissions.reclaim_states()[obj]->Some_0 == g.infos()[obj].ptr()
                    &&& OwnPred::owns(
                        permissions.reclaim_states()[obj]->Some_0,
                        permissions.ownership(obj),
                    )
                } by {
                    assert(obj == initial_obj);
                    assert(g.infos().contains_key(initial_obj));
                    assert(equal(info.ptr(), g.infos()[initial_obj].ptr()));
                    assert(permissions.reclaim_states()[initial_obj] == Some(info.ptr()));
                    assert(permissions.ownership(initial_obj) == initial_ownership);
                };
            } else {
                assert(g.current_registration() is None);
                assert(permissions.keys() == Set::<nat>::empty());
                assert forall|obj: nat| #[trigger] permissions.keys().contains(obj) implies {
                    &&& g.infos().contains_key(obj)
                    &&& permissions.reclaim_states()[obj] is Some
                    &&& permissions.reclaim_states()[obj]->Some_0 == g.infos()[obj].ptr()
                    &&& OwnPred::owns(
                        permissions.reclaim_states()[obj]->Some_0,
                        permissions.ownership(obj),
                    )
                } by {};
            }
            assert(permissions.allocations() == g.infos().dom());
            assert(permissions.scheduler() == scheduler);
            assert(permissions.unretired_claims().dom() == match g.current_registration() {
                Some(registration) => Set::empty().insert(registration.0.obj()),
                None => Set::empty(),
            });
            assert forall|obj: nat| #[trigger]
                g.removals().contains_key(obj) implies !permissions.has_unretired_claim(obj) by {};
            assert forall|obj: nat| #[trigger] permissions.reclaimed().contains_key(obj) implies {
                &&& g.removals().contains_key(obj)
                &&& permissions.reclaimed()[obj].record().removal == g.removals()[obj]
            } by {};
            state = RcuRootAtomicState { points_to, root: g, permissions };
        }
        let ghost key = rcu_spec::RcuRootKey {
            nullable,
            scheduler,
            domain: state.root.domain(),
            reader_registry: state.root.reader_registry(),
            retire_observation_registry: state.root.retire_observation_registry(),
            reclaim_registry: state.permissions.reclaim_registry(),
            active_lease_registry: state.permissions.active_lease_registry(),
        };
        proof {
            assert(rcu_spec::rcu_history_inv(nullable, state.points_to.hist())) by {
                assert(!state.points_to.hist().dom().is_empty());
                if !nullable {
                    assert forall|ts: nat|
                        state.points_to.hist().contains_timestamp(
                            ts,
                        ) implies #[trigger] state.points_to.hist().value(ts).addr() != 0 by {
                        assert(ts == timestamp);
                        assert(equal(state.points_to.hist().value(ts), init));
                    };
                }
            };
            assert forall|obj: nat| state.root.removals().contains_key(obj) implies {
                let removal = #[trigger] state.root.removals()[obj];
                state.points_to.get_timestamp(removal.message_view) == Some(removal.timestamp)
            } by {
                assert(state.root.removals() == Map::empty());
            };
            assert(RcuRootAtomicInv::<OwnPred>::inv((key, atomic.loc()), state));
        }
        let tracked atomic_inv = AtomicInvariant::new((key, atomic.loc()), state, 0);
        let tracked atomic_inv = tracked_static_ref(atomic_inv);
        Self { atomic, tracked_atomic_inv: Tracked(atomic_inv) }
    }

    fn raw_atomic(&self) -> (res: &PAtomicWeakPtr<T>)
        requires
            self.well_formed(),
        ensures
            res.loc() == self.native_loc(),
        opens_invariants none
        no_unwind
    {
        &self.atomic
    }

    pub proof fn tracked_atomic_inv(tracked &self) -> (tracked res: &'static RcuRootAtomicInvariant<
        T,
        O,
        OwnPred,
    >)
        requires
            self.well_formed(),
        ensures
            res.constant() == (self.constant(), self.native_loc()),
    {
        self.tracked_atomic_inv.get()
    }

    /// Acquire-load helper for RCU root pointers.
    #[inline(always)]
    pub fn load_acquire_rcu(&self, Tracked(tv): Tracked<&mut ViewSeen>) -> (res: (
        *mut T,
        Ghost<Timestamp>,
        Ghost<Option<rcu_spec::RcuPublishedObject>>,
        Tracked<Option<rcu_spec::RcuBlockInfo<T>>>,
    ))
        requires
            self.well_formed(),
        ensures
            old(tv)@.spec_le(final(tv)@),
            !self.constant().nullable ==> !res.0.is_null(),
            match (res.2@, res.3@) {
                (None, None) => res.0.addr() == 0,
                (Some(object), Some(info)) => {
                    &&& res.0.addr() != 0
                    &&& object.addr == res.0.addr()
                    &&& info.wf()
                    &&& info.domain() == object.domain
                    &&& info.obj() == object.obj
                    &&& info.addr() == object.addr
                    &&& equal(info.ptr(), res.0)
                },
                _ => false,
            },
    {
        let result;
        let ghost start_view = tv@;
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => state => {
            proof {
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
            let tracked RcuRootAtomicState { points_to, root: g, permissions } = state;
            proof {
                assert(points_to.loc() == self.native_loc());
            }
            let loaded = raw_atomic.load(
                Ordering::Acquire,
                Tracked(tv),
                Tracked(&points_to),
            );
            proof {
                assert(rcu_spec::rcu_owned_root_history_inv(points_to.hist(), g));
            }
            proof_decl! {
                let ghost timestamp = loaded.2@.timestamp;
                let ghost published = g.published_at(timestamp);
                let tracked loaded_info;
            }
            proof {
                loaded_info = g.tracked_info_at(points_to.hist(), timestamp);
                match (published, &loaded_info) {
                    (Some(object), Some(info)) => {
                        assert(equal(points_to.hist().value(timestamp), loaded.0));
                        assert(equal(info.ptr(), loaded.0));
                    },
                    (None, None) => {
                        assert(loaded.0.addr() == 0);
                    },
                    _ => assert(false),
                };
                if !self.constant().nullable {
                    rcu_spec::rcu_history_inv_read_nonnull::<T>(points_to.hist(), timestamp);
                    assert(!loaded.0.is_null());
                }
            }
            result = (loaded.0, Ghost(timestamp), Ghost(published), Tracked(loaded_info));
            proof {
                state = RcuRootAtomicState { points_to, root: g, permissions };
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
        });
        result
    }

    /// Acquire-load an RCU root while starting a paper read-side guard.
    ///
    /// The ghost reader transition occurs in the same invariant opening as the
    /// real acquire load. Executably this is identical to `load_acquire_rcu`.
    #[inline(always)]
    pub fn load_acquire_rcu_guarded_with_retired(
        &self,
        Ghost(reader): Ghost<rcu_spec::RcuReaderContext>,
        Tracked(retired_facts): Tracked<&rcu_spec::RcuRetiredFacts>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: (
        *mut T,
        Ghost<Timestamp>,
        Ghost<Option<rcu_spec::RcuPublishedObject>>,
        Tracked<Option<rcu_spec::RcuBlockInfo<T>>>,
        Tracked<rcu_spec::RcuReadGuardToken<T>>,
    ))
        requires
            self.well_formed(),
            retired_facts.observed_by(old(tv)@),
        ensures
            old(tv)@.spec_le(final(tv)@),
            !self.constant().nullable ==> !res.0.is_null(),
            res.4@.wf(),
            res.4@.domain() == self.constant().domain,
            res.4@.reader_registry() == self.constant().reader_registry,
            res.4@.retire_observation_registry() == self.constant().retire_observation_registry,
            res.4@.reader() == reader,
            res.4@.root() == self.id(),
            res.4@.start_view() == old(tv)@,
            forall|record: rcu_spec::RcuRetiredRecord| #[trigger]
                retired_facts.records().contains(record) && record.domain == res.4@.domain()
                    && record.retire_observation_registry == res.4@.retire_observation_registry()
                    && record.removal.root == res.4@.root() ==> res.4@.expired().contains(
                    record.obj,
                ),
            match (res.2@, res.3@) {
                (None, None) => res.0.addr() == 0,
                (Some(object), Some(info)) => {
                    &&& res.0.addr() != 0
                    &&& object.addr == res.0.addr()
                    &&& info.wf()
                    &&& info.domain() == object.domain
                    &&& info.domain() == res.4@.domain()
                    &&& info.obj() == object.obj
                    &&& info.addr() == object.addr
                    &&& equal(info.ptr(), res.0)
                    &&& !res.4@.expired().contains(info.obj())
                    &&& !res.4@.seen_removed().removed.contains(info.obj())
                    &&& res.4@.protects(info.addr(), info.obj())
                },
                _ => false,
            },
    {
        let result;
        proof {
            use_type_invariant(self);
        }
        let ghost start_view = tv@;
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => state => {
            proof {
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
            let tracked RcuRootAtomicState { points_to, root: mut g, permissions } = state;
            let ghost root_before_reader = g;
            proof {
                assert(points_to.loc() == self.native_loc());
                assert(g.retire_observation_registry()
                    == self.constant().retire_observation_registry);
                permissions.lemma_all_live_reclaim_states();
                permissions.lemma_all_unretired_domains();
            }
            proof_decl! {
                let tracked base_guard =
                    g.tracked_start_reader(points_to.hist(), self.id(), start_view, reader);
            }
            proof {
                g.lemma_retired_facts_observed(
                    points_to.hist(),
                    &retired_facts,
                    self.id(),
                    start_view,
                );
            }
            let loaded = raw_atomic.load(
                Ordering::Acquire,
                Tracked(tv),
                Tracked(&points_to),
            );
            let ghost timestamp = loaded.2@.timestamp;
            proof {
                assert(rcu_spec::rcu_owned_root_history_inv(points_to.hist(), g));
            }
            proof_decl! {
                let tracked loaded_info;
            }
            proof {
                loaded_info = g.tracked_info_at(points_to.hist(), timestamp);
            }
            proof_decl! {
                let ghost published = g.published_at(timestamp);
            }
            proof {
                match (published, &loaded_info) {
                    (Some(object), Some(info)) => {
                        assert(equal(points_to.hist().value(timestamp), loaded.0));
                        assert(equal(info.ptr(), loaded.0));
                        assert(info.domain() == g.domain());
                        assert(info.domain() == base_guard.domain());
                    },
                    (None, None) => {
                        assert(loaded.0.addr() == 0);
                    },
                    _ => assert(false),
                };
                if !self.constant().nullable {
                    rcu_spec::rcu_history_inv_read_nonnull::<T>(points_to.hist(), timestamp);
                    assert(!loaded.0.is_null());
                }
                assert(base_guard.domain() == self.constant().domain);
                assert(base_guard.reader_registry() == self.constant().reader_registry);
                assert(base_guard.retire_observation_registry()
                    == g.retire_observation_registry());
                assert(g.retire_observation_registry()
                    == self.constant().retire_observation_registry);
                assert(base_guard.retire_observation_registry()
                    == self.constant().retire_observation_registry);
            }
            proof_decl! {
                let tracked mut guard =
                    rcu_spec::RcuReadGuardToken::tracked_from_base(base_guard);
            }
            proof {
                assert(guard.expired()
                    == g.root().domain_auth().observed_retired(self.id(), start_view));
                match &loaded_info {
                    Some(info) => {
                        if guard.expired().contains(info.obj()) {
                            assert(g.root().domain_auth().observed_retired(
                                self.id(),
                                start_view,
                            ).contains(info.obj()));
                            g.lemma_observed_retired(
                                points_to.hist(),
                                self.id(),
                                start_view,
                                info.obj(),
                            );
                            let ghost removal = g.removals()[info.obj()];
                            assert(removal.root == self.id());
                            assert(removal.observed_by(start_view));
                            assert(points_to.get_timestamp(removal.message_view)
                                == Some(removal.timestamp));
                            points_to.get_timestamp_monotonic(start_view, removal.message_view);
                            assert(points_to.get_timestamp(start_view) is Some);
                            assert(removal.timestamp
                                <= points_to.get_timestamp(start_view)->Some_0);
                            assert(points_to.get_timestamp(start_view)->Some_0 <= timestamp);
                            assert(removal.timestamp <= timestamp);
                            assert(g.removals_wf(points_to.hist()));
                            assert(g.publications()[timestamp] != Some(info.obj()));
                            assert(published == Some(rcu_spec::RcuPublishedObject {
                                domain: info.domain(),
                                obj: info.obj(),
                                addr: info.addr(),
                            }));
                            g.lemma_published_object_id(
                                points_to.hist(),
                                timestamp,
                                rcu_spec::RcuPublishedObject {
                                    domain: info.domain(),
                                    obj: info.obj(),
                                    addr: info.addr(),
                                },
                            );
                            assert(g.publications()[timestamp] == Some(info.obj()));
                            assert(false);
                        }
                        assert(guard.can_protect(*info));
                        guard.tracked_protect(info);
                    },
                    None => {},
                }
            }
            result = (
                loaded.0,
                Ghost(timestamp),
                Ghost(published),
                Tracked(loaded_info),
                Tracked(guard),
            );
            proof {
                assert(g.current_owned() == root_before_reader.current_owned());
                assert(g.domain() == root_before_reader.domain());
                assert(g.reader_registry() == root_before_reader.reader_registry());
                assert(g.retire_observation_registry()
                    == root_before_reader.retire_observation_registry());
                assert(g.publications() == root_before_reader.publications());
                assert(g.infos() == root_before_reader.infos());
                assert(g.removals() == root_before_reader.removals());
                assert(rcu_spec::rcu_current_ownership_inv::<
                    T,
                    (),
                    rcu_spec::UnitRcuRootOwnership,
                >(g));
                assert forall|obj: nat| g.removals().contains_key(obj) implies {
                    let removal = #[trigger] g.removals()[obj];
                    points_to.get_timestamp(removal.message_view) == Some(removal.timestamp)
                } by {
                    assert(root_before_reader.removals().contains_key(obj));
                };
                assert(rcu_spec::RcuOwnedWeakAtomicInv::<
                    rcu_spec::UnitRcuRootOwnership,
                >::inv(
                    (self.constant(), self.native_loc()),
                    (points_to, g),
                ));
                assert(permissions.allocations() == g.infos().dom());
                permissions.lemma_all_live_reclaim_states();
                permissions.lemma_all_unretired_domains();
                assert forall|obj: nat| #[trigger]
                    permissions.keys().contains(obj) implies {
                        &&& g.infos().contains_key(obj)
                        &&& permissions.reclaim_states()[obj] is Some
                        &&& permissions.reclaim_states()[obj]->Some_0 == g.infos()[obj].ptr()
                        &&& OwnPred::owns(
                            permissions.reclaim_states()[obj]->Some_0,
                            permissions.ownership(obj),
                        )
                    } by {};
                assert(permissions.unretired_claims().dom() == match g.current_registration() {
                    Some(registration) => Set::empty().insert(registration.0.obj()),
                    None => Set::empty(),
                });
                assert forall|obj: nat| #[trigger]
                    g.removals().contains_key(obj) implies !permissions.has_unretired_claim(obj) by {};
                assert forall|obj: nat| #[trigger]
                    permissions.reclaimed().contains_key(obj) implies {
                        &&& g.removals().contains_key(obj)
                        &&& permissions.reclaimed()[obj].record().removal == g.removals()[obj]
                    } by {};
                state = RcuRootAtomicState { points_to, root: g, permissions };
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
        });
        result
    }

    /// Acquire-load an RCU root while starting a paper read-side guard.
    ///
    /// This compatibility entry point has no CPU-generation retirement
    /// history, so it starts the guard with only the root invariant's directly
    /// observed retirements.
    #[inline(always)]
    pub fn load_acquire_rcu_guarded(
        &self,
        Ghost(reader): Ghost<rcu_spec::RcuReaderContext>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: (
        *mut T,
        Ghost<Timestamp>,
        Ghost<Option<rcu_spec::RcuPublishedObject>>,
        Tracked<Option<rcu_spec::RcuBlockInfo<T>>>,
        Tracked<rcu_spec::RcuReadGuardToken<T>>,
    ))
        requires
            self.well_formed(),
        ensures
            old(tv)@.spec_le(final(tv)@),
            !self.constant().nullable ==> !res.0.is_null(),
            res.4@.wf(),
            res.4@.domain() == self.constant().domain,
            res.4@.reader_registry() == self.constant().reader_registry,
            res.4@.retire_observation_registry() == self.constant().retire_observation_registry,
            res.4@.reader() == reader,
            res.4@.root() == self.id(),
            res.4@.start_view() == old(tv)@,
            match (res.2@, res.3@) {
                (None, None) => res.0.addr() == 0,
                (Some(object), Some(info)) => {
                    &&& res.0.addr() != 0
                    &&& object.addr == res.0.addr()
                    &&& info.wf()
                    &&& info.domain() == object.domain
                    &&& info.domain() == res.4@.domain()
                    &&& info.obj() == object.obj
                    &&& info.addr() == object.addr
                    &&& equal(info.ptr(), res.0)
                    &&& !res.4@.expired().contains(info.obj())
                    &&& !res.4@.seen_removed().removed.contains(info.obj())
                    &&& res.4@.protects(info.addr(), info.obj())
                },
                _ => false,
            },
    {
        proof_decl! {
            let tracked retired_facts = rcu_spec::RcuRetiredFacts::empty();
        }
        self.load_acquire_rcu_guarded_with_retired(
            Ghost(reader),
            Tracked(&retired_facts),
            Tracked(tv),
        )
    }

    /// Acquire-load an RCU root while retaining the CPU implementation
    /// fragment in the returned guard.
    ///
    /// The caller must split `cpu_reader` after disabling preemption and before
    /// calling this method. The fragment is therefore live before the first
    /// protected load, while the participant view bound ensures that the paper
    /// guard starts no earlier than the CPU state from which it was split.
    #[inline(always)]
    pub fn load_acquire_rcu_guarded_cpu(
        &self,
        Ghost(reader): Ghost<rcu_spec::RcuReaderContext>,
        Tracked(cpu_reader): Tracked<rcu_cpu_spec::CpuRcuReaderFragment>,
        Tracked(binding): Tracked<rcu_cpu_spec::CpuRcuCoreBinding>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: (
        *mut T,
        Ghost<Timestamp>,
        Ghost<Option<rcu_spec::RcuPublishedObject>>,
        Tracked<Option<rcu_spec::RcuBlockInfo<T>>>,
        Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<T>>,
        Tracked<Option<rcu_cpu_spec::RcuRootReadLease<O>>>,
    ))
        requires
            self.well_formed(),
            cpu_reader.wf(),
            reader.cpu == cpu_reader.cpu(),
            reader.generation == cpu_reader.generation(),
            binding.registry() == reader.scheduler,
            reader.scheduler == self.constant().scheduler,
            binding.cpu() == cpu_reader.cpu(),
            binding.locals_key().len() == 1,
            binding.single_local_id() == cpu_reader.participant_id(),
            online_cpus().contains(cpu_reader.cpu()),
            cpu_reader.participant_view().spec_le(old(tv)@),
        ensures
            old(tv)@.spec_le(final(tv)@),
            !self.constant().nullable ==> !res.0.is_null(),
            res.4@.wf(),
            res.4@.participant_id() == cpu_reader.participant_id(),
            res.4@.cpu() == cpu_reader.cpu(),
            res.4@.generation() == cpu_reader.generation(),
            res.4@.participant_view() == cpu_reader.participant_view(),
            res.4@.scheduler() == binding.registry(),
            res.4@.domain() == self.constant().domain,
            res.4@.reader_registry() == self.constant().reader_registry,
            res.4@.retire_observation_registry() == self.constant().retire_observation_registry,
            res.4@.reader_context() == reader,
            res.4@.root() == self.id(),
            res.4@.start_view() == old(tv)@,
            match (res.2@, res.3@, res.5@) {
                (None, None, None) => {
                    &&& res.0.addr() == 0
                    &&& res.4@.reader_fragment() == cpu_reader
                },
                (Some(object), Some(info), Some(lease)) => {
                    &&& res.0.addr() != 0
                    &&& object.addr == res.0.addr()
                    &&& info.wf()
                    &&& info.domain() == object.domain
                    &&& info.domain() == res.4@.domain()
                    &&& info.obj() == object.obj
                    &&& info.addr() == object.addr
                    &&& equal(info.ptr(), res.0)
                    &&& !res.4@.expired().contains(info.obj())
                    &&& !res.4@.seen_removed().removed.contains(info.obj())
                    &&& res.4@.protects(info.addr(), info.obj())
                    &&& res.4@.reader_fragment().fraction() == cpu_reader.fraction() / 2real
                    &&& lease.key() == info.obj()
                    &&& lease.active_registry() == self.constant().active_lease_registry
                    &&& lease.participant_id() == res.4@.participant_id()
                    &&& lease.reader_fraction() == res.4@.reader_fragment().fraction()
                    &&& lease.domain() == res.4@.domain()
                    &&& lease.root() == res.4@.root()
                    &&& lease.reader_context() == res.4@.reader_context()
                    &&& lease.start_view() == res.4@.start_view()
                    &&& lease.protected_addr() == info.addr()
                    &&& OwnPred::owns(res.0, lease.resource())
                },
                _ => false,
            },
    {
        let result;
        proof {
            use_type_invariant(self);
        }
        let ghost start_view = tv@;
        let ghost cpu_reader_at_entry = cpu_reader;
        proof_decl! {
            let tracked retired_facts_ref =
                cpu_reader.tracked_retired_facts_observed_by(start_view);
            let tracked retired_facts = retired_facts_ref.tracked_duplicate();
            let tracked mut cpu_reader = cpu_reader;
        }
        proof {
            assert(retired_facts.observed_by(start_view));
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => state => {
            proof {
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
            let tracked RcuRootAtomicState {
                points_to,
                root: mut g,
                permissions: mut permissions,
            } = state;
            let ghost root_before_cpu_reader = g;
            let ghost permissions_before_cpu_reader = permissions;
            proof {
                assert(points_to.loc() == self.native_loc());
                assert(g.retire_observation_registry()
                    == self.constant().retire_observation_registry);
                permissions.lemma_all_live_reclaim_states();
                permissions.lemma_all_unretired_domains();
            }
            proof_decl! {
                let tracked base_guard =
                    g.tracked_start_reader(points_to.hist(), self.id(), start_view, reader);
            }
            proof {
                g.lemma_retired_facts_observed(
                    points_to.hist(),
                    &retired_facts,
                    self.id(),
                    start_view,
                );
            }
            let loaded = raw_atomic.load(Ordering::Acquire, Tracked(tv), Tracked(&points_to));
            let ghost timestamp = loaded.2@.timestamp;
            proof_decl! {
                let tracked loaded_info;
            }
            proof {
                assert(rcu_spec::rcu_owned_root_history_inv(points_to.hist(), g));
                loaded_info = g.tracked_info_at(points_to.hist(), timestamp);
                assert(g.publications().contains_key(timestamp));
            }
            proof_decl! {
                let ghost published = g.published_at(timestamp);
            }
            proof {
                match (published, &loaded_info) {
                    (Some(object), Some(info)) => {
                        assert(equal(points_to.hist().value(timestamp), loaded.0));
                        assert(equal(info.ptr(), loaded.0));
                        assert(info.domain() == g.domain());
                        assert(info.domain() == base_guard.domain());
                    },
                    (None, None) => assert(loaded.0.addr() == 0),
                    _ => assert(false),
                }
                if !self.constant().nullable {
                    rcu_spec::rcu_history_inv_read_nonnull::<T>(points_to.hist(), timestamp);
                    assert(!loaded.0.is_null());
                }
                assert(base_guard.domain() == self.constant().domain);
                assert(base_guard.reader_registry() == self.constant().reader_registry);
                assert(base_guard.retire_observation_registry()
                    == self.constant().retire_observation_registry);
            }
            proof_decl! {
                let tracked mut paper_guard =
                    rcu_spec::RcuReadGuardToken::tracked_from_base(base_guard);
            }
            proof {
                assert(paper_guard.expired()
                    == g.root().domain_auth().observed_retired(self.id(), start_view));
                match &loaded_info {
                    Some(info) => {
                        assert(g.infos().contains_key(info.obj()));
                        assert(permissions.allocations().contains(info.obj()));
                        if !permissions.contains(info.obj()) {
                            let tracked completed = permissions.tracked_reclaimed(info.obj());
                            assert(permissions.reclaimed().contains_key(info.obj()));
                            assert(g.removals().contains_key(info.obj()));
                            assert(completed.record().removal == g.removals()[info.obj()]);
                            let tracked closed = completed.tracked_closed_generation(
                                cpu_reader.cpu(),
                            );
                            assert(closed.scheduler() == permissions.scheduler());
                            assert(permissions.scheduler() == self.constant().scheduler);
                            assert(binding.registry() == self.constant().scheduler);
                            closed.lemma_same_participant_as_binding(&binding);
                            assert(completed.closed_generations()[cpu_reader.cpu()].participant_id()
                                == cpu_reader.participant_id());
                            cpu_reader = completed.tracked_later_reader(cpu_reader);
                            assert(retired_facts.records().contains(completed.record()));
                        }
                        if paper_guard.expired().contains(info.obj()) {
                            assert(g.root().domain_auth().observed_retired(
                                self.id(),
                                start_view,
                            ).contains(info.obj()));
                            g.lemma_observed_retired(
                                points_to.hist(),
                                self.id(),
                                start_view,
                                info.obj(),
                            );
                            let ghost removal = g.removals()[info.obj()];
                            assert(removal.root == self.id());
                            assert(removal.observed_by(start_view));
                            assert(points_to.get_timestamp(removal.message_view)
                                == Some(removal.timestamp));
                            points_to.get_timestamp_monotonic(start_view, removal.message_view);
                            assert(points_to.get_timestamp(start_view) is Some);
                            assert(removal.timestamp
                                <= points_to.get_timestamp(start_view)->Some_0);
                            assert(points_to.get_timestamp(start_view)->Some_0 <= timestamp);
                            assert(removal.timestamp <= timestamp);
                            assert(g.removals_wf(points_to.hist()));
                            assert(g.publications()[timestamp] != Some(info.obj()));
                            assert(published == Some(rcu_spec::RcuPublishedObject {
                                domain: info.domain(),
                                obj: info.obj(),
                                addr: info.addr(),
                            }));
                            g.lemma_published_object_id(
                                points_to.hist(),
                                timestamp,
                                rcu_spec::RcuPublishedObject {
                                    domain: info.domain(),
                                    obj: info.obj(),
                                    addr: info.addr(),
                                },
                            );
                            assert(g.publications()[timestamp] == Some(info.obj()));
                            assert(false);
                        }
                        assert(permissions.contains(info.obj()));
                        assert(paper_guard.can_protect(*info));
                        paper_guard.tracked_protect(info);
                    },
                    None => {},
                }
                assert(cpu_reader == cpu_reader_at_entry);
            }
            proof_decl! {
                let tracked cpu_guard = rcu_cpu_spec::CpuRcuReadGuardToken::tracked_new(
                    paper_guard,
                    cpu_reader,
                    binding,
                );
                let tracked final_guard;
                let tracked lease;
            }
            proof {
                assert(cpu_guard.reader_context() == reader);
                match &loaded_info {
                    Some(info) => {
                        assert(permissions.contains(info.obj()));
                        permissions.lemma_live_reclaim_state(info.obj());
                        assert(g.infos().contains_key(info.obj()));
                        let ghost loaded_ownership = permissions.ownership(info.obj());
                        assert(permissions.reclaim_states()[info.obj()] is Some);
                        assert(permissions.reclaim_states()[info.obj()]->Some_0 == info.ptr());
                        assert(equal(info.ptr(), loaded.0));
                        assert(OwnPred::owns(loaded.0, loaded_ownership));
                        let tracked split = permissions.tracked_split_loaded(
                            cpu_guard,
                            info,
                        );
                        final_guard = split.0;
                        lease = Some(split.1);
                        assert(split.1.resource() == loaded_ownership);
                        assert(OwnPred::owns(loaded.0, split.1.resource()));
                        assert(final_guard.scheduler() == binding.registry());
                        assert(final_guard.domain() == self.constant().domain);
                    },
                    None => {
                        final_guard = cpu_guard;
                        lease = None;
                        assert(final_guard.scheduler() == binding.registry());
                        assert(final_guard.domain() == self.constant().domain);
                    },
                }
                assert(final_guard.reader_context() == reader);
                assert(final_guard.start_view() == start_view);
                match (&loaded_info, &lease) {
                    (None, None) => {
                        assert(final_guard.reader_fragment() == cpu_reader_at_entry);
                    },
                    (Some(info), Some(lease)) => {
                        assert(lease.key() == info.obj());
                        assert(final_guard.reader_fragment().fraction()
                            == cpu_reader_at_entry.fraction() / 2real);
                    },
                    _ => assert(false),
                }
                assert(g.current_owned() == root_before_cpu_reader.current_owned());
                assert(g.domain() == root_before_cpu_reader.domain());
                assert(g.reader_registry() == root_before_cpu_reader.reader_registry());
                assert(g.retire_observation_registry()
                    == root_before_cpu_reader.retire_observation_registry());
                assert(g.publications() == root_before_cpu_reader.publications());
                assert(g.infos() == root_before_cpu_reader.infos());
                assert(g.removals() == root_before_cpu_reader.removals());
                assert(rcu_spec::rcu_current_ownership_inv::<
                    T,
                    (),
                    rcu_spec::UnitRcuRootOwnership,
                >(g));
                assert forall|obj: nat| g.removals().contains_key(obj) implies {
                    let removal = #[trigger] g.removals()[obj];
                    points_to.get_timestamp(removal.message_view) == Some(removal.timestamp)
                } by {
                    assert(root_before_cpu_reader.removals().contains_key(obj));
                };
                assert(rcu_spec::RcuOwnedWeakAtomicInv::<
                    rcu_spec::UnitRcuRootOwnership,
                >::inv(
                    (self.constant(), self.native_loc()),
                    (points_to, g),
                ));
                assert(permissions.allocations()
                    == permissions_before_cpu_reader.allocations());
                assert(permissions.reclaim_states()
                    == permissions_before_cpu_reader.reclaim_states());
                assert(permissions.reclaimed() == permissions_before_cpu_reader.reclaimed());
                assert(permissions.unretired_claims()
                    == permissions_before_cpu_reader.unretired_claims());
                assert(permissions.wf());
                assert(permissions.domain() == self.constant().domain);
                assert(permissions.root() == self.constant().domain);
                assert(permissions.retire_observation_registry()
                    == self.constant().retire_observation_registry);
                assert(permissions.reclaim_registry() == self.constant().reclaim_registry);
                assert(permissions.allocations() == g.infos().dom());
                permissions.lemma_all_live_reclaim_states();
                permissions.lemma_all_unretired_domains();
                assert forall|obj: nat| #[trigger]
                    permissions.keys().contains(obj) implies {
                        &&& g.infos().contains_key(obj)
                        &&& permissions.reclaim_states()[obj] is Some
                        &&& permissions.reclaim_states()[obj]->Some_0 == g.infos()[obj].ptr()
                        &&& OwnPred::owns(
                            permissions.reclaim_states()[obj]->Some_0,
                            permissions.ownership(obj),
                        )
                    } by {
                    assert(permissions_before_cpu_reader.keys().contains(obj));
                    assert(permissions.ownership(obj)
                        == permissions_before_cpu_reader.ownership(obj));
                };
                assert(permissions.unretired_claims().dom() == match g.current_registration() {
                    Some(registration) => Set::empty().insert(registration.0.obj()),
                    None => Set::empty(),
                });
                assert forall|obj: nat| #[trigger]
                    g.removals().contains_key(obj) implies !permissions.has_unretired_claim(obj) by {};
                assert forall|obj: nat| #[trigger]
                    permissions.reclaimed().contains_key(obj) implies {
                        &&& g.removals().contains_key(obj)
                        &&& permissions.reclaimed()[obj].record().removal == g.removals()[obj]
                    } by {};
                state = RcuRootAtomicState { points_to, root: g, permissions };
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
            result = (
                loaded.0,
                Ghost(timestamp),
                Ghost(published),
                Tracked(loaded_info),
                Tracked(final_guard),
                Tracked(lease),
            );
        });
        result
    }

    /// Return a guarded load's physical lease to this root.
    ///
    /// The lease's linear membership receipt identifies the active registry
    /// entry after the atomic invariant is reopened. Returning it also rejoins
    /// the CPU fragment retained by that entry with the executable guard.
    #[verifier::atomic]
    pub fn return_cpu_rcu_read_lease(
        &self,
        Tracked(lease): Tracked<Option<rcu_cpu_spec::RcuRootReadLease<O>>>,
        Tracked(guard): Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<T>>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<T>>)
        requires
            self.well_formed(),
            match lease {
                None => true,
                Some(lease) => {
                    &&& lease.active_registry() == self.constant().active_lease_registry
                    &&& lease.participant_id() == guard.participant_id()
                    &&& lease.reader_fraction() == guard.reader_fragment().fraction()
                    &&& lease.domain() == guard.domain()
                    &&& lease.root() == guard.root()
                    &&& lease.reader_context() == guard.reader_context()
                    &&& lease.start_view() == guard.start_view()
                    &&& guard.protects(lease.protected_addr(), lease.key())
                },
            },
            guard.wf(),
            guard.domain() == self.constant().domain,
            guard.root() == self.id(),
            guard.retire_observation_registry() == self.constant().retire_observation_registry,
        ensures
            old(tv)@.spec_le(final(tv)@),
            res@.wf(),
            res@.paper_guard() == guard.paper_guard(),
            res@.binding() == guard.binding(),
            res@.participant_id() == guard.participant_id(),
            res@.cpu() == guard.cpu(),
            res@.generation() == guard.generation(),
            res@.participant_view() == guard.participant_view(),
            res@.known_retired() == guard.known_retired(),
            res@.domain() == guard.domain(),
            res@.root() == guard.root(),
            res@.reader_registry() == guard.reader_registry(),
            res@.retire_observation_registry() == guard.retire_observation_registry(),
            res@.reader_context() == guard.reader_context(),
            res@.start_view() == guard.start_view(),
            res@.expired() == guard.expired(),
            res@.seen_removed() == guard.seen_removed(),
            res@.protected() == guard.protected(),
            res@.reader_fragment().fraction() == match lease {
                None => guard.reader_fragment().fraction(),
                Some(_) => guard.reader_fragment().fraction() * 2real,
            },
        no_unwind
    {
        let raw_atomic = &self.atomic;
        proof_decl! {
            let tracked final_guard;
        }
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => state => {
            let _loaded = raw_atomic.load(
                Ordering::Relaxed,
                Tracked(tv),
                Tracked(&state.points_to),
            );
            proof {
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
                assert(state.permissions.active_lease_registry()
                    == self.constant().active_lease_registry);
                match lease {
                    None => {
                        final_guard = guard;
                    },
                    Some(lease) => {
                        let ghost permissions_before = state.permissions;
                        final_guard = state.permissions.tracked_return_loaded(lease, guard);
                        assert(state.permissions.allocations()
                            == permissions_before.allocations());
                        assert(state.permissions.keys() == permissions_before.keys());
                        assert(state.permissions.reclaim_states()
                            == permissions_before.reclaim_states());
                        assert(state.permissions.unretired_claims()
                            == permissions_before.unretired_claims());
                        assert(state.permissions.reclaimed()
                            == permissions_before.reclaimed());
                        assert forall|obj: nat| #[trigger]
                            state.permissions.keys().contains(obj) implies {
                                &&& state.root.infos().contains_key(obj)
                                &&& state.permissions.reclaim_states()[obj] is Some
                                &&& state.permissions.reclaim_states()[obj]->Some_0
                                    == state.root.infos()[obj].ptr()
                                &&& OwnPred::owns(
                                    state.permissions.reclaim_states()[obj]->Some_0,
                                    state.permissions.ownership(obj),
                                )
                        } by {
                            assert(permissions_before.keys().contains(obj));
                            assert(permissions_before.contains(obj));
                            assert(state.permissions.contains(obj));
                            assert(state.permissions.allocations().contains(obj));
                            assert(state.permissions.reclaim_states().dom().contains(obj));
                            assert(state.permissions.ownership(obj)
                                == permissions_before.ownership(obj));
                        };
                        assert forall|obj: nat| #[trigger]
                            state.root.removals().contains_key(obj) implies
                                !state.permissions.has_unretired_claim(obj) by {
                            assert(!permissions_before.has_unretired_claim(obj));
                        };
                        assert forall|obj: nat| #[trigger]
                            state.permissions.reclaimed().contains_key(obj) implies {
                                &&& state.root.removals().contains_key(obj)
                                &&& state.permissions.reclaimed()[obj].record().removal
                                    == state.root.removals()[obj]
                            } by {
                            assert(permissions_before.reclaimed().contains_key(obj));
                        };
                    },
                }
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
        });
        Tracked(final_guard)
    }

    /// End a paper read-side guard without executing another atomic operation.
    #[inline(always)]
    pub fn stop_rcu_reader(&self, Tracked(guard): Tracked<rcu_spec::RcuReadGuardToken<T>>)
        requires
            self.well_formed(),
            guard.wf(),
            guard.domain() == self.constant().domain,
            guard.reader_registry() == self.constant().reader_registry,
            guard.retire_observation_registry() == self.constant().retire_observation_registry,
    {
        proof_decl! {
            let tracked base_guard = guard.tracked_into_base();
            let tracked _inactive = base_guard.tracked_stop();
        }
        proof {
            use_type_invariant(self);
        }
    }

    /// Ends a CPU-refined reader and returns its linear CPU fragment.
    ///
    /// The fragment is intentionally returned instead of dropped. The standard
    /// guard destruction path must join it back into the current CPU's
    /// participant before executable preemption is re-enabled.
    #[inline(always)]
    pub fn stop_cpu_rcu_reader(
        &self,
        Tracked(guard): Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<T>>,
    ) -> (res: Tracked<rcu_cpu_spec::CpuRcuReaderFragment>)
        requires
            self.well_formed(),
            guard.wf(),
            guard.domain() == self.constant().domain,
            guard.root() == self.id(),
            guard.retire_observation_registry() == self.constant().retire_observation_registry,
        ensures
            res@.wf(),
            res@ == guard.reader_fragment(),
            res@.participant_id() == guard.participant_id(),
            res@.cpu() == guard.cpu(),
            res@.generation() == guard.generation(),
        opens_invariants none
        no_unwind
    {
        proof_decl! {
            let tracked (_inactive, reader) = guard.tracked_stop();
        }
        proof {
            use_type_invariant(self);
        }
        Tracked(reader)
    }

    /// Release-swap helper for a freshly introduced RCU root pointer.
    ///
    /// The new registration remains owned by the atomic invariant. The return
    /// value contains the previous root's retired ownership, if any. Root
    /// removal and the base retire transition happen while the same atomic
    /// invariant is open.
    #[inline(always)]
    pub fn swap_release_rcu(
        &self,
        value: *mut T,
        Tracked(ownership): Tracked<Option<O>>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: (*mut T, Tracked<Option<RcuRetiredRootObject<T>>>))
        requires
            self.well_formed(),
            self.constant().nullable || !value.is_null(),
            match ownership {
                Some(ownership) => {
                    &&& !value.is_null()
                    &&& OwnPred::owns(value, ownership)
                },
                None => value.is_null(),
            },
        ensures
            old(tv)@.spec_le(final(tv)@),
            (res.1@ is Some) == !res.0.is_null(),
            res.1@ is Some ==> res.1@->Some_0.object().wf(),
            res.1@ is Some ==> res.1@->Some_0.object().domain() == self.constant().domain,
            res.1@ is Some ==> equal(res.1@->Some_0.object().ptr(), res.0),
            res.1@ is Some ==> equal(res.1@->Some_0.ptr(), res.0),
            res.1@ is Some ==> res.1@->Some_0.retired().obj() == res.1@->Some_0.obj(),
            res.1@ is Some ==> res.1@->Some_0.retired().removal().root == self.id(),
            res.1@ is Some ==> res.1@->Some_0.retired().removal().root == self.constant().domain,
            res.1@ is Some ==> res.1@->Some_0.retired().retire_observation_registry()
                == self.constant().retire_observation_registry,
            res.1@ is Some ==> res.1@->Some_0.retired().removal().observed_by(final(tv)@),
            res.1@ is Some ==> res.1@->Some_0.claim().obj() == res.1@->Some_0.obj(),
            res.1@ is Some ==> res.1@->Some_0.claim().registry()
                == self.constant().reclaim_registry,
    {
        let result;
        let ghost start_view = tv@;
        proof_decl! {
            let tracked retired_ownership;
            let tracked unit_ownership: Option<()>;
            let tracked physical_ownership: Option<O>;
        }
        proof {
            use_type_invariant(self);
            match ownership {
                Some(ownership) => {
                    unit_ownership = Some(());
                    physical_ownership = Some(ownership);
                },
                None => {
                    unit_ownership = None;
                    physical_ownership = None;
                },
            }
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => state => {
            proof {
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
            let tracked RcuRootAtomicState {
                points_to: mut points_to,
                root: mut g,
                permissions: mut permissions,
            } = state;
            let ghost root_before_update = g;
            let ghost permissions_before_update = permissions;
            proof {
                assert(points_to.loc() == self.native_loc());
                permissions.lemma_all_live_reclaim_states();
                permissions.lemma_all_unretired_domains();
                match g.current_registration() {
                    Some(registration) => {
                        assert(permissions.has_unretired_claim(registration.0.obj()));
                        permissions.lemma_unretired_is_live(registration.0.obj());
                    },
                    None => {},
                }
            }
            let ghost prev = points_to.hist();
            let ghost previous_removals = g.removals();
            let swap = raw_atomic.swap_release(value, Tracked(tv), Tracked(&mut points_to));
            result = swap.0;
            let ghost update = swap.2@;
            let ghost next = points_to.hist();
            proof {
                assert(rcu_spec::rcu_owned_root_history_inv(prev, g));
                if !self.constant().nullable {
                    assert(!value.is_null());
                }
                rcu_spec::preserve_rcu_history_inv_on_push(
                    self.constant().nullable,
                    prev,
                    next,
                    update.load_timestamp + 1,
                    value,
                    update.store_message_view,
                );
                let tracked detached = g.tracked_push_fresh::<rcu_spec::UnitRcuRootOwnership>(
                    prev,
                    next,
                    update.load_timestamp,
                    update.load_timestamp + 1,
                    value,
                    update.store_message_view,
                    self.id(),
                    unit_ownership,
                );
                assert(detached is Some ==> detached->Some_0.object().wf());
                assert(detached is Some ==> equal(detached->Some_0.ptr(), result));
                assert(detached is Some ==> detached->Some_0.retired().removal().root
                    == self.id());
                assert(detached is Some ==> detached->Some_0.retired().removal().timestamp
                    == update.load_timestamp + 1);
                assert(detached is Some ==> detached->Some_0.retired().removal().observed_by(
                    tv@,
                ));
                assert(match detached {
                    Some(detached) => {
                        &&& root_before_update.current_registration() is Some
                        &&& detached.object()
                            == root_before_update.current_registration()->Some_0.0
                    },
                    None => root_before_update.current_registration() is None,
                });
                assert forall|obj: nat| g.removals().contains_key(obj) implies {
                    let removal = #[trigger] g.removals()[obj];
                    points_to.get_timestamp(removal.message_view) == Some(removal.timestamp)
                } by {
                    match detached {
                        Some(detached) => {
                            if obj == detached.obj() {
                                assert(g.removals()[obj] == detached.retired().removal());
                            } else {
                                assert(previous_removals.contains_key(obj));
                                assert(g.removals()[obj] == previous_removals[obj]);
                            }
                        },
                        None => {
                            assert(previous_removals.contains_key(obj));
                            assert(g.removals()[obj] == previous_removals[obj]);
                        },
                    }
                };
                retired_ownership = match detached {
                    Some(detached) => {
                        assert(permissions.has_unretired_claim(detached.obj()));
                        assert(permissions.keys().contains(detached.obj()));
                        assert(permissions.reclaim_states()[detached.obj()] is Some);
                        assert(permissions.reclaim_states()[detached.obj()]->Some_0
                            == root_before_update.infos()[detached.obj()].ptr());
                        assert(equal(
                            root_before_update.infos()[detached.obj()].ptr(),
                            detached.object().ptr(),
                        ));
                        let tracked claim = permissions.tracked_retire(detached.obj());
                        assert(claim.obj() == detached.object().obj());
                        assert(equal(claim.ptr(), detached.object().ptr()));
                        Some(RcuRetiredRootObject { detached, claim })
                    },
                    None => None,
                };
                permissions.lemma_all_live_reclaim_states();
                let ghost permissions_after_retire = permissions;
                if physical_ownership is Some {
                    let tracked info = g.tracked_info_at(
                        points_to.hist(),
                        update.load_timestamp + 1,
                    ).tracked_unwrap();
                    let ghost inserted_obj = info.obj();
                    let ghost inserted_ownership = physical_ownership->Some_0;
                    permissions.tracked_insert(&info, physical_ownership.tracked_unwrap());
                    assert(permissions.contains(inserted_obj));
                    permissions.lemma_live_reclaim_state(inserted_obj);
                    permissions.lemma_all_live_reclaim_states();
                    assert(permissions.ownership(inserted_obj) == inserted_ownership);
                    assert(equal(info.ptr(), value));
                    assert(OwnPred::owns(info.ptr(), inserted_ownership));
                    assert forall|obj: nat| #[trigger]
                        permissions.keys().contains(obj) implies {
                            &&& g.infos().contains_key(obj)
                            &&& permissions.reclaim_states()[obj] is Some
                            &&& permissions.reclaim_states()[obj]->Some_0 == g.infos()[obj].ptr()
                            &&& OwnPred::owns(
                                permissions.reclaim_states()[obj]->Some_0,
                                permissions.ownership(obj),
                            )
                        } by {
                        if obj == inserted_obj {
                            assert(equal(info.ptr(), g.infos()[obj].ptr()));
                        } else {
                            assert(permissions_before_update.keys().contains(obj));
                            assert(permissions_after_retire.keys().contains(obj));
                            assert(permissions_after_retire.contains(obj));
                            assert(root_before_update.infos().contains_key(obj));
                            assert(g.infos()[obj] == root_before_update.infos()[obj]);
                            assert(permissions.reclaim_states()[obj]
                                == permissions_before_update.reclaim_states()[obj]);
                            assert(permissions.ownership(obj)
                                == permissions_after_retire.ownership(obj));
                            assert(permissions_after_retire.ownership(obj)
                                == permissions_before_update.ownership(obj));
                        }
                    };
                } else {
                    permissions.lemma_all_live_reclaim_states();
                    assert forall|obj: nat| #[trigger]
                        permissions.keys().contains(obj) implies {
                            &&& g.infos().contains_key(obj)
                            &&& permissions.reclaim_states()[obj] is Some
                            &&& permissions.reclaim_states()[obj]->Some_0 == g.infos()[obj].ptr()
                            &&& OwnPred::owns(
                                permissions.reclaim_states()[obj]->Some_0,
                                permissions.ownership(obj),
                            )
                        } by {
                        assert(permissions_before_update.keys().contains(obj));
                        assert(permissions_after_retire.keys().contains(obj));
                        assert(root_before_update.infos().contains_key(obj));
                        assert(g.infos()[obj] == root_before_update.infos()[obj]);
                        assert(permissions.reclaim_states()[obj]
                            == permissions_before_update.reclaim_states()[obj]);
                        assert(permissions.ownership(obj)
                            == permissions_after_retire.ownership(obj));
                        assert(permissions_after_retire.ownership(obj)
                            == permissions_before_update.ownership(obj));
                    };
                }
                assert(permissions.allocations() == g.infos().dom());
                assert forall|obj: nat| #[trigger]
                    permissions.reclaimed().contains_key(obj) implies {
                        &&& g.removals().contains_key(obj)
                        &&& permissions.reclaimed()[obj].record().removal == g.removals()[obj]
                    } by {
                    assert(permissions_before_update.reclaimed().contains_key(obj));
                    assert(root_before_update.removals().contains_key(obj));
                    assert(g.removals()[obj] == root_before_update.removals()[obj]);
                };
                assert(rcu_spec::RcuOwnedWeakAtomicInv::<
                    rcu_spec::UnitRcuRootOwnership,
                >::inv(
                    (self.constant(), self.native_loc()),
                    (points_to, g),
                ));
                permissions.lemma_all_unretired_domains();
                assert(permissions.unretired_claims().dom() == match g.current_registration() {
                    Some(registration) => Set::empty().insert(registration.0.obj()),
                    None => Set::empty(),
                });
                assert forall|obj: nat| #[trigger]
                    g.removals().contains_key(obj) implies !permissions.has_unretired_claim(obj) by {
                    if !root_before_update.removals().contains_key(obj) {
                        assert(retired_ownership is Some);
                        assert(retired_ownership->Some_0.obj() == obj);
                    }
                };
                state = RcuRootAtomicState { points_to, root: g, permissions };
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
        });
        (result, Tracked(retired_ownership))
    }

    /// Strong AcqRel/Acquire CAS helper for a freshly introduced RCU pointer.
    ///
    /// Registration occurs only in the successful CAS branch. A successful
    /// CAS returns the previous root registration; a failed CAS leaves the
    /// ownership state unchanged and returns no detached registration.
    #[inline(always)]
    pub fn compare_exchange_acqrel_acquire_rcu(
        &self,
        current: *mut T,
        new: *mut T,
        Tracked(new_ownership): Tracked<Option<O>>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: (
        Result<*mut T, *mut T>,
        Ghost<Timestamp>,
        Tracked<(Option<RcuRetiredRootObject<T>>, Option<O>)>,
    ))
        requires
            self.well_formed(),
            self.constant().nullable || !new.is_null(),
            match new_ownership {
                Some(ownership) => {
                    &&& !new.is_null()
                    &&& OwnPred::owns(new, ownership)
                },
                None => new.is_null(),
            },
        ensures
            old(tv)@.spec_le(final(tv)@),
            res.0 is Err ==> res.2@.0 is None,
            res.0 is Err ==> res.2@.1 == new_ownership,
            res.0 is Ok ==> res.2@.1 is None,
            res.0 is Ok ==> ((res.2@.0 is Some) == !res.0->Ok_0.is_null()),
            res.2@.0 is Some ==> res.2@.0->Some_0.object().wf(),
            res.2@.0 is Some ==> res.2@.0->Some_0.object().domain() == self.constant().domain,
            res.2@.0 is Some ==> equal(res.2@.0->Some_0.object().ptr(), res.0->Ok_0),
            res.2@.0 is Some ==> equal(res.2@.0->Some_0.ptr(), res.0->Ok_0),
            res.2@.0 is Some ==> res.2@.0->Some_0.retired().obj() == res.2@.0->Some_0.obj(),
            res.2@.0 is Some ==> res.2@.0->Some_0.retired().removal().root == self.id(),
            res.2@.0 is Some ==> res.2@.0->Some_0.retired().removal().root
                == self.constant().domain,
            res.2@.0 is Some ==> res.2@.0->Some_0.retired().retire_observation_registry()
                == self.constant().retire_observation_registry,
            res.2@.0 is Some ==> res.2@.0->Some_0.retired().removal().observed_by(final(tv)@),
            res.2@.0 is Some ==> res.2@.0->Some_0.claim().obj() == res.2@.0->Some_0.obj(),
            res.2@.0 is Some ==> res.2@.0->Some_0.claim().registry()
                == self.constant().reclaim_registry,
    {
        let result;
        let ghost start_view = tv@;
        proof_decl! {
            let tracked retired_ownership;
            let tracked unit_ownership: Option<()>;
            let tracked physical_ownership: Option<O>;
        }
        proof {
            use_type_invariant(self);
            match new_ownership {
                Some(ownership) => {
                    unit_ownership = Some(());
                    physical_ownership = Some(ownership);
                },
                None => {
                    unit_ownership = None;
                    physical_ownership = None;
                },
            }
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => state => {
            proof {
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
            let tracked RcuRootAtomicState {
                points_to: mut points_to,
                root: mut g,
                permissions: mut permissions,
            } = state;
            let ghost root_before_cas = g;
            let ghost permissions_before_cas = permissions;
            proof {
                assert(points_to.loc() == self.native_loc());
                permissions.lemma_all_live_reclaim_states();
                permissions.lemma_all_unretired_domains();
                match g.current_registration() {
                    Some(registration) => {
                        assert(permissions.has_unretired_claim(registration.0.obj()));
                        permissions.lemma_unretired_is_live(registration.0.obj());
                    },
                    None => {},
                }
            }
            let ghost prev = points_to.hist();
            let ghost previous_removals = g.removals();
            proof_decl! {
                let tracked release_view = vstd::thread_view::ReleaseViewSeen::new();
            }
            let cas_result = raw_atomic.compare_exchange(
                current,
                new,
                Ordering::AcqRel,
                Ordering::Acquire,
                Tracked(tv),
                Tracked(release_view),
                Tracked(&mut points_to),
            );
            result = (cas_result.0, Ghost(cas_result.2@.load_timestamp));
            let ghost update = cas_result.2@;
            let ghost next = points_to.hist();
            proof {
                assert(rcu_spec::rcu_owned_root_history_inv(prev, g));
                match cas_result.0 {
                    Result::Ok(_) => {
                        rcu_spec::preserve_rcu_history_inv_on_push(
                            self.constant().nullable,
                            prev,
                            next,
                            update.load_timestamp + 1,
                            new,
                            update.store_message_view,
                        );
                        let tracked detached = g.tracked_push_fresh::<
                            rcu_spec::UnitRcuRootOwnership,
                        >(
                            prev,
                            next,
                            update.load_timestamp,
                            update.load_timestamp + 1,
                            new,
                            update.store_message_view,
                            self.id(),
                            unit_ownership,
                        );
                        assert(detached is Some ==> detached->Some_0.object().wf());
                        assert(detached is Some ==> equal(
                            detached->Some_0.ptr(),
                            cas_result.0->Ok_0,
                        ));
                        assert(detached is Some ==> detached->Some_0.retired().removal().root
                            == self.id());
                        assert(detached is Some ==>
                            detached->Some_0.retired().removal().observed_by(tv@));
                        assert(match detached {
                            Some(detached) => {
                                &&& root_before_cas.current_registration() is Some
                                &&& detached.object()
                                    == root_before_cas.current_registration()->Some_0.0
                            },
                            None => root_before_cas.current_registration() is None,
                        });
                        assert forall|obj: nat| g.removals().contains_key(obj) implies {
                            let removal = #[trigger] g.removals()[obj];
                            points_to.get_timestamp(removal.message_view)
                                == Some(removal.timestamp)
                        } by {
                            match detached {
                                Some(detached) => {
                                    if obj == detached.obj() {
                                        assert(g.removals()[obj] == detached.retired().removal());
                                    } else {
                                        assert(previous_removals.contains_key(obj));
                                        assert(g.removals()[obj] == previous_removals[obj]);
                                    }
                                },
                                None => {
                                    assert(previous_removals.contains_key(obj));
                                    assert(g.removals()[obj] == previous_removals[obj]);
                                },
                            }
                        };
                        let tracked detached = match detached {
                            Some(detached) => {
                                assert(permissions.has_unretired_claim(detached.obj()));
                                assert(permissions.keys().contains(detached.obj()));
                                assert(permissions.reclaim_states()[detached.obj()] is Some);
                                assert(permissions.reclaim_states()[detached.obj()]->Some_0
                                    == root_before_cas.infos()[detached.obj()].ptr());
                                assert(equal(
                                    root_before_cas.infos()[detached.obj()].ptr(),
                                    detached.object().ptr(),
                                ));
                                let tracked claim = permissions.tracked_retire(detached.obj());
                                assert(claim.obj() == detached.object().obj());
                                assert(equal(claim.ptr(), detached.object().ptr()));
                                Some(RcuRetiredRootObject { detached, claim })
                            },
                            None => None,
                        };
                        permissions.lemma_all_live_reclaim_states();
                        let ghost permissions_after_retire = permissions;
                        if physical_ownership is Some {
                            let tracked info = g.tracked_info_at(
                                points_to.hist(),
                                update.load_timestamp + 1,
                            ).tracked_unwrap();
                            let ghost inserted_obj = info.obj();
                            let ghost inserted_ownership = physical_ownership->Some_0;
                            permissions.tracked_insert(
                                &info,
                                physical_ownership.tracked_unwrap(),
                            );
                            assert(permissions.contains(inserted_obj));
                            permissions.lemma_live_reclaim_state(inserted_obj);
                            permissions.lemma_all_live_reclaim_states();
                            assert(permissions.ownership(inserted_obj) == inserted_ownership);
                            assert(equal(info.ptr(), new));
                            assert(OwnPred::owns(info.ptr(), inserted_ownership));
                            assert forall|obj: nat| #[trigger]
                                permissions.keys().contains(obj) implies {
                                    &&& g.infos().contains_key(obj)
                                    &&& permissions.reclaim_states()[obj] is Some
                                    &&& permissions.reclaim_states()[obj]->Some_0
                                        == g.infos()[obj].ptr()
                                    &&& OwnPred::owns(
                                        permissions.reclaim_states()[obj]->Some_0,
                                        permissions.ownership(obj),
                                    )
                                } by {
                                if obj == inserted_obj {
                                    assert(equal(info.ptr(), g.infos()[obj].ptr()));
                                } else {
                                    assert(permissions_before_cas.keys().contains(obj));
                                    assert(permissions_after_retire.keys().contains(obj));
                                    assert(permissions_after_retire.contains(obj));
                                    assert(root_before_cas.infos().contains_key(obj));
                                    assert(g.infos()[obj] == root_before_cas.infos()[obj]);
                                    assert(permissions.reclaim_states()[obj]
                                        == permissions_before_cas.reclaim_states()[obj]);
                                    assert(permissions.ownership(obj)
                                        == permissions_after_retire.ownership(obj));
                                    assert(permissions_after_retire.ownership(obj)
                                        == permissions_before_cas.ownership(obj));
                                }
                            };
                        } else {
                            permissions.lemma_all_live_reclaim_states();
                            assert forall|obj: nat| #[trigger]
                                permissions.keys().contains(obj) implies {
                                    &&& g.infos().contains_key(obj)
                                    &&& permissions.reclaim_states()[obj] is Some
                                    &&& permissions.reclaim_states()[obj]->Some_0
                                        == g.infos()[obj].ptr()
                                    &&& OwnPred::owns(
                                        permissions.reclaim_states()[obj]->Some_0,
                                        permissions.ownership(obj),
                                    )
                                } by {
                                assert(permissions_before_cas.keys().contains(obj));
                                assert(permissions_after_retire.keys().contains(obj));
                                assert(root_before_cas.infos().contains_key(obj));
                                assert(g.infos()[obj] == root_before_cas.infos()[obj]);
                                assert(permissions.reclaim_states()[obj]
                                    == permissions_before_cas.reclaim_states()[obj]);
                                assert(permissions.ownership(obj)
                                    == permissions_after_retire.ownership(obj));
                                assert(permissions_after_retire.ownership(obj)
                                    == permissions_before_cas.ownership(obj));
                            };
                        }
                        assert(rcu_spec::RcuOwnedWeakAtomicInv::<
                            rcu_spec::UnitRcuRootOwnership,
                        >::inv(
                            (self.constant(), self.native_loc()),
                            (points_to, g),
                        ));
                        permissions.lemma_all_unretired_domains();
                        assert(permissions.unretired_claims().dom()
                            == match g.current_registration() {
                                Some(registration) => {
                                    Set::empty().insert(registration.0.obj())
                                },
                                None => Set::empty(),
                            });
                        assert forall|obj: nat| #[trigger]
                            g.removals().contains_key(obj) implies !permissions.has_unretired_claim(
                            obj,
                        ) by {
                            if !root_before_cas.removals().contains_key(obj) {
                                assert(detached is Some);
                                assert(detached->Some_0.obj() == obj);
                            }
                        };
                        retired_ownership = (detached, None);
                    },
                    Result::Err(_) => {
                        retired_ownership = (None, physical_ownership);
                        assert(next == prev);
                        assert(permissions == permissions_before_cas);
                        assert(g == root_before_cas);
                    },
                }
                assert(permissions.allocations() == g.infos().dom());
                assert forall|obj: nat| #[trigger]
                    permissions.reclaimed().contains_key(obj) implies {
                        &&& g.removals().contains_key(obj)
                        &&& permissions.reclaimed()[obj].record().removal == g.removals()[obj]
                    } by {
                    assert(permissions_before_cas.reclaimed().contains_key(obj));
                    match cas_result.0 {
                        Result::Ok(_) => {
                            assert(root_before_cas.removals().contains_key(obj));
                            assert(g.removals()[obj] == root_before_cas.removals()[obj]);
                        },
                        Result::Err(_) => {},
                    }
                };
                state = RcuRootAtomicState { points_to, root: g, permissions };
                assert(RcuRootAtomicInv::<OwnPred>::inv(
                    (self.constant(), self.native_loc()),
                    state,
                ));
            }
        });
        (result.0, result.1, Tracked(retired_ownership))
    }
}

/// Native IRC11 weak boolean atomic specialized for the RCU monitor flag.
pub struct RcuMonitorWeakAtomicBool {
    atomic: Irc11AtomicBool,
    tracked_atomic_inv: Tracked<
        AtomicInvariant<
            Irc11AtomicId,
            (AtomicPointsTo<bool>, rcu_spec::RcuMonitorFlagGhost),
            rcu_spec::RcuMonitorFlagInv,
        >,
    >,
}

impl RcuMonitorWeakAtomicBool {
    pub closed spec fn id(&self) -> Irc11AtomicId {
        self.atomic.loc()
    }

    pub closed spec fn well_formed(&self) -> bool {
        self.tracked_atomic_inv@.constant() == self.id()
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(&self) -> bool {
        self.well_formed()
    }

    pub const fn new() -> (res: Self)
        ensures
            res.well_formed(),
    {
        let (atomic, Tracked(points_to), Tracked(initial_view), Ghost(timestamp)) =
            Irc11AtomicBool::new(false);
        let tracked flag_ghost = rcu_spec::RcuMonitorFlagGhost::tracked_initial(timestamp);
        proof {
            rcu_spec::rcu_monitor_flag_initial_inv(points_to.hist(), timestamp, initial_view@);
            assert(rcu_spec::RcuMonitorFlagInv::inv(atomic.loc(), (points_to, flag_ghost)));
        }
        let tracked pair = (points_to, flag_ghost);
        let tracked atomic_inv = AtomicInvariant::new(atomic.loc(), pair, 0);
        Self { atomic, tracked_atomic_inv: Tracked(atomic_inv) }
    }

    pub fn load_relaxed(&self, Tracked(tv): Tracked<&mut ViewSeen>) -> (res: (bool, Ghost<nat>))
        requires
            self.well_formed(),
        ensures
            old(tv)@.spec_le(final(tv)@),
    {
        let result;
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (points_to, flag_ghost) = pair;
            let loaded = raw_atomic.load(
                Ordering::Relaxed,
                Tracked(tv),
                Tracked(&points_to),
            );
            result = (loaded.0, Ghost(loaded.2@.timestamp));
            proof {
                pair = (points_to, flag_ghost);
            }
        });
        result
    }

    fn raw_atomic(&self) -> (res: &Irc11AtomicBool)
        requires
            self.well_formed(),
        ensures
            res.loc() == self.id(),
    {
        &self.atomic
    }

    proof fn tracked_atomic_inv(tracked &self) -> (tracked res: &vstd::invariant::AtomicInvariant<
        Irc11AtomicId,
        (AtomicPointsTo<bool>, rcu_spec::RcuMonitorFlagGhost),
        rcu_spec::RcuMonitorFlagInv,
    >)
        requires
            self.well_formed(),
        ensures
            res.constant() == self.id(),
    {
        self.tracked_atomic_inv.borrow()
    }

    /// Relaxed-store helper for the RCU monitor flag.
    ///
    /// The executable flag remains a relaxed atomic flag, matching the old
    /// monitor protocol. The proof-side effect is stronger: each stored flag
    /// message inserts the lock-protected monitor-state snapshot supplied by
    /// the writer.
    #[inline(always)]
    pub fn store_relaxed_rcu_monitor(
        &self,
        value: bool,
        Ghost(state): Ghost<rcu_spec::MonitorStateView>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    )
        requires
            self.well_formed(),
            state.wf(),
            !value ==> state.no_pending_work(),
        ensures
            old(tv)@.spec_le(final(tv)@),
    {
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (mut points_to, mut flag_ghost) = pair;
            proof {
                assert(points_to.loc() == self.id());
                assert(raw_atomic.loc() == self.id());
            }
            let ghost prev = points_to.hist();
            proof_decl! {
                let tracked release_view = ReleaseViewSeen::new();
            }
            let store = raw_atomic.store(
                value,
                Ordering::Relaxed,
                Tracked(tv),
                Tracked(release_view),
                Tracked(&mut points_to),
            );
            let ghost next = points_to.hist();
            proof {
                rcu_spec::preserve_rcu_monitor_flag_inv_on_insert(
                    prev,
                    next,
                    store@.timestamp,
                    value,
                    store@.message_view,
                    flag_ghost,
                    flag_ghost.insert(store@.timestamp, state),
                    state,
                );
                flag_ghost = flag_ghost.tracked_insert(store@.timestamp, state);
                pair = (points_to, flag_ghost);
            }
        });
    }
}

} // verus!
