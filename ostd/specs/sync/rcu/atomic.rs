// SPDX-License-Identifier: MPL-2.0
//! Native IRC11 root histories coupled to CPU witnesses and physical leases.
//!
//! # Verified Properties
//! A selected non-null history message names an exact typed allocation. Native
//! per-location load coherence rules out allocations whose removal the reader
//! already observed. The resulting CPU witness then excludes previously
//! reclaimed allocations before any physical permission is borrowed.
use vstd::{prelude::*, raw_ptr::spec_cast_ptr_to_thin_ptr, resource::Loc};
use vstd_extra::{
    atomic_irc11::{AtomicPointsTo, Objective, ThreadView, load_acquire},
    ownership::Inv,
    rcu_objects::RcuBlockInfo,
};

use super::{
    cpu::{CpuRcuCoreBinding, CpuRcuReaderFragment},
    grace_period::RcuReclaimPermit,
    link::{
        RcuLinkObservation, RcuLinkRemoval, lemma_observed_link_removals, lemma_owned_link_graph,
        owned_link_graph,
    },
    owned_root::{RcuRootOwnedGhost, rcu_owned_root_history_inv},
    permissions::{CpuRcuLeaseWitness, RcuReclaimClaim, RcuRootPermissionState, RcuRootReadLease},
    retirement::{
        RcuRemovalObservation, RcuRetiredFact, RcuRetiredRecord, RcuRetiredRegistration,
        RcuRetirementAuth,
    },
    traversal::{AllocationId, LinkEdge, SeenRemoved, TraversalGuard},
};
use crate::cpu::CpuId;

verus! {

broadcast use {
    vstd::atomic_weak::group_view_history,
    vstd::set::group_set_lemmas,
    vstd::set::Set::lemma_map_by_contains,
};

/// Client interpretation of the full physical permission for a typed pointer.
pub trait RcuRootOwnershipPredicate<T, O> {
    /// Relates the complete physical permission to its exact pointer.
    spec fn owns(ptr: *mut T, ownership: O) -> bool;
}

/// Complete resources held by a root's native atomic invariant.
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(O)]
pub tracked struct RcuRootAtomicState<T, O> {
    points_to: AtomicPointsTo<*mut T>,
    root: RcuRootOwnedGhost<T, ()>,
    retirement: RcuRetirementAuth,
    permissions: RcuRootPermissionState<T, O>,
    ghost condition: spec_fn(O) -> bool,
}

// SAFETY: all protocol fields contain objective resource-algebra ownership or
// ghost view snapshots. No subjective ViewSeen/AcquireViewSeen is stored here.
// The client's physical permission must itself be Objective.
unsafe impl<T, O: Objective> Objective for RcuRootAtomicState<T, O> {

}

/// Reader protection for either a non-null allocation or a null observation.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRootProtection<T, O> {
    info: Option<RcuBlockInfo<T>>,
    lease: Option<RcuRootReadLease<O>>,
    null_reader: Option<CpuRcuReaderFragment>,
}

/// One proof result keeps the physical permission and its same-load topology together.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuLinkProtection<T, O> {
    pub protection: RcuRootProtection<T, O>,
    pub ghost observation: RcuLinkObservation<T>,
}

/// A detached registration paired with its unique exact-pointer reclaim claim.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRetiredRoot<T> {
    registration: RcuRetiredRegistration<T>,
    claim: RcuReclaimClaim<T>,
    fact: RcuRetiredFact,
    ghost link_removal: Option<RcuLinkRemoval<T>>,
}

impl<T> Inv for RcuRetiredRoot<T> {
    closed spec fn inv(self) -> bool {
        &&& self.claim.inv()
        &&& self.claim.obj() == self.registration.record().obj
        &&& equal(self.claim.ptr(), self.registration.ptr())
        &&& self.fact.record() == self.registration.record()
        &&& self.link_removal matches Some(link) ==> {
            &&& link.inv()
            &&& link.child == (AllocationId {
                domain: self.record().domain,
                object: self.record().obj,
            })
            &&& link.removal == self.record().removal
            &&& equal(link.graph.objects[link.child], self.ptr())
        }
    }
}

impl<T> RcuRetiredRoot<T> {
    /// Additional no-incoming-edge evidence when this ticket came from an owning link unlink.
    pub closed spec fn link_removal(self) -> Option<RcuLinkRemoval<T>> {
        self.link_removal
    }

    /// Exposes the link proof's binding to this ticket without exposing its linear claim.
    pub proof fn lemma_link_removal(tracked &self)
        requires
            self.inv(),
        ensures
            self.link_removal() matches Some(link) ==> {
                &&& link.inv()
                &&& link.child == (AllocationId {
                    domain: self.record().domain,
                    object: self.record().obj,
                })
                &&& link.removal == self.record().removal
                &&& equal(link.graph.objects[link.child], self.ptr())
            },
    {
    }

    /// Exact detached pointer retained until the callback runs.
    pub closed spec fn ptr(self) -> *mut T {
        self.registration.ptr()
    }

    /// Certified removal that the callback's reports must cover.
    pub closed spec fn record(self) -> RcuRetiredRecord {
        self.registration.record()
    }

    /// Unique-claim authority responsible for physical recovery.
    pub closed spec fn registry(self) -> Loc {
        self.claim.registry()
    }

    /// Copies retirement evidence for the monitor without copying the reclaim claim.
    pub proof fn tracked_fact(tracked &self) -> (tracked res: RcuRetiredFact)
        requires
            self.inv(),
        ensures
            res.record() == self.record(),
            res.wf(),
    {
        self.fact.tracked_duplicate()
    }
}

impl<T, O> Inv for RcuRootProtection<T, O> {
    closed spec fn inv(self) -> bool {
        match (self.info, self.lease, self.null_reader) {
            (Some(info), Some(lease), None) => {
                &&& info.inv()
                &&& lease.inv()
                &&& lease.witness().inv()
                &&& info.obj() == lease.obj()
                &&& info.domain() == lease.witness().domain()
            },
            (None, None, Some(reader)) => reader.wf(),
            _ => false,
        }
    }
}

impl<T, O> RcuRootProtection<T, O> {
    /// Typed identity selected from the native history, absent for null.
    pub closed spec fn info(self) -> Option<RcuBlockInfo<T>> {
        self.info
    }

    /// Physical lease, absent for null.
    pub closed spec fn lease(self) -> Option<RcuRootReadLease<O>> {
        self.lease
    }

    /// CPU resource retained directly for null or in the active lease registry.
    pub closed spec fn reader(self) -> CpuRcuReaderFragment {
        match self.lease {
            Some(lease) => lease.witness().reader(),
            None => self.null_reader->Some_0,
        }
    }

    /// Borrows physical ownership while retaining the complete read protection.
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &O)
        requires
            self.inv(),
            self.lease() is Some,
        ensures
            *res == self.lease()->Some_0.resource(),
    {
        self.lease.tracked_borrow().tracked_borrow()
    }
}

impl<T, O> RcuRootAtomicState<T, O> {
    /// Immutable client predicate required of every published physical resource.
    pub closed spec fn condition(self) -> spec_fn(O) -> bool {
        self.condition
    }

    /// Native atomic points-to resource.
    pub closed spec fn points_to(self) -> AtomicPointsTo<*mut T> {
        self.points_to
    }

    /// Typed publication history metadata.
    pub closed spec fn root(self) -> RcuRootOwnedGhost<T, ()> {
        self.root
    }

    /// Certified root-removal history.
    pub closed spec fn retirement(self) -> RcuRetirementAuth {
        self.retirement
    }

    /// Physical resources still owned by this root or its pending callbacks.
    pub closed spec fn permissions(self) -> RcuRootPermissionState<T, O> {
        self.permissions
    }

    /// Borrows the native resource without exposing the protocol representation.
    pub proof fn tracked_borrow_points_to(tracked &self) -> (tracked res: &AtomicPointsTo<*mut T>)
        ensures
            *res == self.points_to(),
    {
        &self.points_to
    }

    /// Borrows native ownership for a store, preserving every protocol field.
    pub proof fn tracked_borrow_points_to_mut(tracked &mut self) -> (tracked res:
        &mut AtomicPointsTo<*mut T>)
        ensures
            *res == old(self).points_to(),
            final(self).condition() == old(self).condition(),
            *final(res) == final(self).points_to(),
            final(self).root() == old(self).root(),
            final(self).retirement() == old(self).retirement(),
            final(self).permissions() == old(self).permissions(),
    {
        &mut self.points_to
    }

    /// Metadata invariant evaluated against a particular native history resource.
    pub open spec fn inv_at<Pred: RcuRootOwnershipPredicate<T, O>>(
        self,
        points_to: AtomicPointsTo<*mut T>,
    ) -> bool {
        &&& rcu_owned_root_history_inv(points_to.hist(), self.root())
        &&& self.retirement().domain() == self.root().domain()
        &&& self.permissions().inv()
        &&& self.permissions().domain() == self.root().domain()
        &&& self.permissions().observations() == self.retirement().id()
        &&& self.permissions().allocations() == self.root().infos().dom()
        &&& forall|obj: nat| #[trigger]
            self.permissions().keys().contains(obj) ==> {
                &&& self.root().infos().contains_key(obj)
                &&& equal(self.permissions().ptr(obj), self.root().infos()[obj].ptr())
                &&& Pred::owns(self.root().infos()[obj].ptr(), self.permissions().ownership(obj))
                &&& (self.condition())(self.permissions().ownership(obj))
            }
        &&& self.retirement().removals().dom().subset_of(self.root().infos().dom())
        &&& forall|obj: nat| #[trigger]
            self.retirement().removals().contains_key(obj) ==> {
                let removal = self.retirement().removals()[obj];
                &&& removal.root == self.root().domain()
                &&& points_to.hist().contains_timestamp(removal.timestamp)
                &&& points_to.get_timestamp(removal.message_view) == Some(removal.timestamp)
                &&& forall|ts: nat| #[trigger]
                    self.root().root().publications().contains_pair(ts, Some(obj)) ==> ts
                        < removal.timestamp
            }
        &&& match self.root().current_owned() {
            Some(owned) => !self.retirement().removals().contains_key(owned.block_info().obj()),
            None => true,
        }
        &&& self.permissions().unretired() == match self.root().current_owned() {
            Some(owned) => Set::empty().insert(owned.block_info().obj()),
            None => Set::empty(),
        }
    }

    /// Full root invariant, interpreted using this client's physical ownership predicate.
    pub open spec fn inv<Pred: RcuRootOwnershipPredicate<T, O>>(self) -> bool {
        self.inv_at::<Pred>(self.points_to())
    }

    /// Initializes identity, retirement, and physical permission under the native initial message.
    pub proof fn tracked_initial<Pred: RcuRootOwnershipPredicate<T, O>>(
        tracked domain: vstd_extra::rcu_objects::RcuDomainAuth,
        condition: spec_fn(O) -> bool,
        tracked points_to: AtomicPointsTo<*mut T>,
        ptr: *mut T,
        tracked ownership: Option<O>,
        timestamp: nat,
        view: ThreadView,
        scheduler: Loc,
        online: Set<CpuId>,
    ) -> (tracked res: Self)
        requires
            domain.inv(),
            domain.objects() == Map::<nat, usize>::empty(),
            points_to.hist().is_singleton(timestamp, (ptr, view)),
            (ownership is Some) == (ptr.addr() != 0),
            ownership matches Some(owned) ==> Pred::owns(ptr, owned) && condition(owned),
        ensures
            res.inv::<Pred>(),
            res.root().domain() == domain.id(),
            res.condition() == condition,
            res.points_to() == points_to,
            res.permissions().scheduler() == scheduler,
            res.permissions().online() == online,
    {
        let tracked registration_ownership = match ownership {
            Some(_) => Some(()),
            None => None,
        };
        let tracked root = RcuRootOwnedGhost::tracked_initial(
            domain,
            ptr,
            registration_ownership,
            points_to.hist(),
            timestamp,
            view,
        );
        let tracked retirement = RcuRetirementAuth::tracked_new(root.domain());
        let tracked mut permissions = RcuRootPermissionState::tracked_empty(
            scheduler,
            root.domain(),
            retirement.id(),
            online,
        );
        match ownership {
            Some(owned) => {
                let ghost obj = root.current_owned()->Some_0.block_info().obj();
                permissions.tracked_insert(obj, ptr, owned);
                assert(root.infos().dom() == Set::empty().insert(obj));
            },
            None => {},
        }
        Self { points_to, root, retirement, permissions, condition }
    }

    /// Turns a native acquire-load result into a registered physical lease.
    ///
    /// This method does not invent a load or a subjective view: the caller
    /// must supply the relation established by the native atomic primitive.
    pub proof fn tracked_protect_load<Pred: RcuRootOwnershipPredicate<T, O>>(
        tracked &mut self,
        ptr: *mut T,
        timestamp: nat,
        message_view: ThreadView,
        start_view: ThreadView,
        after_view: ThreadView,
        tracked reader: CpuRcuReaderFragment,
        tracked binding: CpuRcuCoreBinding,
    ) -> (tracked res: RcuRootProtection<T, O>)
        requires
            old(self).inv::<Pred>(),
            load_acquire(
                old(self).points_to(),
                start_view,
                after_view,
                ptr,
                timestamp,
                message_view,
            ),
            reader.wf(),
            binding.registry() == old(self).permissions().scheduler(),
            binding.cpu() == reader.cpu(),
            binding.locals_key().len() == 1,
            binding.single_local_id() == reader.participant_id(),
            start_view.contains(reader.participant_view()),
            old(self).permissions().online().contains(reader.cpu()),
        ensures
            final(self).inv::<Pred>(),
            final(self).points_to() == old(self).points_to(),
            final(self).condition() == old(self).condition(),
            final(self).root() == old(self).root(),
            final(self).retirement() == old(self).retirement(),
            final(self).permissions().registry() == old(self).permissions().registry(),
            final(self).permissions().reclaim_registry() == old(
                self,
            ).permissions().reclaim_registry(),
            final(self).permissions().scheduler() == old(self).permissions().scheduler(),
            final(self).permissions().online() == old(self).permissions().online(),
            res.inv(),
            res.reader() == reader,
            res.lease() matches Some(lease) ==> lease.witness().start_view() == start_view,
            match (res.info(), res.lease()) {
                (Some(info), Some(lease)) => {
                    &&& ptr.addr() != 0
                    &&& equal(info.ptr(), ptr)
                    &&& info.domain() == old(self).root().domain()
                    &&& lease.registry() == old(self).permissions().registry()
                    &&& Pred::owns(ptr, lease.resource())
                    &&& (old(self).condition())(lease.resource())
                },
                (None, None) => ptr.addr() == 0,
                _ => false,
            },
    {
        let tracked info = self.root.tracked_info_at(self.points_to.hist(), timestamp);
        match info {
            Some(info) => {
                info.lemma_address();
                let ghost obj = info.obj();
                if exists|record: RcuRetiredRecord| #[trigger]
                    reader.known_retired().contains(record) && record.domain == self.root.domain()
                        && record.retire_observation_registry == self.retirement.id() && record.obj
                        == obj {
                    let ghost record = choose|record: RcuRetiredRecord| #[trigger]
                        reader.known_retired().contains(record) && record.domain
                            == self.root.domain() && record.retire_observation_registry
                            == self.retirement.id() && record.obj == obj;
                    let tracked fact = reader.tracked_known_retired(record);
                    fact.lemma_agree(&self.retirement);
                    let tracked facts = reader.tracked_retired_facts_observed_by(start_view);
                    assert(record.removal.observed_by(start_view));
                    self.points_to.get_timestamp_monotonic(start_view, record.removal.message_view);
                    assert(self.root.root().publications().contains_pair(timestamp, Some(obj)));
                    assert(self.points_to.get_timestamp(start_view)->Some_0 <= timestamp
                        < record.removal.timestamp);
                    assert(false);
                }
                let tracked mut witness = CpuRcuLeaseWitness::tracked_new(
                    reader,
                    binding,
                    self.root.domain(),
                    self.retirement.id(),
                    obj,
                    start_view,
                );
                self.permissions.lemma_live_allocation(&mut witness);
                let tracked lease = self.permissions.tracked_lease(witness);
                RcuRootProtection { info: Some(info), lease: Some(lease), null_reader: None }
            },
            None => RcuRootProtection { info: None, lease: None, null_reader: Some(reader) },
        }
    }

    /// A single native link load extends topology protection and issues its matching lease.
    /// The owning-slot representation has exactly one source; shared-node graphs
    /// must use a different publication/retirement invariant.
    pub proof fn tracked_protect_link_load<Pred: RcuRootOwnershipPredicate<T, O>, U, A>(
        tracked &mut self,
        ptr: *mut T,
        timestamp: nat,
        message_view: ThreadView,
        before_view: ThreadView,
        after_view: ThreadView,
        start_view: ThreadView,
        source: AllocationId,
        source_ptr: *mut T,
        tracked reader: CpuRcuReaderFragment,
        tracked binding: CpuRcuCoreBinding,
        tracked parent: &RcuRootProtection<U, A>,
    ) -> (tracked res: RcuLinkProtection<T, O>)
        requires
            old(self).inv::<Pred>(),
            parent.inv(),
            parent.info() is Some,
            parent.lease() is Some,
            source == (AllocationId {
                domain: parent.info()->Some_0.domain(),
                object: parent.info()->Some_0.obj(),
            }),
            source_ptr == spec_cast_ptr_to_thin_ptr::<U, T>(parent.info()->Some_0.ptr()),
            reader.participant_id() == parent.reader().participant_id(),
            reader.generation() == parent.reader().generation(),
            reader.participant_view() == parent.reader().participant_view(),
            reader.known_retired() == parent.reader().known_retired(),
            start_view == parent.lease()->Some_0.witness().start_view(),
            load_acquire(
                old(self).points_to(),
                before_view,
                after_view,
                ptr,
                timestamp,
                message_view,
            ),
            source.domain != old(self).root().domain(),
            reader.wf(),
            binding.registry() == old(self).permissions().scheduler(),
            binding.cpu() == reader.cpu(),
            binding.locals_key().len() == 1,
            binding.single_local_id() == reader.participant_id(),
            before_view.contains(start_view),
            start_view.contains(reader.participant_view()),
            old(self).permissions().online().contains(reader.cpu()),
        ensures
            final(self).inv::<Pred>(),
            final(self).points_to() == old(self).points_to(),
            final(self).condition() == old(self).condition(),
            final(self).root() == old(self).root(),
            final(self).retirement() == old(self).retirement(),
            final(self).permissions().registry() == old(self).permissions().registry(),
            final(self).permissions().reclaim_registry() == old(
                self,
            ).permissions().reclaim_registry(),
            final(self).permissions().scheduler() == old(self).permissions().scheduler(),
            final(self).permissions().online() == old(self).permissions().online(),
            res.protection.inv(),
            res.protection.reader() == reader,
            res.observation.inv(),
            res.observation.source == source,
            res.observation.timestamp == timestamp,
            res.observation.reader == reader.participant_id(),
            res.observation.generation == reader.generation(),
            res.observation.start_view == start_view,
            match (res.protection.info(), res.protection.lease(), res.observation.child) {
                (Some(info), Some(lease), Some(child)) => {
                    &&& ptr.addr() != 0
                    &&& equal(info.ptr(), ptr)
                    &&& child == (AllocationId { domain: info.domain(), object: info.obj() })
                    &&& info.domain() == old(self).root().domain()
                    &&& lease.registry() == old(self).permissions().registry()
                    &&& lease.witness().start_view() == start_view
                    &&& Pred::owns(ptr, lease.resource())
                    &&& (old(self).condition())(lease.resource())
                    &&& equal(ptr, res.observation.graph.objects[child])
                },
                (None, None, None) => ptr.addr() == 0,
                _ => false,
            },
    {
        let ghost domain = self.root.domain();
        let ghost graph = owned_link_graph(
            self.root,
            self.retirement.removals().dom(),
            source,
            source_ptr,
        );
        lemma_owned_link_graph(
            self.root,
            self.points_to.hist(),
            self.retirement.removals().dom(),
            source,
            source_ptr,
        );
        assert forall|obj: nat| #[trigger] self.retirement.removals().contains_key(obj) implies {
            &&& self.points_to.get_timestamp(self.retirement.removals()[obj].message_view) == Some(
                self.retirement.removals()[obj].timestamp,
            )
            &&& graph.events.contains_key((source, self.retirement.removals()[obj].timestamp))
            &&& forall|edge: LinkEdge| #[trigger]
                graph.incoming[AllocationId { domain, object: obj }].contains(edge) ==> {
                    &&& edge.0 == source
                    &&& edge.1 < self.retirement.removals()[obj].timestamp
                }
        } by {
            assert forall|edge: LinkEdge| #[trigger]
                graph.incoming[AllocationId { domain, object: obj }].contains(edge) implies {
                &&& edge.0 == source
                &&& edge.1 < self.retirement.removals()[obj].timestamp
            } by {
                assert(self.root.root().publications().contains_pair(edge.1, Some(obj)));
            };
        };
        let ghost (observed, observed_view) = lemma_observed_link_removals(
            &self.points_to,
            graph,
            source,
            domain,
            self.retirement.removals(),
            before_view,
        );
        let ghost (expired, _) = lemma_observed_link_removals(
            &self.points_to,
            graph,
            source,
            domain,
            self.retirement.removals(),
            start_view,
        );
        assert(expired.removed.subset_of(observed.removed)) by {
            assert forall|id: AllocationId|
                expired.removed.contains(id) implies observed.removed.contains(id) by {
                ThreadView::contains_trans(
                    before_view,
                    start_view,
                    self.retirement.removals()[id.object].message_view,
                );
            };
        };
        let ghost guard = TraversalGuard {
            reader: reader.participant_id(),
            expired: expired.removed,
            protected: Set::empty().insert(source),
            observed,
        };
        let tracked info = self.root.tracked_info_at(self.points_to.hist(), timestamp);
        let ghost updated;
        let ghost child;
        let tracked protection = match info {
            Some(info) => {
                info.lemma_address();
                let ghost id = AllocationId { domain, object: info.obj() };
                updated =
                guard.protect_link(
                    graph,
                    source,
                    id,
                    &self.points_to,
                    before_view,
                    after_view,
                    ptr,
                    timestamp,
                    message_view,
                    observed_view,
                );
                child = Some(id);
                if exists|record: RcuRetiredRecord| #[trigger]
                    reader.known_retired().contains(record) && record.domain == domain
                        && record.retire_observation_registry == self.retirement.id() && record.obj
                        == info.obj() {
                    let ghost record = choose|record: RcuRetiredRecord| #[trigger]
                        reader.known_retired().contains(record) && record.domain == domain
                            && record.retire_observation_registry == self.retirement.id()
                            && record.obj == info.obj();
                    let tracked fact = reader.tracked_known_retired(record);
                    fact.lemma_agree(&self.retirement);
                    let tracked facts = reader.tracked_retired_facts_observed_by(start_view);
                    assert(expired.removed.contains(AllocationId { domain, object: record.obj }));
                    assert(false);
                }
                let tracked mut witness = CpuRcuLeaseWitness::tracked_new(
                    reader,
                    binding,
                    domain,
                    self.retirement.id(),
                    info.obj(),
                    start_view,
                );
                self.permissions.lemma_live_allocation(&mut witness);
                let tracked lease = self.permissions.tracked_lease(witness);
                RcuRootProtection { info: Some(info), lease: Some(lease), null_reader: None }
            },
            None => {
                if observed.links.contains_key(source) {
                    self.points_to.get_timestamp_monotonic(before_view, observed_view);
                    assert(observed.seen_at(source) <= timestamp);
                }
                updated =
                TraversalGuard { observed: observed.observe(graph, source, timestamp), ..guard };
                child = None;
                RcuRootProtection { info: None, lease: None, null_reader: Some(reader) }
            },
        };
        RcuLinkProtection {
            protection,
            observation: RcuLinkObservation {
                graph,
                guard: updated,
                source,
                child,
                timestamp,
                reader: reader.participant_id(),
                generation: reader.generation(),
                start_view,
            },
        }
    }

    /// Closes a physical lease and returns the same CPU fragment that began the read.
    pub proof fn tracked_close<Pred: RcuRootOwnershipPredicate<T, O>>(
        tracked &mut self,
        tracked protection: RcuRootProtection<T, O>,
    ) -> (tracked reader: CpuRcuReaderFragment)
        requires
            old(self).inv::<Pred>(),
            protection.inv(),
            protection.lease() matches Some(lease) ==> lease.registry() == old(
                self,
            ).permissions().registry(),
        ensures
            final(self).inv::<Pred>(),
            reader.wf(),
            final(self).points_to() == old(self).points_to(),
            final(self).condition() == old(self).condition(),
            final(self).root() == old(self).root(),
            final(self).retirement() == old(self).retirement(),
            final(self).permissions().registry() == old(self).permissions().registry(),
            final(self).permissions().reclaim_registry() == old(
                self,
            ).permissions().reclaim_registry(),
            final(self).permissions().scheduler() == old(self).permissions().scheduler(),
            final(self).permissions().online() == old(self).permissions().online(),
        returns
            protection.reader(),
    {
        match protection.lease {
            Some(lease) => self.permissions.tracked_return(lease).tracked_into_reader(),
            None => protection.null_reader.tracked_unwrap(),
        }
    }

    /// Publishes fresh ownership after a native release replacement and retires the old root.
    pub proof fn tracked_replace<Pred: RcuRootOwnershipPredicate<T, O>>(
        tracked &mut self,
        before: AtomicPointsTo<*mut T>,
        ptr: *mut T,
        timestamp: nat,
        message_view: ThreadView,
        tracked ownership: Option<O>,
        link_source: Option<(AllocationId, *mut T)>,
    ) -> (tracked retired: Option<RcuRetiredRoot<T>>)
        requires
            old(self).inv_at::<Pred>(before),
            old(self).root().root().current_timestamp() < timestamp,
            old(self).points_to().hist() == before.hist().insert(timestamp, ptr, message_view),
            old(self).points_to().get_timestamp(message_view) == Some(timestamp),
            forall|view: ThreadView| #[trigger]
                before.get_timestamp(view) == old(self).points_to().get_timestamp(view),
            (ownership is Some) == (ptr.addr() != 0),
            ownership matches Some(owned) ==> Pred::owns(ptr, owned) && (old(self).condition())(
                owned,
            ),
            link_source matches Some((source, _)) ==> source.domain != old(self).root().domain()
                && ptr.addr() == 0,
        ensures
            final(self).inv::<Pred>(),
            final(self).points_to() == old(self).points_to(),
            final(self).condition() == old(self).condition(),
            final(self).root().domain() == old(self).root().domain(),
            final(self).retirement().id() == old(self).retirement().id(),
            final(self).permissions().registry() == old(self).permissions().registry(),
            final(self).permissions().reclaim_registry() == old(
                self,
            ).permissions().reclaim_registry(),
            final(self).permissions().scheduler() == old(self).permissions().scheduler(),
            final(self).permissions().online() == old(self).permissions().online(),
            (retired is Some) == (old(self).root().current_owned() is Some),
            retired matches Some(retired) ==> {
                &&& retired.inv()
                &&& (retired.link_removal() is Some) == (link_source is Some)
                &&& retired.link_removal() matches Some(link) ==> link.source
                    == link_source->Some_0.0
                &&& equal(
                    retired.ptr(),
                    before.hist().value(old(self).root().root().current_timestamp()),
                )
                &&& retired.registry() == final(self).permissions().reclaim_registry()
                &&& retired.record().domain == final(self).root().domain()
                &&& retired.record().retire_observation_registry == final(self).retirement().id()
                &&& retired.record().removal == (RcuRemovalObservation {
                    root: final(self).root().domain(),
                    timestamp,
                    message_view,
                })
            },
    {
        let ghost original_root = self.root;
        let ghost original_permissions = self.permissions;
        let tracked unit = match ownership {
            Some(_) => Some(()),
            None => None,
        };
        let tracked previous = self.root.tracked_push_fresh(
            before.hist(),
            self.points_to.hist(),
            timestamp,
            ptr,
            message_view,
            unit,
        );
        match ownership {
            Some(owned) => {
                let ghost obj = self.root.current_owned()->Some_0.block_info().obj();
                self.permissions.tracked_insert(obj, ptr, owned);
            },
            None => {},
        }
        let tracked retired = match previous {
            Some(previous) => {
                let ghost obj = previous.block_info().obj();
                original_permissions.lemma_unretired_live(obj);
                assert(equal(original_permissions.ptr(obj), original_root.infos()[obj].ptr()));
                assert(equal(original_root.infos()[obj].ptr(), previous.block_info().ptr()));
                let tracked claim = self.permissions.tracked_take_claim(obj);
                original_root.root().lemma_domain_identity();
                self.root.root().lemma_domain_identity();
                previous.retire_perm().lemma_same_domain(
                    original_root.root().domain_auth(),
                    self.root.root().domain_auth(),
                );
                assert forall|ts: nat| #[trigger]
                    self.root.root().publications().contains_pair(ts, Some(obj)) implies ts
                    < timestamp by {
                    if ts != timestamp {
                        assert(before.hist().contains_timestamp(ts));
                    } else {
                        assert(!original_root.infos().contains_key(
                            self.root.current_owned()->Some_0.block_info().obj(),
                        ));
                    }
                };
                let ghost removal = RcuRemovalObservation {
                    root: self.root.domain(),
                    timestamp,
                    message_view,
                };
                // Establish the no-incoming-edge premise before issuing retirement.
                let ghost link_removal = match link_source {
                    Some((source, source_ptr)) => {
                        let graph = owned_link_graph(
                            self.root,
                            self.retirement.removals().dom(),
                            source,
                            source_ptr,
                        );
                        lemma_owned_link_graph(
                            self.root,
                            self.points_to.hist(),
                            self.retirement.removals().dom(),
                            source,
                            source_ptr,
                        );
                        let child = AllocationId { domain: self.root.domain(), object: obj };
                        let observed = SeenRemoved {
                            removed: Set::empty(),
                            links: Map::empty().insert(source, timestamp),
                        };
                        assert forall|edge: LinkEdge| #[trigger]
                            graph.incoming[child].contains(edge) implies observed.dead(edge) by {
                            assert(self.root.root().publications().contains_pair(
                                edge.1,
                                Some(obj),
                            ));
                            assert(edge.0 == source && edge.1 < timestamp);
                        };
                        let (observed, graph) = observed.retire(graph, child);
                        Some(RcuLinkRemoval { graph, observed, source, child, removal })
                    },
                    None => None,
                };
                let tracked (registration, fact) = self.retirement.tracked_retire_root(
                    &self.root,
                    previous,
                    self.points_to.hist(),
                    removal,
                );
                assert(equal(claim.ptr(), registration.ptr()));
                Some(RcuRetiredRoot { registration, claim, fact, link_removal })
            },
            None => None,
        };
        assert forall|obj: nat| #[trigger] self.permissions.keys().contains(obj) implies {
            &&& self.root.infos().contains_key(obj)
            &&& equal(self.permissions.ptr(obj), self.root.infos()[obj].ptr())
            &&& Pred::owns(self.root.infos()[obj].ptr(), self.permissions.ownership(obj))
            &&& (self.condition())(self.permissions.ownership(obj))
        } by {
            if original_permissions.keys().contains(obj) {
                assert(original_root.infos().contains_key(obj));
            } else {
                assert(self.root.current_owned() is Some);
                assert(obj == self.root.current_owned()->Some_0.block_info().obj());
            }
        };
        assert forall|obj: nat| #[trigger] self.retirement.removals().contains_key(obj) implies {
            let removal = self.retirement.removals()[obj];
            &&& removal.root == self.root.domain()
            &&& self.points_to.hist().contains_timestamp(removal.timestamp)
            &&& self.points_to.get_timestamp(removal.message_view) == Some(removal.timestamp)
            &&& forall|ts: nat| #[trigger]
                self.root.root().publications().contains_pair(ts, Some(obj)) ==> ts
                    < removal.timestamp
        } by {
            if old(self).retirement().removals().contains_key(obj) {
                assert(original_root.infos().contains_key(obj));
                assert forall|ts: nat| #[trigger]
                    self.root.root().publications().contains_pair(ts, Some(obj)) implies ts
                    < self.retirement.removals()[obj].timestamp by {
                    assert(ts != timestamp);
                    assert(original_root.root().publications().contains_pair(ts, Some(obj)));
                };
            } else {
                assert(previous is Some);
                assert(obj == previous->Some_0.block_info().obj());
            }
        };
        assert(self.permissions.unretired() =~= match self.root.current_owned() {
            Some(owned) => Set::empty().insert(owned.block_info().obj()),
            None => Set::empty(),
        });
        retired
    }

    /// Recovers the physical resource for the callback's exact pointer, once.
    pub proof fn tracked_reclaim<Pred: RcuRootOwnershipPredicate<T, O>>(
        tracked &mut self,
        tracked retired: RcuRetiredRoot<T>,
        tracked permit: RcuReclaimPermit,
    ) -> (tracked ownership: O)
        requires
            old(self).inv::<Pred>(),
            retired.inv(),
            permit.inv(),
            retired.registry() == old(self).permissions().reclaim_registry(),
            retired.record() == permit.summary().retired,
            permit.summary().scheduler == old(self).permissions().scheduler(),
            permit.summary().retired.domain == old(self).root().domain(),
            permit.summary().retired.retire_observation_registry == old(self).retirement().id(),
            permit.online() == old(self).permissions().online(),
        ensures
            final(self).inv::<Pred>(),
            Pred::owns(retired.ptr(), ownership),
            final(self).points_to() == old(self).points_to(),
            final(self).condition() == old(self).condition(),
            final(self).root() == old(self).root(),
            final(self).retirement() == old(self).retirement(),
            final(self).permissions().registry() == old(self).permissions().registry(),
            final(self).permissions().reclaim_registry() == old(
                self,
            ).permissions().reclaim_registry(),
            final(self).permissions().scheduler() == old(self).permissions().scheduler(),
            final(self).permissions().online() == old(self).permissions().online(),
    {
        self.permissions.lemma_claim_agrees(&retired.claim);
        self.permissions.tracked_reclaim(retired.registration, retired.claim, permit)
    }
}

} // verus!
