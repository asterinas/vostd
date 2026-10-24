// SPDX-License-Identifier: MPL-2.0
//! Physical read leases coupled to canonical CPU reader generations.
//!
//! # Verified Properties
//! Each outstanding physical lease retains a CPU reader fragment in its
//! registry. Completed grace-period evidence excludes every matching active
//! lease before the full resource is recovered. Allocation IDs cannot be
//! inserted again after reclamation. Returning a lease consumes its exact
//! authoritative binding and returns its CPU fragment.
use vstd::{
    prelude::*,
    resource::{
        Loc,
        map::{GhostMapAuth, GhostPointsTo},
    },
};
use vstd_extra::{
    atomic_irc11::ThreadView,
    ownership::Inv,
    rcu_read_lease::{RcuActiveReadLeaseRecord, RcuReadLeaseRegistry, RcuRegisteredReadLease},
};

use super::{
    cpu::{CpuRcuCoreBinding, CpuRcuReaderFragment},
    grace_period::RcuReclaimPermit,
    retirement::{RcuRetiredRecord, RcuRetiredRegistration},
};
use crate::cpu::CpuId;

verus! {

broadcast use {vstd::set::group_set_lemmas, vstd::thread_view::group_thread_view_axioms};

/// CPU authority retained alongside an outstanding physical lease.
pub tracked struct CpuRcuLeaseWitness {
    reader: CpuRcuReaderFragment,
    binding: CpuRcuCoreBinding,
    ghost domain: Loc,
    ghost observations: Loc,
    ghost obj: nat,
    ghost start_view: ThreadView,
}

impl Inv for CpuRcuLeaseWitness {
    closed spec fn inv(self) -> bool {
        &&& self.reader.wf()
        &&& self.binding.cpu() == self.reader.cpu()
        &&& self.binding.locals_key().len() == 1
        &&& self.binding.single_local_id() == self.reader.participant_id()
        &&& self.start_view.contains(self.reader.participant_view())
        &&& forall|record: RcuRetiredRecord| #[trigger]
            self.reader.known_retired().contains(record) && record.domain == self.domain
                && record.retire_observation_registry == self.observations ==> record.obj
                != self.obj
    }
}

impl CpuRcuLeaseWitness {
    /// Couples a protected allocation to one CPU's live reader resource.
    ///
    /// The atomic-load adapter must discharge the non-expiration premise using
    /// native load coherence and the certified root removal history.
    pub proof fn tracked_new(
        tracked reader: CpuRcuReaderFragment,
        tracked binding: CpuRcuCoreBinding,
        domain: Loc,
        observations: Loc,
        obj: nat,
        start_view: ThreadView,
    ) -> (tracked res: Self)
        requires
            reader.wf(),
            binding.cpu() == reader.cpu(),
            binding.locals_key().len() == 1,
            binding.single_local_id() == reader.participant_id(),
            start_view.contains(reader.participant_view()),
            forall|record: RcuRetiredRecord| #[trigger]
                reader.known_retired().contains(record) && record.domain == domain
                    && record.retire_observation_registry == observations ==> record.obj != obj,
        ensures
            res.inv(),
            res.reader() == reader,
            res.scheduler() == binding.registry(),
            res.domain() == domain,
            res.observations() == observations,
            res.obj() == obj,
            res.start_view() == start_view,
    {
        Self { reader, binding, domain, observations, obj, start_view }
    }

    /// Exact reader resource that must eventually return to its CPU.
    pub closed spec fn reader(self) -> CpuRcuReaderFragment {
        self.reader
    }

    /// Canonical scheduler registry.
    pub closed spec fn scheduler(self) -> Loc {
        self.binding.registry()
    }

    /// Allocation domain.
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    /// Retirement observation registry for this root.
    pub closed spec fn observations(self) -> Loc {
        self.observations
    }

    /// Protected allocation ID.
    pub closed spec fn obj(self) -> nat {
        self.obj
    }

    /// Native view at the beginning of this read.
    pub closed spec fn start_view(self) -> ThreadView {
        self.start_view
    }

    /// Ends this protection witness while preserving its linear CPU resource.
    pub proof fn tracked_into_reader(tracked self) -> (tracked res: CpuRcuReaderFragment)
        requires
            self.inv(),
        ensures
            res.wf(),
        returns
            self.reader(),
    {
        self.reader
    }

    /// A matching completed grace period cannot coexist with this live lease.
    pub proof fn lemma_excluded(tracked &mut self, tracked permit: &RcuReclaimPermit)
        requires
            old(self).inv(),
            permit.inv(),
            permit.summary().scheduler == old(self).scheduler(),
            permit.summary().retired.domain == old(self).domain(),
            permit.summary().retired.retire_observation_registry == old(self).observations(),
            permit.summary().retired.obj == old(self).obj(),
            permit.online().contains(old(self).reader().cpu()),
        ensures
            false,
    {
        let tracked report = permit.tracked_report(self.reader.cpu());
        report.lemma_same_participant_as_binding(&self.binding);
        report.lemma_later_reader_ref(&mut self.reader);
        assert(self.reader.known_retired().contains(permit.summary().retired));
    }
}

/// Physical lease and unique token for its entry in the root's active registry.
pub tracked struct RcuRootReadLease<O> {
    lease: RcuRegisteredReadLease<nat, O>,
    active: GhostPointsTo<nat, RcuActiveReadLeaseRecord<nat, CpuRcuLeaseWitness>>,
}

impl<O> Inv for RcuRootReadLease<O> {
    closed spec fn inv(self) -> bool {
        &&& self.active.key() == self.lease.lease_id()
        &&& self.active.value().key() == self.lease.key()
        &&& self.active.value().accumulator_id() == self.lease.accumulator_id()
        &&& self.active.value().fraction() == self.lease.fraction()
    }
}

impl<O> RcuRootReadLease<O> {
    /// Allocation protected by this lease.
    pub closed spec fn obj(self) -> nat {
        self.lease.key()
    }

    /// Authority to which this lease must be returned.
    pub closed spec fn registry(self) -> Loc {
        self.active.id()
    }

    /// Physical permission borrowed by a reader's get operation.
    pub closed spec fn resource(self) -> O {
        self.lease.resource()
    }

    /// CPU witness retained in the authoritative active record.
    pub closed spec fn witness(self) -> CpuRcuLeaseWitness {
        self.active.value().witness()
    }

    /// Borrows physical permission without transferring ownership out of the lease.
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &O)
        ensures
            *res == self.resource(),
    {
        self.lease.tracked_borrow()
    }
}

/// Unique authority to recover one allocation's exact pointer and permission.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuReclaimClaim<T> {
    entry: GhostPointsTo<nat, Option<*mut T>>,
}

impl<T> Inv for RcuReclaimClaim<T> {
    closed spec fn inv(self) -> bool {
        self.entry.value() is Some
    }
}

impl<T> RcuReclaimClaim<T> {
    /// Allocation identity for which the claim is unique.
    pub closed spec fn obj(self) -> nat {
        self.entry.key()
    }

    /// Root registry that must redeem this claim.
    pub closed spec fn registry(self) -> Loc {
        self.entry.id()
    }

    /// Complete pointer, including provenance, certified by the registry.
    pub closed spec fn ptr(self) -> *mut T {
        self.entry.value()->Some_0
    }
}

/// Root-owned physical resources and authoritative live-lease accounting.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRootPermissionState<T, O> {
    pools: RcuReadLeaseRegistry<nat, O, CpuRcuLeaseWitness>,
    active: GhostMapAuth<nat, RcuActiveReadLeaseRecord<nat, CpuRcuLeaseWitness>>,
    reclaimed: Map<nat, RcuReclaimPermit>,
    claims: GhostMapAuth<nat, Option<*mut T>>,
    unretired: Map<nat, RcuReclaimClaim<T>>,
    ghost allocated: Set<nat>,
    ghost scheduler: Loc,
    ghost domain: Loc,
    ghost observations: Loc,
    ghost online: Set<CpuId>,
}

impl<T, O> Inv for RcuRootPermissionState<T, O> {
    closed spec fn inv(self) -> bool {
        &&& self.pools.wf()
        &&& self.pools.keys().union(self.reclaimed.dom()) == self.allocated
        &&& self.pools.keys().disjoint(self.reclaimed.dom())
        &&& self.claims@.dom() == self.allocated
        &&& forall|obj: nat| #[trigger]
            self.claims@.contains_key(obj) ==> {
                (self.claims@[obj] is Some) == self.pools.keys().contains(obj)
            }
        &&& self.unretired.dom().subset_of(self.pools.keys())
        &&& forall|obj: nat| #[trigger]
            self.unretired.contains_key(obj) ==> {
                let claim = self.unretired[obj];
                &&& claim.inv()
                &&& claim.obj() == obj
                &&& claim.registry() == self.claims.id()
                &&& self.claims@[obj] == Some(claim.ptr())
            }
        &&& forall|obj: nat| #[trigger]
            self.reclaimed.contains_key(obj) ==> {
                let permit = self.reclaimed[obj];
                &&& permit.inv()
                &&& permit.summary().retired.obj == obj
                &&& permit.summary().retired.domain == self.domain
                &&& permit.summary().retired.retire_observation_registry == self.observations
                &&& permit.summary().scheduler == self.scheduler
                &&& permit.online() == self.online
            }
        &&& self.active@.dom() == self.pools.active_ids()
        &&& forall|id: nat| #[trigger]
            self.pools.active_ids().contains(id) ==> {
                let record = self.pools.active_record(id);
                let witness = record.witness();
                &&& witness.inv()
                &&& witness.scheduler() == self.scheduler
                &&& witness.domain() == self.domain
                &&& witness.observations() == self.observations
                &&& witness.obj() == record.key()
                &&& self.online.contains(witness.reader().cpu())
                &&& self.active@[id] == record
            }
    }
}

impl<T, O> RcuRootPermissionState<T, O> {
    /// Creates an empty registry for a fixed scheduler, root, and online CPU set.
    pub proof fn tracked_empty(
        scheduler: Loc,
        domain: Loc,
        observations: Loc,
        online: Set<CpuId>,
    ) -> (tracked res: Self)
        ensures
            res.inv(),
            res.keys() == Set::<nat>::empty(),
            res.allocations() == Set::<nat>::empty(),
            res.unretired() == Set::<nat>::empty(),
            res.scheduler() == scheduler,
            res.domain() == domain,
            res.observations() == observations,
            res.online() == online,
    {
        let tracked pools = RcuReadLeaseRegistry::empty();
        let tracked (active, _) = GhostMapAuth::new(Map::empty());
        let tracked (claims, _) = GhostMapAuth::new(Map::empty());
        let tracked res = Self {
            pools,
            active,
            reclaimed: Map::tracked_empty(),
            allocated: Set::empty(),
            claims,
            unretired: Map::tracked_empty(),
            scheduler,
            domain,
            observations,
            online,
        };
        assert(res.pools.keys().union(res.reclaimed.dom()) =~= res.allocated);
        res
    }

    /// Allocations whose physical permission has not yet been recovered.
    pub closed spec fn keys(self) -> Set<nat> {
        self.pools.keys()
    }

    /// All allocation IDs ever inserted, including reclaimed allocations.
    pub closed spec fn allocations(self) -> Set<nat> {
        self.allocated
    }

    /// Identity of the active-record registry.
    pub closed spec fn registry(self) -> Loc {
        self.active.id()
    }

    /// Unique-claim registry, retained across allocation and reclamation.
    pub closed spec fn reclaim_registry(self) -> Loc {
        self.claims.id()
    }

    /// Exact pointer associated with an unreclaimed allocation.
    pub closed spec fn ptr(self, obj: nat) -> *mut T {
        self.claims@[obj]->Some_0
    }

    /// Allocations whose unique reclaim claim is still retained by the root.
    pub closed spec fn unretired(self) -> Set<nat> {
        self.unretired.dom()
    }

    /// Canonical CPU scheduler identity.
    pub closed spec fn scheduler(self) -> Loc {
        self.scheduler
    }

    /// Root allocation domain.
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    /// Retirement certificate authority.
    pub closed spec fn observations(self) -> Loc {
        self.observations
    }

    /// Stable CPU set containing every reader allowed to acquire a lease.
    pub closed spec fn online(self) -> Set<CpuId> {
        self.online
    }

    /// Full permission stored under a live allocation ID.
    pub closed spec fn ownership(self, obj: nat) -> O {
        self.pools.accumulator(obj).resource()
    }

    /// Whether an allocation still has an outstanding physical lease.
    pub closed spec fn has_active(self, obj: nat) -> bool {
        self.pools.has_active(obj)
    }

    /// A claim still retained by the root names an unreclaimed physical pool.
    pub proof fn lemma_unretired_live(self, obj: nat)
        requires
            self.inv(),
            self.unretired().contains(obj),
        ensures
            self.keys().contains(obj),
    {
    }

    /// Inserts a fresh allocation; reclaiming an ID never makes it reusable.
    pub proof fn tracked_insert(tracked &mut self, obj: nat, ptr: *mut T, tracked ownership: O)
        requires
            old(self).inv(),
            !old(self).allocations().contains(obj),
        ensures
            final(self).inv(),
            final(self).keys() == old(self).keys().insert(obj),
            final(self).allocations() == old(self).allocations().insert(obj),
            final(self).ownership(obj) == ownership,
            final(self).ptr(obj) == ptr,
            final(self).unretired() == old(self).unretired().insert(obj),
            final(self).reclaim_registry() == old(self).reclaim_registry(),
            final(self).registry() == old(self).registry(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).domain() == old(self).domain(),
            final(self).observations() == old(self).observations(),
            final(self).online() == old(self).online(),
            forall|other: nat| #[trigger]
                old(self).keys().contains(other) ==> final(self).ownership(other) == old(
                    self,
                ).ownership(other),
            forall|other: nat| #[trigger]
                old(self).keys().contains(other) ==> equal(
                    final(self).ptr(other),
                    old(self).ptr(other),
                ),
    {
        self.pools.lemma_all_contains_iff_keys();
        self.pools.insert(obj, ownership);
        let tracked entry = self.claims.insert(obj, Some(ptr));
        self.unretired.tracked_insert(obj, RcuReclaimClaim { entry });
        self.allocated = self.allocated.insert(obj);
        assert(self.pools.keys().union(self.reclaimed.dom()) =~= self.allocated);
        assert(self.pools.keys().disjoint(self.reclaimed.dom()));
    }

    /// Issues a lease only with a non-expired, canonical CPU witness.
    pub proof fn tracked_lease(
        tracked &mut self,
        tracked witness: CpuRcuLeaseWitness,
    ) -> (tracked res: RcuRootReadLease<O>)
        requires
            old(self).inv(),
            old(self).keys().contains(witness.obj()),
            witness.inv(),
            witness.scheduler() == old(self).scheduler(),
            witness.domain() == old(self).domain(),
            witness.observations() == old(self).observations(),
            old(self).online().contains(witness.reader().cpu()),
        ensures
            final(self).inv(),
            final(self).keys() == old(self).keys(),
            final(self).allocations() == old(self).allocations(),
            final(self).registry() == old(self).registry(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).domain() == old(self).domain(),
            final(self).observations() == old(self).observations(),
            final(self).online() == old(self).online(),
            forall|obj: nat| #[trigger]
                old(self).keys().contains(obj) ==> final(self).ownership(obj) == old(
                    self,
                ).ownership(obj),
            res.inv(),
            res.registry() == old(self).registry(),
            res.obj() == witness.obj(),
            res.witness() == witness,
            res.resource() == old(self).ownership(witness.obj()),
            final(self).unretired() == old(self).unretired(),
            final(self).reclaim_registry() == old(self).reclaim_registry(),
            forall|obj: nat| #[trigger]
                old(self).keys().contains(obj) ==> equal(final(self).ptr(obj), old(self).ptr(obj)),
    {
        self.pools.lemma_all_contains_iff_keys();
        let tracked lease = self.pools.split_lease(witness.obj(), witness);
        let ghost id = lease.lease_id();
        let ghost binding = self.pools.active_record(id);
        let tracked active = self.active.insert(id, binding);
        assert forall|other: nat| #[trigger] self.pools.active_ids().contains(other) implies {
            let record = self.pools.active_record(other);
            let w = record.witness();
            &&& w.inv()
            &&& w.scheduler() == self.scheduler
            &&& w.domain() == self.domain
            &&& w.observations() == self.observations
            &&& w.obj() == record.key()
            &&& self.online.contains(w.reader().cpu())
            &&& self.active@[other] == record
        } by {
            if other != id {
                assert(old(self).pools.active_ids().contains(other));
            }
        };
        RcuRootReadLease { lease, active }
    }

    /// Returns the exact active lease and restores its CPU resource to the caller.
    pub proof fn tracked_return(
        tracked &mut self,
        tracked lease: RcuRootReadLease<O>,
    ) -> (tracked witness: CpuRcuLeaseWitness)
        requires
            old(self).inv(),
            lease.inv(),
            lease.registry() == old(self).registry(),
        ensures
            final(self).inv(),
            witness.inv(),
            final(self).keys() == old(self).keys(),
            final(self).allocations() == old(self).allocations(),
            final(self).registry() == old(self).registry(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).domain() == old(self).domain(),
            final(self).observations() == old(self).observations(),
            final(self).online() == old(self).online(),
            forall|obj: nat| #[trigger]
                old(self).keys().contains(obj) ==> final(self).ownership(obj) == old(
                    self,
                ).ownership(obj),
            final(self).unretired() == old(self).unretired(),
            final(self).reclaim_registry() == old(self).reclaim_registry(),
            forall|obj: nat| #[trigger]
                old(self).keys().contains(obj) ==> equal(final(self).ptr(obj), old(self).ptr(obj)),
        returns
            lease.witness(),
    {
        self.pools.lemma_all_contains_iff_keys();
        lease.active.agree(&self.active);
        let tracked witness = self.pools.return_lease(lease.lease);
        self.active.delete_points_to(lease.active);
        witness
    }

    /// Transfers the root's unique claim to the pending reclamation callback.
    pub proof fn tracked_take_claim(tracked &mut self, obj: nat) -> (tracked res: RcuReclaimClaim<
        T,
    >)
        requires
            old(self).inv(),
            old(self).unretired().contains(obj),
        ensures
            final(self).inv(),
            final(self).unretired() == old(self).unretired().remove(obj),
            final(self).keys() == old(self).keys(),
            final(self).allocations() == old(self).allocations(),
            final(self).registry() == old(self).registry(),
            final(self).reclaim_registry() == old(self).reclaim_registry(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).domain() == old(self).domain(),
            final(self).observations() == old(self).observations(),
            final(self).online() == old(self).online(),
            forall|key: nat| #[trigger]
                old(self).keys().contains(key) ==> {
                    &&& final(self).ownership(key) == old(self).ownership(key)
                    &&& equal(final(self).ptr(key), old(self).ptr(key))
                },
            res.inv(),
            res.obj() == obj,
            res.registry() == old(self).reclaim_registry(),
            equal(res.ptr(), old(self).ptr(obj)),
    {
        self.unretired.tracked_remove(obj)
    }

    /// Checks a callback's exact pointer against the root's authoritative claim map.
    pub proof fn lemma_claim_agrees(tracked &self, tracked claim: &RcuReclaimClaim<T>)
        requires
            self.inv(),
            claim.inv(),
            claim.registry() == self.reclaim_registry(),
        ensures
            self.keys().contains(claim.obj()),
            equal(self.ptr(claim.obj()), claim.ptr()),
    {
        claim.entry.agree(&self.claims);
    }

    /// Rules out a stale history message for an already reclaimed allocation.
    ///
    /// Retained completion evidence handles arbitrarily late weak loads; the
    /// allocation ID is never forgotten when its physical pool is removed.
    pub proof fn lemma_live_allocation(tracked &self, tracked witness: &mut CpuRcuLeaseWitness)
        requires
            self.inv(),
            old(witness).inv(),
            self.allocations().contains(old(witness).obj()),
            old(witness).scheduler() == self.scheduler(),
            old(witness).domain() == self.domain(),
            old(witness).observations() == self.observations(),
            self.online().contains(old(witness).reader().cpu()),
        ensures
            *final(witness) == *old(witness),
            self.keys().contains(final(witness).obj()),
    {
        if !self.keys().contains(witness.obj()) {
            let tracked permit = self.reclaimed.tracked_borrow(witness.obj());
            witness.lemma_excluded(permit);
        }
    }

    /// Derives absence of live leases from grace-period reports, not an assumption.
    pub proof fn lemma_no_active(tracked &mut self, tracked permit: &RcuReclaimPermit)
        requires
            old(self).inv(),
            permit.inv(),
            permit.summary().scheduler == old(self).scheduler(),
            permit.summary().retired.domain == old(self).domain(),
            permit.summary().retired.retire_observation_registry == old(self).observations(),
            permit.online() == old(self).online(),
        ensures
            *final(self) == *old(self),
            !final(self).has_active(permit.summary().retired.obj),
    {
        let ghost obj = permit.summary().retired.obj;
        if self.pools.has_active(obj) {
            let ghost id = choose|id: nat| #[trigger]
                self.pools.active_ids().contains(id) && self.pools.active_record(id).key() == obj;
            let tracked witness = self.pools.tracked_borrow_active_witness_mut(id);
            witness.lemma_excluded(permit);
        }
    }

    /// Consumes the retired registration and recovers its full physical permission once.
    pub proof fn tracked_reclaim(
        tracked &mut self,
        tracked retired: RcuRetiredRegistration<T>,
        tracked claim: RcuReclaimClaim<T>,
        tracked permit: RcuReclaimPermit,
    ) -> (tracked ownership: O)
        requires
            old(self).inv(),
            permit.inv(),
            retired.record() == permit.summary().retired,
            permit.summary().scheduler == old(self).scheduler(),
            permit.summary().retired.domain == old(self).domain(),
            permit.summary().retired.retire_observation_registry == old(self).observations(),
            permit.online() == old(self).online(),
            old(self).keys().contains(retired.record().obj),
            claim.inv(),
            claim.registry() == old(self).reclaim_registry(),
            claim.obj() == retired.record().obj,
            claim.ptr() == retired.ptr(),
        ensures
            final(self).inv(),
            final(self).keys() == old(self).keys().remove(retired.record().obj),
            final(self).allocations() == old(self).allocations(),
            final(self).registry() == old(self).registry(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).domain() == old(self).domain(),
            final(self).observations() == old(self).observations(),
            final(self).online() == old(self).online(),
            final(self).reclaim_registry() == old(self).reclaim_registry(),
            final(self).unretired() == old(self).unretired(),
            forall|obj: nat| #[trigger]
                final(self).keys().contains(obj) ==> final(self).ownership(obj) == old(
                    self,
                ).ownership(obj),
            forall|obj: nat| #[trigger]
                final(self).keys().contains(obj) ==> equal(
                    final(self).ptr(obj),
                    old(self).ptr(obj),
                ),
        returns
            old(self).ownership(retired.record().obj),
    {
        self.lemma_no_active(&permit);
        self.pools.lemma_all_contains_iff_keys();
        let ghost obj = retired.record().obj;
        let tracked mut claim = claim;
        claim.entry.agree(&self.claims);
        if self.unretired.contains_key(obj) {
            let tracked retained = self.unretired.tracked_borrow(obj);
            claim.entry.disjoint(&retained.entry);
            assert(false);
        }
        claim.entry.update(&mut self.claims, None);
        assert(self.claims@.dom() =~= self.allocated);
        let tracked ownership = self.pools.reclaim(obj);
        self.reclaimed.tracked_insert(obj, permit);
        assert(self.pools.keys().union(self.reclaimed.dom()) =~= self.allocated);
        assert(self.pools.keys().disjoint(self.reclaimed.dom()));
        assert forall|other: nat| #[trigger] self.reclaimed.contains_key(other) implies {
            let saved = self.reclaimed[other];
            &&& saved.inv()
            &&& saved.summary().retired.obj == other
            &&& saved.summary().retired.domain == self.domain
            &&& saved.summary().retired.retire_observation_registry == self.observations
            &&& saved.summary().scheduler == self.scheduler
            &&& saved.online() == self.online
        } by {
            if other != obj {
                assert(old(self).reclaimed.contains_key(other));
            }
        };
        assert forall|other: nat| #[trigger] self.claims@.contains_key(other) implies (
        self.claims@[other] is Some) == self.pools.keys().contains(other) by {
            if other != obj {
                assert(old(self).claims@.contains_key(other));
            }
        };
        assert(self.unretired.dom().subset_of(self.pools.keys()));
        assert forall|other: nat| #[trigger] self.unretired.contains_key(other) implies {
            let saved = self.unretired[other];
            &&& saved.inv()
            &&& saved.obj() == other
            &&& saved.registry() == self.claims.id()
            &&& self.claims@[other] == Some(saved.ptr())
        } by {
            assert(other != obj);
            assert(old(self).unretired.contains_key(other));
        };
        ownership
    }
}

} // verus!
