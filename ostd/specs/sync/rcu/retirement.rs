// SPDX-License-Identifier: MPL-2.0
//! Persistent root-retirement observations for CPU reports and callbacks.
//!
//! # Verified Properties
//! A retirement consumes the root's previous linear registration and records
//! the exact removal message in a persistent registry. All publications of that
//! allocation precede the recorded timestamp. This certifies root detachment,
//! not removal of incoming links and not permission to reclaim physical memory.
use vstd::{
    prelude::*,
    resource::{
        Loc,
        map::{GhostMapAuth, GhostPersistentPointsTo},
    },
};
use vstd_extra::{
    atomic_irc11::{AtomicHistory, ThreadView as Irc11ThreadView},
    ownership::Inv,
    rcu_objects::{
        RcuOwnedObject,
        owned_root::{RcuRootOwnedGhost, rcu_owned_root_history_inv},
    },
};

verus! {

broadcast use vstd::set::group_set_lemmas;

/// Description of a removal message; the description alone is not a certificate.
pub ghost struct RcuRemovalObservation {
    pub root: Loc,
    pub timestamp: nat,
    pub message_view: Irc11ThreadView,
}

impl RcuRemovalObservation {
    /// A native view covers the removal's publication view.
    pub open spec fn observed_by(self, view: Irc11ThreadView) -> bool {
        view.contains(self.message_view)
    }
}

/// Full identity of a retirement, including the registry that certified it.
pub ghost struct RcuRetiredRecord {
    pub domain: Loc,
    pub obj: nat,
    pub removal: RcuRemovalObservation,
    pub retire_observation_registry: Loc,
}

/// Every retirement record's removal observation is covered by `view`.
pub open spec fn records_observed(records: Set<RcuRetiredRecord>, view: Irc11ThreadView) -> bool {
    forall|record: RcuRetiredRecord| #[trigger]
        records.contains(record) ==> record.removal.observed_by(view)
}

/// Persistent certificate issued by one retirement authority.
pub tracked struct RcuRetiredFact {
    ghost domain: Loc,
    observation: GhostPersistentPointsTo<nat, RcuRemovalObservation>,
}

impl RcuRetiredFact {
    /// Domain of the detached allocation.
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    /// Allocation identity, independent of its reused address.
    pub closed spec fn obj(self) -> nat {
        self.observation.key()
    }

    /// Exact removal message.
    pub closed spec fn removal(self) -> RcuRemovalObservation {
        self.observation.value()
    }

    /// Authority that certified this retirement.
    pub closed spec fn retire_observation_registry(self) -> Loc {
        self.observation.id()
    }

    /// This wrapper imposes no additional conditions beyond its private constructor.
    pub closed spec fn wf(self) -> bool {
        true
    }

    /// Complete retirement descriptor.
    pub open spec fn record(self) -> RcuRetiredRecord {
        RcuRetiredRecord {
            domain: self.domain(),
            obj: self.obj(),
            removal: self.removal(),
            retire_observation_registry: self.retire_observation_registry(),
        }
    }

    /// Copies persistent evidence without copying the linear retirement resource.
    pub proof fn tracked_duplicate(tracked &self) -> (tracked res: Self)
        ensures
            res.wf(),
            res.record() == self.record(),
            res.domain() == self.domain(),
            res.obj() == self.obj(),
            res.removal() == self.removal(),
            res.retire_observation_registry() == self.retire_observation_registry(),
    {
        Self { domain: self.domain, observation: self.observation.duplicate() }
    }

    /// Agrees the certificate with its issuing authority.
    pub proof fn lemma_agree(tracked &self, tracked authority: &RcuRetirementAuth)
        requires
            self.retire_observation_registry() == authority.id(),
        ensures
            authority.removals().contains_pair(self.obj(), self.removal()),
    {
        self.observation.agree(&authority.observations);
    }
}

/// Linear registration retained after retirement, without physical permission.
///
/// There is deliberately no reclamation method: a completed grace period and
/// the matching physical-permission registry are still required.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRetiredRegistration<T> {
    registration: RcuOwnedObject<T, ()>,
    fact: RcuRetiredFact,
}

impl<T> RcuRetiredRegistration<T> {
    /// Certified retirement associated with this linear registration.
    pub closed spec fn record(self) -> RcuRetiredRecord {
        self.fact.record()
    }

    /// Exact pointer, including provenance.
    pub closed spec fn ptr(self) -> *mut T {
        self.registration.block_info().ptr()
    }
}

/// Monotone retirement registry for one typed root.
pub tracked struct RcuRetirementAuth {
    ghost domain: Loc,
    observations: GhostMapAuth<nat, RcuRemovalObservation>,
}

impl RcuRetirementAuth {
    /// Creates an empty registry; the domain is subsequently checked against each root.
    pub proof fn tracked_new(domain: Loc) -> (tracked res: Self)
        ensures
            res.domain() == domain,
            res.removals() == Map::<nat, RcuRemovalObservation>::empty(),
    {
        let tracked (observations, _) = GhostMapAuth::new(Map::empty());
        Self { domain, observations }
    }

    /// Stable allocation domain.
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    /// Stable identity of this observation registry.
    pub closed spec fn id(self) -> Loc {
        self.observations.id()
    }

    /// All certified removal messages.
    pub closed spec fn removals(self) -> Map<nat, RcuRemovalObservation> {
        self.observations@
    }

    /// Records a root replacement after checking all historical publications.
    ///
    /// The caller must keep these removals in the root atomic invariant, so
    /// future publications cannot republish a retired allocation identity.
    /// Linked-node retirement needs an additional no-incoming-links certificate.
    pub proof fn tracked_retire_root<T>(
        tracked &mut self,
        tracked root: &RcuRootOwnedGhost<T, ()>,
        tracked previous: RcuOwnedObject<T, ()>,
        history: AtomicHistory<*mut T>,
        removal: RcuRemovalObservation,
    ) -> (tracked res: (RcuRetiredRegistration<T>, RcuRetiredFact))
        requires
            rcu_owned_root_history_inv(history, *root),
            root.domain() == old(self).domain(),
            previous.inv(),
            previous.retire_perm().belongs_to(root.root().domain_auth()),
            !old(self).removals().contains_key(previous.block_info().obj()),
            removal.root == root.domain(),
            root.root().current_timestamp() == removal.timestamp,
            history.thread_view(removal.timestamp) == removal.message_view,
            forall|ts: nat| #[trigger]
                root.root().publications().contains_pair(ts, Some(previous.block_info().obj()))
                    ==> ts < removal.timestamp,
        ensures
            final(self).domain() == old(self).domain(),
            final(self).id() == old(self).id(),
            final(self).removals() == old(self).removals().insert(
                previous.block_info().obj(),
                removal,
            ),
            res.0.ptr() == previous.block_info().ptr(),
            res.0.record() == res.1.record(),
            res.1.wf(),
            res.1.domain() == old(self).domain(),
            res.1.obj() == previous.block_info().obj(),
            res.1.removal() == removal,
            res.1.retire_observation_registry() == old(self).id(),
    {
        let tracked entry = self.observations.insert(previous.block_info().obj(), removal);
        let tracked fact = RcuRetiredFact { domain: self.domain, observation: entry.persist() };
        let tracked duplicate = fact.tracked_duplicate();
        (RcuRetiredRegistration { registration: previous, fact }, duplicate)
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
        records_observed(self.records(), view)
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

} // verus!
