//! Unbounded fractional read leases for delayed reclamation.
//!
//! An owner-side accumulator stores one linear resource in Verus' Leaf-style
//! storage protocol. Each reader-held lease receives half of the accumulator's
//! current rational fraction, so the number of outstanding leases has no fixed
//! integer bound. Reclamation can recover the resource only after all leases
//! have been returned and the accumulator fraction is whole.
use vstd::{
    prelude::*,
    resource::{Loc, frac_opt::Frac},
};

verus! {

/// Owner-side fractional accumulator for one delayed-reclamation resource.
pub tracked struct RcuLeaseAccumulator<T> {
    frac: Frac<T>,
}

/// Reader-held fractional permission split from an [`RcuLeaseAccumulator`].
pub tracked struct RcuReadLease<T> {
    frac: Frac<T>,
}

/// Reader-held lease registered under an allocation key and a unique lease ID.
///
/// The private `lease_id` names the matching [`RcuActiveReadLeaseRecord`] in
/// the authoritative [`RcuReadLeaseRegistry`]. Returning this lease must
/// consume that exact record, so it cannot be returned to another allocation
/// that happens to store an equal resource.
pub tracked struct RcuRegisteredReadLease<K, T> {
    ghost lease_id: nat,
    ghost key: K,
    lease: RcuReadLease<T>,
}

/// Registry-held accounting record paired with one outstanding reader lease.
///
/// `W` is a client-provided linear witness. RCU uses it to retain enough of the
/// reader's CPU-generation authority for a completed grace period to rule out
/// this record before reclamation.
pub tracked struct RcuActiveReadLeaseRecord<K, W> {
    ghost key: K,
    ghost accumulator_id: Loc,
    ghost fraction: real,
    witness: W,
}

/// Authoritative allocation-indexed registry for physical read permissions.
///
/// Each allocation keeps an owner-side [`RcuLeaseAccumulator`]. The registry
/// also records every issued lease and removes its record only when the
/// matching [`RcuRegisteredReadLease`] is returned. Its invariant says that
/// the accumulator fraction plus all active reader fractions for an allocation
/// is exactly one. Therefore proving that the allocation has no active record
/// is sufficient to recover its stored resource.
pub tracked struct RcuReadLeaseRegistry<K, T, W> {
    accumulators: Map<K, RcuLeaseAccumulator<T>>,
    active: Map<nat, RcuActiveReadLeaseRecord<K, W>>,
    ghost next_lease: nat,
}

impl<K, W> RcuActiveReadLeaseRecord<K, W> {
    pub closed spec fn key(self) -> K {
        self.key
    }

    pub closed spec fn accumulator_id(self) -> Loc {
        self.accumulator_id
    }

    pub closed spec fn fraction(self) -> real {
        self.fraction
    }

    pub closed spec fn witness(self) -> W {
        self.witness
    }
}

impl<K, T> RcuRegisteredReadLease<K, T> {
    pub closed spec fn lease_id(self) -> nat {
        self.lease_id
    }

    pub closed spec fn key(self) -> K {
        self.key
    }

    pub closed spec fn accumulator_id(self) -> Loc {
        self.lease.id()
    }

    pub closed spec fn resource(self) -> T {
        self.lease.resource()
    }

    pub closed spec fn fraction(self) -> real {
        self.lease.fraction()
    }

    /// Borrows the protected resource while this registered lease remains live.
    pub proof fn tracked_borrow(tracked &self) -> (tracked resource: &T)
        ensures
            *resource == self.resource(),
    {
        self.lease.tracked_borrow()
    }
}

/// Sum of active lease fractions for `key` among record IDs below `upto`.
pub open spec fn active_lease_fraction<K, W>(
    active: Map<nat, RcuActiveReadLeaseRecord<K, W>>,
    key: K,
    upto: nat,
) -> real
    decreases upto,
{
    if upto == 0 {
        0real
    } else {
        let id = (upto - 1) as nat;
        active_lease_fraction(active, key, id) + if active.contains_key(id) && active[id].key()
            == key {
            active[id].fraction()
        } else {
            0real
        }
    }
}

proof fn lemma_active_fraction_insert_above<K, W>(
    active: Map<nat, RcuActiveReadLeaseRecord<K, W>>,
    inserted: nat,
    record: RcuActiveReadLeaseRecord<K, W>,
    key: K,
    upto: nat,
)
    requires
        upto <= inserted,
    ensures
        active_lease_fraction(active.insert(inserted, record), key, upto) == active_lease_fraction(
            active,
            key,
            upto,
        ),
    decreases upto,
{
    if upto > 0 {
        let id = (upto - 1) as nat;
        lemma_active_fraction_insert_above(active, inserted, record, key, id);
        assert(id < inserted);
        assert(active.insert(inserted, record).contains_key(id) == active.contains_key(id));
        if active.contains_key(id) {
            assert(active.insert(inserted, record)[id] == active[id]);
        }
    }
}

proof fn lemma_active_fraction_insert_next<K, W>(
    active: Map<nat, RcuActiveReadLeaseRecord<K, W>>,
    next: nat,
    record: RcuActiveReadLeaseRecord<K, W>,
    key: K,
)
    ensures
        active_lease_fraction(active.insert(next, record), key, next + 1) == active_lease_fraction(
            active,
            key,
            next,
        ) + if record.key() == key {
            record.fraction()
        } else {
            0real
        },
{
    lemma_active_fraction_insert_above(active, next, record, key, next);
}

proof fn lemma_active_fraction_remove<K, W>(
    active: Map<nat, RcuActiveReadLeaseRecord<K, W>>,
    removed: nat,
    key: K,
    upto: nat,
)
    requires
        removed < upto,
        active.contains_key(removed),
    ensures
        active_lease_fraction(active.remove(removed), key, upto) == active_lease_fraction(
            active,
            key,
            upto,
        ) - if active[removed].key() == key {
            active[removed].fraction()
        } else {
            0real
        },
    decreases upto,
{
    let id = (upto - 1) as nat;
    if removed == id {
        lemma_active_fraction_remove_above(active, removed, key, id);
        assert(!active.remove(removed).contains_key(id));
        assert(active_lease_fraction(active.remove(removed), key, upto) == active_lease_fraction(
            active.remove(removed),
            key,
            id,
        ));
        assert(active_lease_fraction(active, key, upto) == active_lease_fraction(active, key, id)
            + if active[removed].key() == key {
            active[removed].fraction()
        } else {
            0real
        });
    } else {
        assert(removed < id);
        lemma_active_fraction_remove(active, removed, key, id);
        assert(active.remove(removed).contains_key(id) == active.contains_key(id));
        if active.contains_key(id) {
            assert(active.remove(removed)[id] == active[id]);
        }
        assert(active_lease_fraction(active.remove(removed), key, upto) == active_lease_fraction(
            active.remove(removed),
            key,
            id,
        ) + if active.contains_key(id) && active[id].key() == key {
            active[id].fraction()
        } else {
            0real
        });
        assert(active_lease_fraction(active, key, upto) == active_lease_fraction(active, key, id)
            + if active.contains_key(id) && active[id].key() == key {
            active[id].fraction()
        } else {
            0real
        });
    }
}

proof fn lemma_active_fraction_remove_above<K, W>(
    active: Map<nat, RcuActiveReadLeaseRecord<K, W>>,
    removed: nat,
    key: K,
    upto: nat,
)
    requires
        upto <= removed,
    ensures
        active_lease_fraction(active.remove(removed), key, upto) == active_lease_fraction(
            active,
            key,
            upto,
        ),
    decreases upto,
{
    if upto > 0 {
        let id = (upto - 1) as nat;
        lemma_active_fraction_remove_above(active, removed, key, id);
        assert(id < removed);
        assert(active.remove(removed).contains_key(id) == active.contains_key(id));
        if active.contains_key(id) {
            assert(active.remove(removed)[id] == active[id]);
        }
    }
}

proof fn lemma_active_fraction_zero<K, W>(
    active: Map<nat, RcuActiveReadLeaseRecord<K, W>>,
    key: K,
    upto: nat,
)
    requires
        forall|id: nat| #![auto] id < upto && active.contains_key(id) ==> active[id].key() != key,
    ensures
        active_lease_fraction(active, key, upto) == 0real,
    decreases upto,
{
    if upto > 0 {
        let id = (upto - 1) as nat;
        lemma_active_fraction_zero(active, key, id);
    }
}

impl<T> RcuLeaseAccumulator<T> {
    /// Stores `resource` and creates a whole read accumulator.
    pub proof fn new(tracked resource: T) -> (tracked res: Self)
        ensures
            res.resource() == resource,
            res.fraction() == 1real,
    {
        let tracked frac = Frac::new(resource);
        RcuLeaseAccumulator { frac }
    }

    /// Storage-protocol identity shared by this accumulator and all of its leases.
    pub closed spec fn id(self) -> Loc {
        self.frac.id()
    }

    /// The resource retained in storage while read leases exist.
    pub closed spec fn resource(self) -> T {
        self.frac.resource()
    }

    /// Rational fraction currently accumulated by the owner.
    pub closed spec fn fraction(self) -> real {
        self.frac.frac()
    }

    /// Splits a fresh lease without imposing a fixed reader capacity.
    pub proof fn split_lease(tracked &mut self) -> (tracked lease: RcuReadLease<T>)
        ensures
            final(self).id() == old(self).id(),
            final(self).resource() == old(self).resource(),
            lease.id() == old(self).id(),
            lease.resource() == old(self).resource(),
            final(self).fraction() == old(self).fraction() / 2real,
            lease.fraction() == old(self).fraction() / 2real,
    {
        let tracked frac = self.frac.split();
        RcuReadLease { frac }
    }

    /// Returns one lease to its originating accumulator.
    pub proof fn return_lease(tracked &mut self, tracked lease: RcuReadLease<T>)
        requires
            old(self).id() == lease.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).resource() == old(self).resource(),
            final(self).resource() == lease.resource(),
            final(self).fraction() == old(self).fraction() + lease.fraction(),
    {
        self.frac.combine(lease.frac);
    }

    /// Recovers the stored resource after every lease has returned.
    pub proof fn reclaim(tracked self) -> (tracked resource: T)
        requires
            self.fraction() == 1real,
        ensures
            resource == self.resource(),
    {
        let tracked (resource, _empty) = self.frac.take_resource();
        resource
    }

    /// Establishes the valid range of the accumulated rational fraction.
    pub proof fn lemma_fraction_bounded(tracked &self)
        ensures
            0real < self.fraction() <= 1real,
    {
        self.frac.bounded();
    }
}

impl<T> RcuReadLease<T> {
    /// Storage-protocol identity of the originating accumulator.
    pub closed spec fn id(self) -> Loc {
        self.frac.id()
    }

    /// The resource protected by this lease.
    pub closed spec fn resource(self) -> T {
        self.frac.resource()
    }

    /// Rational fraction carried by this lease.
    pub closed spec fn fraction(self) -> real {
        self.frac.frac()
    }

    /// Borrows the protected resource for the lifetime of this lease borrow.
    pub proof fn tracked_borrow(tracked &self) -> (tracked resource: &T)
        ensures
            *resource == self.resource(),
    {
        self.frac.borrow()
    }

    /// Establishes that every lease carries a positive rational fraction.
    pub proof fn lemma_fraction_bounded(tracked &self)
        ensures
            0real < self.fraction() <= 1real,
    {
        self.frac.bounded();
    }
}

impl<K, T, W> RcuReadLeaseRegistry<K, T, W> {
    /// Creates an empty tracked registry.
    pub proof fn empty() -> (tracked res: Self)
        ensures
            res.wf(),
            res.keys() == Set::<K>::empty(),
            res.active_ids() == Set::<nat>::empty(),
            res.next_lease() == 0,
    {
        RcuReadLeaseRegistry {
            accumulators: Map::tracked_empty(),
            active: Map::tracked_empty(),
            next_lease: 0,
        }
    }

    pub closed spec fn keys(self) -> Set<K> {
        self.accumulators.dom()
    }

    pub closed spec fn contains(self, key: K) -> bool {
        self.accumulators.contains_key(key)
    }

    /// Relates keyed lookup to membership in the registry's key set.
    pub proof fn lemma_contains_iff_key(tracked &self, key: K)
        ensures
            self.contains(key) <==> self.keys().contains(key),
    {
    }

    /// Relates registry membership to the complete key set for all keys.
    pub proof fn lemma_all_contains_iff_keys(tracked &self)
        ensures
            forall|key: K| #[trigger] self.contains(key) <==> self.keys().contains(key),
    {
    }

    pub closed spec fn accumulator(self, key: K) -> RcuLeaseAccumulator<T>
        recommends
            self.contains(key),
    {
        self.accumulators[key]
    }

    pub closed spec fn active_ids(self) -> Set<nat> {
        self.active.dom()
    }

    /// Ghost snapshot used to state the per-allocation accounting invariant.
    pub closed spec fn active_records(self) -> Map<nat, RcuActiveReadLeaseRecord<K, W>> {
        self.active
    }

    pub closed spec fn next_lease(self) -> nat {
        self.next_lease
    }

    pub closed spec fn active_record(self, lease_id: nat) -> RcuActiveReadLeaseRecord<K, W>
        recommends
            self.active_ids().contains(lease_id),
    {
        self.active[lease_id]
    }

    /// Borrows the client witness associated with one active lease.
    ///
    /// The witness remains owned by the registry until the matching lease is
    /// returned. Reclamation proofs use this borrow to show that an allegedly
    /// active lease is incompatible with a completed grace period.
    pub proof fn tracked_borrow_active_witness(tracked &self, lease_id: nat) -> (tracked witness:
        &W)
        requires
            self.active_ids().contains(lease_id),
        ensures
            *witness == self.active_record(lease_id).witness(),
    {
        let tracked record = self.active.tracked_borrow(lease_id);
        &record.witness
    }

    /// Mutably borrows an active witness while preserving the registry.
    ///
    /// Resource-algebra validation may require a mutable receiver even when
    /// its postcondition leaves the witness unchanged.
    pub proof fn tracked_borrow_active_witness_mut(
        tracked &mut self,
        lease_id: nat,
    ) -> (tracked witness: &mut W)
        requires
            old(self).active_ids().contains(lease_id),
        ensures
            *witness == old(self).active_record(lease_id).witness(),
            final(self).keys() == old(self).keys(),
            final(self).active_ids() == old(self).active_ids(),
            final(self).next_lease() == old(self).next_lease(),
            final(self).active_record(lease_id).key() == old(self).active_record(lease_id).key(),
            final(self).active_record(lease_id).accumulator_id() == old(self).active_record(
                lease_id,
            ).accumulator_id(),
            final(self).active_record(lease_id).fraction() == old(self).active_record(
                lease_id,
            ).fraction(),
            final(self).active_record(lease_id).witness() == *final(witness),
            forall|other: nat|
                #![auto]
                other != lease_id && old(self).active_ids().contains(other)
                    ==> final(self).active_record(other) == old(self).active_record(other),
    {
        let tracked record = self.active.tracked_borrow_mut(lease_id);
        &mut record.witness
    }

    pub open spec fn has_active(self, key: K) -> bool {
        exists|lease_id: nat|
            #![auto]
            self.active_ids().contains(lease_id) && self.active_record(lease_id).key() == key
    }

    pub open spec fn wf(self) -> bool {
        &&& forall|lease_id: nat| #[trigger]
            self.active_ids().contains(lease_id) ==> {
                let record = self.active_record(lease_id);
                &&& lease_id < self.next_lease()
                &&& self.contains(record.key())
                &&& record.accumulator_id() == self.accumulator(record.key()).id()
                &&& record.fraction() > 0real
            }
        &&& forall|key: K| #[trigger]
            self.contains(key) ==> self.accumulator(key).fraction() + active_lease_fraction(
                self.active_records(),
                key,
                self.next_lease(),
            ) == 1real
    }

    /// Registers one allocation and stores its complete ownership resource.
    pub proof fn insert(tracked &mut self, key: K, tracked resource: T)
        requires
            old(self).wf(),
            !old(self).contains(key),
        ensures
            final(self).wf(),
            final(self).keys() == old(self).keys().insert(key),
            final(self).active_ids() == old(self).active_ids(),
            final(self).next_lease() == old(self).next_lease(),
            forall|lease_id: nat|
                #![auto]
                old(self).active_ids().contains(lease_id) ==> final(self).active_record(lease_id)
                    == old(self).active_record(lease_id),
            final(self).contains(key),
            final(self).accumulator(key).resource() == resource,
            final(self).accumulator(key).fraction() == 1real,
            forall|other: K|
                old(self).contains(other) ==> final(self).accumulator(other) == old(
                    self,
                ).accumulator(other),
    {
        reveal(RcuReadLeaseRegistry::active_ids);
        reveal(RcuReadLeaseRegistry::active_records);
        reveal(RcuReadLeaseRegistry::active_record);
        assert forall|lease_id: nat| #[trigger] old(self).active_ids().contains(lease_id) implies {
            let record = old(self).active_record(lease_id);
            &&& lease_id < old(self).next_lease()
            &&& old(self).contains(record.key())
            &&& record.accumulator_id() == old(self).accumulator(record.key()).id()
            &&& record.fraction() > 0real
        } by {};
        assert forall|old_key: K| #[trigger] old(self).contains(old_key) implies old(
            self,
        ).accumulator(old_key).fraction() + active_lease_fraction(
            old(self).active_records(),
            old_key,
            old(self).next_lease(),
        ) == 1real by {};
        let tracked accumulator = RcuLeaseAccumulator::new(resource);
        self.accumulators.tracked_insert(key, accumulator);
        assert forall|lease_id: nat| #![auto] self.active_ids().contains(lease_id) implies {
            &&& lease_id < self.next_lease()
            &&& self.contains(self.active_record(lease_id).key())
            &&& self.active_record(lease_id).accumulator_id() == self.accumulator(
                self.active_record(lease_id).key(),
            ).id()
            &&& self.active_record(lease_id).fraction() > 0real
        } by {
            assert(old(self).active_ids().contains(lease_id));
            assert(old(self).active_record(lease_id).key() != key);
        };
        assert forall|lease_id: nat|
            #![auto]
            lease_id < self.next_lease() && self.active_records().contains_key(
                lease_id,
            ) implies self.active_records()[lease_id].key() != key by {
            assert(old(self).active_ids().contains(lease_id));
            assert(old(self).contains(old(self).active_record(lease_id).key()));
        };
        assert(active_lease_fraction(self.active_records(), key, self.next_lease()) == 0real) by {
            lemma_active_fraction_zero(self.active_records(), key, self.next_lease());
        };
        assert forall|other: K| #![auto] self.contains(other) implies self.accumulator(
            other,
        ).fraction() + active_lease_fraction(self.active_records(), other, self.next_lease())
            == 1real by {
            if other == key {
                assert(self.accumulator(key).fraction() == 1real);
            } else {
                assert(old(self).contains(other));
                assert(self.accumulator(other) == old(self).accumulator(other));
            }
        };
    }

    /// Splits a lease and installs its client witness in the active registry.
    pub proof fn split_lease(tracked &mut self, key: K, tracked witness: W) -> (tracked lease:
        RcuRegisteredReadLease<K, T>)
        requires
            old(self).wf(),
            old(self).contains(key),
        ensures
            final(self).wf(),
            final(self).keys() == old(self).keys(),
            forall|candidate: K| #[trigger]
                final(self).contains(candidate) == old(self).contains(candidate),
            final(self).next_lease() == old(self).next_lease() + 1,
            lease.lease_id() == old(self).next_lease(),
            lease.key() == key,
            final(self).active_ids() == old(self).active_ids().insert(lease.lease_id()),
            final(self).active_record(lease.lease_id()).key() == key,
            final(self).active_record(lease.lease_id()).accumulator_id() == lease.accumulator_id(),
            final(self).active_record(lease.lease_id()).fraction() == lease.fraction(),
            final(self).active_record(lease.lease_id()).witness() == witness,
            forall|lease_id: nat|
                #![auto]
                old(self).active_ids().contains(lease_id) ==> final(self).active_record(lease_id)
                    == old(self).active_record(lease_id),
            lease.accumulator_id() == old(self).accumulator(key).id(),
            lease.resource() == old(self).accumulator(key).resource(),
            lease.fraction() == old(self).accumulator(key).fraction() / 2real,
            final(self).accumulator(key).id() == old(self).accumulator(key).id(),
            final(self).accumulator(key).resource() == old(self).accumulator(key).resource(),
            final(self).accumulator(key).fraction() == old(self).accumulator(key).fraction()
                / 2real,
            forall|other: K|
                other != key && old(self).contains(other) ==> final(self).accumulator(other) == old(
                    self,
                ).accumulator(other),
    {
        reveal(RcuReadLeaseRegistry::active_ids);
        reveal(RcuReadLeaseRegistry::active_records);
        reveal(RcuReadLeaseRegistry::active_record);
        assert forall|old_key: K| #[trigger] old(self).contains(old_key) implies old(
            self,
        ).accumulator(old_key).fraction() + active_lease_fraction(
            old(self).active_records(),
            old_key,
            old(self).next_lease(),
        ) == 1real by {};
        let ghost lease_id = self.next_lease;
        let tracked accumulator = self.accumulators.tracked_borrow_mut(key);
        let tracked lease = accumulator.split_lease();
        lease.lemma_fraction_bounded();
        let ghost accumulator_id = lease.id();
        let ghost fraction = lease.fraction();
        let tracked record = RcuActiveReadLeaseRecord { key, accumulator_id, fraction, witness };
        self.active.tracked_insert(lease_id, record);
        self.next_lease = lease_id + 1;

        assert forall|active_id: nat| #![auto] self.active_ids().contains(active_id) implies {
            &&& active_id < self.next_lease()
            &&& self.contains(self.active_record(active_id).key())
            &&& self.active_record(active_id).accumulator_id() == self.accumulator(
                self.active_record(active_id).key(),
            ).id()
            &&& self.active_record(active_id).fraction() > 0real
        } by {
            if active_id == lease_id {
                assert(self.active_record(active_id).fraction() == fraction);
            } else {
                assert(old(self).active_ids().contains(active_id));
                assert(self.active_record(active_id) == old(self).active_record(active_id));
            }
        };

        assert forall|other: K| #![auto] self.contains(other) implies self.accumulator(
            other,
        ).fraction() + active_lease_fraction(self.active_records(), other, self.next_lease())
            == 1real by {
            lemma_active_fraction_insert_next(
                old(self).active_records(),
                lease_id,
                self.active_record(lease_id),
                other,
            );
            if other == key {
                assert(old(self).accumulator(key).fraction() + active_lease_fraction(
                    old(self).active_records(),
                    key,
                    lease_id,
                ) == 1real);
            } else {
                assert(old(self).contains(other));
                assert(self.accumulator(other) == old(self).accumulator(other));
                assert(old(self).accumulator(other).fraction() + active_lease_fraction(
                    old(self).active_records(),
                    other,
                    lease_id,
                ) == 1real);
            }
        };
        RcuRegisteredReadLease { lease_id, key, lease }
    }

    /// Returns one lease and removes exactly its matching active record.
    pub proof fn return_lease(
        tracked &mut self,
        tracked lease: RcuRegisteredReadLease<K, T>,
    ) -> (tracked witness: W)
        requires
            old(self).wf(),
            old(self).active_ids().contains(lease.lease_id()),
            old(self).active_record(lease.lease_id()).key() == lease.key(),
            old(self).active_record(lease.lease_id()).accumulator_id() == lease.accumulator_id(),
            old(self).active_record(lease.lease_id()).fraction() == lease.fraction(),
        ensures
            final(self).wf(),
            final(self).keys() == old(self).keys(),
            forall|candidate: K| #[trigger]
                final(self).contains(candidate) == old(self).contains(candidate),
            final(self).next_lease() == old(self).next_lease(),
            final(self).active_ids() == old(self).active_ids().remove(lease.lease_id()),
            witness == old(self).active_record(lease.lease_id()).witness(),
            forall|lease_id: nat|
                #![auto]
                lease_id != lease.lease_id() && old(self).active_ids().contains(lease_id)
                    ==> final(self).active_record(lease_id) == old(self).active_record(lease_id),
            final(self).accumulator(lease.key()).id() == old(self).accumulator(lease.key()).id(),
            final(self).accumulator(lease.key()).resource() == old(self).accumulator(
                lease.key(),
            ).resource(),
            final(self).accumulator(lease.key()).fraction() == old(self).accumulator(
                lease.key(),
            ).fraction() + lease.fraction(),
            forall|other: K|
                other != lease.key() && old(self).contains(other) ==> final(self).accumulator(other)
                    == old(self).accumulator(other),
    {
        reveal(RcuReadLeaseRegistry::active_ids);
        reveal(RcuReadLeaseRegistry::active_records);
        reveal(RcuReadLeaseRegistry::active_record);
        assert forall|old_key: K| #[trigger] old(self).contains(old_key) implies old(
            self,
        ).accumulator(old_key).fraction() + active_lease_fraction(
            old(self).active_records(),
            old_key,
            old(self).next_lease(),
        ) == 1real by {};
        let ghost lease_id = lease.lease_id;
        let ghost key = lease.key;
        let tracked record = self.active.tracked_remove(lease_id);
        let tracked accumulator = self.accumulators.tracked_borrow_mut(key);
        accumulator.return_lease(lease.lease);

        assert forall|active_id: nat| #![auto] self.active_ids().contains(active_id) implies {
            &&& active_id < self.next_lease()
            &&& self.contains(self.active_record(active_id).key())
            &&& self.active_record(active_id).accumulator_id() == self.accumulator(
                self.active_record(active_id).key(),
            ).id()
            &&& self.active_record(active_id).fraction() > 0real
        } by {
            assert(old(self).active_ids().contains(active_id));
            assert(active_id != lease_id);
            assert(self.active_record(active_id) == old(self).active_record(active_id));
        };

        assert forall|other: K| #![auto] self.contains(other) implies self.accumulator(
            other,
        ).fraction() + active_lease_fraction(self.active_records(), other, self.next_lease())
            == 1real by {
            lemma_active_fraction_remove(
                old(self).active_records(),
                lease_id,
                other,
                self.next_lease(),
            );
            if other == key {
                assert(old(self).accumulator(key).fraction() + active_lease_fraction(
                    old(self).active_records(),
                    key,
                    self.next_lease(),
                ) == 1real);
            } else {
                assert(old(self).contains(other));
                assert(self.accumulator(other) == old(self).accumulator(other));
                assert(old(self).accumulator(other).fraction() + active_lease_fraction(
                    old(self).active_records(),
                    other,
                    self.next_lease(),
                ) == 1real);
            }
        };
        record.witness
    }

    /// Recovers one allocation after a client proof rules out all active leases.
    pub proof fn reclaim(tracked &mut self, key: K) -> (tracked resource: T)
        requires
            old(self).wf(),
            old(self).contains(key),
            !old(self).has_active(key),
        ensures
            final(self).wf(),
            final(self).keys() == old(self).keys().remove(key),
            final(self).active_ids() == old(self).active_ids(),
            final(self).active_records() == old(self).active_records(),
            final(self).next_lease() == old(self).next_lease(),
            forall|lease_id: nat|
                #![auto]
                old(self).active_ids().contains(lease_id) ==> final(self).active_record(lease_id)
                    == old(self).active_record(lease_id),
            !final(self).contains(key),
            resource == old(self).accumulator(key).resource(),
            forall|other: K|
                other != key && old(self).contains(other) ==> final(self).accumulator(other) == old(
                    self,
                ).accumulator(other),
    {
        reveal(RcuReadLeaseRegistry::active_ids);
        reveal(RcuReadLeaseRegistry::active_records);
        reveal(RcuReadLeaseRegistry::active_record);
        assert forall|old_key: K| #[trigger] old(self).contains(old_key) implies old(
            self,
        ).accumulator(old_key).fraction() + active_lease_fraction(
            old(self).active_records(),
            old_key,
            old(self).next_lease(),
        ) == 1real by {};
        assert forall|lease_id: nat|
            #![auto]
            lease_id < self.next_lease() && self.active_records().contains_key(
                lease_id,
            ) implies self.active_records()[lease_id].key() != key by {
            if self.active_records()[lease_id].key() == key {
                assert(self.active_ids().contains(lease_id));
                assert(exists|candidate: nat|
                    #![auto]
                    self.active_ids().contains(candidate) && self.active_record(candidate).key()
                        == key) by {
                    assert(self.active_record(lease_id).key() == key);
                };
                assert(self.has_active(key));
            }
        };
        lemma_active_fraction_zero(self.active_records(), key, self.next_lease());
        assert(self.accumulator(key).fraction() == 1real);
        let tracked accumulator = self.accumulators.tracked_remove(key);
        let tracked resource = accumulator.reclaim();
        assert forall|lease_id: nat| #![auto] self.active_ids().contains(lease_id) implies {
            &&& lease_id < self.next_lease()
            &&& self.contains(self.active_record(lease_id).key())
            &&& self.active_record(lease_id).accumulator_id() == self.accumulator(
                self.active_record(lease_id).key(),
            ).id()
            &&& self.active_record(lease_id).fraction() > 0real
        } by {
            assert(old(self).active_ids().contains(lease_id));
            assert(old(self).active_record(lease_id).key() != key);
        };
        assert forall|other: K| #![auto] self.contains(other) implies self.accumulator(
            other,
        ).fraction() + active_lease_fraction(self.active_records(), other, self.next_lease())
            == 1real by {
            assert(other != key);
            assert(old(self).contains(other));
            assert(self.accumulator(other) == old(self).accumulator(other));
            assert(self.active_records() == old(self).active_records());
            assert(old(self).accumulator(other).fraction() + active_lease_fraction(
                old(self).active_records(),
                other,
                old(self).next_lease(),
            ) == 1real);
        };
        resource
    }
}

/// Regression proof for the complete indexed split/return/reclaim lifecycle.
proof fn read_lease_registry_reclaims_after_returns<K, T, W>(
    key: K,
    tracked resource: T,
    tracked first_witness: W,
    tracked second_witness: W,
) -> (tracked res: T)
    ensures
        res == resource,
{
    let tracked mut registry = RcuReadLeaseRegistry::empty();
    registry.insert(key, resource);
    let tracked first = registry.split_lease(key, first_witness);
    let tracked second = registry.split_lease(key, second_witness);
    let tracked _first_witness = registry.return_lease(first);
    let tracked _second_witness = registry.return_lease(second);
    assert(!registry.has_active(key));
    assert(registry.accumulator(key).resource() == resource);
    let tracked res = registry.reclaim(key);
    assert(res == resource);
    res
}

/// Regression proof: recursively splitting leases does not require a capacity
/// assumption, and returning them restores the whole resource.
pub proof fn lease_accumulator_reclaims_after_returns<T>(tracked resource: T) -> (tracked res: T)
    ensures
        res == resource,
{
    let tracked mut accumulator = RcuLeaseAccumulator::new(resource);
    let tracked first = accumulator.split_lease();
    let tracked second = accumulator.split_lease();
    accumulator.return_lease(first);
    accumulator.return_lease(second);
    assert(accumulator.fraction() == 1real);
    accumulator.reclaim()
}

} // verus!
