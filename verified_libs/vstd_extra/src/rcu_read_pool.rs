//! Unbounded fractional read leases for delayed reclamation.
//!
//! The pool stores one linear resource in Verus' Leaf-style storage protocol.
//! Each lease receives half of the pool's current rational fraction, so the
//! number of outstanding leases has no fixed integer bound. A lease guards a
//! shared borrow of the stored resource. Reclamation can recover the resource
//! only after all leases have been returned and the pool fraction is whole.
use vstd::{
    prelude::*,
    resource::{Loc, frac_opt::Frac},
};

verus! {

/// Owner-side accumulator for one delayed-reclamation resource.
pub tracked struct RcuReadPool<T> {
    frac: Frac<T>,
}

/// One read-side fraction split from an [`RcuReadPool`].
pub tracked struct RcuReadLease<T> {
    frac: Frac<T>,
}

/// Allocation-indexed ownership pools retained across publication changes.
///
/// An RCU root needs this indirection because a weak load may select an older
/// publication after a newer pointer has already been installed.
pub tracked struct RcuReadPoolRegistry<K, T> {
    pools: Map<K, RcuReadPool<T>>,
}

/// One allocation-indexed lease issued by a tracked registry.
///
/// The private `lease_id` names the matching active record in the registry.
/// Returning a lease must consume that exact record, so a lease cannot be
/// returned to another allocation that happens to store an equal resource.
pub tracked struct RcuTrackedReadLease<K, T> {
    ghost lease_id: nat,
    ghost key: K,
    lease: RcuReadLease<T>,
}

/// Registry-side accounting for one outstanding read lease.
///
/// `W` is a client-provided linear witness. RCU uses it to retain enough of the
/// reader's CPU-generation authority for a completed grace period to rule out
/// this record before reclamation.
pub tracked struct RcuReadLeaseRecord<K, W> {
    ghost key: K,
    ghost pool_id: Loc,
    ghost fraction: real,
    witness: W,
}

/// Allocation-indexed pools with explicit accounting for every issued lease.
///
/// Unlike [`RcuReadPoolRegistry`], this registry records every split and only
/// removes the record when the matching lease is returned. Its invariant says
/// that each pool's owner fraction plus all of that allocation's active lease
/// fractions is exactly one. Consequently, proving that an allocation has no
/// active records is sufficient to recover its stored resource.
pub tracked struct RcuTrackedReadPoolRegistry<K, T, W> {
    pools: Map<K, RcuReadPool<T>>,
    active: Map<nat, RcuReadLeaseRecord<K, W>>,
    ghost next_lease: nat,
}

impl<K, W> RcuReadLeaseRecord<K, W> {
    pub closed spec fn key(self) -> K {
        self.key
    }

    pub closed spec fn pool_id(self) -> Loc {
        self.pool_id
    }

    pub closed spec fn fraction(self) -> real {
        self.fraction
    }

    pub closed spec fn witness(self) -> W {
        self.witness
    }
}

impl<K, T> RcuTrackedReadLease<K, T> {
    pub closed spec fn lease_id(self) -> nat {
        self.lease_id
    }

    pub closed spec fn key(self) -> K {
        self.key
    }

    pub closed spec fn pool_id(self) -> Loc {
        self.lease.id()
    }

    pub closed spec fn resource(self) -> T {
        self.lease.resource()
    }

    pub closed spec fn fraction(self) -> real {
        self.lease.fraction()
    }

    pub proof fn borrow(tracked &self) -> (tracked resource: &T)
        ensures
            *resource == self.resource(),
    {
        self.lease.borrow()
    }
}

/// Sum of active lease fractions for `key` among record IDs below `upto`.
pub open spec fn active_lease_fraction<K, W>(
    active: Map<nat, RcuReadLeaseRecord<K, W>>,
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
    active: Map<nat, RcuReadLeaseRecord<K, W>>,
    inserted: nat,
    record: RcuReadLeaseRecord<K, W>,
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
    active: Map<nat, RcuReadLeaseRecord<K, W>>,
    next: nat,
    record: RcuReadLeaseRecord<K, W>,
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
    active: Map<nat, RcuReadLeaseRecord<K, W>>,
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
    active: Map<nat, RcuReadLeaseRecord<K, W>>,
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
    active: Map<nat, RcuReadLeaseRecord<K, W>>,
    key: K,
    upto: nat,
)
    requires
        forall|id: nat| id < upto && active.contains_key(id) ==> active[id].key() != key,
    ensures
        active_lease_fraction(active, key, upto) == 0real,
    decreases upto,
{
    if upto > 0 {
        let id = (upto - 1) as nat;
        lemma_active_fraction_zero(active, key, id);
    }
}

impl<T> RcuReadPool<T> {
    /// Stores `resource` and creates a whole read pool.
    pub proof fn new(tracked resource: T) -> (tracked res: Self)
        ensures
            res.resource() == resource,
            res.fraction() == 1real,
    {
        let tracked frac = Frac::new(resource);
        RcuReadPool { frac }
    }

    /// Storage-protocol identity shared by this pool and all of its leases.
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

    /// Returns one lease to its originating pool.
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
    /// Storage-protocol identity of the originating pool.
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
    pub proof fn borrow(tracked &self) -> (tracked resource: &T)
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

impl<K, T> RcuReadPoolRegistry<K, T> {
    /// Creates an empty pool registry.
    pub proof fn empty() -> (tracked res: Self)
        ensures
            res.keys() == Set::<K>::empty(),
    {
        RcuReadPoolRegistry { pools: Map::tracked_empty() }
    }

    /// Registered allocation identities.
    pub closed spec fn keys(self) -> Set<K> {
        self.pools.dom()
    }

    pub closed spec fn contains(self, key: K) -> bool {
        self.pools.contains_key(key)
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
            forall|key: K| #[trigger] self.keys().contains(key) ==> self.contains(key),
    {
    }

    pub closed spec fn pool(self, key: K) -> RcuReadPool<T>
        recommends
            self.contains(key),
    {
        self.pools[key]
    }

    /// Registers a fresh allocation and stores its linear permission.
    pub proof fn insert(tracked &mut self, key: K, tracked resource: T)
        requires
            !old(self).contains(key),
        ensures
            final(self).keys() == old(self).keys().insert(key),
            final(self).contains(key),
            final(self).pool(key).resource() == resource,
            final(self).pool(key).fraction() == 1real,
            forall|other: K|
                old(self).contains(other) ==> final(self).pool(other) == old(self).pool(other),
    {
        let tracked pool = RcuReadPool::new(resource);
        self.pools.tracked_insert(key, pool);
    }

    /// Splits a lease from the allocation selected by `key`.
    pub proof fn split_lease(tracked &mut self, key: K) -> (tracked lease: RcuReadLease<T>)
        requires
            old(self).contains(key),
        ensures
            final(self).keys() == old(self).keys(),
            final(self).contains(key),
            final(self).pool(key).id() == old(self).pool(key).id(),
            final(self).pool(key).resource() == old(self).pool(key).resource(),
            lease.id() == old(self).pool(key).id(),
            lease.resource() == old(self).pool(key).resource(),
            final(self).pool(key).fraction() == old(self).pool(key).fraction() / 2real,
            lease.fraction() == old(self).pool(key).fraction() / 2real,
            forall|other: K|
                other != key && old(self).contains(other) ==> final(self).pool(other) == old(
                    self,
                ).pool(other),
    {
        let tracked pool = self.pools.tracked_borrow_mut(key);
        pool.split_lease()
    }

    /// Returns a lease to the pool identified by `key`.
    pub proof fn return_lease(tracked &mut self, key: K, tracked lease: RcuReadLease<T>)
        requires
            old(self).contains(key),
            old(self).pool(key).id() == lease.id(),
        ensures
            final(self).keys() == old(self).keys(),
            final(self).contains(key),
            final(self).pool(key).id() == old(self).pool(key).id(),
            final(self).pool(key).resource() == old(self).pool(key).resource(),
            final(self).pool(key).resource() == lease.resource(),
            final(self).pool(key).fraction() == old(self).pool(key).fraction() + lease.fraction(),
            forall|other: K|
                other != key && old(self).contains(other) ==> final(self).pool(other) == old(
                    self,
                ).pool(other),
    {
        let tracked pool = self.pools.tracked_borrow_mut(key);
        pool.return_lease(lease);
    }

    /// Removes a whole pool and recovers its stored ownership resource.
    pub proof fn reclaim(tracked &mut self, key: K) -> (tracked resource: T)
        requires
            old(self).contains(key),
            old(self).pool(key).fraction() == 1real,
        ensures
            final(self).keys() == old(self).keys().remove(key),
            !final(self).contains(key),
            resource == old(self).pool(key).resource(),
            forall|other: K|
                other != key && old(self).contains(other) ==> final(self).pool(other) == old(
                    self,
                ).pool(other),
    {
        let tracked pool = self.pools.tracked_remove(key);
        pool.reclaim()
    }
}

impl<K, T, W> RcuTrackedReadPoolRegistry<K, T, W> {
    /// Creates an empty tracked registry.
    pub proof fn empty() -> (tracked res: Self)
        ensures
            res.wf(),
            res.keys() == Set::<K>::empty(),
            res.active_ids() == Set::<nat>::empty(),
            res.next_lease() == 0,
    {
        RcuTrackedReadPoolRegistry {
            pools: Map::tracked_empty(),
            active: Map::tracked_empty(),
            next_lease: 0,
        }
    }

    pub closed spec fn keys(self) -> Set<K> {
        self.pools.dom()
    }

    pub closed spec fn contains(self, key: K) -> bool {
        self.pools.contains_key(key)
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
            forall|key: K| #[trigger] self.keys().contains(key) ==> self.contains(key),
    {
    }

    pub closed spec fn pool(self, key: K) -> RcuReadPool<T>
        recommends
            self.contains(key),
    {
        self.pools[key]
    }

    pub closed spec fn active_ids(self) -> Set<nat> {
        self.active.dom()
    }

    /// Ghost snapshot used to state the per-allocation accounting invariant.
    pub closed spec fn active_records(self) -> Map<nat, RcuReadLeaseRecord<K, W>> {
        self.active
    }

    pub closed spec fn next_lease(self) -> nat {
        self.next_lease
    }

    pub closed spec fn active_record(self, lease_id: nat) -> RcuReadLeaseRecord<K, W>
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
            final(self).active_record(lease_id).pool_id() == old(self).active_record(
                lease_id,
            ).pool_id(),
            final(self).active_record(lease_id).fraction() == old(self).active_record(
                lease_id,
            ).fraction(),
            final(self).active_record(lease_id).witness() == *final(witness),
            forall|other: nat|
                other != lease_id && old(self).active_ids().contains(other)
                    ==> final(self).active_record(other) == old(self).active_record(other),
    {
        let tracked record = self.active.tracked_borrow_mut(lease_id);
        &mut record.witness
    }

    pub open spec fn has_active(self, key: K) -> bool {
        exists|lease_id: nat|
            self.active_ids().contains(lease_id) && self.active_record(lease_id).key() == key
    }

    pub open spec fn wf(self) -> bool {
        &&& forall|lease_id: nat| #[trigger]
            self.active_ids().contains(lease_id) ==> {
                let record = self.active_record(lease_id);
                &&& lease_id < self.next_lease()
                &&& self.contains(record.key())
                &&& record.pool_id() == self.pool(record.key()).id()
                &&& record.fraction() > 0real
            }
        &&& forall|key: K| #[trigger]
            self.contains(key) ==> self.pool(key).fraction() + active_lease_fraction(
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
                old(self).active_ids().contains(lease_id) ==> final(self).active_record(lease_id)
                    == old(self).active_record(lease_id),
            final(self).contains(key),
            final(self).pool(key).resource() == resource,
            final(self).pool(key).fraction() == 1real,
            forall|other: K|
                old(self).contains(other) ==> final(self).pool(other) == old(self).pool(other),
    {
        reveal(RcuTrackedReadPoolRegistry::active_ids);
        reveal(RcuTrackedReadPoolRegistry::active_records);
        reveal(RcuTrackedReadPoolRegistry::active_record);
        assert forall|lease_id: nat| #[trigger] old(self).active_ids().contains(lease_id) implies {
            let record = old(self).active_record(lease_id);
            &&& lease_id < old(self).next_lease()
            &&& old(self).contains(record.key())
            &&& record.pool_id() == old(self).pool(record.key()).id()
            &&& record.fraction() > 0real
        } by {};
        assert forall|old_key: K| #[trigger] old(self).contains(old_key) implies old(self).pool(
            old_key,
        ).fraction() + active_lease_fraction(
            old(self).active_records(),
            old_key,
            old(self).next_lease(),
        ) == 1real by {};
        let tracked pool = RcuReadPool::new(resource);
        self.pools.tracked_insert(key, pool);
        assert forall|lease_id: nat| self.active_ids().contains(lease_id) implies {
            &&& lease_id < self.next_lease()
            &&& self.contains(self.active_record(lease_id).key())
            &&& self.active_record(lease_id).pool_id() == self.pool(
                self.active_record(lease_id).key(),
            ).id()
            &&& self.active_record(lease_id).fraction() > 0real
        } by {
            assert(old(self).active_ids().contains(lease_id));
            assert(old(self).active_record(lease_id).key() != key);
        };
        assert forall|lease_id: nat|
            lease_id < self.next_lease() && self.active_records().contains_key(
                lease_id,
            ) implies self.active_records()[lease_id].key() != key by {
            assert(old(self).active_ids().contains(lease_id));
            assert(old(self).contains(old(self).active_record(lease_id).key()));
        };
        assert(active_lease_fraction(self.active_records(), key, self.next_lease()) == 0real) by {
            lemma_active_fraction_zero(self.active_records(), key, self.next_lease());
        };
        assert forall|other: K| self.contains(other) implies self.pool(other).fraction()
            + active_lease_fraction(self.active_records(), other, self.next_lease()) == 1real by {
            if other == key {
                assert(self.pool(key).fraction() == 1real);
            } else {
                assert(old(self).contains(other));
                assert(self.pool(other) == old(self).pool(other));
            }
        };
    }

    /// Splits a lease and installs its client witness in the active registry.
    pub proof fn split_lease(tracked &mut self, key: K, tracked witness: W) -> (tracked lease:
        RcuTrackedReadLease<K, T>)
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
            final(self).active_record(lease.lease_id()).pool_id() == lease.pool_id(),
            final(self).active_record(lease.lease_id()).fraction() == lease.fraction(),
            final(self).active_record(lease.lease_id()).witness() == witness,
            forall|lease_id: nat|
                old(self).active_ids().contains(lease_id) ==> final(self).active_record(lease_id)
                    == old(self).active_record(lease_id),
            lease.pool_id() == old(self).pool(key).id(),
            lease.resource() == old(self).pool(key).resource(),
            lease.fraction() == old(self).pool(key).fraction() / 2real,
            final(self).pool(key).id() == old(self).pool(key).id(),
            final(self).pool(key).resource() == old(self).pool(key).resource(),
            final(self).pool(key).fraction() == old(self).pool(key).fraction() / 2real,
            forall|other: K|
                other != key && old(self).contains(other) ==> final(self).pool(other) == old(
                    self,
                ).pool(other),
    {
        reveal(RcuTrackedReadPoolRegistry::active_ids);
        reveal(RcuTrackedReadPoolRegistry::active_records);
        reveal(RcuTrackedReadPoolRegistry::active_record);
        assert forall|old_key: K| #[trigger] old(self).contains(old_key) implies old(self).pool(
            old_key,
        ).fraction() + active_lease_fraction(
            old(self).active_records(),
            old_key,
            old(self).next_lease(),
        ) == 1real by {};
        let ghost lease_id = self.next_lease;
        let tracked pool = self.pools.tracked_borrow_mut(key);
        let tracked lease = pool.split_lease();
        lease.lemma_fraction_bounded();
        let ghost pool_id = lease.id();
        let ghost fraction = lease.fraction();
        let tracked record = RcuReadLeaseRecord { key, pool_id, fraction, witness };
        self.active.tracked_insert(lease_id, record);
        self.next_lease = lease_id + 1;

        assert forall|active_id: nat| self.active_ids().contains(active_id) implies {
            &&& active_id < self.next_lease()
            &&& self.contains(self.active_record(active_id).key())
            &&& self.active_record(active_id).pool_id() == self.pool(
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

        assert forall|other: K| self.contains(other) implies self.pool(other).fraction()
            + active_lease_fraction(self.active_records(), other, self.next_lease()) == 1real by {
            lemma_active_fraction_insert_next(
                old(self).active_records(),
                lease_id,
                self.active_record(lease_id),
                other,
            );
            if other == key {
                assert(old(self).pool(key).fraction() + active_lease_fraction(
                    old(self).active_records(),
                    key,
                    lease_id,
                ) == 1real);
            } else {
                assert(old(self).contains(other));
                assert(self.pool(other) == old(self).pool(other));
                assert(old(self).pool(other).fraction() + active_lease_fraction(
                    old(self).active_records(),
                    other,
                    lease_id,
                ) == 1real);
            }
        };
        RcuTrackedReadLease { lease_id, key, lease }
    }

    /// Returns one lease and removes exactly its matching active record.
    pub proof fn return_lease(
        tracked &mut self,
        tracked lease: RcuTrackedReadLease<K, T>,
    ) -> (tracked witness: W)
        requires
            old(self).wf(),
            old(self).active_ids().contains(lease.lease_id()),
            old(self).active_record(lease.lease_id()).key() == lease.key(),
            old(self).active_record(lease.lease_id()).pool_id() == lease.pool_id(),
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
                lease_id != lease.lease_id() && old(self).active_ids().contains(lease_id)
                    ==> final(self).active_record(lease_id) == old(self).active_record(lease_id),
            final(self).pool(lease.key()).id() == old(self).pool(lease.key()).id(),
            final(self).pool(lease.key()).resource() == old(self).pool(lease.key()).resource(),
            final(self).pool(lease.key()).fraction() == old(self).pool(lease.key()).fraction()
                + lease.fraction(),
            forall|other: K|
                other != lease.key() && old(self).contains(other) ==> final(self).pool(other)
                    == old(self).pool(other),
    {
        reveal(RcuTrackedReadPoolRegistry::active_ids);
        reveal(RcuTrackedReadPoolRegistry::active_records);
        reveal(RcuTrackedReadPoolRegistry::active_record);
        assert forall|old_key: K| #[trigger] old(self).contains(old_key) implies old(self).pool(
            old_key,
        ).fraction() + active_lease_fraction(
            old(self).active_records(),
            old_key,
            old(self).next_lease(),
        ) == 1real by {};
        let ghost lease_id = lease.lease_id;
        let ghost key = lease.key;
        let tracked record = self.active.tracked_remove(lease_id);
        let tracked pool = self.pools.tracked_borrow_mut(key);
        pool.return_lease(lease.lease);

        assert forall|active_id: nat| self.active_ids().contains(active_id) implies {
            &&& active_id < self.next_lease()
            &&& self.contains(self.active_record(active_id).key())
            &&& self.active_record(active_id).pool_id() == self.pool(
                self.active_record(active_id).key(),
            ).id()
            &&& self.active_record(active_id).fraction() > 0real
        } by {
            assert(old(self).active_ids().contains(active_id));
            assert(active_id != lease_id);
            assert(self.active_record(active_id) == old(self).active_record(active_id));
        };

        assert forall|other: K| self.contains(other) implies self.pool(other).fraction()
            + active_lease_fraction(self.active_records(), other, self.next_lease()) == 1real by {
            lemma_active_fraction_remove(
                old(self).active_records(),
                lease_id,
                other,
                self.next_lease(),
            );
            if other == key {
                assert(old(self).pool(key).fraction() + active_lease_fraction(
                    old(self).active_records(),
                    key,
                    self.next_lease(),
                ) == 1real);
            } else {
                assert(old(self).contains(other));
                assert(self.pool(other) == old(self).pool(other));
                assert(old(self).pool(other).fraction() + active_lease_fraction(
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
                old(self).active_ids().contains(lease_id) ==> final(self).active_record(lease_id)
                    == old(self).active_record(lease_id),
            !final(self).contains(key),
            resource == old(self).pool(key).resource(),
            forall|other: K|
                other != key && old(self).contains(other) ==> final(self).pool(other) == old(
                    self,
                ).pool(other),
    {
        reveal(RcuTrackedReadPoolRegistry::active_ids);
        reveal(RcuTrackedReadPoolRegistry::active_records);
        reveal(RcuTrackedReadPoolRegistry::active_record);
        assert forall|old_key: K| #[trigger] old(self).contains(old_key) implies old(self).pool(
            old_key,
        ).fraction() + active_lease_fraction(
            old(self).active_records(),
            old_key,
            old(self).next_lease(),
        ) == 1real by {};
        assert forall|lease_id: nat|
            lease_id < self.next_lease() && self.active_records().contains_key(
                lease_id,
            ) implies self.active_records()[lease_id].key() != key by {
            if self.active_records()[lease_id].key() == key {
                assert(self.active_ids().contains(lease_id));
                assert(exists|candidate: nat|
                    self.active_ids().contains(candidate) && self.active_record(candidate).key()
                        == key) by {
                    assert(self.active_record(lease_id).key() == key);
                };
                assert(self.has_active(key));
            }
        };
        lemma_active_fraction_zero(self.active_records(), key, self.next_lease());
        assert(self.pool(key).fraction() == 1real);
        let tracked pool = self.pools.tracked_remove(key);
        let tracked resource = pool.reclaim();
        assert forall|lease_id: nat| self.active_ids().contains(lease_id) implies {
            &&& lease_id < self.next_lease()
            &&& self.contains(self.active_record(lease_id).key())
            &&& self.active_record(lease_id).pool_id() == self.pool(
                self.active_record(lease_id).key(),
            ).id()
            &&& self.active_record(lease_id).fraction() > 0real
        } by {
            assert(old(self).active_ids().contains(lease_id));
            assert(old(self).active_record(lease_id).key() != key);
        };
        assert forall|other: K| self.contains(other) implies self.pool(other).fraction()
            + active_lease_fraction(self.active_records(), other, self.next_lease()) == 1real by {
            assert(other != key);
            assert(old(self).contains(other));
            assert(self.pool(other) == old(self).pool(other));
            assert(self.active_records() == old(self).active_records());
            assert(old(self).pool(other).fraction() + active_lease_fraction(
                old(self).active_records(),
                other,
                old(self).next_lease(),
            ) == 1real);
        };
        resource
    }
}

/// Regression proof for the complete indexed split/return/reclaim lifecycle.
proof fn tracked_registry_reclaims_after_returns<K, T, W>(
    key: K,
    tracked resource: T,
    tracked first_witness: W,
    tracked second_witness: W,
) -> (tracked res: T)
    ensures
        res == resource,
{
    let tracked mut registry = RcuTrackedReadPoolRegistry::empty();
    registry.insert(key, resource);
    let tracked first = registry.split_lease(key, first_witness);
    let tracked second = registry.split_lease(key, second_witness);
    let tracked _first_witness = registry.return_lease(first);
    let tracked _second_witness = registry.return_lease(second);
    assert(!registry.has_active(key));
    assert(registry.pool(key).resource() == resource);
    let tracked res = registry.reclaim(key);
    assert(res == resource);
    res
}

/// Regression proof: recursively splitting leases does not require a capacity
/// assumption, and returning them restores the whole resource.
pub proof fn split_return_reclaims<T>(tracked resource: T) -> (tracked res: T)
    ensures
        res == resource,
{
    let tracked mut pool = RcuReadPool::new(resource);
    let tracked first = pool.split_lease();
    let tracked second = pool.split_lease();
    pool.return_lease(first);
    pool.return_lease(second);
    assert(pool.fraction() == 1real);
    pool.reclaim()
}

} // verus!
