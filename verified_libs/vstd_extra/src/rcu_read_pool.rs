//! Unbounded fractional read leases for delayed reclamation.
//!
//! The pool stores one linear resource in Verus' Leaf-style storage protocol.
//! Each lease receives half of the pool's current rational fraction, so the
//! number of outstanding leases has no fixed integer bound. A lease guards a
//! shared borrow of the stored resource. Reclamation can recover the resource
//! only after all leases have been returned and the pool fraction is whole.
use vstd::{
    prelude::*,
    resource::{frac_opt::Frac, Loc},
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
