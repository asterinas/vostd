use vstd::prelude::*;

verus! {

/// A mutable partition of the raw-token store. Splitting out a shared loan
/// freezes only the selected token, not the recursive subtree or other slots.
/// The backing map must outlive every `FrameRef` built from a loan. In
/// particular, a loaned token cannot be removed to restore an owning `Frame`
/// until those borrows end; this type does not circumvent that restriction.
///
/// The borrow/writeback mechanism is independent of the token representation;
/// the page-table instantiation uses `Paddr` and `FrameRawPerms`.
pub tracked struct MetadataPermissionPartition<'a, K, P> {
    pub permissions: &'a mut Map<K, P>,
}

impl<'a, K, P> MetadataPermissionPartition<'a, K, P> {
    /// Parks an already-transferred token without replacing an existing count.
    pub proof fn tracked_insert(tracked self, key: K, tracked permission: P) -> (tracked result: Self)
        requires
            !self.permissions.contains_key(key),
        ensures
            *result.permissions == old(self.permissions).insert(key, permission),
            mut_ref_future(self.permissions) == mut_ref_future(result.permissions),
    {
        self.permissions.tracked_insert(key, permission);
        self
    }

    /// Removes the original raw token for restoration into an owning handle.
    pub proof fn tracked_remove(tracked self, key: K) -> (tracked (permission, remainder): (P, Self))
        requires
            self.permissions.contains_key(key),
        ensures
            permission == (*old(self.permissions))[key],
            *remainder.permissions == old(self.permissions).remove(key),
            mut_ref_future(self.permissions) == mut_ref_future(remainder.permissions),
    {
        let tracked permission = self.permissions.tracked_remove(key);
        (permission, self)
    }

    /// Borrows a stable map slot and returns the independently mutable rest.
    /// Moving the returned partition or a recursive owner does not move the
    /// token backing `permission`; writeback rejoins the maps at borrow end.
    pub proof fn tracked_borrow(
        tracked self,
        key: K,
    ) -> (tracked (permission, remainder): (&'a P, Self))
        requires
            self.permissions.contains_key(key),
        ensures
            *permission == (*old(self.permissions))[key],
            *remainder.permissions == old(self.permissions).remove_keys(set![key]),
            mut_ref_future(self.permissions) == Map::empty().insert(key, *permission)
                .union_prefer_right(mut_ref_future(remainder.permissions)),
    {
        let tracked (slot, permissions) = self.permissions.tracked_borrow_mut_split(set![key]);
        let tracked permission = slot.tracked_borrow(key);
        (permission, Self { permissions })
    }

    /// Parks a transferred token and immediately lends it for a returned guard.
    pub proof fn tracked_insert_and_borrow(
        tracked self,
        key: K,
        tracked permission: P,
    ) -> (tracked (loan, remainder): (&'a P, Self))
        requires
            !self.permissions.contains_key(key),
        ensures
            *loan == permission,
            *remainder.permissions == *old(self.permissions),
            mut_ref_future(self.permissions) == Map::empty().insert(
                key, permission,
            ).union_prefer_right(mut_ref_future(remainder.permissions)),
    {
        let tracked partition = self.tracked_insert(key, permission);
        partition.tracked_borrow(key)
    }
}

/// Cursor-side metadata loans. Only references travel with cursor navigation;
/// all counted resources remain in the caller-owned backing map. This state
/// is independent of the recursive structural CursorOwner continuations.
/// Each operation records the remainder's current value and future writeback,
/// so the caller can recover the same tokens after the session and its loans
/// end. Moving or consuming this wrapper does not itself end escaped loans.
pub tracked struct MetadataPermissionLoans<'a, K, P> {
    pub remainder: Option<MetadataPermissionPartition<'a, K, P>>,
    pub loans: Map<K, &'a P>,
}

/// One-use authority to consume a live handle whose token has been parked.
/// A shared metadata borrow alone must not authorize another raw PTE. Fields
/// are private: the only constructor consumes and parks an owned token.
pub tracked struct MetadataPermissionLoan<'a, K, P> {
    ghost key: K,
    permission: &'a P,
}

impl<'a, K, P> MetadataPermissionLoan<'a, K, P> {
    pub closed spec fn key(self) -> K { self.key }

    pub closed spec fn value(self) -> P { *self.permission }

    /// The borrow is of the stable slot, not of this movable one-use ticket.
    pub proof fn tracked_borrow(tracked &self) -> (tracked permission: &'a P)
        returns self.value(),
    {
        self.permission
    }
}

impl<'a, K, P> MetadataPermissionLoans<'a, K, P> {
    pub open spec fn permissions(self) -> Map<K, P> {
        let remaining = if self.remainder is Some {
            *self.remainder->0.permissions
        } else {
            Map::empty()
        };
        remaining.union_prefer_right(self.loans.map_values(|permission: &P| *permission))
    }

    /// Starts a borrowing session without moving any tokens from the map.
    pub proof fn tracked_new(tracked permissions: &'a mut Map<K, P>) -> (tracked result: Self)
        ensures
            result.remainder is Some,
            result.loans == Map::<K, &'a P>::empty(),
            result.permissions() == *old(permissions),
            mut_ref_future(permissions) == mut_ref_future(result.remainder->0.permissions),
    {
        Self {
            remainder: Some(MetadataPermissionPartition { permissions }),
            loans: Map::tracked_empty(),
        }
    }

    /// Reuses an existing shared loan, or splits a new slot from the remainder.
    pub proof fn tracked_borrow(tracked &mut self, key: K) -> (tracked permission: &'a P)
        requires
            old(self).remainder is Some,
            old(self).permissions().contains_key(key),
        ensures
            final(self).remainder is Some,
            *permission == old(self).permissions()[key],
            final(self).permissions() == old(self).permissions(),
            final(self).loans == old(self).loans.insert(key, permission),
            *final(self).remainder->0.permissions
                == if old(self).loans.contains_key(key) {
                    *old(self).remainder->0.permissions
                } else {
                    old(self).remainder->0.permissions.remove(key)
                },
            mut_ref_future(old(self).remainder->0.permissions)
                == if old(self).loans.contains_key(key) {
                    mut_ref_future(final(self).remainder->0.permissions)
                } else {
                    Map::empty().insert(key, *permission).union_prefer_right(
                        mut_ref_future(final(self).remainder->0.permissions),
                    )
                },
    {
        if self.loans.contains_key(key) {
            *self.loans.tracked_borrow(key)
        } else {
            let tracked partition = self.remainder.tracked_take();
            let tracked (permission, remainder) = partition.tracked_borrow(key);
            self.remainder = Some(remainder);
            self.loans.tracked_insert(key, permission);
            permission
        }
    }

    /// Parks the one token transferred from a live handle.
    pub proof fn tracked_insert(tracked &mut self, key: K, tracked permission: P)
        requires
            old(self).remainder is Some,
            !old(self).permissions().contains_key(key),
        ensures
            final(self).remainder is Some,
            final(self).loans == old(self).loans,
            final(self).permissions() == old(self).permissions().insert(key, permission),
            *final(self).remainder->0.permissions
                == old(self).remainder->0.permissions.insert(key, permission),
            mut_ref_future(old(self).remainder->0.permissions)
                == mut_ref_future(final(self).remainder->0.permissions),
    {
        let tracked partition = self.remainder.tracked_take();
        self.remainder = Some(partition.tracked_insert(key, permission));
    }

    /// Moves an owned token into stable storage and issues exactly one ticket
    /// for the subsequent live-handle-to-PTE transition.
    pub proof fn tracked_park_and_lend(
        tracked &mut self,
        key: K,
        tracked permission: P,
    ) -> (tracked loan: MetadataPermissionLoan<'a, K, P>)
        requires
            old(self).remainder is Some,
            !old(self).permissions().contains_key(key),
        ensures
            final(self).remainder is Some,
            final(self).permissions() == old(self).permissions().insert(key, permission),
            loan.key() == key,
            loan.value() == permission,
            *final(self).remainder->0.permissions == *old(self).remainder->0.permissions,
            mut_ref_future(old(self).remainder->0.permissions)
                == Map::empty().insert(key, permission).union_prefer_right(
                    mut_ref_future(final(self).remainder->0.permissions),
                ),
    {
        self.tracked_insert(key, permission);
        let tracked permission = self.tracked_borrow(key);
        MetadataPermissionLoan { key, permission }
    }

    /// Restores an unborrowed token. A leased token can only be recovered from
    /// the backing map after the session and every escaped loan have ended;
    /// it cannot be taken through this API, even if its guard was dropped.
    pub proof fn tracked_remove(tracked &mut self, key: K) -> (tracked permission: P)
        requires
            old(self).remainder is Some,
            old(self).remainder->0.permissions.contains_key(key),
            !old(self).loans.contains_key(key),
        ensures
            final(self).remainder is Some,
            final(self).loans == old(self).loans,
            permission == old(self).permissions()[key],
            final(self).permissions() == old(self).permissions().remove(key),
            *final(self).remainder->0.permissions
                == old(self).remainder->0.permissions.remove(key),
            mut_ref_future(old(self).remainder->0.permissions)
                == mut_ref_future(final(self).remainder->0.permissions),
    {
        let tracked partition = self.remainder.tracked_take();
        let tracked (permission, remainder) = partition.tracked_remove(key);
        self.remainder = Some(remainder);
        permission
    }
}

} // verus!
