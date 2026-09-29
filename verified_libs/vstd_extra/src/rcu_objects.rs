// SPDX-License-Identifier: MPL-2.0
//! Allocation identity and ownership resources for RCU proofs.
//!
//! # Verified Properties
//!
//! Each registration receives a fresh allocation ID within its domain. Persistent
//! block information preserves that ID across publications, including after the
//! physical address is reused. A separate linear permission belongs to the same
//! registration and will be consumed by the retirement protocol.
//!
//! Registration records identity only: neither block information nor a base
//! retire permission grants access to the allocation or permission to reclaim it.
//! A registered object can retain a client-defined linear resource, whose meaning
//! remains the client's responsibility.
use crate::ownership::Inv;
use vstd::{
    prelude::*,
    resource::{
        Loc,
        map::{GhostMapAuth, GhostPersistentPointsTo, GhostPointsTo},
    },
};

verus! {

/// Authoritative allocation registry for one RCU protection domain.
pub tracked struct RcuDomainAuth {
    objects: GhostMapAuth<nat, usize>,
    retire_perms: GhostMapAuth<nat, usize>,
    ghost next_obj: nat,
}

impl Inv for RcuDomainAuth {
    closed spec fn inv(self) -> bool {
        &&& self.objects@ == self.retire_perms@
        &&& forall|obj: nat| #[trigger] self.objects@.contains_key(obj) ==> obj < self.next_obj
    }
}

impl RcuDomainAuth {
    /// Stable identity of this protection domain.
    pub closed spec fn id(self) -> Loc {
        self.objects.id()
    }

    /// Registered allocation IDs and their physical addresses.
    pub closed spec fn objects(self) -> Map<nat, usize> {
        self.objects@
    }

    /// Fresh ID reserved for the next registration.
    pub closed spec fn next_obj(self) -> nat {
        self.next_obj
    }

    /// Resource registry that owns the unique base retire permissions.
    pub closed spec fn retire_registry(self) -> Loc {
        self.retire_perms.id()
    }

    /// Creates an empty RCU protection domain.
    ///
    /// # Postconditions
    /// The invariant holds and the first registration receives ID zero.
    pub proof fn tracked_new() -> (tracked res: Self)
        ensures
            res.inv(),
            res.objects() == Map::<nat, usize>::empty(),
            res.next_obj() == 0,
    {
        let tracked (objects, _) = GhostMapAuth::new(Map::empty());
        let tracked (retire_perms, _) = GhostMapAuth::new(Map::empty());
        RcuDomainAuth { objects, retire_perms, next_obj: 0 }
    }

    /// Registers a non-null pointer with a fresh allocation ID.
    ///
    /// # Preconditions
    /// The domain invariant holds and the pointer is non-null. Registering an
    /// address does not establish that it points to a live allocation.
    ///
    /// # Postconditions
    /// Existing registrations are preserved. The returned persistent identity
    /// and linear permission describe the same new registration.
    pub proof fn tracked_register<T>(tracked &mut self, ptr: *mut T) -> (tracked res:
        RcuRegistration<T>)
        requires
            old(self).inv(),
            ptr.addr() != 0,
        ensures
            final(self).inv(),
            final(self).id() == old(self).id(),
            final(self).retire_registry() == old(self).retire_registry(),
            final(self).next_obj() == old(self).next_obj() + 1,
            final(self).objects() == old(self).objects().insert(old(self).next_obj(), ptr.addr()),
            !old(self).objects().contains_key(res.0.obj()),
            res.0.domain() == final(self).id(),
            res.0.obj() == old(self).next_obj(),
            res.0.ptr() == ptr,
            res.0.addr() == ptr.addr(),
            res.0.inv(),
            res.1.domain() == res.0.domain(),
            res.1.obj() == res.0.obj(),
            res.1.ptr() == ptr,
            res.1.inv(),
            res.1.belongs_to(*final(self)),
    {
        let ghost obj = self.next_obj;
        let tracked object = self.objects.insert(obj, ptr.addr());
        let tracked info = object.persist();
        let tracked perm = self.retire_perms.insert(obj, ptr.addr());
        self.next_obj = self.next_obj + 1;

        assert forall|registered: nat| #[trigger]
            self.objects@.contains_key(registered) implies registered < self.next_obj by {
            if registered != obj {
                assert(old(self).objects().contains_key(registered));
            }
        };

        (RcuBlockInfo { info, ptr }, RcuBaseRetirePerm { domain: self.id(), perm, ptr })
    }

    /// Agrees a persistent registration with its authoritative address entry.
    ///
    /// # Preconditions
    /// The block information belongs to this protection domain.
    ///
    /// # Postconditions
    /// The domain contains the recorded allocation ID and address.
    pub proof fn lemma_block_info_agree<T>(tracked &self, tracked info: &RcuBlockInfo<T>)
        requires
            info.domain() == self.id(),
        ensures
            self.objects().contains_pair(info.obj(), info.addr()),
    {
        info.info.agree(&self.objects);
    }
}

/// Persistent identity of one registered allocation, without physical ownership.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuBlockInfo<T> {
    info: GhostPersistentPointsTo<nat, usize>,
    ghost ptr: *mut T,
}

impl<T> Inv for RcuBlockInfo<T> {
    closed spec fn inv(self) -> bool {
        &&& self.addr() == self.ptr().addr()
        &&& self.ptr().addr() != 0
    }
}

impl<T> RcuBlockInfo<T> {
    /// Protection domain in which the allocation was registered.
    pub closed spec fn domain(self) -> Loc {
        self.info.id()
    }

    /// Allocation ID, independent of address and publication timestamp.
    pub closed spec fn obj(self) -> nat {
        self.info.key()
    }

    /// Typed pointer supplied at registration.
    pub closed spec fn ptr(self) -> *mut T {
        self.ptr
    }

    /// Physical address recorded in the authoritative registry.
    pub closed spec fn addr(self) -> usize {
        self.info.value()
    }

    /// Exposes the address facts hidden by the registration invariant.
    ///
    /// # Preconditions
    /// The block information satisfies its invariant.
    ///
    /// # Postconditions
    /// Its recorded address equals the pointer address and is nonzero.
    pub proof fn lemma_address(tracked &self)
        requires
            self.inv(),
        ensures
            self.addr() == self.ptr().addr(),
            self.ptr().addr() != 0,
    {
    }

    /// Duplicates persistent block information for another publication.
    ///
    /// # Postconditions
    /// The duplicate describes exactly the same registration.
    pub proof fn tracked_duplicate(tracked &self) -> (tracked res: Self)
        ensures
            res.domain() == self.domain(),
            res.obj() == self.obj(),
            res.ptr() == self.ptr(),
            res.addr() == self.addr(),
            res.inv() == self.inv(),
    {
        let tracked info = self.info.duplicate();
        RcuBlockInfo { info, ptr: self.ptr }
    }
}

/// Unique base permission retained until the allocation is retired.
///
/// This token supplies linear identity, not evidence of detachment or a grace
/// period. It cannot justify reclaiming physical ownership by itself.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuBaseRetirePerm<T> {
    ghost domain: Loc,
    perm: GhostPointsTo<nat, usize>,
    ghost ptr: *mut T,
}

impl<T> Inv for RcuBaseRetirePerm<T> {
    closed spec fn inv(self) -> bool {
        &&& self.addr() == self.ptr().addr()
        &&& self.ptr().addr() != 0
    }
}

impl<T> RcuBaseRetirePerm<T> {
    /// Protection domain of the matching block information.
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    /// Allocation ID for which this permission is unique.
    pub closed spec fn obj(self) -> nat {
        self.perm.key()
    }

    /// Typed pointer supplied at registration.
    pub closed spec fn ptr(self) -> *mut T {
        self.ptr
    }

    /// Physical address of the registered allocation.
    pub closed spec fn addr(self) -> usize {
        self.perm.value()
    }

    /// Binds the permission to both registries owned by the domain.
    pub closed spec fn belongs_to(self, domain: RcuDomainAuth) -> bool {
        &&& self.domain() == domain.id()
        &&& self.perm.id() == domain.retire_registry()
    }

    /// Proves that two base retire permissions cannot name the same allocation.
    ///
    /// # Preconditions
    /// Both permissions belong to the same domain.
    ///
    /// # Postconditions
    /// Their allocation IDs differ and this permission is preserved.
    pub proof fn lemma_distinct(tracked &mut self, tracked other: &Self, domain: RcuDomainAuth)
        requires
            old(self).belongs_to(domain),
            other.belongs_to(domain),
        ensures
            final(self).domain() == old(self).domain(),
            final(self).obj() == old(self).obj(),
            final(self).ptr() == old(self).ptr(),
            final(self).addr() == old(self).addr(),
            final(self).inv() == old(self).inv(),
            final(self).belongs_to(domain),
            final(self).obj() != other.obj(),
    {
        self.perm.disjoint(&other.perm);
    }
}

/// Persistent identity and linear base retire permission from one registration.
pub type RcuRegistration<T> = (RcuBlockInfo<T>, RcuBaseRetirePerm<T>);

/// Proves that address reuse creates a new ID while duplication preserves it.
///
/// # Preconditions
/// The pointer has a nonzero address.
///
/// # Postconditions
/// Two copies of the first registration agree, while a second registration at
/// that same address has a different allocation ID in the same domain.
pub proof fn lemma_registration_distinguishes_reused_address<T>(ptr: *mut T) -> (tracked res: (
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
        res.0.obj() < res.2.obj(),
        res.0.addr() == res.1.addr() == res.2.addr() == ptr.addr(),
{
    let tracked mut domain = RcuDomainAuth::tracked_new();
    let tracked (first, _) = domain.tracked_register(ptr);
    let tracked history_copy = first.tracked_duplicate();
    let tracked (second, _) = domain.tracked_register(ptr);
    assert(first.domain() == history_copy.domain());
    assert(first.domain() == second.domain());
    assert(first.obj() == history_copy.obj());
    assert(first.obj() < second.obj());
    assert(first.addr() == history_copy.addr() == second.addr() == ptr.addr());
    domain.lemma_block_info_agree(&history_copy);
    assert(domain.objects().contains_pair(first.obj(), ptr.addr()));
    (first, history_copy, second)
}

/// One allocation's registration paired with a linear client resource.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuOwnedObject<T, O> {
    registration: RcuRegistration<T>,
    ownership: O,
}

impl<T, O> Inv for RcuOwnedObject<T, O> {
    open spec fn inv(self) -> bool {
        &&& self.block_info().inv()
        &&& self.retire_perm().inv()
        &&& self.block_info().domain() == self.retire_perm().domain()
        &&& self.block_info().obj() == self.retire_perm().obj()
        &&& equal(self.block_info().ptr(), self.retire_perm().ptr())
    }
}

impl<T, O> RcuOwnedObject<T, O> {
    /// Persistent identity and unique base retire permission.
    pub closed spec fn registration(self) -> RcuRegistration<T> {
        self.registration
    }

    /// Persistent identity of the registered allocation.
    pub open spec fn block_info(self) -> RcuBlockInfo<T> {
        self.registration().0
    }

    /// Unique base retire permission for the registered allocation.
    pub open spec fn retire_perm(self) -> RcuBaseRetirePerm<T> {
        self.registration().1
    }

    /// Client resource associated with this registration.
    pub closed spec fn ownership(self) -> O {
        self.ownership
    }

    /// Pairs a consistent registration with a client resource without copying either.
    pub proof fn tracked_new(
        tracked registration: RcuRegistration<T>,
        tracked ownership: O,
    ) -> (tracked res: Self)
        requires
            registration.0.inv(),
            registration.1.inv(),
            registration.0.domain() == registration.1.domain(),
            registration.0.obj() == registration.1.obj(),
            equal(registration.0.ptr(), registration.1.ptr()),
        ensures
            res.inv(),
            res.registration() == registration,
            res.ownership() == ownership,
    {
        Self { registration, ownership }
    }

    /// Consumes the wrapper and returns its unchanged registration and client resource.
    pub proof fn tracked_into_parts(tracked self) -> tracked (RcuRegistration<T>, O)
        returns
            (self.registration(), self.ownership()),
    {
        (self.registration, self.ownership)
    }
}

} // verus!
