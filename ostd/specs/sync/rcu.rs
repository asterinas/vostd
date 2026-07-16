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
//! The module remains proof-only. The executable RCU must still connect its
//! preemption guard to the same domain's reader token and route the retire
//! permission released by pointer replacement into the callback monitor.
use core::marker::PhantomData;

use super::weak_memory::{History, Msg, WeakAtomicInvariantPredicate, WmView};
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::map::{GhostMapAuth, GhostPersistentPointsTo, GhostPointsTo};

verus! {

pub type LinkIndex = nat;

pub type LinkEdge = (nat, LinkIndex);

/// Proof summary for a type-erased RCU callback.
///
/// The executable callback may close over any sized Rust value, but the RCU
/// proof only needs to know which logical object it will reclaim and which
/// grace-period generation retired that object. `domain` identifies the RCU
/// protection domain, and `obj` identifies the reclaimed allocation/object
/// inside that domain.
pub ghost struct RcuCallbackSummary {
    /// The RCU protection domain whose grace period governs this callback.
    pub domain: Loc,
    /// Logical identity of the retired object inside `domain`.
    pub obj: nat,
    /// The domain-local epoch in which `obj` was retired.
    pub retire_epoch: nat,
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

    pub closed spec fn wf(self) -> bool {
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
/// grace-period epoch. In the paper, removal belongs to `SeenRemoved` and link
/// histories, while expiration/reclamation belongs to the base RCU protocol.
/// A root store publishes a pointer, but cannot by itself prove that a node is
/// unreachable from every incoming link.
pub tracked struct RcuRootGhost {
    domain: RcuDomainAuth,
    ghost publications: Seq<Option<nat>>,
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

    pub closed spec fn publications(self) -> Seq<Option<nat>> {
        self.publications
    }

    pub open spec fn published_at(self, ts: nat) -> Option<RcuPublishedObject>
        recommends
            ts < self.publications().len(),
    {
        match self.publications()[ts as int] {
            Some(obj) => Some(
                RcuPublishedObject { domain: self.domain(), obj, addr: self.objects()[obj] },
            ),
            None => None,
        }
    }

    /// Allocation identity carried by the latest atomic message.
    pub open spec fn current(self) -> Option<RcuPublishedObject>
        recommends
            self.publications().len() > 0,
    {
        self.published_at((self.publications().len() - 1) as nat)
    }

    /// Allocate a fresh publication registry containing the initial message.
    ///
    /// A non-null initial value is registered exactly once and the registration
    /// resources are returned to the caller. The root history retains only the
    /// allocation ID; it does not consume the unique retire permission.
    pub proof fn tracked_initial<T>(ptr: *mut T) -> (tracked res: (
        Self,
        Option<RcuRegistration<T>>,
    ))
        ensures
            rcu_root_history_inv(seq![Msg { value: ptr, view: WmView::empty() }], res.0),
            (res.1 is Some) == (ptr.addr() != 0),
            res.1 is Some ==> res.1->Some_0.0.ptr() == ptr,
            res.1 is Some ==> res.1->Some_0.0.obj() == res.1->Some_0.1.obj(),
            res.1 is Some ==> res.1->Some_0.0.domain() == res.0.domain(),
            res.1 is Some ==> res.0.publications()[0] == Some(res.1->Some_0.0.obj()),
            res.1 is Some ==> res.1->Some_0.0.wf(),
            current_registration_matches(res.0, res.1),
    {
        let tracked mut domain = RcuDomainAuth::tracked_new();
        if ptr.addr() == 0 {
            (RcuRootGhost { domain, publications: seq![None] }, None)
        } else {
            let tracked (block_info, retire_perm) = domain.tracked_register(ptr);
            let ghost obj = block_info.obj();
            assert(domain.objects().contains_pair(obj, ptr.addr()));
            (
                RcuRootGhost { domain, publications: seq![Some(obj)] },
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
        prev: History<*mut T>,
        next: History<*mut T>,
        msg: Msg<*mut T>,
    ) -> (tracked res: Option<RcuRegistration<T>>)
        requires
            rcu_root_history_inv(prev, *old(self)),
            next == prev.push(msg),
        ensures
            rcu_root_history_inv(next, *final(self)),
            final(self).domain() == old(self).domain(),
            final(self).domain_auth().retire_registry() == old(
                self,
            ).domain_auth().retire_registry(),
            (res is Some) == (msg.value.addr() != 0),
            res is Some ==> res->Some_0.0.ptr() == msg.value,
            res is Some ==> res->Some_0.0.obj() == res->Some_0.1.obj(),
            current_registration_matches(*final(self), res),
    {
        let ghost ts = prev.len();
        assert(self.publications().len() == ts);

        let tracked res = if msg.value.addr() == 0 {
            self.publications = self.publications.push(None);
            None
        } else {
            let tracked (block_info, retire_perm) = self.domain.tracked_register(msg.value);
            let ghost obj = block_info.obj();
            self.publications = self.publications.push(Some(obj));
            Some((block_info, retire_perm))
        };

        assert forall|i: int| 0 <= i < next.len() implies {
            match #[trigger] self.publications()[i] {
                None => next[i].value.addr() == 0,
                Some(obj) => {
                    &&& next[i].value.addr() != 0
                    &&& self.objects().contains_pair(obj, next[i].value.addr())
                },
            }
        } by {
            if i == prev.len() {
                assert(next[i] == msg);
            } else {
                assert(i < prev.len());
                assert(next[i] == prev[i]);
                assert(self.publications()[i] == old(self).publications()[i]);
                match self.publications()[i] {
                    Some(obj) => {
                        assert(old(self).objects().contains_pair(obj, prev[i].value.addr()));
                        assert(self.objects().contains_pair(obj, next[i].value.addr()));
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
        prev: History<*mut T>,
        next: History<*mut T>,
        msg: Msg<*mut T>,
        tracked info: &RcuBlockInfo<T>,
    )
        requires
            rcu_root_history_inv(prev, *old(self)),
            next == prev.push(msg),
            info.domain() == old(self).domain(),
            info.ptr() == msg.value,
            info.wf(),
        ensures
            rcu_root_history_inv(next, *final(self)),
            final(self).domain() == old(self).domain(),
            final(self).domain_auth().retire_registry() == old(
                self,
            ).domain_auth().retire_registry(),
            final(self).objects() == old(self).objects(),
            final(self).publications() == old(self).publications().push(Some(info.obj())),
    {
        let ghost ts = prev.len();
        assert(self.publications().len() == ts);
        self.domain.lemma_block_info_agree(info);
        self.publications = self.publications.push(Some(info.obj()));
        assert(self.objects() == old(self).objects());

        assert forall|i: int| 0 <= i < next.len() implies {
            match #[trigger] self.publications()[i] {
                None => next[i].value.addr() == 0,
                Some(obj) => {
                    &&& next[i].value.addr() != 0
                    &&& self.objects().contains_pair(obj, next[i].value.addr())
                },
            }
        } by {
            if i == prev.len() {
                assert(next[i] == msg);
                assert(info.addr() == msg.value.addr());
                assert(msg.value.addr() != 0);
                assert(self.publications()[i] == Some(info.obj()));
                assert(self.objects().contains_pair(info.obj(), next[i].value.addr()));
            } else {
                assert(i < prev.len());
                assert(next[i] == prev[i]);
                assert(self.publications()[i] == old(self).publications()[i]);
                match self.publications()[i] {
                    Some(obj) => {
                        assert(old(self).objects().contains_pair(obj, prev[i].value.addr()));
                        assert(self.objects().contains_pair(obj, next[i].value.addr()));
                    },
                    None => {},
                }
            }
        };
    }
}

/// Agreement between the weak-memory message history and RCU allocation IDs.
pub open spec fn rcu_root_history_inv<T>(history: History<*mut T>, ghost: RcuRootGhost) -> bool {
    &&& history.len() >= 1
    &&& ghost.domain_wf()
    &&& ghost.publications().len() == history.len()
    &&& forall|i: int|
        0 <= i < history.len() ==> {
            match #[trigger] ghost.publications()[i] {
                None => history[i].value.addr() == 0,
                Some(obj) => {
                    &&& history[i].value.addr() != 0
                    &&& ghost.objects().contains_pair(obj, history[i].value.addr())
                },
            }
        }
}

/// The weak-memory invariant for the root pointer stored in an executable RCU
/// cell.
///
/// The key is the cell's nullability: `true` for `RcuOption`, `false` for
/// `Rcu`. The predicate connects each atomic message both to the public
/// nullability contract and to its domain-local allocation identity. Physical
/// ownership, read tokens, and reclamation are deliberately modeled by the
/// traversal/reclaim tokens below and will be wired in later steps.
pub struct RcuWeakAtomicInv;

pub open spec fn rcu_history_inv<T>(nullable: bool, history: History<*mut T>) -> bool {
    &&& history.len() >= 1
    &&& !nullable ==> forall|i: int|
        0 <= i < history.len() ==> #[trigger] history[i].value.addr() != 0
}

impl<T> WeakAtomicInvariantPredicate<bool, *mut T, RcuRootGhost> for RcuWeakAtomicInv {
    open spec fn atomic_inv(nullable: bool, history: History<*mut T>, g: RcuRootGhost) -> bool {
        &&& rcu_history_inv(nullable, history)
        &&& rcu_root_history_inv(history, g)
    }
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
}

impl<T, O> RcuRootOwnedGhost<T, O> {
    pub closed spec fn root(self) -> RcuRootGhost {
        self.root
    }

    pub closed spec fn domain(self) -> Loc {
        self.root().domain()
    }

    pub closed spec fn publications(self) -> Seq<Option<nat>> {
        self.root().publications()
    }

    pub open spec fn published_at(self, ts: nat) -> Option<RcuPublishedObject>
        recommends
            ts < self.publications().len(),
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

    pub open spec fn ownership_wf(self) -> bool {
        current_registration_matches(self.root(), self.current_registration())
    }

    /// Initializes root history and retains the initial registration as the
    /// current unique ownership resource.
    pub proof fn tracked_initial(ptr: *mut T, tracked ownership: Option<O>) -> (tracked res: Self)
        requires
            (ownership is Some) == (ptr.addr() != 0),
        ensures
            rcu_owned_root_history_inv(seq![Msg { value: ptr, view: WmView::empty() }], res),
            (res.current_registration() is Some) == (ptr.addr() != 0),
            res.current_registration() is Some ==> res.current_registration()->Some_0.0.ptr()
                == ptr,
            res.current_ownership() == ownership,
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
        let tracked (root, registration) = RcuRootGhost::tracked_initial(ptr);
        let tracked current = match registration {
            Some(registration) => {
                Some(RcuOwnedObject { registration, ownership: ownership.tracked_unwrap() })
            },
            None => None,
        };
        RcuRootOwnedGhost { root, current }
    }

    /// Publishes a fresh allocation and retires the previously current root.
    ///
    /// A root replacement is also the complete traversal-removal proof for
    /// the old root: this cell was its only incoming root edge. The old base
    /// retire permission is therefore consumed before ownership leaves the
    /// atomic invariant.
    pub proof fn tracked_push_fresh<OwnPred>(
        tracked &mut self,
        prev: History<*mut T>,
        next: History<*mut T>,
        msg: Msg<*mut T>,
        tracked ownership: Option<O>,
    ) -> (tracked detached: Option<RcuRetiredOwnedObject<T, O>>) where
        OwnPred: RcuRootOwnershipPredicate<T, O>,

        requires
            rcu_owned_root_history_inv(prev, *old(self)),
            rcu_current_ownership_inv::<T, O, OwnPred>(*old(self)),
            next == prev.push(msg),
            (ownership is Some) == (msg.value.addr() != 0),
        ensures
            rcu_owned_root_history_inv(next, *final(self)),
            final(self).domain() == old(self).domain(),
            match detached {
                Some(detached) => {
                    &&& old(self).current_registration() is Some
                    &&& detached.object() == old(self).current_registration()->Some_0.0
                    &&& detached.retired().domain() == detached.domain()
                    &&& detached.retired().obj() == detached.obj()
                    &&& detached.retired().ptr() == detached.ptr()
                    &&& old(self).current_ownership() == Some(detached.ownership())
                    &&& equal(detached.ptr(), prev[(prev.len() - 1) as int].value)
                    &&& OwnPred::owns(detached.ptr(), detached.ownership())
                },
                None => old(self).current_registration() is None,
            },
            (final(self).current_registration() is Some) == (msg.value.addr() != 0),
            final(self).current_registration() is Some
                ==> final(self).current_registration()->Some_0.0.ptr() == msg.value,
            final(self).current_ownership() == ownership,
            match final(self).current_owned() {
                Some(owned) => {
                    &&& msg.value.addr() != 0
                    &&& equal(owned.block_info().ptr(), msg.value)
                    &&& ownership == Some(owned.ownership())
                },
                None => {
                    &&& msg.value.addr() == 0
                    &&& ownership is None
                },
            },
    {
        assert(current_registration_matches(self.root(), self.current_registration()));
        let tracked old_current = if self.current is Some {
            Some(self.current.tracked_take())
        } else {
            None
        };
        let tracked new_registration = self.root.tracked_push_fresh(prev, next, msg);
        let tracked new_current = match new_registration {
            Some(registration) => {
                Some(RcuOwnedObject { registration, ownership: ownership.tracked_unwrap() })
            },
            None => None,
        };
        let tracked detached = match old_current {
            Some(owned) => {
                let tracked (registration, old_ownership) = owned.tracked_into_parts();
                let tracked (object, base) = registration;
                assert(base.belongs_to(self.root.domain));
                let ghost seen_removed = RcuSeenRemoved {
                    removed: Set::empty().insert(object.obj()),
                    link_view: RcuLinkView::empty(),
                };
                let tracked retire = lift_retire_perm(base, seen_removed);
                let tracked retired = self.root.domain.tracked_retire(retire);
                Some(RcuRetiredOwnedObject { object, retired, ownership: old_ownership })
            },
            None => None,
        };
        self.current = new_current;
        assert(current_registration_matches(self.root(), self.current_registration()));
        detached
    }

    /// Re-publishes the currently owned registration without changing its AId
    /// or releasing its unique retire permission.
    pub proof fn tracked_republish_current(
        tracked &mut self,
        prev: History<*mut T>,
        next: History<*mut T>,
        msg: Msg<*mut T>,
    )
        requires
            rcu_owned_root_history_inv(prev, *old(self)),
            next == prev.push(msg),
            old(self).current_registration() is Some,
            old(self).current_registration()->Some_0.0.ptr() == msg.value,
        ensures
            rcu_owned_root_history_inv(next, *final(self)),
            final(self).domain() == old(self).domain(),
            final(self).current_registration() == old(self).current_registration(),
    {
        let tracked owned = self.current.tracked_take();
        self.root.tracked_push_registered(prev, next, msg, &owned.registration.0);
        self.current = Some(owned);
        assert(current_registration_matches(self.root(), self.current_registration()));
    }
}

/// The current ownership resource agrees with the latest publication, while
/// older history entries need only agree with persistent registration metadata.
pub open spec fn rcu_owned_root_history_inv<T, O>(
    history: History<*mut T>,
    ghost: RcuRootOwnedGhost<T, O>,
) -> bool {
    &&& rcu_root_history_inv(history, ghost.root())
    &&& ghost.ownership_wf()
    &&& match ghost.current_registration() {
        Some(registration) => equal(
            registration.0.ptr(),
            history[(history.len() - 1) as int].value,
        ),
        None => history[(history.len() - 1) as int].value.addr() == 0,
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
    history: History<*mut T>,
    tracked ghost: &RcuRootOwnedGhost<T, O>,
) where OwnPred: RcuRootOwnershipPredicate<T, O>
    requires
        rcu_owned_root_history_inv(history, *ghost),
        rcu_current_ownership_inv::<T, O, OwnPred>(*ghost),
    ensures
        match ghost.current_owned() {
            Some(owned) => {
                &&& owned.block_info().wf()
                &&& equal(owned.block_info().ptr(), history[(history.len() - 1) as int].value)
                &&& OwnPred::owns(owned.block_info().ptr(), owned.ownership())
            },
            None => history[(history.len() - 1) as int].value.addr() == 0,
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

impl<T, O, OwnPred> WeakAtomicInvariantPredicate<
    bool,
    *mut T,
    RcuRootOwnedGhost<T, O>,
> for RcuOwnedWeakAtomicInv<OwnPred> where OwnPred: RcuRootOwnershipPredicate<T, O> {
    open spec fn atomic_inv(
        nullable: bool,
        history: History<*mut T>,
        g: RcuRootOwnedGhost<T, O>,
    ) -> bool {
        &&& rcu_history_inv(nullable, history)
        &&& rcu_owned_root_history_inv(history, g)
        &&& rcu_current_ownership_inv::<T, O, OwnPred>(g)
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
/// `states[i]` summarizes the lock-protected monitor state at the moment flag
/// message `i` was appended. This is intentionally a summary: the concrete
/// callback vectors live in the monitor state protected by its lock, and the
/// agreement between `states[i]` and that state is established by the writer,
/// which performs every flag store while holding the monitor lock.
pub tracked struct RcuMonitorFlagGhost {
    pub ghost states: Seq<MonitorStateView>,
}

impl RcuMonitorFlagGhost {
    pub open spec fn initial() -> Self {
        RcuMonitorFlagGhost { states: seq![MonitorStateView::initial()] }
    }

    /// Proof-mode constructor for the tracked ghost state stored inside the
    /// monitor flag's weak atomic invariant.
    pub proof fn tracked_initial() -> (tracked res: Self)
        ensures
            res == Self::initial(),
    {
        RcuMonitorFlagGhost { states: seq![MonitorStateView::initial()] }
    }

    pub open spec fn push(self, state: MonitorStateView) -> Self {
        RcuMonitorFlagGhost { states: self.states.push(state) }
    }

    pub proof fn tracked_push(tracked self, state: MonitorStateView) -> (tracked res: Self)
        ensures
            res == self.push(state),
    {
        RcuMonitorFlagGhost { states: self.states.push(state) }
    }

    /// Whether the state recorded at flag message `i` still had work pending.
    pub open spec fn pending_at(self, i: int) -> bool {
        self.states[i].has_pending_work()
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
    history: History<bool>,
    ghost: RcuMonitorFlagGhost,
) -> bool {
    &&& history.len() >= 1
    &&& ghost.states.len() == history.len()
    &&& forall|i: int| 0 <= i < history.len() ==> (#[trigger] ghost.states[i]).wf()
    &&& forall|i: int|
        0 <= i < history.len() ==> {
            !(#[trigger] history[i].value) ==> ghost.states[i].no_pending_work()
        }
}

pub struct RcuMonitorFlagInv;

impl WeakAtomicInvariantPredicate<(), bool, RcuMonitorFlagGhost> for RcuMonitorFlagInv {
    open spec fn atomic_inv(_k: (), history: History<bool>, ghost: RcuMonitorFlagGhost) -> bool {
        rcu_monitor_flag_history_inv(history, ghost)
    }
}

pub proof fn rcu_monitor_flag_initial_inv()
    ensures
        RcuMonitorFlagInv::atomic_inv(
            (),
            seq![Msg { value: false, view: WmView::empty() }],
            RcuMonitorFlagGhost::initial(),
        ),
{
}

/// Pushing one flag message preserves the history invariant, provided the
/// writer records a well-formed state snapshot and only writes `false` when
/// that snapshot has no pending work.
///
/// This is the proof obligation of the future `set_monitoring` helper: it
/// stores the flag while holding the monitor lock, so it can supply the
/// lock-protected state view as the snapshot.
pub proof fn preserve_rcu_monitor_flag_inv_on_push(
    prev: History<bool>,
    next: History<bool>,
    msg: Msg<bool>,
    prev_ghost: RcuMonitorFlagGhost,
    next_ghost: RcuMonitorFlagGhost,
    state: MonitorStateView,
)
    requires
        rcu_monitor_flag_history_inv(prev, prev_ghost),
        next == prev.push(msg),
        next_ghost == prev_ghost.push(state),
        state.wf(),
        !msg.value ==> state.no_pending_work(),
    ensures
        rcu_monitor_flag_history_inv(next, next_ghost),
{
    assert(next.len() >= 1);
    assert(next_ghost.states.len() == next.len());
    assert forall|i: int| 0 <= i < next.len() implies (#[trigger] next_ghost.states[i]).wf() by {
        if i == prev.len() {
            assert(next_ghost.states[i] == state);
        } else {
            assert(i < prev.len());
            assert(next_ghost.states[i] == prev_ghost.states[i]);
        }
    };
    assert forall|i: int| 0 <= i < next.len() implies {
        !(#[trigger] next[i].value) ==> next_ghost.states[i].no_pending_work()
    } by {
        if i == prev.len() {
            assert(next[i] == msg);
            assert(next_ghost.states[i] == state);
        } else {
            assert(i < prev.len());
            assert(next[i] == prev[i]);
            assert(next_ghost.states[i] == prev_ghost.states[i]);
        }
    };
}

/// The key safety fact behind the monitor fast path: observing a `false` flag
/// message certifies that the monitor state recorded at that message had no
/// queued callbacks and no incomplete grace period.
pub proof fn rcu_monitor_flag_false_has_no_pending(
    history: History<bool>,
    ghost: RcuMonitorFlagGhost,
    ts: nat,
)
    requires
        rcu_monitor_flag_history_inv(history, ghost),
        ts < history.len(),
        !history[ts as int].value,
    ensures
        ghost.states[ts as int].no_pending_work(),
        ghost.states[ts as int].pending_summaries() == Seq::<RcuCallbackSummary>::empty(),
        ghost.states[ts as int].current_gp.is_complete,
{
    monitor_state_pending_iff_incomplete(ghost.states[ts as int]);
    monitor_state_no_pending_no_summaries(ghost.states[ts as int]);
}

pub proof fn preserve_rcu_history_inv_on_push<T>(
    nullable: bool,
    prev: History<*mut T>,
    next: History<*mut T>,
    msg: Msg<*mut T>,
)
    requires
        rcu_history_inv(nullable, prev),
        next == prev.push(msg),
        nullable || msg.value.addr() != 0,
    ensures
        rcu_history_inv(nullable, next),
{
    assert(next.len() >= 1);
    if !nullable {
        assert forall|i: int| 0 <= i < next.len() implies #[trigger] next[i].value.addr() != 0 by {
            if i == prev.len() {
                assert(next[i] == msg);
            } else {
                assert(i < prev.len());
            }
        };
    }
}

pub proof fn rcu_history_inv_read_nonnull<T>(history: History<*mut T>, ts: nat)
    requires
        rcu_history_inv(false, history),
        ts < history.len(),
    ensures
        history[ts as int].value.addr() != 0,
        !history[ts as int].value.is_null(),
{
    assert(history[ts as int].value.addr() != 0);
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
/// fields private so clients cannot manufacture domain authority.
pub tracked struct RcuDomainAuth {
    objects: GhostMapAuth<nat, usize>,
    retire_perms: GhostMapAuth<nat, usize>,
    readers: GhostMapAuth<nat, bool>,
    ghost next_obj: nat,
    ghost next_reader: nat,
    ghost retired: Set<nat>,
    ghost expired: Set<nat>,
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

    /// Allocations whose retirement is covered by a completed grace period.
    ///
    /// This is the paper's implementation-specific expired set. It is kept
    /// separate from `retired`: a newly retired allocation remains protected
    /// by critical sections until monitor completion moves it here.
    pub closed spec fn expired(self) -> Set<nat> {
        self.expired
    }

    pub closed spec fn reader_registry(self) -> Loc {
        self.readers.id()
    }

    pub closed spec fn retire_registry(self) -> Loc {
        self.retire_perms.id()
    }

    pub closed spec fn next_reader(self) -> nat {
        self.next_reader
    }

    /// Internal consistency of the two resource algebras used by the base RCU
    /// model. The first map backs persistent `BlockInfo`; the second map backs
    /// the unique retire capability.
    pub closed spec fn wf(self) -> bool {
        &&& self.objects@ == self.retire_perms@
        &&& forall|obj: nat| #[trigger] self.objects@.contains_key(obj) ==> obj < self.next_obj()
        &&& forall|tid: nat| #[trigger] self.readers@.contains_key(tid) ==> tid < self.next_reader()
        &&& self.retired().subset_of(self.objects().dom())
        &&& self.expired().subset_of(self.retired())
    }

    /// Allocates a fresh RCU protection domain.
    pub proof fn tracked_new() -> (tracked res: Self)
        ensures
            res.wf(),
            res.objects() == Map::<nat, usize>::empty(),
            res.next_obj() == 0,
    {
        let tracked (objects, _objects_entries) = GhostMapAuth::new(Map::empty());
        let tracked (retire_perms, _retire_entries) = GhostMapAuth::new(Map::empty());
        let tracked (readers, _reader_entries) = GhostMapAuth::new(Map::empty());
        RcuDomainAuth {
            objects,
            retire_perms,
            readers,
            next_obj: 0,
            next_reader: 0,
            retired: Set::empty(),
            expired: Set::empty(),
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
            final(self).next_obj() == old(self).next_obj() + 1,
            final(self).retired() == old(self).retired(),
            final(self).expired() == old(self).expired(),
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
        self.next_obj = self.next_obj + 1;

        assert forall|registered: nat| #[trigger]
            self.objects@.contains_key(registered) implies registered < self.next_obj by {
            if registered != obj {
                assert(old(self).objects().contains_key(registered));
            }
        };

        (
            RcuBlockInfo { info: block_info, ptr },
            RcuBaseRetirePerm { domain: self.id(), perm: retire_perm, ptr },
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
    pub proof fn tracked_register_reader(tracked &mut self) -> (tracked res: RcuInactive)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).retire_registry() == old(self).retire_registry(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).objects() == old(self).objects(),
            final(self).retired() == old(self).retired(),
            final(self).expired() == old(self).expired(),
            res.domain() == final(self).id(),
            res.tid() == old(self).next_reader(),
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
        RcuInactive { domain: self.id(), state }
    }

    /// Starts a read-side critical section, snapshotting the set `X` of AIds
    /// whose grace period had already completed.
    ///
    /// The paper only requires `X` to be a subset of all retired allocations.
    /// Using `retired` itself here would be too strong: a reader may safely
    /// observe a newly retired stale pointer while that retirement's grace
    /// period is still in progress.
    pub proof fn tracked_guard_start(
        tracked &mut self,
        tracked mut inactive: RcuInactive,
    ) -> (tracked res: RcuBaseGuard)
        requires
            old(self).wf(),
            inactive.belongs_to(*old(self)),
            inactive.wf(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).retire_registry() == old(self).retire_registry(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).objects() == old(self).objects(),
            final(self).retired() == old(self).retired(),
            final(self).expired() == old(self).expired(),
            res.belongs_to(*final(self)),
            res.tid() == inactive.tid(),
            res.expired() == old(self).expired(),
            res.protected() == Map::<usize, nat>::empty(),
            res.wf(),
    {
        let ghost tid = inactive.tid();
        inactive.state.agree(&self.readers);
        assert(self.readers@.contains_key(tid));
        inactive.state.update(&mut self.readers, true);
        assert forall|registered: nat| #[trigger]
            self.readers@.contains_key(registered) implies registered < self.next_reader by {
            if registered == tid {
                assert(old(self).readers@.contains_key(registered));
            } else {
                assert(old(self).readers@.contains_key(registered));
            }
        };
        RcuBaseGuard {
            domain: self.id(),
            state: inactive.state,
            expired: self.expired,
            protected: Map::empty(),
        }
    }

    /// Ends a read-side critical section and returns the unique inactive token
    /// for the same reader slot.
    pub proof fn tracked_guard_stop(
        tracked &mut self,
        tracked mut guard: RcuBaseGuard,
    ) -> (tracked res: RcuInactive)
        requires
            old(self).wf(),
            guard.belongs_to(*old(self)),
            guard.wf(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).retire_registry() == old(self).retire_registry(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).objects() == old(self).objects(),
            final(self).retired() == old(self).retired(),
            final(self).expired() == old(self).expired(),
            res.belongs_to(*final(self)),
            res.tid() == guard.tid(),
            res.wf(),
    {
        let ghost tid = guard.tid();
        guard.state.agree(&self.readers);
        assert(self.readers@.contains_key(tid));
        guard.state.update(&mut self.readers, false);
        assert forall|registered: nat| #[trigger]
            self.readers@.contains_key(registered) implies registered < self.next_reader by {
            if registered == tid {
                assert(old(self).readers@.contains_key(registered));
            } else {
                assert(old(self).readers@.contains_key(registered));
            }
        };
        RcuInactive { domain: self.id(), state: guard.state }
    }

    /// Implements the base `rcu-retire` transition by adding the detached AId
    /// to `RcuState.R` and consuming its unique traversal retire permission.
    pub proof fn tracked_retire<T>(
        tracked &mut self,
        tracked retire: RcuRetirePerm<T>,
    ) -> (tracked res: RcuRetired<T>)
        requires
            old(self).wf(),
            retire.belongs_to(*old(self)),
            retire.ready_to_retire(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).retire_registry() == old(self).retire_registry(),
            final(self).reader_registry() == old(self).reader_registry(),
            final(self).objects() == old(self).objects(),
            final(self).retired() == old(self).retired().insert(retire.obj()),
            final(self).expired() == old(self).expired(),
            res.domain() == final(self).id(),
            res.obj() == retire.obj(),
            res.ptr() == retire.ptr(),
    {
        retire.base.perm.agree(&self.retire_perms);
        assert(self.objects().contains_key(retire.obj()));
        self.retired = self.retired.insert(retire.obj());
        assert(self.retired().subset_of(self.objects().dom()));
        assert(self.expired().subset_of(self.retired()));
        RcuRetired { retire }
    }
}

/// The paper's unique `Inactive(tid)` reader resource.
pub tracked struct RcuInactive {
    ghost domain: Loc,
    state: GhostPointsTo<nat, bool>,
}

impl RcuInactive {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn tid(self) -> nat {
        self.state.key()
    }

    pub closed spec fn wf(self) -> bool {
        !self.state.value()
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
pub tracked struct RcuBaseGuard {
    ghost domain: Loc,
    state: GhostPointsTo<nat, bool>,
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

    pub closed spec fn expired(self) -> Set<nat> {
        self.expired
    }

    pub closed spec fn protected(self) -> Map<usize, nat> {
        self.protected
    }

    pub closed spec fn wf(self) -> bool {
        self.state.value()
    }

    pub closed spec fn belongs_to(self, domain: RcuDomainAuth) -> bool {
        &&& self.domain() == domain.id()
        &&& self.state.id() == domain.reader_registry()
    }

    pub closed spec fn protects(self, addr: usize, obj: nat) -> bool {
        self.protected().contains_pair(addr, obj)
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
            final(self).expired() == old(self).expired(),
            final(self).protected() == old(self).protected().insert(info.addr(), info.obj()),
            final(self).protects(info.addr(), info.obj()),
    {
        self.protected = self.protected.insert(info.addr(), info.obj());
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

    pub open spec fn wf(self) -> bool {
        &&& self.addr() == self.ptr().addr()
        &&& self.ptr().addr() != 0
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
        res.0.publications().len() == 2,
        res.0.publications()[0] == Some(res.1.0.obj()),
        res.0.publications()[1] == Some(res.1.0.obj()),
        res.1.0.domain() == res.0.domain(),
        res.1.0.obj() == res.1.1.obj(),
{
    let ghost initial = seq![Msg { value: ptr, view: WmView::empty() }];
    let tracked (mut root, registration_opt) = RcuRootGhost::tracked_initial(ptr);
    let tracked registration = registration_opt.tracked_unwrap();
    let ghost msg = Msg { value: ptr, view: WmView::empty() };
    let ghost next = initial.push(msg);
    root.tracked_push_registered(initial, next, msg, &registration.0);
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
    let ghost initial = seq![Msg { value: first_ptr, view: WmView::empty() }];
    let tracked mut root = RcuRootOwnedGhost::tracked_initial(first_ptr, Some(()));
    let ghost next_msg = Msg { value: next_ptr, view: WmView::empty() };
    let ghost next_history = initial.push(next_msg);
    let tracked detached = root.tracked_push_fresh::<UnitRcuRootOwnership>(
        initial,
        next_history,
        next_msg,
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

    pub open spec fn wf(self) -> bool {
        self.addr() == self.ptr().addr()
    }

    pub closed spec fn belongs_to(self, domain: RcuDomainAuth) -> bool {
        &&& self.domain() == domain.id()
        &&& self.perm.id() == domain.retire_registry()
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

    /// The traversal layer has established that this object may be retired.
    /// Reclamation still requires a completed base-RCU grace period.
    pub open spec fn ready_to_retire(self) -> bool {
        self.seen_removed().removed.contains(self.obj())
    }

    pub closed spec fn belongs_to(self, domain: RcuDomainAuth) -> bool {
        self.base.belongs_to(domain)
    }
}

/// Lift a base retire permission once the caller has observed the object in the
/// removed set.
pub proof fn lift_retire_perm<T>(
    tracked base: RcuBaseRetirePerm<T>,
    seen_removed: RcuSeenRemoved<T>,
) -> (tracked perm: RcuRetirePerm<T>)
    requires
        seen_removed.removed.contains(base.obj()),
    ensures
        perm.base() == base,
        perm.domain() == base.domain(),
        perm.ptr() == base.ptr(),
        perm.obj() == base.obj(),
        perm.seen_removed() == seen_removed,
        perm.ready_to_retire(),
{
    RcuRetirePerm { base, seen_removed }
}

/// Objective record that an allocation has passed the base `rcu-retire`
/// transition. It is safe to enqueue its callback, but not yet safe to execute
/// it; execution additionally needs monitor grace-period completion.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRetired<T> {
    retire: RcuRetirePerm<T>,
}

impl<T> RcuRetired<T> {
    pub closed spec fn domain(self) -> Loc {
        self.retire.domain()
    }

    pub closed spec fn obj(self) -> nat {
        self.retire.obj()
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.retire.ptr()
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
    let ghost seen_removed = RcuSeenRemoved {
        removed: Set::empty().insert(info.obj()),
        link_view: RcuLinkView::empty(),
    };
    let tracked retire = lift_retire_perm(base, seen_removed);
    let tracked _retired = domain.tracked_retire(retire);

    let tracked inactive = domain.tracked_register_reader();
    let tracked mut guard = domain.tracked_guard_start(inactive);
    assert(guard.expired() == Set::<nat>::empty());
    assert(!guard.expired().contains(info.obj()));
    guard.tracked_protect(&info);
    (guard, info)
}

/// Non-generic proof certificate carried across the type-erasure boundary.
///
/// A certificate can only be produced from a typed traversal retire permission,
/// but after that point the monitor only needs the erased callback summary.
pub tracked struct RcuCallbackSafety {
    ghost domain: Loc,
    ghost obj: nat,
}

impl RcuCallbackSafety {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn obj(self) -> nat {
        self.obj
    }

    /// The monitor may assign any future batch generation, but it cannot
    /// change the retired object's domain or allocation identity.
    pub open spec fn matches(self, summary: RcuCallbackSummary) -> bool {
        &&& summary.domain == self.domain()
        &&& summary.obj == self.obj()
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
        callback_safety_from_traversal(cert, *object),
{
    RcuCallbackSafety { domain: retired.domain(), obj: object.obj() }
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

    pub open spec fn can_protect(self, info: RcuBlockInfo<T>) -> bool {
        &&& self.wf()
        &&& info.wf()
        &&& info.domain() == self.domain()
        &&& !self.expired().contains(info.obj())
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
            res.seen_removed() == seen_removed,
    {
        RcuReadGuardToken { base, seen_removed }
    }

    /// Records one successful base `Guard-protect` operation in `G`.
    pub proof fn tracked_protect(tracked &mut self, tracked info: &RcuBlockInfo<T>)
        requires
            old(self).can_protect(*info),
        ensures
            final(self).wf(),
            final(self).domain() == old(self).domain(),
            final(self).tid() == old(self).tid(),
            final(self).expired() == old(self).expired(),
            final(self).seen_removed() == old(self).seen_removed(),
            final(self).protected() == old(self).protected().insert(info.addr(), info.obj()),
            final(self).protects(info.addr(), info.obj()),
    {
        self.base.tracked_protect(info);
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

    pub open spec fn protected_by(self, guard: RcuReadGuardToken<T>) -> bool {
        &&& self.domain() == guard.domain()
        &&& self.seen_removed() == guard.seen_removed()
        &&& !self.seen_removed().removed.contains(self.obj())
        &&& guard.protects(self.ptr().addr(), self.obj())
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
    tracked domain: &RcuDomainAuth,
    tracked guard: &mut RcuReadGuardToken<S::Node>,
    tracked info: &RcuBlockInfo<S::Node>,
    p: *mut S::Node,
    g: S::Ghost,
) -> (tracked root: RcuProtectedPtr<S::Node>)
    requires
        old(guard).is_for(*domain),
        old(guard).can_protect(*info),
        info.ptr() == p,
        S::root_inv(p, info.obj(), g),
    ensures
        root.ptr() == p,
        root.obj() == info.obj(),
        root.domain() == domain.id(),
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
        domain: domain.id(),
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
        old(guard).can_protect(*to_info),
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
/// `RcuPointsTo(p, s)`.
///
/// `incoming_all[p]` is the set of all incoming edges that have ever pointed to
/// `p`, corresponding to the authoritative incoming set in `RcuPointedBy(p, B)`.
///
/// `current_incoming[p]` is the current incoming set `B`. It is not required for
/// the simple one-step traversal proof below, but keeping it in the ghost state
/// makes the example match the paper's predicate shape.
pub ghost struct LinkedListGhost {
    pub root: *mut LinkedListNode,
    pub root_obj: nat,
    pub objects: Map<*mut LinkedListNode, nat>,
    pub successors: Map<*mut LinkedListNode, Seq<Option<*mut LinkedListNode>>>,
    pub incoming_all: Map<nat, Set<LinkEdge>>,
    pub current_incoming: Map<nat, Set<LinkEdge>>,
}

pub struct LinkedListTraversalSpec;

impl RcuTraversalSafety for LinkedListTraversalSpec {
    type Node = LinkedListNode;

    type Ghost = LinkedListGhost;

    open spec fn root_inv(p: *mut LinkedListNode, obj: nat, g: LinkedListGhost) -> bool {
        &&& p == g.root
        &&& obj == g.root_obj
        &&& g.objects.contains_pair(p, obj)
        &&& g.successors.contains_key(p)
        &&& g.incoming_all.contains_key(obj)
    }

    open spec fn node_inv(p: *mut LinkedListNode, obj: nat, g: LinkedListGhost) -> bool {
        &&& g.objects.contains_pair(p, obj)
        &&& g.successors.contains_key(p)
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
        &&& g.objects.contains_pair(from, from_obj)
        &&& g.objects.contains_pair(to, to_obj)
        &&& g.successors.contains_key(from)
        &&& n < g.successors[from].len()
        &&& g.successors[from][n as int] == Some(to)
        &&& g.successors.contains_key(to)
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

/// Example: after protecting the root, following a non-stale successor-history
/// event protects the next node under the same guard.
pub proof fn linked_list_protect_next_example(
    tracked domain: &RcuDomainAuth,
    tracked guard: &mut RcuReadGuardToken<LinkedListNode>,
    tracked root_info: &RcuBlockInfo<LinkedListNode>,
    tracked next_info: &RcuBlockInfo<LinkedListNode>,
    root: *mut LinkedListNode,
    n: LinkIndex,
    next: *mut LinkedListNode,
    g: LinkedListGhost,
) -> (tracked next_protected: RcuProtectedPtr<LinkedListNode>)
    requires
        old(guard).is_for(*domain),
        old(guard).can_protect(*root_info),
        old(guard).can_protect(*next_info),
        root_info.ptr() == root,
        next_info.ptr() == next,
        LinkedListTraversalSpec::root_inv(root, root_info.obj(), g),
        LinkedListTraversalSpec::link_inv(root, root_info.obj(), n, next, next_info.obj(), g),
        LinkedListTraversalSpec::seen_removed_sound(old(guard).seen_removed(), g),
        old(guard).seen_at(root_info.obj()) <= n,
    ensures
        next_protected.ptr() == next,
        next_protected.obj() == next_info.obj(),
        next_protected.domain() == domain.id(),
        next_protected.protected_by(*final(guard)),
        final(guard).wf(),
        LinkedListTraversalSpec::node_inv(next, next_info.obj(), g),
{
    let tracked root_protected = protect_root::<LinkedListTraversalSpec>(
        domain,
        guard,
        root_info,
        root,
        g,
    );
    protect_link::<LinkedListTraversalSpec>(guard, &root_protected, next_info, n, next, g)
}

} // verus!
