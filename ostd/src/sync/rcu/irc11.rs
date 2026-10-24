// SPDX-License-Identifier: MPL-2.0
//! Explicit-context nullable RCU pointers and proof-carrying delayed destruction.
//!
//! # Verified Properties
//! `read` uses the running task's native acquire view. `try_get` borrows the
//! physical lease for the guard's lifetime (including BoxRef/ArcRef, without an
//! Arc increment). Consuming `close` returns the original CPU fraction. Update
//! returns a one-shot retirement capture; only its matching GP permit allows
//! reconstructing and dropping the original smart pointer.
//!
//! This API intentionally has explicit close/report operations: the legacy
//! implicit preemption and Drop glue is not part of this IRC11 proof.
use vstd::{prelude::*, raw_ptr::spec_cast_ptr_to_thin_ptr, resource::Loc};
use vstd_extra::{
    atomic_irc11::ThreadView,
    external::NonNullAdditionalFns,
    ownership::Inv,
    raw_callback::{RawCallbackContextWithProof, RawCallbackWithProof},
    rcu_objects::RcuDomainAuth,
};

use crate::{
    cpu::CpuId,
    specs::{
        sync::rcu::{
            atomic::{RcuRetiredRoot, RcuRootOwnershipPredicate, RcuRootProtection},
            cpu::CpuRcuReaderFragment,
            grace_period::{RcuCallbackSummary, RcuReclaimPermit},
            link::{RcuLinkObservation, RcuLinkRemoval},
            retirement::RcuRetiredFact,
            traversal::AllocationId,
        },
        task::rcu::RunningRcuContext,
    },
};

use super::{
    non_null::{NonNullPtr, NonNullPtrRef},
    weak_root::{RcuRootKey, RcuRootReclaimer, RcuWeakRoot},
};
use core::{marker::PhantomData, ptr::NonNull};

verus! {

broadcast use {
    vstd_extra::external::nonnull::group_nonull_axioms,
    vstd::thread_view::group_thread_view_axioms,
};

pub ghost struct SmartPointerOwnership<P> {
    marker: PhantomData<P>,
}

impl<P: NonNullPtr> RcuRootOwnershipPredicate<P::Target, P::Permission> for SmartPointerOwnership<
    P,
> {
    open spec fn owns(ptr: *mut P::Target, ownership: P::Permission) -> bool {
        ownership.inv() && P::ptr_perm_match(ptr, ownership)
    }
}

/* Explicit context and close are required until kernel scheduler/preemption
 * glue can supply these capabilities. Native pointer instructions are unchanged.
 * Origin Rust: <none; new executable code>
 */

pub struct Irc11RcuOption<P: NonNullPtr> {
    root: RcuWeakRoot<P::Target, P::Permission, SmartPointerOwnership<P>>,
}

/// Non-null policy wrapper: every native history message, including stale ones, is non-null.
/* New explicit lifetime/callback container; erased fields carry only the corresponding proof resources.
 * Origin Rust: <none; new executable code>
 */
pub struct Irc11Rcu<P: NonNullPtr> {
    inner: Irc11RcuOption<P>,
}

impl<P: NonNullPtr> Inv for Irc11Rcu<P> {
    closed spec fn inv(self) -> bool {
        self.inner.inv() && !self.inner.key().nullable && self.inner.condition() == (|
            _: P::Permission,
        |
            true)
    }
}

impl<P: NonNullPtr> Irc11Rcu<P> {
    /// Fixed scheduler, domain, online-set, and permission-registry identities.
    pub closed spec fn key(&self) -> RcuRootKey {
        self.inner.key()
    }

    /// Initializes a non-null root.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - The smart pointer's physical permission is retained in the native root invariant.
    /// ## Functional Correctness
    /// - Every historical publication is non-null.
    /// ## Preconditions
    /// - Supply a valid running context with real CPU pinning supplied by kernel integration.
    /// ## Postconditions
    /// - Returns a root for the context's scheduler and requested online set; Preserves context identity and monotonically preserves its native view.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn new(
        value: P,
        Tracked(context): Tracked<&mut RunningRcuContext>,
        Ghost(online): Ghost<Set<CpuId>>,
    ) -> (res: Self)
        requires
            old(context).inv(),
        ensures
            res.inv(),
            res.key().scheduler == old(context).scheduler(),
            res.key().online == online,
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant() == old(context).participant(),
            final(context)@.contains(old(context)@),
    {
        Self {
            inner: Irc11RcuOption::new_with_policy(
                Some(value),
                Tracked(context),
                Ghost(online),
                Ghost(false),
            ),
        }
    }

    /// Acquires a non-null read guard.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - A physical lease protects the selected allocation until explicit close.
    /// ## Functional Correctness
    /// - Native acquire selects a typed history message and splits the CPU reader fraction.
    /// ## Preconditions
    /// - The root and context are valid, their schedulers match, and the CPU is online.
    /// ## Postconditions
    /// - Returns a non-null guard retaining half the participant fraction; Preserves context identity and monotonically preserves its native view.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn read<'a>(&'a self, Tracked(context): Tracked<&mut RunningRcuContext>) -> (res:
        Irc11RcuReadGuard<'a, P>)
        requires
            self.inv(),
            old(context).inv(),
            self.key().scheduler == old(context).scheduler(),
            self.key().online.contains(old(context).cpu()),
        ensures
            res.inv(),
            res.is_some(),
            res.condition() == (|_: P::Permission| true),
            res.root_key() == self.key(),
            res.participant() == old(context).participant().id(),
            res.fraction() == old(context).participant().fraction() / 2real,
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant().fraction() == old(context).participant().fraction()
                / 2real,
            final(context)@.contains(old(context)@),
    {
        self.inner.read(Tracked(context))
    }

    /// Publishes a non-null replacement.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Ownership of the old allocation remains retained until certified reclamation.
    /// ## Functional Correctness
    /// - Native release replacement returns the detached allocation's one-shot ticket.
    /// ## Preconditions
    /// - The root and running context are valid.
    /// ## Postconditions
    /// - Returns a valid ticket with removal observed by the caller; Preserves context identity and monotonically preserves its native view.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn update(&self, value: P, Tracked(context): Tracked<&mut RunningRcuContext>) -> (res:
        PendingRcuDrop<P>)
        requires
            self.inv(),
            old(context).inv(),
        ensures
            res.inv(),
            res.key() == self.key(),
            res.record().removal.observed_by(final(context)@),
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant() == old(context).participant(),
            final(context)@.contains(old(context)@),
    {
        self.inner.update(Some(value), Tracked(context)).unwrap()
    }
}

#[must_use]
/* New explicit lifetime/callback container; erased fields carry only the corresponding proof resources.
 * Origin Rust: <none; new executable code>
 */
pub struct Irc11RcuReadGuard<'a, P: NonNullPtr> {
    root: &'a Irc11RcuOption<P>,
    ptr: *mut P::Target,
    tracked_protection: Tracked<RcuRootProtection<P::Target, P::Permission>>,
    ghost_start_view: Ghost<ThreadView>,
    ghost_link: Ghost<Option<RcuLinkObservation<P::Target>>>,
}

/// Detached pointer whose ownership remains in the root authority until GP completion.
#[must_use]
/* New explicit lifetime/callback container; erased fields carry only the corresponding proof resources.
 * Origin Rust: <none; new executable code>
 */
pub struct PendingRcuDrop<P: NonNullPtr> {
    ptr: NonNull<P::Target>,
    reclaimer: RcuRootReclaimer<P::Target, P::Permission, SmartPointerOwnership<P>>,
    tracked_retired: Tracked<RcuRetiredRoot<P::Target>>,
}

// SAFETY: the capture never accesses the raw pointer before recovering the
// unique P::Permission. Reconstruction transfers the original P, which is Send.
// The reclaimer stores only objective invariant ownership, not subjective views.
#[verifier::external]
unsafe impl<P: NonNullPtr + Send> Send for PendingRcuDrop<P> {

}

/// Erased callback and the exact batch metadata checked before invocation.
#[must_use]
/* New explicit lifetime/callback container; erased fields carry only the corresponding proof resources.
 * Origin Rust: <none; new executable code>
 */
pub struct RcuCallbackWork {
    callback: RawCallbackWithProof<RcuReclaimPermit>,
    ghost_summary: Ghost<RcuCallbackSummary>,
    ghost_online: Ghost<Set<CpuId>>,
    tracked_fact: Tracked<RcuRetiredFact>,
}

impl<P: NonNullPtr> Inv for Irc11RcuOption<P> {
    closed spec fn inv(self) -> bool {
        self.root.inv()
    }
}

impl<P: NonNullPtr> Irc11RcuOption<P> {
    /// Client predicate preserved by every publication and physical read lease.
    pub closed spec fn condition(&self) -> spec_fn(P::Permission) -> bool {
        self.root.condition()
    }

    /// Every permission produced by this value's pointer conversion satisfies the root predicate.
    pub open spec fn accepts(&self, value: P) -> bool {
        forall|owned: P::Permission| #[trigger] value.rel_perm(owned) ==> (self.condition())(owned)
    }

    /// Fixed scheduler, domain, online-set, and permission-registry identities.
    pub closed spec fn key(&self) -> RcuRootKey {
        self.root.key()
    }

    /// Initializes a nullable root and imports only its actual native initialization view.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - The smart pointer's physical permission is retained when the initial value is non-null.
    /// ## Functional Correctness
    /// - Initializes a nullable root using only its actual native initialization view.
    /// ## Preconditions
    /// - Supply a valid running context with real CPU pinning supplied by kernel integration.
    /// ## Postconditions
    /// - Returns a nullable root with the requested online set; Preserves context identity and monotonically preserves its native view.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn new(
        value: Option<P>,
        Tracked(context): Tracked<&mut RunningRcuContext>,
        Ghost(online): Ghost<Set<CpuId>>,
    ) -> (res: Self)
        requires
            old(context).inv(),
        ensures
            res.inv(),
            res.key().scheduler == old(context).scheduler(),
            res.key().online == online,
            res.key().nullable,
            res.condition() == (|_: P::Permission| true),
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant() == old(context).participant(),
            final(context)@.contains(old(context)@),
    {
        Self::new_with_policy(value, Tracked(context), Ghost(online), Ghost(true))
    }

    /* Share native initialization while preserving the nullable/non-null history policy.
     * Origin Rust: <none; new executable code>
     */
    fn new_with_policy(
        value: Option<P>,
        Tracked(context): Tracked<&mut RunningRcuContext>,
        Ghost(online): Ghost<Set<CpuId>>,
        Ghost(nullable): Ghost<bool>,
    ) -> (res: Self)
        requires
            old(context).inv(),
            nullable || value is Some,
        ensures
            res.inv(),
            res.key().scheduler == old(context).scheduler(),
            res.key().online == online,
            res.key().nullable == nullable,
            res.condition() == (|_: P::Permission| true),
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant() == old(context).participant(),
            final(context)@.contains(old(context)@),
    {
        let tracked domain = RcuDomainAuth::tracked_new();
        Self::new_with_domain(
            value,
            Tracked(context),
            Ghost(online),
            Ghost(nullable),
            Tracked(domain),
            Ghost(|_: P::Permission| true),
        )
    }

    /// Initializes a root in a supplied empty domain with a fixed client ownership predicate.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Retains physical ownership; each later publication must satisfy the same predicate.
    /// ## Functional Correctness
    /// - Preserves the chosen domain and client predicate across historical reads.
    /// ## Preconditions
    /// - The domain is empty, the context is valid, and every initial permission satisfies the predicate.
    /// ## Postconditions
    /// - Returns the requested policy and configuration while preserving the native context.
    /* Exposes erased initialization inputs for constructing data-structure invariants;
     * native allocation and pointer initialization are unchanged.
     * Origin Rust: <none; new proof-configurable initialization entry point>
     */
    pub fn new_with_domain(
        value: Option<P>,
        Tracked(context): Tracked<&mut RunningRcuContext>,
        Ghost(online): Ghost<Set<CpuId>>,
        Ghost(nullable): Ghost<bool>,
        Tracked(domain): Tracked<RcuDomainAuth>,
        Ghost(condition): Ghost<spec_fn(P::Permission) -> bool>,
    ) -> (res: Self)
        requires
            old(context).inv(),
            domain.inv(),
            domain.objects() == Map::<nat, usize>::empty(),
            nullable || value is Some,
            value matches Some(value) ==> forall|owned: P::Permission| #[trigger]
                value.rel_perm(owned) ==> condition(owned),
        ensures
            res.inv(),
            res.key().domain == domain.id(),
            res.key().scheduler == old(context).scheduler(),
            res.key().online == online,
            res.key().nullable == nullable,
            res.condition() == condition,
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant() == old(context).participant(),
            final(context)@.contains(old(context)@),
    {
        let (ptr, Tracked(ownership)) = match value {
            Some(value) => {
                let (ptr, Tracked(owned)) = value.into_raw();
                (ptr.as_ptr(), Tracked(Some(owned)))
            },
            None => (core::ptr::null_mut(), Tracked(None)),
        };
        let (root, Tracked(initial)) = RcuWeakRoot::new(
            ptr,
            Tracked(ownership),
            Ghost(context.scheduler()),
            Ghost(online),
            Ghost(nullable),
            Tracked(domain),
            Ghost(condition),
        );
        proof {
            let ghost before = context@;
            let tracked view = context.tracked_view_mut();
            let tracked previous = *view;
            *view = previous.join(initial);
            vstd::thread_view::ThreadView::join_contains(before, initial@);
            assert(view@.contains(before));
        }
        Self { root }
    }

    /// Opens an unbounded reader fraction and acquire-loads the exact typed allocation.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - The selected allocation's physical lease prevents reclamation while borrowed.
    /// ## Functional Correctness
    /// - Native acquire may select null or a typed historical allocation.
    /// ## Preconditions
    /// - The root and context are valid, their schedulers match, and the CPU is online.
    /// ## Postconditions
    /// - Returns the matching guard and splits the participant fraction in half; Preserves context identity and monotonically preserves its native view.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn read<'a>(&'a self, Tracked(context): Tracked<&mut RunningRcuContext>) -> (res:
        Irc11RcuReadGuard<'a, P>)
        requires
            self.inv(),
            old(context).inv(),
            self.key().scheduler == old(context).scheduler(),
            self.key().online.contains(old(context).cpu()),
        ensures
            res.inv(),
            res.root_key() == self.key(),
            res.reader_in(*final(context)),
            (res.resource() is Some) == res.is_some(),
            res.resource() matches Some(owned) ==> (self.condition())(owned),
            res.condition() == self.condition(),
            res.start_view() == old(context)@,
            final(context).participant().generation() == old(context).participant().generation(),
            final(context).participant().known_retired() == old(
                context,
            ).participant().known_retired(),
            final(context).participant().view() == old(context).participant().view(),
            !self.key().nullable ==> res.is_some(),
            res.participant() == old(context).participant().id(),
            res.fraction() == old(context).participant().fraction() / 2real,
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant().fraction() == old(context).participant().fraction()
                / 2real,
            final(context)@.contains(old(context)@),
    {
        let ghost start_view = context@;
        let tracked reader = context.tracked_start_reader();
        let tracked binding = context.tracked_binding();
        let (ptr, protection, _) = self.root.load_acquire(
            Tracked(context.tracked_view_mut()),
            Tracked(reader),
            Tracked(binding),
        );
        Irc11RcuReadGuard {
            root: self,
            ptr,
            tracked_protection: protection,
            ghost_start_view: Ghost(start_view),
            ghost_link: Ghost(None),
        }
    }

    /// Follows this owning link while borrowing its physically protected predecessor.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - The child borrow cannot outlive the predecessor borrow; its lease prevents reclamation.
    /// ## Functional Correctness
    /// - One native acquire extends topology protection and returns the matching physical lease.
    /// ## Preconditions
    /// - The predecessor is non-null, uses the same live CPU generation, and belongs to another domain.
    /// - The caller obtains this owning slot through the predecessor; shared-node aliases are not modeled.
    /// ## Postconditions
    /// - Preserves the predecessor's starting view and generation in the child witness and observation.
    /* Extend the existing read API with erased topology evidence; no additional native synchronization.
     * Origin Rust: <none; new executable code>
     */
    pub fn read_link<'b, 'p, Q: NonNullPtr>(
        &'b self,
        parent: &'b Irc11RcuReadGuard<'p, Q>,
        Tracked(context): Tracked<&mut RunningRcuContext>,
    ) -> (res: Irc11RcuReadGuard<'b, P>)
        requires
            self.inv(),
            parent.inv(),
            parent.is_some(),
            old(context).inv(),
            parent.reader_in(*old(context)),
            old(context)@.contains(parent.start_view()),
            self.key().scheduler == old(context).scheduler(),
            self.key().online.contains(old(context).cpu()),
            parent.root_key().domain != self.key().domain,
        ensures
            res.inv(),
            res.root_key() == self.key(),
            res.reader_in(*final(context)),
            parent.reader_in(*final(context)),
            res.start_view() == parent.start_view(),
            res.generation() == parent.generation(),
            res.link_observation() is Some,
            res.link_observation()->Some_0.inv(),
            res.link_observation()->Some_0.child == res.allocation(),
            (res.allocation() is Some) == res.is_some(),
            res.link_observation()->Some_0.start_view == parent.start_view(),
            res.link_observation()->Some_0.generation == parent.generation(),
            res.link_observation()->Some_0.source == parent.allocation()->Some_0,
            res.fraction() == old(context).participant().fraction() / 2real,
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant().fraction() == old(context).participant().fraction()
                / 2real,
            final(context)@.contains(old(context)@),
    {
        let tracked reader = context.tracked_start_reader();
        let tracked binding = context.tracked_binding();
        let (ptr, protection, observation) = self.root.load_acquire_link::<
            Q::Target,
            Q::Permission,
        >(
            Tracked(context.tracked_view_mut()),
            Tracked(reader),
            Tracked(binding),
            Ghost(parent.start_view()),
            Ghost(parent.allocation()->Some_0),
            Ghost(spec_cast_ptr_to_thin_ptr::<Q::Target, P::Target>(parent.ptr)),
            Tracked(parent.tracked_protection.borrow()),
        );
        Irc11RcuReadGuard {
            root: self,
            ptr,
            tracked_protection: protection,
            ghost_start_view: Ghost(parent.start_view()),
            ghost_link: Ghost(Some(observation@)),
        }
    }

    /// Release-publishes a new pointer, retaining the old one as a unique retirement ticket.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - The old allocation is retained, not destroyed by this operation.
    /// ## Functional Correctness
    /// - Native release publishes the replacement and returns a ticket exactly when the old value is non-null.
    /// ## Preconditions
    /// - The root and context are valid; non-null roots require a non-null replacement.
    /// ## Postconditions
    /// - Every returned ticket matches this root and its observed removal; Preserves context identity and monotonically preserves its native view.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn update(
        &self,
        value: Option<P>,
        Tracked(context): Tracked<&mut RunningRcuContext>,
    ) -> (res: Option<PendingRcuDrop<P>>)
        requires
            self.inv(),
            old(context).inv(),
            self.key().nullable || value is Some,
            value matches Some(value) ==> self.accepts(value),
        ensures
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant() == old(context).participant(),
            final(context)@.contains(old(context)@),
            !self.key().nullable ==> res is Some,
            res matches Some(pending) ==> {
                &&& pending.inv()
                &&& pending.key() == self.key()
                &&& pending.record().removal.observed_by(final(context)@)
            },
    {
        let (ptr, Tracked(ownership)) = match value {
            Some(value) => {
                let (ptr, Tracked(owned)) = value.into_raw();
                (ptr.as_ptr(), Tracked(Some(owned)))
            },
            None => (core::ptr::null_mut(), Tracked(None)),
        };
        let (old_ptr, Tracked(retired)) = self.root.replace_release(
            ptr,
            Tracked(ownership),
            Tracked(context.tracked_view_mut()),
            Ghost(None),
        );
        if old_ptr.is_null() {
            None
        } else {
            let ptr = NonNull::new(old_ptr).unwrap();
            Some(
                PendingRcuDrop {
                    ptr,
                    reclaimer: self.root.reclaimer(),
                    tracked_retired: Tracked(retired.tracked_unwrap()),
                },
            )
        }
    }
}

impl<P: NonNullPtr> Irc11RcuOption<P> {
    /// Unlinks an owning edge and certifies every historical incoming edge dead.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - No allocation is reclaimed; the unique ticket still needs the matching GP permit.
    /// ## Functional Correctness
    /// - A release swap to null derives topology removal and retirement from the same native message.
    /// ## Preconditions
    /// - This nullable owning slot is accessed through a protected predecessor from another domain.
    /// ## Postconditions
    /// - Any returned ticket retains the exact no-incoming-edge proof and observed removal view.
    /* Reuse the release swap with an erased owning-link retirement certificate.
     * Origin Rust: <none; new executable code>
     */
    pub fn unlink<Q: NonNullPtr>(
        &self,
        parent: &Irc11RcuReadGuard<'_, Q>,
        Tracked(context): Tracked<&mut RunningRcuContext>,
    ) -> (res: Option<PendingRcuDrop<P>>)
        requires
            self.inv(),
            self.key().nullable,
            parent.inv(),
            parent.is_some(),
            old(context).inv(),
            parent.reader_in(*old(context)),
            parent.root_key().domain != self.key().domain,
        ensures
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant() == old(context).participant(),
            final(context)@.contains(old(context)@),
            res matches Some(pending) ==> {
                &&& pending.inv()
                &&& pending.key() == self.key()
                &&& pending.record().removal.observed_by(final(context)@)
                &&& pending.link_removal() is Some
                &&& pending.link_removal()->Some_0.inv()
                &&& pending.link_removal()->Some_0.source == parent.allocation()->Some_0
                &&& pending.link_removal()->Some_0.child == (AllocationId {
                    domain: pending.record().domain,
                    object: pending.record().obj,
                })
                &&& pending.link_removal()->Some_0.removal == pending.record().removal
            },
    {
        let (ptr, Tracked(retired)) = self.root.replace_release(
            core::ptr::null_mut(),
            Tracked(None),
            Tracked(context.tracked_view_mut()),
            Ghost(
                Some(
                    (
                        parent.allocation()->Some_0,
                        spec_cast_ptr_to_thin_ptr::<Q::Target, P::Target>(parent.ptr),
                    ),
                ),
            ),
        );
        if ptr.is_null() {
            None
        } else {
            let tracked retired = retired.tracked_unwrap();
            proof {
                retired.lemma_link_removal();
            }
            Some(
                PendingRcuDrop {
                    ptr: NonNull::new(ptr).unwrap(),
                    reclaimer: self.root.reclaimer(),
                    tracked_retired: Tracked(retired),
                },
            )
        }
    }
}

impl<'a, P: NonNullPtr> Inv for Irc11RcuReadGuard<'a, P> {
    closed spec fn inv(self) -> bool {
        &&& self.root.inv()
        &&& self.tracked_protection@.inv()
        &&& (self.tracked_protection@.info() is Some) == self.is_some()
        &&& self.start_view().contains(self.tracked_protection@.reader().participant_view())
        &&& self.tracked_protection@.info() matches Some(info) ==> {
            &&& equal(info.ptr(), self.ptr)
            &&& info.domain() == self.root.key().domain
        }
        &&& match self.tracked_protection@.lease() {
            Some(lease) => {
                &&& self.ptr.addr() != 0
                &&& lease.registry() == self.root.key().active
                &&& SmartPointerOwnership::<P>::owns(self.ptr, lease.resource())
                &&& (self.root.condition())(lease.resource())
                &&& lease.witness().start_view() == self.start_view()
            },
            None => self.ptr.addr() == 0,
        }
        &&& self.ghost_link@ matches Some(observation) ==> {
            &&& observation.inv()
            &&& observation.child == self.allocation()
            &&& observation.reader == self.participant()
            &&& observation.generation == self.generation()
            &&& observation.start_view == self.start_view()
            &&& observation.child matches Some(child) ==> equal(
                self.ptr,
                observation.graph.objects[child],
            )
        }
    }
}

impl<'a, P: NonNullPtr> Irc11RcuReadGuard<'a, P> {
    /// Exact typed allocation selected by this read; never reconstructed from its address.
    pub closed spec fn allocation(self) -> Option<AllocationId> {
        match self.tracked_protection@.info() {
            Some(info) => Some(AllocationId { domain: info.domain(), object: info.obj() }),
            None => None,
        }
    }

    /// Starting native view of the enclosing critical section, also retained by child leases.
    pub closed spec fn start_view(self) -> ThreadView {
        self.ghost_start_view@
    }

    /// Live CPU generation of the physical lease.
    pub closed spec fn generation(self) -> nat {
        self.tracked_protection@.reader().generation()
    }

    /// Persistent topology snapshot established by the same acquire as this guard's lease.
    pub closed spec fn link_observation(self) -> Option<RcuLinkObservation<P::Target>> {
        self.ghost_link@
    }

    /// Compatibility with the participant state before any quiescent report.
    pub open spec fn reader_in(self, context: RunningRcuContext) -> bool {
        let reader = self.reader();
        &&& self.participant() == context.participant().id()
        &&& reader.cpu() == context.cpu()
        &&& self.generation() == context.participant().generation()
        &&& reader.participant_view() == context.participant().view()
        &&& reader.known_retired() == context.participant().known_retired()
    }

    /// A snapshot of the linear reader's identity; this grants no reader ownership.
    pub closed spec fn reader(self) -> CpuRcuReaderFragment {
        self.tracked_protection@.reader()
    }

    /// Identity and publication policy of the root protected by this guard.
    pub closed spec fn root_key(self) -> RcuRootKey {
        self.root.key()
    }

    /// Canonical CPU participant whose reader fraction this guard retains.
    pub closed spec fn participant(self) -> Loc {
        self.tracked_protection@.reader().participant_id()
    }

    /// Positive reader fraction that explicit close must return.
    pub closed spec fn fraction(self) -> real {
        self.tracked_protection@.reader().fraction()
    }

    /// Whether the native load selected a protected non-null allocation.
    pub closed spec fn is_some(self) -> bool {
        self.tracked_protection@.lease() is Some
    }

    /// Fixed publication predicate required by this guard's compare-exchange.
    pub closed spec fn condition(self) -> spec_fn(P::Permission) -> bool {
        self.root.condition()
    }

    /// Physical permission's logical value; this snapshot grants no ownership.
    pub closed spec fn resource(self) -> Option<P::Permission> {
        match self.tracked_protection@.lease() {
            Some(lease) => Some(lease.resource()),
            None => None,
        }
    }

    /// Borrows from the lease, tying the returned smart-pointer reference to this guard.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Borrows physical permission for the guard's lifetime through the existing NonNullPtrRef adapter.
    /// ## Functional Correctness
    /// - Returns None exactly for a null observation; Arc borrowing does not increment its count.
    /// ## Preconditions
    /// - The guard is valid and the pointer type supports borrowed references.
    /// ## Postconditions
    /// - Any returned reference has a matching borrowed permission derived from this guard.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn try_get<'b>(&'b self) -> (res: Option<<P as NonNullPtrRef<'b>>::Ref>) where
        P: NonNullPtrRef<'b>,

        requires
            self.inv(),
        ensures
            (res is Some) == self.is_some(),
            res matches Some(reference) ==> exists|
                permission: <P as NonNullPtrRef<'b>>::RefPermission,
            |
                #![trigger permission.inv()]
                #![trigger P::ref_perm_view_permission(permission)]
                permission.inv() && P::ref_rel_perm(reference, permission)
                    && P::ref_perm_view_permission(permission) == self.resource()->Some_0,
    {
        if self.ptr.is_null() {
            return None;
        }
        let tracked owned = self.tracked_protection.borrow().tracked_borrow();
        let tracked permission = P::borrow_perm_as_ref_perm(owned);
        let ghost borrowed_permission = permission;
        let ptr = NonNull::new(self.ptr).unwrap();
        // SAFETY: the physical lease is borrowed for 'b; consuming close cannot
        // overlap this borrow, and reclaim requires that lease to have returned.
        let reference = unsafe { P::raw_as_ref(ptr, Tracked(permission)) };
        proof {
            assert(borrowed_permission.inv());
            assert(P::ref_rel_perm(reference, borrowed_permission));
            assert(P::ref_perm_view_permission(borrowed_permission) == self.resource()->Some_0);
        }
        Some(reference)
    }

    /// Non-null counterpart of try_get; the policy wrapper establishes its precondition.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - The returned borrow cannot outlive the guard's physical lease.
    /// ## Functional Correctness
    /// - Unwraps the non-null borrowed reference without cloning the smart pointer.
    /// ## Preconditions
    /// - The guard is valid and its selected allocation is non-null.
    /// ## Postconditions
    /// - Returns a reference tied to this guard; no termination or no-unwind guarantee is added.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn get<'b>(&'b self) -> <P as NonNullPtrRef<'b>>::Ref where P: NonNullPtrRef<'b>
        requires
            self.inv(),
            self.is_some(),
    {
        self.try_get().unwrap()
    }

    /// Consumes the guard and conditionally publishes a replacement. On failure
    /// the unpublished smart pointer is reconstructed from its original permission.
    /// On success the caller enqueues the returned retirement ticket explicitly.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Reconstructs an unpublished pointer only with its returned exact permission.
    /// ## Functional Correctness
    /// - Consumes the guard; native CAS either publishes the new pointer or returns it to the caller.
    /// ## Preconditions
    /// - The guard and context are valid and belong to the same participant.
    /// ## Postconditions
    /// - Returns the reader fraction; a successful retirement ticket matches the observed removal; Preserves context identity and monotonically preserves its native view.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn compare_exchange(
        self,
        value: P,
        Tracked(context): Tracked<&mut RunningRcuContext>,
    ) -> (res: Result<Option<PendingRcuDrop<P>>, P>)
        requires
            self.inv(),
            old(context).inv(),
            self.participant() == old(context).participant().id(),
            forall|owned: P::Permission| #[trigger]
                value.rel_perm(owned) ==> (self.condition())(owned),
        ensures
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant().fraction() == old(context).participant().fraction()
                + self.fraction(),
            final(context)@.contains(old(context)@),
            res matches Ok(Some(pending)) ==> pending.inv() && pending.key() == self.root_key()
                && pending.record().removal.observed_by(final(context)@),
    {
        let (ptr, Tracked(ownership)) = value.into_raw();
        let (exchanged, Tracked(retired), Tracked(returned)) = self.root.root.compare_exchange(
            self.ptr,
            ptr.as_ptr(),
            Tracked(Some(ownership)),
            Tracked(context.tracked_view_mut()),
        );
        match exchanged {
            Ok(previous) => {
                let pending = if previous.is_null() {
                    None
                } else {
                    Some(
                        PendingRcuDrop {
                            ptr: NonNull::new(previous).unwrap(),
                            reclaimer: self.root.root.reclaimer(),
                            tracked_retired: Tracked(retired.tracked_unwrap()),
                        },
                    )
                };
                self.close(Tracked(context));
                Ok(pending)
            },
            Err(_) => {
                // SAFETY: failed CAS never published ptr and returned the exact
                // permission produced by into_raw. No callback was registered.
                let value = unsafe { P::from_raw(ptr, Tracked(returned.tracked_unwrap())) };
                self.close(Tracked(context));
                Err(value)
            },
        }
    }

    /// Explicitly closes the physical lease before returning the CPU reader fraction.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Ends the physical lease before returning its CPU reader authority.
    /// ## Functional Correctness
    /// - Consumes the guard and reunites its reader fraction with the participant.
    /// ## Preconditions
    /// - The guard and running context are valid and name the same participant.
    /// ## Postconditions
    /// - Preserves the native view exactly and adds the guard's fraction back to the participant.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn close(self, Tracked(context): Tracked<&mut RunningRcuContext>)
        requires
            self.inv(),
            old(context).inv(),
            self.participant() == old(context).participant().id(),
        ensures
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context)@ == old(context)@,
            final(context).participant().generation() == old(context).participant().generation(),
            final(context).participant().known_retired() == old(
                context,
            ).participant().known_retired(),
            final(context).participant().view() == old(context).participant().view(),
            final(context).participant().fraction() == old(context).participant().fraction()
                + self.fraction(),
    {
        let Tracked(reader) = self.root.root.close(self.tracked_protection);
        proof {
            context.tracked_stop_reader(reader);
        }
    }
}

impl<P: NonNullPtr> Inv for PendingRcuDrop<P> {
    closed spec fn inv(self) -> bool {
        &&& self.tracked_retired@.inv()
        &&& equal(self.ptr.view_ptr_mut(), self.tracked_retired@.ptr())
        &&& self.tracked_retired@.registry() == self.key().reclaim
        &&& self.record().domain == self.key().domain
        &&& self.record().retire_observation_registry == self.key().observations
    }
}

impl<P: NonNullPtr> PendingRcuDrop<P> {
    /// Topology evidence for owning-link unlink, retained with the linear claim.
    pub closed spec fn link_removal(self) -> Option<RcuLinkRemoval<P::Target>> {
        self.tracked_retired@.link_removal()
    }

    /// Fixed scheduler, domain, online-set, and permission-registry identities.
    pub closed spec fn key(&self) -> RcuRootKey {
        self.reclaimer.key()
    }

    /// Certified removal identity retained by this pending destruction.
    pub closed spec fn record(&self) -> crate::specs::sync::rcu::retirement::RcuRetiredRecord {
        self.tracked_retired@.record()
    }
}

impl<P: NonNullPtr + Send> RawCallbackContextWithProof<RcuReclaimPermit> for PendingRcuDrop<P> {
    open spec fn call_requires(&self, permit: RcuReclaimPermit) -> bool {
        &&& self.inv() && permit.inv()
        &&& permit.summary().retired == self.record()
        &&& permit.summary().scheduler == self.key().scheduler
        &&& permit.online() == self.key().online
    }

    /* New checked callback runner recovers ownership before reconstructing and dropping the smart pointer.
     * Origin Rust: <none; new executable code>
     */
    fn run(self, Tracked(permit): Tracked<RcuReclaimPermit>) {
        let ownership = self.reclaimer.reclaim(self.tracked_retired, Tracked(permit));
        // SAFETY: reclaim recovered the exact, unique original permission only
        // after excluding every active physical lease for this allocation.
        // Rust drops this binding exactly once when the verified runner returns.
        let _owned = unsafe { P::from_raw(self.ptr, ownership) };
    }
}

impl<P: NonNullPtr + Send> PendingRcuDrop<P> {
    /// Erases a capture without destroying or reconstructing its retired pointer.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Erasure does not reconstruct or destroy the retired allocation.
    /// ## Functional Correctness
    /// - Retains the exact retirement metadata and its future invocation obligation.
    /// ## Preconditions
    /// - The ticket is valid and the supplied summary matches its scheduler, retirement, and observed removal.
    /// ## Postconditions
    /// - Returns valid callback work with exactly the supplied summary and stable online set.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn into_callback(self, Ghost(summary): Ghost<RcuCallbackSummary>) -> (res: RcuCallbackWork)
        requires
            self.inv(),
            summary.retired == self.record(),
            summary.scheduler == self.key().scheduler,
            summary.retired.removal.observed_by(summary.retire_view),
        ensures
            res.inv(),
            res.summary() == summary,
            res.online() == self.key().online,
    {
        let tracked fact = self.tracked_retired.borrow().tracked_fact();
        let ghost online = self.key().online;
        let callback = RawCallbackWithProof::new(self);
        RcuCallbackWork {
            callback,
            ghost_summary: Ghost(summary),
            ghost_online: Ghost(online),
            tracked_fact: Tracked(fact),
        }
    }
}

impl Inv for RcuCallbackWork {
    closed spec fn inv(self) -> bool {
        &&& self.tracked_fact@.wf()
        &&& self.tracked_fact@.record() == self.summary().retired
        &&& self.summary().retired.removal.observed_by(self.summary().retire_view)
        &&& forall|permit: RcuReclaimPermit|
            permit.inv() && permit.summary() == self.summary() && permit.online() == self.online()
                ==> #[trigger] self.callback.call_requires(permit)
    }
}

impl RcuCallbackWork {
    /// Frozen callback identity and observation obligations used by its grace period.
    pub closed spec fn summary(&self) -> RcuCallbackSummary {
        self.ghost_summary@
    }

    /// Stable CPU set whose quiescent reports this callback requires.
    pub closed spec fn online(&self) -> Set<CpuId> {
        self.ghost_online@
    }

    /// Exposes the queued retirement's observation obligation without exposing erasure fields.
    pub proof fn lemma_summary(self)
        requires
            self.inv(),
        ensures
            self.summary().retired.removal.observed_by(self.summary().retire_view),
    {
    }

    /// Borrows the certified removal fact without duplicating reclamation authority.
    pub proof fn tracked_fact(tracked &self) -> (tracked res: &RcuRetiredFact)
        requires
            self.inv(),
        ensures
            res.record() == self.summary().retired,
            res.wf(),
    {
        self.tracked_fact.borrow()
    }

    /// Runs exactly once, outside the monitor lock, with matching completion evidence.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Uses the approved raw-call boundary only after proving the full invocation predicate.
    /// ## Functional Correctness
    /// - Consumes one callback and transfers its matching completion permit to the checked runner.
    /// ## Preconditions
    /// - The callback and permit are valid and have identical summaries and online sets; invoke outside the monitor lock.
    /// ## Postconditions
    /// - The callback is consumed; no eventual-return, no-unwind, or destructor-termination guarantee is made.
    /* New explicit-context RCU API; the legacy implicit preemption and Drop path is not used.
     * Origin Rust: <none; new executable code>
     */
    pub fn invoke(self, Tracked(permit): Tracked<RcuReclaimPermit>)
        requires
            self.inv(),
            permit.inv(),
            permit.summary() == self.summary(),
            permit.online() == self.online(),
    {
        // SAFETY: private paired construction and consuming ownership satisfy
        // the raw erasure boundary; the complete invocation predicate is proven.
        unsafe {
            self.callback.call_once(Tracked(permit));
        }
    }
}

} // verus!
