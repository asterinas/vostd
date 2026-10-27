// SPDX-License-Identifier: MPL-2.0
//! Executable root operations under the native IRC11 model.
//!
//! # Verified Properties
//! Acquire loads return a physical lease for the exact selected allocation.
//! Release replacement transfers a unique retirement ticket to the caller.
//! Closing a read returns its original CPU fragment; reclaiming a ticket
//! requires the matching completed grace-period permit.
use vstd::{
    invariant::{AtomicInvariant, InvariantPredicate},
    modes::tracked_static_ref,
    prelude::*,
    raw_ptr::spec_cast_ptr_to_thin_ptr,
    resource::Loc,
};
use vstd_extra::{
    atomic_irc11::{AtomicId, Objective, PAtomicWeakPtr, ThreadView, ViewSeen},
    ownership::Inv,
};

use crate::specs::sync::rcu::{
    atomic::{RcuRetiredRoot, RcuRootAtomicState, RcuRootOwnershipPredicate, RcuRootProtection},
    cpu::{CpuRcuCoreBinding, CpuRcuReaderFragment},
    grace_period::RcuReclaimPermit,
    link::RcuLinkObservation,
    traversal::AllocationId,
};

use crate::cpu::CpuId;
use core::{marker::PhantomData, sync::atomic::Ordering};

verus! {

broadcast use vstd::atomic_weak::group_view_history;

/// Stable identities captured by a root and every callback it produces.
pub ghost struct RcuRootKey {
    pub nullable: bool,
    pub scheduler: Loc,
    pub online: Set<CpuId>,
    pub domain: Loc,
    pub observations: Loc,
    pub active: Loc,
    pub reclaim: Loc,
}

/// Interprets the native root invariant using the client's physical ownership predicate.
pub ghost struct RcuRootAtomicPredicate<Pred> {
    marker: PhantomData<Pred>,
}

impl<T, O: Objective, Pred: RcuRootOwnershipPredicate<T, O>> InvariantPredicate<
    (RcuRootKey, AtomicId, spec_fn(O) -> bool),
    RcuRootAtomicState<T, O>,
> for RcuRootAtomicPredicate<Pred> {
    open spec fn inv(
        key: (RcuRootKey, AtomicId, spec_fn(O) -> bool),
        state: RcuRootAtomicState<T, O>,
    ) -> bool {
        &&& state.inv::<Pred>()
        &&& state.condition() == key.2
        &&& (!key.0.nullable ==> (forall|ts: nat|
            state.points_to().hist().contains_timestamp(ts)
                ==> #[trigger] state.points_to().hist().value(ts).addr() != 0))
        &&& state.points_to().loc() == key.1
        &&& state.root().domain() == key.0.domain
        &&& state.retirement().id() == key.0.observations
        &&& state.permissions().registry() == key.0.active
        &&& state.permissions().reclaim_registry() == key.0.reclaim
        &&& state.permissions().scheduler() == key.0.scheduler
        &&& state.permissions().online() == key.0.online
    }
}

type RootInvariant<T, O, Pred> = AtomicInvariant<
    (RcuRootKey, AtomicId, spec_fn(O) -> bool),
    RcuRootAtomicState<T, O>,
    RcuRootAtomicPredicate<Pred>,
>;

/* This adapter uses the existing native IRC11 pointer primitive so the same
 * load/release-swap instructions carry checked RCU state transitions.
 * Origin Rust: <none; new executable code>
 */

#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(O)]
pub struct RcuWeakRoot<T: 'static, O: Objective + 'static, Pred: 'static> {
    atomic: PAtomicWeakPtr<T>,
    tracked_state: Tracked<&'static RootInvariant<T, O, Pred>>,
}

/// Callback handle for detached allocations, independent of the root's lifetime.
/// It owns no native pointer and exposes no load or publication operation.
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(O)]
pub struct RcuRootReclaimer<T: 'static, O: Objective + 'static, Pred: 'static> {
    tracked_state: Tracked<&'static RootInvariant<T, O, Pred>>,
}

impl<T: 'static, O: Objective + 'static, Pred: 'static> RcuRootReclaimer<T, O, Pred> {
    /// Fixed allocation, scheduler, and reclamation authority identities.
    pub closed spec fn key(&self) -> RcuRootKey {
        self.tracked_state@.constant().0
    }
}

impl<T: 'static, O: Objective + 'static, Pred: 'static> RcuWeakRoot<T, O, Pred> {
    /// Stable resource identities used by readers and callbacks.
    pub closed spec fn key(&self) -> RcuRootKey {
        self.tracked_state@.constant().0
    }

    /// Immutable client predicate attached to every publication in this root.
    pub closed spec fn condition(&self) -> spec_fn(O) -> bool {
        self.tracked_state@.constant().2
    }

    /// Native atomic location corresponding to the protected points-to resource.
    pub closed spec fn native_loc(&self) -> AtomicId {
        self.atomic.loc()
    }
}

impl<T: 'static, O: Objective + 'static, Pred: 'static> Inv for RcuWeakRoot<T, O, Pred> {
    closed spec fn inv(self) -> bool {
        self.tracked_state@.constant().1 == self.native_loc()
    }
}

/* The methods below preserve native AtomicPtr ordering. All additional
 * registration, lease, and retirement operations erase during compilation.
 * Origin Rust: <none; new executable code>
 */

impl<
    T: 'static,
    O: Objective + 'static,
    Pred: RcuRootOwnershipPredicate<T, O> + 'static,
> RcuWeakRoot<T, O, Pred> {
    /// Creates a root and returns the native initialization view to its caller.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Retains the supplied physical ownership in the native invariant.
    ///
    /// ## Functional Correctness
    ///
    /// - Creates a nullable or non-null typed publication history.
    ///
    /// ## Preconditions
    ///
    /// - Non-null pointers carry matching ownership; the requested non-null policy forbids null.
    ///
    /// ## Postconditions
    ///
    /// - Returns a valid root with the requested key and its actual native initialization view.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn new(
        ptr: *mut T,
        Tracked(ownership): Tracked<Option<O>>,
        Ghost(scheduler): Ghost<Loc>,
        Ghost(online): Ghost<Set<CpuId>>,
        Ghost(nullable): Ghost<bool>,
        Tracked(domain): Tracked<vstd_extra::rcu_objects::RcuDomainAuth>,
        Ghost(condition): Ghost<spec_fn(O) -> bool>,
    ) -> (res: (Self, Tracked<ViewSeen>))
        requires
            domain.inv(),
            domain.objects() == Map::<nat, usize>::empty(),
            (ownership is Some) == (ptr.addr() != 0),
            ownership matches Some(owned) ==> Pred::owns(ptr, owned) && condition(owned),
            nullable || ptr.addr() != 0,
        ensures
            res.0.inv(),
            res.0.key().domain == domain.id(),
            res.0.condition() == condition,
            res.0.key().scheduler == scheduler,
            res.0.key().online == online,
            res.0.key().nullable == nullable,
    {
        let (atomic, Tracked(points_to), Tracked(view), Ghost(timestamp)) = PAtomicWeakPtr::new(
            ptr,
        );
        let tracked state = RcuRootAtomicState::tracked_initial::<Pred>(
            domain,
            condition,
            points_to,
            ptr,
            ownership,
            timestamp,
            view@,
            scheduler,
            online,
        );
        let ghost key = RcuRootKey {
            nullable,
            scheduler,
            online,
            domain: state.root().domain(),
            observations: state.retirement().id(),
            active: state.permissions().registry(),
            reclaim: state.permissions().reclaim_registry(),
        };
        let tracked invariant = AtomicInvariant::new((key, atomic.loc(), condition), state, 0);
        let tracked invariant = tracked_static_ref(invariant);
        (Self { atomic, tracked_state: Tracked(invariant) }, Tracked(view))
    }

    fn raw_atomic(&self) -> (res: &PAtomicWeakPtr<T>)
        ensures
            res.loc() == self.native_loc(),
        opens_invariants none
        no_unwind
    {
        &self.atomic
    }

    proof fn tracked_invariant(tracked &self) -> (tracked res: &'static RootInvariant<T, O, Pred>)
        requires
            self.inv(),
        ensures
            res.constant() == (self.key(), self.native_loc(), self.condition()),
    {
        self.tracked_state.get()
    }

    /// Keeps the detached allocation authority available for delayed callbacks.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Copies only the retained invariant handle, not allocation ownership.
    ///
    /// ## Functional Correctness
    ///
    /// - Makes delayed reclamation independent of the atomic root's lifetime.
    ///
    /// ## Preconditions
    ///
    /// - The root is valid.
    ///
    /// ## Postconditions
    ///
    /// - Returns a handle with this root's exact key.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn reclaimer(&self) -> (res: RcuRootReclaimer<T, O, Pred>)
        requires
            self.inv(),
        ensures
            res.key() == self.key(),
    {
        RcuRootReclaimer { tracked_state: Tracked(self.tracked_state.get()) }
    }

    /// Acquire-loads and protects a historical value using the caller's native view.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Obtains physical ownership only as a live read lease after native coherence checks.
    ///
    /// ## Functional Correctness
    ///
    /// - Acquire-loads a historical pointer using the actual caller view.
    ///
    /// ## Preconditions
    ///
    /// - The canonical reader and CPU binding match this root's scheduler and online set; the view covers the reader's observations.
    ///
    /// ## Postconditions
    ///
    /// - Returns the exact selected pointer and protection; non-null policy holds and the view grows monotonically.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn load_acquire(
        &self,
        Tracked(view): Tracked<&mut ViewSeen>,
        Tracked(reader): Tracked<CpuRcuReaderFragment>,
        Tracked(binding): Tracked<CpuRcuCoreBinding>,
    ) -> (res: (*mut T, Tracked<RcuRootProtection<T, O>>, Ghost<nat>))
        requires
            self.inv(),
            reader.wf(),
            binding.registry() == self.key().scheduler,
            binding.cpu() == reader.cpu(),
            binding.locals_key().len() == 1,
            binding.single_local_id() == reader.participant_id(),
            old(view)@.contains(reader.participant_view()),
            self.key().online.contains(reader.cpu()),
        ensures
            final(view)@.contains(old(view)@),
            res.1@.inv(),
            res.1@.reader() == reader,
            res.1@.lease() matches Some(lease) ==> lease.witness().start_view() == old(view)@,
            !self.key().nullable ==> res.1@.lease() is Some,
            match (res.1@.info(), res.1@.lease()) {
                (Some(info), Some(lease)) => {
                    &&& res.0.addr() != 0
                    &&& equal(info.ptr(), res.0)
                    &&& info.domain() == self.key().domain
                    &&& lease.registry() == self.key().active
                    &&& Pred::owns(res.0, lease.resource())
                    &&& (self.condition())(lease.resource())
                },
                (None, None) => res.0.addr() == 0,
                _ => false,
            },
    {
        let result;
        let ghost start_view = view@;
        let atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_invariant() => state => {
            let loaded = atomic.load(Ordering::Acquire, Tracked(view), Tracked(state.tracked_borrow_points_to()));
            proof {
                assert(state.points_to().hist().contains_timestamp(loaded.2@.timestamp));
                if !self.key().nullable {
                    assert(state.points_to().hist().value(loaded.2@.timestamp).addr() != 0);
                    assert(loaded.0.addr() != 0);
                }
            }
            let tracked protection = state.tracked_protect_load::<Pred>(
                loaded.0, loaded.2@.timestamp, loaded.2@.message_view,
                start_view, view@, reader, binding,
            );
            result = (loaded.0, Tracked(protection), Ghost(loaded.2@.timestamp));
        });
        result
    }

    /// Acquires a single owning link and its physical lease in the same invariant opening.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Native coherence excludes observed-dead historical edges before issuing the lease.
    /// ## Functional Correctness
    /// - One acquire supplies both the topology observation and exact typed allocation.
    /// ## Preconditions
    /// - Supply a protected predecessor from another domain and its live reader generation/start view.
    /// ## Postconditions
    /// - The child witness retains that reader and start view; null produces no physical lease.
    /* The extra topology operations erase; there is still exactly one native acquire load.
     * Origin Rust: <none; new executable code>
     */
    pub fn load_acquire_link<U, A>(
        &self,
        Tracked(view): Tracked<&mut ViewSeen>,
        Tracked(reader): Tracked<CpuRcuReaderFragment>,
        Tracked(binding): Tracked<CpuRcuCoreBinding>,
        Ghost(start_view): Ghost<ThreadView>,
        Ghost(source): Ghost<AllocationId>,
        Ghost(source_ptr): Ghost<*mut T>,
        Tracked(parent): Tracked<&RcuRootProtection<U, A>>,
    ) -> (res: (*mut T, Tracked<RcuRootProtection<T, O>>, Ghost<RcuLinkObservation<T>>))
        requires
            self.inv(),
            reader.wf(),
            parent.inv(),
            match (parent.info(), parent.lease()) {
                (Some(info), Some(lease)) => {
                    &&& source == (AllocationId { domain: info.domain(), object: info.obj() })
                    &&& source_ptr == spec_cast_ptr_to_thin_ptr::<U, T>(info.ptr())
                    &&& start_view == lease.witness().start_view()
                },
                _ => false,
            },
            reader.participant_id() == parent.reader().participant_id(),
            reader.generation() == parent.reader().generation(),
            reader.participant_view() == parent.reader().participant_view(),
            reader.known_retired() == parent.reader().known_retired(),
            source.domain != self.key().domain,
            binding.registry() == self.key().scheduler,
            binding.cpu() == reader.cpu(),
            binding.locals_key().len() == 1,
            binding.single_local_id() == reader.participant_id(),
            old(view)@.contains(start_view),
            start_view.contains(reader.participant_view()),
            self.key().online.contains(reader.cpu()),
        ensures
            final(view)@.contains(old(view)@),
            res.1@.inv(),
            res.1@.reader() == reader,
            res.2@.inv(),
            res.2@.source == source,
            res.2@.reader == reader.participant_id(),
            res.2@.generation == reader.generation(),
            res.2@.start_view == start_view,
            match (res.1@.info(), res.1@.lease(), res.2@.child) {
                (Some(info), Some(lease), Some(child)) => {
                    &&& res.0.addr() != 0
                    &&& equal(info.ptr(), res.0)
                    &&& info.domain() == self.key().domain
                    &&& child == (AllocationId { domain: info.domain(), object: info.obj() })
                    &&& lease.registry() == self.key().active
                    &&& lease.witness().start_view() == start_view
                    &&& Pred::owns(res.0, lease.resource())
                    &&& (self.condition())(lease.resource())
                    &&& equal(res.0, res.2@.graph.objects[child])
                },
                (None, None, None) => res.0.addr() == 0,
                _ => false,
            },
    {
        let result;
        let ghost before_view = view@;
        let atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_invariant() => state => {
            let loaded = atomic.load(Ordering::Acquire, Tracked(view), Tracked(state.tracked_borrow_points_to()));
            let tracked protected = state.tracked_protect_link_load::<Pred, U, A>(
                loaded.0, loaded.2@.timestamp, loaded.2@.message_view, before_view, view@,
                start_view, source, source_ptr, reader, binding, parent);
            result = (loaded.0, Tracked(protected.protection), Ghost(protected.observation));
        });
        result
    }

    /// Replaces the root with release ordering and returns its old retirement ticket.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Retains old ownership behind a unique retirement ticket.
    ///
    /// ## Functional Correctness
    ///
    /// - Release-swaps the root and certifies the actual detached allocation.
    ///
    /// ## Preconditions
    ///
    /// - The root is valid and the replacement carries matching ownership and obeys nullability.
    ///
    /// ## Postconditions
    ///
    /// - Returns the old pointer and matching ticket, if non-null; the removal is observed in the resulting view.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn replace_release(
        &self,
        ptr: *mut T,
        Tracked(ownership): Tracked<Option<O>>,
        Tracked(view): Tracked<&mut ViewSeen>,
        Ghost(link_source): Ghost<Option<(AllocationId, *mut T)>>,
    ) -> (res: (*mut T, Tracked<Option<RcuRetiredRoot<T>>>))
        requires
            self.inv(),
            (ownership is Some) == (ptr.addr() != 0),
            ownership matches Some(owned) ==> Pred::owns(ptr, owned) && (self.condition())(owned),
            self.key().nullable || ptr.addr() != 0,
            link_source matches Some((source, _)) ==> source.domain != self.key().domain
                && ptr.addr() == 0,
        ensures
            final(view)@.contains(old(view)@),
            !self.key().nullable ==> res.1@ is Some && res.0.addr() != 0,
            match res.1@ {
                Some(retired) => {
                    &&& retired.inv()
                    &&& (retired.link_removal() is Some) == (link_source is Some)
                    &&& retired.link_removal() matches Some(link) ==> link.source
                        == link_source->Some_0.0
                    &&& equal(retired.ptr(), res.0)
                    &&& retired.registry() == self.key().reclaim
                    &&& retired.record().domain == self.key().domain
                    &&& retired.record().retire_observation_registry == self.key().observations
                    &&& retired.record().removal.observed_by(final(view)@)
                },
                None => res.0.addr() == 0,
            },
    {
        let result;
        let atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_invariant() => state => {
            let ghost before = state.points_to();
            let ghost old_timestamp = state.root().root().current_timestamp();
            let swapped = atomic.swap_release(ptr, Tracked(view), Tracked(state.tracked_borrow_points_to_mut()));
            proof {
                assert(swapped.2@.load_timestamp == old_timestamp);
                if !self.key().nullable { assert(swapped.0.addr() != 0); }
                assert forall|ts: nat| state.points_to().hist().contains_timestamp(ts) && !self.key().nullable
                    implies #[trigger] state.points_to().hist().value(ts).addr() != 0 by {
                    if ts != swapped.2@.load_timestamp + 1 {
                        assert(before.hist().contains_timestamp(ts));
                        assert(before.hist().value(ts).addr() != 0);
                    }
                };
            }
            let tracked retired = state.tracked_replace::<Pred>(
                before, ptr, swapped.2@.load_timestamp + 1,
                swapped.2@.store_message_view, ownership, link_source,
            );
            result = (swapped.0, Tracked(retired));
        });
        result
    }

    /// Native conditional replacement. Failure returns the unpublished ownership intact.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Failure returns unpublished ownership; success retains detached ownership in a ticket.
    ///
    /// ## Functional Correctness
    ///
    /// - Uses AcqRel success and Acquire failure ordering on native CAS.
    ///
    /// ## Preconditions
    ///
    /// - The root is valid and the replacement carries matching ownership and obeys nullability.
    ///
    /// ## Postconditions
    ///
    /// - Failure returns the original permission; success returns the observed pointer's ticket; the view only grows.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn compare_exchange(
        &self,
        expected: *mut T,
        ptr: *mut T,
        Tracked(ownership): Tracked<Option<O>>,
        Tracked(view): Tracked<&mut ViewSeen>,
    ) -> (res: (Result<*mut T, *mut T>, Tracked<Option<RcuRetiredRoot<T>>>, Tracked<Option<O>>))
        requires
            self.inv(),
            (ownership is Some) == (ptr.addr() != 0),
            ownership matches Some(owned) ==> Pred::owns(ptr, owned) && (self.condition())(owned),
            self.key().nullable || ptr.addr() != 0,
        ensures
            final(view)@.contains(old(view)@),
            match res.0 {
                Ok(previous) => {
                    &&& previous.addr() == expected.addr()
                    &&& res.2@ is None
                    &&& (!self.key().nullable ==> previous.addr() != 0)
                    &&& match res.1@ {
                        Some(retired) => {
                            &&& retired.inv()
                            &&& equal(retired.ptr(), previous)
                            &&& retired.registry() == self.key().reclaim
                            &&& retired.record().domain == self.key().domain
                            &&& retired.record().retire_observation_registry
                                == self.key().observations
                            &&& retired.record().removal.observed_by(final(view)@)
                        },
                        None => previous.addr() == 0,
                    }
                },
                Err(actual) => {
                    &&& actual.addr() != expected.addr()
                    &&& res.1@ is None
                    &&& res.2@ == ownership
                },
            },
    {
        let result;
        let atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_invariant() => state => {
            let ghost before = state.points_to();
            let ghost previous_ts = state.root().root().current_timestamp();
            let exchanged = atomic.compare_exchange(expected, ptr, Ordering::AcqRel, Ordering::Acquire,
                Tracked(view), Tracked(vstd_extra::atomic_irc11::ReleaseViewSeen::new()),
                Tracked(state.tracked_borrow_points_to_mut()));
            match exchanged.0 {
                Ok(previous) => {
                    proof {
                        assert(exchanged.2@.load_timestamp == previous_ts);
                        if !self.key().nullable { assert(previous.addr() != 0); }
                        assert forall|ts: nat| state.points_to().hist().contains_timestamp(ts) && !self.key().nullable
                            implies #[trigger] state.points_to().hist().value(ts).addr() != 0 by {
                            if ts != exchanged.2@.load_timestamp + 1 {
                                assert(before.hist().contains_timestamp(ts));
                                assert(before.hist().value(ts).addr() != 0);
                            }
                        };
                    }
                    let tracked retired = state.tracked_replace::<Pred>(before, ptr,
                        exchanged.2@.load_timestamp + 1, exchanged.2@.store_message_view, ownership, None);
                    result = (Ok(previous), Tracked(retired), Tracked(None));
                },
                Err(actual) => { result = (Err(actual), Tracked(None), Tracked(ownership)); },
            }
        });
        result
    }

    /// Returns a physical lease before the enclosing preemption session ends.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Returns the physical lease before releasing its reader authority.
    ///
    /// ## Functional Correctness
    ///
    /// - Consumes the read protection without modifying executable pointer state.
    ///
    /// ## Preconditions
    ///
    /// - The protection is valid and any physical lease belongs to this root.
    ///
    /// ## Postconditions
    ///
    /// - Returns the exact original, valid CPU reader fragment.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn close(&self, Tracked(protection): Tracked<RcuRootProtection<T, O>>) -> (res: Tracked<
        CpuRcuReaderFragment,
    >)
        requires
            self.inv(),
            protection.inv(),
            protection.lease() matches Some(lease) ==> lease.registry() == self.key().active,
        ensures
            res@ == protection.reader(),
            res@.wf(),
    {
        let tracked reader;
        vstd::invariant::open_atomic_invariant!(self.tracked_invariant() => state => {
            proof { reader = state.tracked_close::<Pred>(protection); }
        });
        Tracked(reader)
    }

    /// Recovers ownership only after matching both the callback ticket and permit.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Proves that no active physical lease remains before recovering full ownership.
    ///
    /// ## Functional Correctness
    ///
    /// - Consumes the unique exact-pointer claim and matching completed grace-period permit.
    ///
    /// ## Preconditions
    ///
    /// - The ticket and permit are valid and match this root's registries, scheduler, allocation, and online set.
    ///
    /// ## Postconditions
    ///
    /// - Returns physical ownership satisfying the client's predicate for the retired pointer.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn reclaim(
        &self,
        Tracked(retired): Tracked<RcuRetiredRoot<T>>,
        Tracked(permit): Tracked<RcuReclaimPermit>,
    ) -> (res: Tracked<O>)
        requires
            self.inv(),
            retired.inv(),
            permit.inv(),
            retired.registry() == self.key().reclaim,
            retired.record() == permit.summary().retired,
            retired.record().domain == self.key().domain,
            retired.record().retire_observation_registry == self.key().observations,
            permit.summary().scheduler == self.key().scheduler,
            permit.online() == self.key().online,
        ensures
            Pred::owns(retired.ptr(), res@),
    {
        self.reclaimer().reclaim(Tracked(retired), Tracked(permit))
    }
}

/* Reclamation requires only the retained invariant, not the atomic root's
 * lifetime. All resource manipulation erases; callers reconstruct P afterward.
 * Origin Rust: <none; new executable code>
 */

impl<
    T: 'static,
    O: Objective + 'static,
    Pred: RcuRootOwnershipPredicate<T, O> + 'static,
> RcuRootReclaimer<T, O, Pred> {
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Proves that no active physical lease remains before recovering full ownership.
    ///
    /// ## Functional Correctness
    ///
    /// - Consumes the unique exact-pointer claim and matching completed grace-period permit.
    ///
    /// ## Preconditions
    ///
    /// - The ticket and permit are valid and match this root's registries, scheduler, allocation, and online set.
    ///
    /// ## Postconditions
    ///
    /// - Returns physical ownership satisfying the client's predicate for the retired pointer.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn reclaim(
        &self,
        Tracked(retired): Tracked<RcuRetiredRoot<T>>,
        Tracked(permit): Tracked<RcuReclaimPermit>,
    ) -> (res: Tracked<O>)
        requires
            retired.inv(),
            permit.inv(),
            retired.registry() == self.key().reclaim,
            retired.record() == permit.summary().retired,
            retired.record().domain == self.key().domain,
            retired.record().retire_observation_registry == self.key().observations,
            permit.summary().scheduler == self.key().scheduler,
            permit.online() == self.key().online,
        ensures
            Pred::owns(retired.ptr(), res@),
    {
        let tracked ownership;
        vstd::invariant::open_atomic_invariant!(self.tracked_state.get() => state => {
            proof { ownership = state.tracked_reclaim::<Pred>(retired, permit); }
        });
        Tracked(ownership)
    }
}

} // verus!
