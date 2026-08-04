// SPDX-License-Identifier: MPL-2.0
//! Read-copy update (RCU).
//!
//! This is the new weak-memory RCU skeleton. The previous SC proof-oriented
//! implementation is kept in `__mod.rs` as reference and is not compiled.
//!
//! # Verification model
//!
//! The executable RCU API is being rebuilt around an explicit weak-memory
//! history model. The atomic root pointer is a trusted executable wrapper around
//! Rust atomics, while proofs only rely on the specification in
//! [`specs::sync::weak_memory`]. Each RCU root pointer is represented by a
//! `WeakAtomicPtr` whose history records the messages that may be observed by
//! relaxed/acquire loads and CAS operations. Weak atomic operations borrow the
//! unique `ThreadView` from the current task's `RunningTaskContext`; RCU
//! never mints a fresh view and therefore preserves observations across RCU
//! operations and release publication.
//!
//! The root-pointer invariant keeps publication metadata for the complete
//! atomic history. Each non-null message has a domain-local allocation ID, so
//! stale messages remain distinguishable even if a physical address is later
//! reused. Multiple messages may refer to one registration and therefore carry
//! the same allocation ID; an atomic timestamp is never used as an allocation
//! identity. The owned root invariant retains a persistent typed `BlockInfo`
//! for every registered AId, including retired historical entries. An acquire
//! load therefore returns proof of the exact typed pointer and AId it observed,
//! rather than reconstructing identity from the address. `Rcu` roots are
//! non-null in every message, while `RcuOption` roots may contain null messages
//! without allocation IDs. Physical `P::Permission`, reader permissions,
//! traversal snapshots, and reclamation are modeled separately in
//! [`specs::sync::rcu`] and are being connected incrementally.
//!
//! The traversal layer follows the paper's shape:
//!
//! - [`RcuReadGuardToken<T>`] represents a read-side critical section together
//!   with its base `Guard(tid, X, G)` state and `SeenRemoved(D, LV)` observation.
//! - [`RcuProtectedPtr<T>`] records an AId/address pair installed in the live
//!   guard's mutable protection map `G`.
//! - [`RcuBaseRetirePerm<T>`] becomes [`RcuRetirePerm<T>`] only after the caller has
//!   observed enough traversal state to prove the allocation ID is in the
//!   removed set. The domain's base `rcu-retire` transition then records it in
//!   `RcuState.R` as `RcuRetired<T>`.
//! - `RcuCallbackSafety` compresses that recorded retire proof into an erased
//!   summary containing the domain, AId, removal observation,
//!   observation-registry identity, retire epoch, and retire view,
//!   which is what the monitor stores next to a type-erased executable
//!   callback. `removal` is the paper's `Retired(a, Q)` detachment observation:
//!   it records the root atomic and the first timestamp after the object was
//!   removed. The retire view observes that timestamp and records the
//!   observations that every quiescent report must cover before physical
//!   reclamation.
//!
//! # Callback boundary
//!
//! Executable callbacks are represented by `vstd_extra::raw_callback::RawCallback`.
//! `RawCallback` is proof-opaque: it only stores a thin data pointer plus a
//! monomorphized runner pointer. The RCU monitor wraps it in `monitor::RcuCallback`,
//! which can only be constructed from a `RcuCallbackSafety` certificate. This
//! prevents the proof layer from treating an arbitrary type-erased callback as a
//! safe reclamation callback.
//!
//! The monitor also has a weak-memory `is_monitoring` flag with an RCU-specific
//! invariant: every flag-history message records a snapshot of the
//! lock-protected monitor state (`specs::sync::rcu::MonitorStateView`), and a
//! `false` message certifies that its snapshot has no pending callbacks and no
//! incomplete grace period. `finish_grace_period` removes the completed batch
//! under the monitor lock and produces a private `CompletedGracePeriod`
//! certificate. For each callback, the monitor combines that certificate with
//! the callback's traversal-retire safety token to produce a linear
//! object-level reclaim permit, then executes exactly that batch outside the
//! lock. The monitor lock carries a linear release view: enqueue publishes the
//! callback's `retire_view`, and each CPU report is created only after an
//! acquire imports that view. A completed certificate therefore proves that
//! every online CPU's report view covers every callback in the batch.
//!
//! # Usage outline
//!
//! Use `Rcu<P>` when the root pointer is always non-null, and `RcuOption<P>`
//! when the root may be null. `P` must implement `NonNullPtr`; the common cases
//! are sized thin-pointer owners such as `Box<T>` and `Arc<T>`. Readers call
//! `read()` to obtain a guard and then use `get()` while the guard is live.
//! Writers install a new pointer with `update()` or use the read guard's
//! `compare_exchange()` to replace the value they observed.
//!
//! Verified callers carry one `RunningTaskContext` for the current task. RCU
//! operations receive a mutable borrow of that context through erased
//! `#[verus_spec(with ...)]` arguments. Starting a read-side critical section
//! increments its modeled preemption depth and removes one session fraction;
//! guard destruction reverses both changes. The scheduler can check the
//! updated view back in only after the context is quiescent.
//!
//! Delayed reclamation is still being wired into the weak-memory proof. The
//! weak atomic invariant retains the current registration together with
//! `P::Permission`; release swap and successful CAS establish root removal,
//! return the old raw pointer and matching ownership, and route a certified
//! callback into the monitor. Scheduler handoff now preserves a per-CPU
//! `ThreadView`: schedule-out joins the departing task's observations into the
//! CPU view, and schedule-in imports that view into the incoming task together
//! with the CPU's canonical `CpuRcuParticipant`.
//!
//! An executable `read()` now performs the paper's `Inactive -> Guard`
//! transition while opening the root weak-atomic invariant. The resulting
//! `CpuRcuReadGuardToken`, its fractional CPU reader fragment, and the exact
//! historical `BlockInfo` remain in the executable read guard until
//! destruction or consuming CAS performs `Guard -> Inactive` and returns the
//! fragment before re-enabling preemption.
//!
//! A guarded weak load now installs the loaded root's exact `BlockInfo` in the
//! guard's protection map. The proof derives the guard's expired set from the
//! entering task's view and the recorded root-removal observations. If the
//! loaded AId were expired, weak-memory coherence and the root history's
//! removal invariant would contradict the load timestamp. The remaining
//! traversal boundary is converting that abstract protection into the client
//! pointer's physical reference permission; `assume_shared_ref` still stands
//! in for that final argument.
//!
//! The proof-only `rcu_cpu` module now defines the required persistent
//! `CpuRcuParticipant`: a reader splits a fractional fragment, and a quiescent
//! report requires the full fraction before advancing the CPU generation and
//! view. Monitor completion retains one `CpuRcuClosedGeneration` for every
//! online CPU and duplicates those persistent resources into each callback's
//! `RcuReclaimPermit`. A live guard that coexists with such a permit is
//! necessarily from a later CPU generation and its start view includes the
//! callback's removal observation. The matching retirement record therefore
//! belongs to the guard's expired set. Since traversal well-formedness embeds
//! expired objects in `SeenRemoved`, a callback permit and a guard-protected
//! pointer to the same object are proved mutually exclusive.
//!
//! The remaining end-to-end boundary is physical reference ownership. Guarded
//! loads must split an `RcuReadLease<P::Permission>`, guard destruction must
//! return it, and reclamation must recover the whole pool before invoking the
//! callback. Until that is connected, `assume_shared_ref` remains the explicit
//! reference-permission bypass.
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref, ptr::NonNull};

use vstd::prelude::*;
use vstd_extra::prelude::*;
use vstd_extra::raw_callback::{RawCallback, RawCallbackContext};
use vstd_extra::rcu_read_pool::RcuReadLease;

use crate::{
    specs::{
        sync::{
            rcu as rcu_spec, rcu_cpu as rcu_cpu_spec,
            weak_memory::{RcuWeakAtomicPtr, ThreadView},
        },
        task::InAtomicMode,
    },
    sync::Once,
    task::{DisabledPreemptGuard, RunningTaskContext, disable_preempt_in_context},
};

use non_null::{NonNullPtr, NonNullPtrRef};

pub mod monitor;
pub mod non_null;

verus! {

broadcast use vstd_extra::external::nonnull::group_nonull_axioms;

exec static RCU_MONITOR: Once<
    monitor::RcuMonitor,
    monitor::RcuMonitorOwner,
    monitor::RcuMonitorPred,
>
    ensures
        RCU_MONITOR.wf(),
        RCU_MONITOR.inv() == monitor::RcuMonitorPred,
{
    Once::new(Ghost(monitor::RcuMonitorPred))
}

struct RcuPointerOwnership<P: NonNullPtr> {
    _marker: PhantomData<P>,
}

impl<P: NonNullPtr> rcu_spec::RcuRootOwnershipPredicate<
    <P as NonNullPtr>::Target,
    <P as NonNullPtr>::Permission,
> for RcuPointerOwnership<P> {
    open spec fn owns(
        ptr: *mut <P as NonNullPtr>::Target,
        ownership: <P as NonNullPtr>::Permission,
    ) -> bool {
        &&& P::ptr_perm_match(ptr, ownership)
        &&& ownership.inv()
    }
}

/// The weak-memory atomic slot used by RCU.
///
/// `bool` is the constant key: `true` means the public cell may contain null
/// (`RcuOption`), and `false` means the public cell is non-null (`Rcu`).  The
/// RCU-specific predicate requires non-null `Rcu` cells to contain only
/// non-null history messages. Its publication registry also assigns every
/// non-null message a domain-local allocation identity, matching the paper's
/// distinction between physical addresses and allocation IDs.
type RcuAtomicGhost<P> = rcu_spec::RcuRootOwnedGhost<
    <P as NonNullPtr>::Target,
    <P as NonNullPtr>::Permission,
>;

type RcuAtomicPtr<P> = RcuWeakAtomicPtr<
    <P as NonNullPtr>::Target,
    <P as NonNullPtr>::Permission,
    RcuPointerOwnership<P>,
>;

/// A Read-Copy Update cell for sharing a non-null pointer.
pub struct Rcu<P: NonNullPtr>(RcuInner<P>);

/// A read-side guard for [`Rcu`].
#[clippy::has_significant_drop]
#[must_use]
pub struct RcuReadGuard<'a, P: NonNullPtr>(RcuReadGuardInner<'a, P>);

/// A Read-Copy Update cell that may contain null.
pub struct RcuOption<P: NonNullPtr>(RcuInner<P>);

/// A read-side guard for [`RcuOption`].
#[clippy::has_significant_drop]
#[must_use]
pub struct RcuOptionReadGuard<'a, P: NonNullPtr>(RcuReadGuardInner<'a, P>);

pub struct RcuInner<P: NonNullPtr> {
    ptr: RcuAtomicPtr<P>,
    ghost_nullable: Ghost<bool>,
    _marker: PhantomData<*const <P as NonNullPtr>::Target>,
}

struct RcuReadGuardInner<'a, P: NonNullPtr> {
    obj_ptr: *mut <P as NonNullPtr>::Target,
    rcu: &'a RcuInner<P>,
    proof_active: bool,
    _inner_guard: DisabledPreemptGuard,
    tracked_info: Tracked<Option<rcu_spec::RcuBlockInfo<<P as NonNullPtr>::Target>>>,
    tracked_guard: Tracked<Option<rcu_cpu_spec::CpuRcuReadGuardToken<<P as NonNullPtr>::Target>>>,
    tracked_session: Tracked<Option<&'a mut RunningTaskContext>>,
}

/// Sized callback payload that retains the physical ownership of one detached
/// RCU object until the monitor executes its callback.
struct RcuDropCallbackContext<P: NonNullPtr + Send> {
    pointer: NonNull<<P as NonNullPtr>::Target>,
    permission: Tracked<<P as NonNullPtr>::Permission>,
}

// SAFETY: the callback consumes the same owning pointer type `P` that was
// accepted by the RCU cell. The tracked permission has no runtime payload.
#[verifier::external]
unsafe impl<P: NonNullPtr + Send> Send for RcuDropCallbackContext<P> {

}

impl<P: NonNullPtr + Send> RawCallbackContext for RcuDropCallbackContext<P> {
    fn run(self) {
        proof {
            use_type_invariant(&self);
        }
        proof_decl! {
            let tracked permission = self.permission.get();
        }
        let _pointer = unsafe { P::from_raw(self.pointer, Tracked(permission)) };
    }
}

impl<P: NonNullPtr + Send> RcuDropCallbackContext<P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& P::ptr_perm_match(self.pointer.as_ptr(), self.permission@)
        &&& self.permission@.inv()
    }
}

/// Erases a detached owned object into an executable callback payload.
///
/// This function does not certify or enqueue the callback. Those operations
/// still require `RcuRetired` and a monitor grace-period certificate.
fn callback_from_detached<P: NonNullPtr + Send>(
    pointer: *mut <P as NonNullPtr>::Target,
    Tracked(owned): Tracked<
        rcu_spec::RcuRetiredOwnedObject<<P as NonNullPtr>::Target, <P as NonNullPtr>::Permission>,
    >,
) -> (res: (RawCallback, Tracked<rcu_spec::RcuCallbackSafety>))
    requires
        !pointer.is_null(),
        equal(owned.ptr(), pointer),
        P::ptr_perm_match(pointer, owned.ownership()),
        owned.ownership().inv(),
    ensures
        res.1@.removal() == owned.retired().removal(),
{
    proof {
        use_type_invariant(&owned);
    }
    proof_decl! {
        let tracked (object, retired, permission) = owned.tracked_into_parts();
        let tracked cert = rcu_spec::certify_callback_from_retired(&object, retired);
    }
    let pointer = unsafe { NonNull::new_unchecked(pointer) };
    let context = RcuDropCallbackContext::<P> { pointer, permission: Tracked(permission) };
    proof {
        use_type_invariant(&context);
    }
    (RawCallback::new(context), Tracked(cert))
}

impl<P: NonNullPtr> RcuInner<P> {
    closed spec fn is_nullable(self) -> bool {
        self.ghost_nullable@
    }

    closed spec fn wf(self) -> bool {
        &&& self.ptr.well_formed()
        &&& self.ptr.constant().nullable == self.ghost_nullable@
    }
}

// SAFETY: `RcuInner` only shares a raw pointer through an atomic slot. Sending
// the cell follows the same requirement as sending the managed pointer wrapper.
#[verifier::external]
unsafe impl<P: NonNullPtr> Send for RcuInner<P> where P: Send {

}

// SAFETY: Readers may obtain shared references, so `P` must be `Sync`; writers
// may install pointers created on another thread, so `P` must be `Send`.
#[verifier::external]
unsafe impl<P: NonNullPtr> Sync for RcuInner<P> where P: Send + Sync {

}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuInner<P> {
    #[inline(always)]
    const fn new_none() -> (res: Self)
        ensures
            res.type_inv(),
            res.is_nullable(),
    {
        proof_decl! {
            let tracked root_ghost: RcuAtomicGhost<P> =
                rcu_spec::RcuRootOwnedGhost::tracked_initial(
                    core::ptr::null_mut::<<P as NonNullPtr>::Target>(),
                    None,
                );
            let ghost key = rcu_spec::RcuRootKey {
                nullable: true,
                domain: root_ghost.domain(),
                reader_registry: root_ghost.reader_registry(),
                retire_observation_registry: root_ghost.retire_observation_registry(),
            };
        }
        let ptr = RcuAtomicPtr::<P>::new(Ghost(key), core::ptr::null_mut(), Tracked(root_ghost));
        Self {
            ptr,
            ghost_nullable: Ghost(true),
            _marker: PhantomData::<*const <P as NonNullPtr>::Target>,
        }
    }

    #[inline(always)]
    #[verus_spec(res =>
        with
            Ghost(nullable): Ghost<bool>,
        ensures
            res.type_inv(),
            res.is_nullable() == nullable,
    )]
    fn new(pointer: P) -> Self {
        let (raw, Tracked(perm)) = P::into_raw(pointer);
        let raw_ptr = raw.as_ptr();
        proof {
            assert(!raw_ptr.is_null());
        }
        proof_decl! {
            let tracked root_ghost =
                rcu_spec::RcuRootOwnedGhost::tracked_initial(raw_ptr, Some(perm));
            let ghost key = rcu_spec::RcuRootKey {
                nullable,
                domain: root_ghost.domain(),
                reader_registry: root_ghost.reader_registry(),
                retire_observation_registry: root_ghost.retire_observation_registry(),
            };
        }
        let ptr = RcuAtomicPtr::<P>::new(Ghost(key), raw_ptr, Tracked(root_ghost));
        Self {
            ptr,
            ghost_nullable: Ghost(nullable),
            _marker: PhantomData::<*const <P as NonNullPtr>::Target>,
        }
    }

    #[inline(always)]
    fn load_ptr_acquire(&self, Tracked(tv): Tracked<&mut ThreadView>) -> (res: (
        *mut <P as NonNullPtr>::Target,
        Tracked<Option<rcu_spec::RcuBlockInfo<<P as NonNullPtr>::Target>>>,
    ))
        requires
            self.type_inv(),
        ensures
            old(tv)@.spec_le(final(tv)@),
            !self.is_nullable() ==> !res.0.is_null(),
            match res.1@ {
                None => res.0.is_null(),
                Some(info) => {
                    &&& !res.0.is_null()
                    &&& info.wf()
                    &&& equal(info.ptr(), res.0)
                },
            },
    {
        proof {
            assert(self.ptr.constant().nullable == self.is_nullable());
        }
        let res = self.ptr.load_acquire_rcu(Tracked(tv));
        proof {
            if !self.is_nullable() {
                assert(!self.ptr.constant().nullable);
                assert(!res.0.is_null());
            }
        }
        (res.0, res.3)
    }

    #[inline(always)]
    fn load_ptr_acquire_guarded(
        &self,
        Ghost(reader): Ghost<rcu_spec::RcuReaderContext>,
        Tracked(cpu_reader): Tracked<rcu_cpu_spec::CpuRcuReaderFragment>,
        Tracked(binding): Tracked<rcu_cpu_spec::CpuRcuCoreBinding>,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (
        *mut <P as NonNullPtr>::Target,
        Tracked<Option<rcu_spec::RcuBlockInfo<<P as NonNullPtr>::Target>>>,
        Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<<P as NonNullPtr>::Target>>,
    ))
        requires
            self.type_inv(),
            cpu_reader.wf(),
            reader.cpu == cpu_reader.cpu(),
            reader.generation == cpu_reader.generation(),
            binding.registry() == reader.scheduler,
            binding.cpu() == cpu_reader.cpu(),
            binding.single_local_id() == cpu_reader.participant_id(),
            cpu_reader.participant_view().spec_le(old(tv)@),
        ensures
            old(tv)@.spec_le(final(tv)@),
            !self.is_nullable() ==> !res.0.is_null(),
            res.2@.wf(),
            res.2@.participant_id() == cpu_reader.participant_id(),
            res.2@.cpu() == cpu_reader.cpu(),
            res.2@.generation() == cpu_reader.generation(),
            res.2@.participant_view() == cpu_reader.participant_view(),
            res.2@.reader_fragment() == cpu_reader,
            res.2@.scheduler() == binding.registry(),
            res.2@.domain() == self.ptr.constant().domain,
            res.2@.reader_registry() == self.ptr.constant().reader_registry,
            res.2@.retire_observation_registry() == self.ptr.constant().retire_observation_registry,
            res.2@.root() == self.ptr.id(),
            res.2@.reader_context() == reader,
            match res.1@ {
                None => res.0.is_null(),
                Some(info) => {
                    &&& !res.0.is_null()
                    &&& info.wf()
                    &&& info.domain() == res.2@.domain()
                    &&& equal(info.ptr(), res.0)
                    &&& !res.2@.expired().contains(info.obj())
                    &&& res.2@.protects(info.addr(), info.obj())
                },
            },
    {
        proof {
            assert(self.ptr.constant().nullable == self.is_nullable());
        }
        let res = self.ptr.load_acquire_rcu_guarded_cpu(
            Ghost(reader),
            Tracked(cpu_reader),
            Tracked(binding),
            Tracked(tv),
        );
        proof {
            if !self.is_nullable() {
                assert(!self.ptr.constant().nullable);
                assert(!res.0.is_null());
            }
        }
        (res.0, res.3, res.4)
    }

    #[inline(always)]
    fn swap_ptr_release(
        &self,
        new_ptr: *mut <P as NonNullPtr>::Target,
        Tracked(ownership): Tracked<Option<<P as NonNullPtr>::Permission>>,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (
        *mut <P as NonNullPtr>::Target,
        Tracked<
            Option<
                rcu_spec::RcuRetiredOwnedObject<
                    <P as NonNullPtr>::Target,
                    <P as NonNullPtr>::Permission,
                >,
            >,
        >,
    ))
        requires
            self.type_inv(),
            self.is_nullable() || !new_ptr.is_null(),
            match ownership {
                Some(ownership) => {
                    &&& !new_ptr.is_null()
                    &&& P::ptr_perm_match(new_ptr, ownership)
                    &&& ownership.inv()
                },
                None => new_ptr.is_null(),
            },
        ensures
            old(tv)@.spec_le(final(tv)@),
            (res.1@ is Some) == !res.0.is_null(),
            res.1@ is Some ==> res.1@->Some_0.object().wf(),
            res.1@ is Some ==> equal(res.1@->Some_0.ptr(), res.0),
            res.1@ is Some ==> res.1@->Some_0.retired().removal().observed_by(final(tv)@),
            res.1@ is Some ==> P::ptr_perm_match(res.0, res.1@->Some_0.ownership()),
            res.1@ is Some ==> res.1@->Some_0.ownership().inv(),
    {
        proof {
            assert(self.ptr.constant().nullable == self.is_nullable());
            assert(self.ptr.constant().nullable || !new_ptr.is_null());
        }
        self.ptr.swap_release_rcu(new_ptr, Tracked(ownership), Tracked(tv))
    }

    fn update(&self, new_ptr: Option<P>, Tracked(session): Tracked<&mut RunningTaskContext>)
        requires
            self.type_inv(),
            self.is_nullable() || new_ptr is Some,
            old(session).wf(),
        ensures
            final(session).wf(),
            final(session).task() == old(session).task(),
            final(session).scheduler() == old(session).scheduler(),
            final(session).cpu() == old(session).cpu(),
            final(session).session_id() == old(session).session_id(),
            final(session).quiescent_generation() == old(session).quiescent_generation(),
            final(session).available_fractions() == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth(),
    {
        proof_decl! {
            let ghost new_ptr_is_some = new_ptr is Some;
        }
        let (raw, Tracked(perm)) = if let Some(new_ptr) = new_ptr {
            let (ptr, Tracked(perm)) = P::into_raw(new_ptr);
            (ptr.as_ptr(), Tracked(Some(perm)))
        } else {
            (core::ptr::null_mut(), Tracked(None))
        };

        proof {
            if !self.is_nullable() {
                assert(new_ptr_is_some);
            }
            assert(self.is_nullable() || !raw.is_null());
        }
        let (old_raw, Tracked(detached)) = {
            proof_decl! {
                let tracked tv = session.tracked_borrow_thread_view_mut();
            }
            self.swap_ptr_release(raw, Tracked(perm), Tracked(tv))
        };
        if !old_raw.is_null() {
            proof_decl! {
                let tracked detached = detached.tracked_unwrap();
            }
            let (callback, cert) = callback_from_detached::<P>(old_raw, Tracked(detached));
            if let Some(monitor) = RCU_MONITOR.get() {
                #[verus_spec(with Tracked(session))]
                monitor.after_grace_period(callback, cert);
            }
        }
    }

    fn read<'a>(&'a self, Tracked(session): Tracked<&'a mut RunningTaskContext>) -> (res:
        RcuReadGuardInner<'a, P>)
        requires
            self.type_inv(),
            old(session).wf(),
            old(session).available_fractions() > 1,
        ensures
            res.type_inv(),
            res.rcu.is_nullable() == self.is_nullable(),
            res.proof_active,
    {
        let ghost context_before_disable = *session;
        let inner_guard = disable_preempt_in_context(Tracked(session));
        proof {
            assert(session.wf());
            session.lemma_rcu_participant_view_le();
        }
        let ghost context_before_reader = *session;
        proof_decl! {
            let tracked cpu_reader = session.tracked_start_rcu_reader();
            let tracked rcu_binding = session.tracked_rcu_binding();
        }
        proof {
            inner_guard.lemma_matches_context_preserved(context_before_reader, session);
            assert(session.rcu_participant_id() == context_before_disable.rcu_participant_id());
            assert(session.rcu_generation() == context_before_disable.rcu_generation());
            assert(session.rcu_participant_view() == context_before_disable.rcu_participant_view());
            assert(context_before_reader.wf());
            assert(context_before_reader.rcu_participant_view().spec_le(
                context_before_reader.view(),
            ));
            assert(cpu_reader.participant_view() == context_before_reader.rcu_participant_view());
            assert(session.view() == context_before_reader.view());
            assert(cpu_reader.participant_view().spec_le(session.view()));
        }
        let ghost reader = rcu_spec::RcuReaderContext {
            scheduler: session.scheduler(),
            task: session.task(),
            session: session.session_id(),
            cpu: session.cpu(),
            generation: session.rcu_generation(),
        };
        let ghost context_before_load = *session;
        proof_decl! {
            let tracked tv = DisabledPreemptGuard::tracked_borrow_thread_view_mut_from_context(
                session,
                &inner_guard,
            );
        }
        let (obj_ptr, tracked_info, tracked_guard) = self.load_ptr_acquire_guarded(
            Ghost(reader),
            Tracked(cpu_reader),
            Tracked(rcu_binding),
            Tracked(tv),
        );
        proof {
            assert(session.rcu_participant_id() == context_before_disable.rcu_participant_id());
            assert(session.rcu_generation() == context_before_disable.rcu_generation());
            assert(session.rcu_participant_view() == context_before_disable.rcu_participant_view());
            assert(tracked_guard@.participant_id() == cpu_reader.participant_id());
            assert(cpu_reader.participant_id() == context_before_reader.rcu_participant_id());
            assert(session.rcu_participant_id() == context_before_reader.rcu_participant_id());
            assert(session.wf());
            inner_guard.lemma_matches_context_preserved(context_before_load, session);
            assert(inner_guard.matches_context(*session));
            assert(inner_guard.has_resource());
            assert(tracked_guard@.wf());
            assert(tracked_guard@.domain() == self.ptr.constant().domain);
            assert(tracked_guard@.root() == self.ptr.id());
            assert(tracked_guard@.reader_registry() == self.ptr.constant().reader_registry);
            assert(tracked_guard@.retire_observation_registry()
                == self.ptr.constant().retire_observation_registry);
            assert(tracked_guard@.cpu() == session.cpu());
            assert(tracked_guard@.generation() == session.rcu_generation());
            assert(cpu_reader.fraction() == context_before_reader.rcu_fraction() / 2real);
            assert(context_before_load.rcu_fraction() == context_before_reader.rcu_fraction()
                / 2real);
            assert(session.rcu_fraction() == context_before_load.rcu_fraction());
            assert(tracked_guard@.reader_fragment().fraction() == cpu_reader.fraction());
            assert(tracked_guard@.reader_fragment().fraction() == session.rcu_fraction());
            assert(tracked_guard@.reader_context() == (rcu_spec::RcuReaderContext {
                scheduler: session.scheduler(),
                task: session.task(),
                session: session.session_id(),
                cpu: session.cpu(),
                generation: session.rcu_generation(),
            }));
            match tracked_info@ {
                None => assert(obj_ptr.is_null()),
                Some(info) => {
                    assert(!obj_ptr.is_null());
                    assert(info.wf());
                    assert(info.domain() == tracked_guard@.domain());
                    assert(equal(info.ptr(), obj_ptr));
                    assert(!tracked_guard@.expired().contains(info.obj()));
                    assert(tracked_guard@.protects(info.addr(), info.obj()));
                },
            }
        }
        let res = RcuReadGuardInner {
            obj_ptr,
            rcu: self,
            proof_active: true,
            _inner_guard: inner_guard,
            tracked_info,
            tracked_guard: Tracked(Some(tracked_guard.get())),
            tracked_session: Tracked(Some(session)),
        };
        proof {
            let ghost stored_context = *res.tracked_session@->Some_0;
            assert(res._inner_guard.matches_context(stored_context));
            assert(res.guard_token().participant_id() == stored_context.rcu_participant_id());
            assert(res.guard_token().cpu() == stored_context.cpu());
            assert(res.guard_token().generation() == stored_context.rcu_generation());
            assert(res.guard_token().reader_fragment().fraction() == stored_context.rcu_fraction());
            assert(res.guard_token().reader_context() == reader);
            assert(res.matches_context(stored_context));
        }
        res
    }
}

/// Detaches the proof-only reader state while leaving the executable
/// preemption guard in place.
///
/// The surrounding guard enters a private transitional state that still owns
/// the preemption resource. Normal completion returns the updated session
/// before the executable guard can be observed again.
fn take_reader_state<'a, T>(
    proof_active: &mut bool,
    Tracked(guard_slot): Tracked<&mut Tracked<Option<rcu_cpu_spec::CpuRcuReadGuardToken<T>>>>,
    Tracked(session_slot): Tracked<&mut Tracked<Option<&'a mut RunningTaskContext>>>,
) -> (res: Tracked<(rcu_cpu_spec::CpuRcuReadGuardToken<T>, &'a mut RunningTaskContext)>)
    requires
        *old(proof_active),
        old(guard_slot)@ is Some,
        old(session_slot)@ is Some,
    ensures
        !*final(proof_active),
        final(guard_slot)@ is None,
        final(session_slot)@ is None,
        res@.0 == old(guard_slot)@->Some_0,
        equal(*res@.1, *old(session_slot)@->Some_0),
    opens_invariants none
    no_unwind
{
    proof_decl! {
        let tracked guard = guard_slot.borrow_mut().tracked_take();
        let tracked session = session_slot.borrow_mut().tracked_take();
    }
        * proof_active = false;
    Tracked((guard, session))
}

/// Completes `Guard -> Inactive` and returns both reader fractions.
fn finish_reader_state<'a, P: NonNullPtr>(
    rcu: &RcuInner<P>,
    inner_guard: &mut DisabledPreemptGuard,
    Tracked(guard): Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<<P as NonNullPtr>::Target>>,
    Tracked(session): Tracked<&'a mut RunningTaskContext>,
) -> (res: Tracked<&'a mut RunningTaskContext>)
    requires
        rcu.type_inv(),
        old(session).wf(),
        old(inner_guard).matches_context(*old(session)),
        guard.wf(),
        guard.domain() == rcu.ptr.constant().domain,
        guard.root() == rcu.ptr.id(),
        guard.retire_observation_registry() == rcu.ptr.constant().retire_observation_registry,
        guard.participant_id() == old(session).rcu_participant_id(),
        guard.reader_fragment().fraction() == old(session).rcu_fraction(),
    ensures
        !final(inner_guard).has_resource(),
        (*res@).wf(),
        (*res@).task() == old(session).task(),
        (*res@).scheduler() == old(session).scheduler(),
        (*res@).cpu() == old(session).cpu(),
        (*res@).view() == old(session).view(),
        (*res@).session_id() == old(session).session_id(),
        (*res@).quiescent_generation() == old(session).quiescent_generation(),
        (*res@).available_fractions() == old(session).available_fractions() + 1,
        (*res@).preempt_depth() + 1 == old(session).preempt_depth(),
        (*res@).rcu_participant_id() == old(session).rcu_participant_id(),
        (*res@).rcu_generation() == old(session).rcu_generation(),
        (*res@).rcu_participant_view() == old(session).rcu_participant_view(),
        (*res@).rcu_fraction() == old(session).rcu_fraction() * 2real,
    opens_invariants none
    no_unwind
{
    let ghost context_before_stop = *session;
    let Tracked(cpu_reader) = rcu.ptr.stop_cpu_rcu_reader(Tracked(guard));
    proof {
        inner_guard.lemma_matches_context_depth(session);
        session.tracked_stop_rcu_reader(cpu_reader);
        inner_guard.lemma_matches_context_preserved(context_before_stop, session);
        inner_guard.lemma_matches_context_depth(session);
    }
    inner_guard.release_in_place_to_context(Tracked(session));
    Tracked(session)
}

fn restore_reader_session<'a>(
    Tracked(session_slot): Tracked<&mut Tracked<Option<&'a mut RunningTaskContext>>>,
    Tracked(session): Tracked<&'a mut RunningTaskContext>,
    Ghost(restored): Ghost<RunningTaskContext>,
)
    requires
        old(session_slot)@ is None,
        old(session).wf(),
        *old(session) == restored,
    ensures
        final(session_slot)@ is Some,
        (*final(session_slot)@->Some_0).wf(),
        *final(session_slot)@->Some_0 == restored,
    opens_invariants none
    no_unwind
{
    proof_decl! {
        *session_slot.borrow_mut() = Some(session);
    }
}

impl<P: NonNullPtr + Send> RcuInner<P> {
    #[inline]
    pub fn read_with<'a, A: InAtomicMode>(
        &'a self,
        _guard: &'a A,
        Tracked(session): Tracked<&mut RunningTaskContext>,
    ) -> Option<<P as NonNullPtrRef<'a>>::Ref> where P: NonNullPtrRef<'a>
        requires
            self.type_inv(),
            old(session).wf(),
        ensures
            final(session).wf(),
            final(session).scheduler() == old(session).scheduler(),
            final(session).cpu() == old(session).cpu(),
            final(session).quiescent_generation() == old(session).quiescent_generation(),
            final(session).available_fractions() == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth(),
    {
        proof_decl! {
            let tracked tv = session.tracked_borrow_thread_view_mut();
        }
        let obj_ptr = #[verus_spec(with => Tracked(tracked_ref_perm))]
        self.load_read_token();
        if obj_ptr.is_null() {
            return None;
        }
        proof_decl! {
            // `read_with` returns only the reference and has no guard object to
            // store the read token. For this temporary skeleton, leak the
            // verification-only token so the returned ref can borrow it for
            // `'a`. The final RCU proof should attach this token to the
            // atomic-mode/CPU epoch state instead.
            let tracked tracked_ref_perm = tracked_ref_perm.tracked_unwrap();
            let tracked tracked_ref_perm = tracked_static_ref(tracked_ref_perm);
            let tracked tracked_ref_perm: <P as NonNullPtrRef<'a>>::RefPermission =
                P::borrow_perm_as_ref_perm(tracked_ref_perm.tracked_borrow());
        }
        // SAFETY:
        // 1. This pointer is not NULL.
        // 2. The `_guard` guarantees atomic mode for the duration of lifetime
        //    `'a`, the pointer is valid because other writers won't release the
        //    allocation until this task passes the quiescent state.
        NonNull::new(obj_ptr).map(
            |ptr|
                requires
                    P::ptr_perm_match(
                        ptr.view_ptr_mut(),
                        P::ref_perm_view_permission(tracked_ref_perm),
                    ),
                {
                    unsafe { P::raw_as_ref(ptr, Tracked(tracked_ref_perm)) }
                },
        )
    }
}

#[verus_verify]
impl<'a, P: NonNullPtr + Send> RcuReadGuardInner<'a, P> {
    #[inline]
    #[verus_spec(res =>
        ensures
            !self.rcu.is_nullable() ==> res is Some,
    )]
    fn get<'b>(&'b self) -> Option<<P as NonNullPtrRef<'b>>::Ref> where P: NonNullPtrRef<'b> {
        let res = NonNull::new(self.obj_ptr).map(|ptr| unsafe { assume_shared_ref::<P>(ptr) });
        proof {
            use_type_invariant(self);
            if !self.rcu.is_nullable() {
                assert(!self.obj_ptr.is_null());
                assert(res is Some);
            }
        }

        // SAFETY: The guard ensures that `P` will not be dropped. Thus, `P`
        // outlives the lifetime of `&self`. Additionally, during this period,
        // it is impossible to create a mutable reference to `P`.
        NonNull::new(self.obj_ptr).map(
            |ptr|
                requires
                    self.tracked_ref_perm@ is Some,
                    P::ptr_perm_match(ptr.view_ptr_mut(), self.tracked_ref_perm->0.resource()),
                {
                    unsafe {
                        P::raw_as_ref(
                            ptr,
                            Tracked(
                                P::borrow_perm_as_ref_perm(
                                    self.tracked_ref_perm.tracked_borrow().tracked_borrow(),
                                ),
                            ),
                        )
                    }
                },
        )
    }

    fn compare_exchange(self, new_ptr: Option<P>) -> (res: Result<(), Option<P>>)
        requires
            self.rcu.is_nullable() || new_ptr is Some,
            self.type_inv(),
            self.proof_active,
        ensures
            new_ptr is Some && res is Err ==> res->Err_0 is Some,
    {
        let mut this = self;
        proof {
            use_type_invariant(&this);
        }
        let expected = this.obj_ptr;
        let rcu = this.rcu;
        let tracked_state = take_reader_state::<<P as NonNullPtr>::Target>(
            &mut this.proof_active,
            Tracked(&mut this.tracked_guard),
            Tracked(&mut this.tracked_session),
        );
        proof_decl! {
            let tracked (guard, session) = tracked_state.get();
        }
        let ghost context_at_entry = *session;
        proof_decl! {
            let ghost new_ptr_is_some = new_ptr is Some;
        }

        let (new_raw, Tracked(new_perm)) = if let Some(new_ptr) = new_ptr {
            let (ptr, Tracked(perm)) = P::into_raw(new_ptr);
            (ptr.as_ptr(), Tracked(Some(perm)))
        } else {
            (core::ptr::null_mut(), Tracked(None))
        };
        proof {
            if !rcu.is_nullable() {
                assert(new_ptr_is_some);
            }
            assert(rcu.is_nullable() || !new_raw.is_null());
            assert(rcu.ptr.constant().nullable == rcu.is_nullable());
            assert(rcu.ptr.constant().nullable || !new_raw.is_null());
        }

        let cas_res = {
            proof_decl! {
                let tracked tv = DisabledPreemptGuard::tracked_borrow_thread_view_mut_from_context(
                    session,
                    &this._inner_guard,
                );
            }
            rcu.ptr.compare_exchange_acqrel_acquire_rcu(
                expected,
                new_raw,
                Tracked(new_perm),
                Tracked(tv),
            )
        };
        let ghost context_before_enqueue = *session;
        proof {
            this._inner_guard.lemma_matches_context_preserved(context_at_entry, session);
            assert(this._inner_guard.matches_context(context_before_enqueue));
        }
        proof_decl! {
            let tracked (detached, rejected_new_perm) = cas_res.2.get();
        }

        let res = match cas_res.0 {
            Result::Ok(old_raw) => {
                if !old_raw.is_null() {
                    proof_decl! {
                        let tracked detached = detached.tracked_unwrap();
                    }
                    let (callback, cert) = callback_from_detached::<P>(old_raw, Tracked(detached));
                    if let Some(monitor) = RCU_MONITOR.get() {
                        #[verus_spec(with Tracked(session))]
                        monitor.after_grace_period(callback, cert);
                    }
                }
                Ok(())
            },
            Result::Err(_) => {
                if let Some(new_nonnull) = NonNull::new(new_raw) {
                    proof_decl! {
                        let tracked perm = rejected_new_perm.tracked_unwrap();
                    }
                    Err(Some(unsafe { P::from_raw(new_nonnull, Tracked(perm)) }))
                } else {
                    Err(None)
                }
            },
        };
        proof {
            this._inner_guard.lemma_matches_context_preserved(context_before_enqueue, session);
        }
        let Tracked(session) = finish_reader_state(
            rcu,
            &mut this._inner_guard,
            Tracked(guard),
            Tracked(session),
        );
        let ghost restored = *session;
        restore_reader_session(
            Tracked(&mut this.tracked_session),
            Tracked(session),
            Ghost(restored),
        );
        res
    }
}

impl<'a, P: NonNullPtr> Drop for RcuReadGuardInner<'a, P> {
    fn drop(&mut self)
        ensures
            !final(self).is_active(),
            old(self).is_active() ==> {
                &&& final(self).stored_context().wf()
                &&& final(self).stored_context().task() == old(self).stored_context().task()
                &&& final(self).stored_context().scheduler() == old(
                    self,
                ).stored_context().scheduler()
                &&& final(self).stored_context().cpu() == old(self).stored_context().cpu()
                &&& final(self).stored_context().view() == old(self).stored_context().view()
                &&& final(self).stored_context().session_id() == old(
                    self,
                ).stored_context().session_id()
                &&& final(self).stored_context().quiescent_generation() == old(
                    self,
                ).stored_context().quiescent_generation()
                &&& final(self).stored_context().available_fractions() == old(
                    self,
                ).stored_context().available_fractions() + 1
                &&& final(self).stored_context().preempt_depth() + 1 == old(
                    self,
                ).stored_context().preempt_depth()
                &&& final(self).stored_context().rcu_participant_id() == old(
                    self,
                ).stored_context().rcu_participant_id()
                &&& final(self).stored_context().rcu_generation() == old(
                    self,
                ).stored_context().rcu_generation()
                &&& final(self).stored_context().rcu_participant_view() == old(
                    self,
                ).stored_context().rcu_participant_view()
                &&& final(self).stored_context().rcu_fraction() == old(
                    self,
                ).stored_context().rcu_fraction() * 2real
            },
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }
        if self.proof_active {
            let tracked_state = take_reader_state::<<P as NonNullPtr>::Target>(
                &mut self.proof_active,
                Tracked(&mut self.tracked_guard),
                Tracked(&mut self.tracked_session),
            );
            proof_decl! {
                let tracked (guard, session) = tracked_state.get();
            }
            let Tracked(session) = finish_reader_state(
                self.rcu,
                &mut self._inner_guard,
                Tracked(guard),
                Tracked(session),
            );
            let ghost restored = *session;
            restore_reader_session(
                Tracked(&mut self.tracked_session),
                Tracked(session),
                Ghost(restored),
            );
        }
    }
}

#[verifier::external_body]
unsafe fn assume_shared_ref<'a, P: NonNullPtrRef<'a>>(ptr: NonNull<P::Target>) -> P::Ref {
    proof_decl! {
        let tracked perm: P::RefPermission = Tracked::<P::RefPermission>::assume_new().get();
    }
    unsafe { P::raw_as_ref(ptr, Tracked(perm)) }
}

/// Converts an RCU storage-protocol lease into the pointer implementation's
/// reusable shared-reference permission.
///
/// Once guarded loads carry this lease, `RcuReadGuardInner::get` can pass the
/// result directly to `P::raw_as_ref` without manufacturing a permission.
proof fn borrow_lease_as_ref_permission<'a, P: NonNullPtrRef<'a>>(
    tracked lease: &'a RcuReadLease<P::Permission>,
) -> (tracked res: P::RefPermission)
    requires
        lease.resource().inv(),
    ensures
        res.inv(),
        P::ref_perm_view_permission(res) == lease.resource(),
{
    P::borrow_perm_as_ref_perm(lease.borrow())
}

#[verus_verify]
impl<P: NonNullPtr + Send> Rcu<P> {
    /// Creates a new RCU primitive with the given pointer.
    #[inline]
    pub fn new(pointer: P) -> Self {
        Self(
            #[verus_spec(with Ghost(false))]
            RcuInner::new(pointer),
        )
    }

    /// Replaces the current pointer with `new_ptr` using a release swap.
    #[inline]
    #[verus_spec(
        with
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
        ensures
            final(session).wf(),
            final(session).scheduler() == old(session).scheduler(),
            final(session).cpu() == old(session).cpu(),
            final(session).quiescent_generation() == old(session).quiescent_generation(),
            final(session).available_fractions() == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth(),
    )]
    pub fn update(&self, new_ptr: P) {
        proof {
            use_type_invariant(self);
        }
        self.0.update(Some(new_ptr), Tracked(session));
    }

    /// Starts a read-side critical section and acquires the current pointer.
    #[inline]
    #[verus_spec(res =>
        with
            Tracked(session): Tracked<&'a mut RunningTaskContext>,
        requires
            old(session).wf(),
            old(session).available_fractions() > 1,
    )]
    pub fn read<'a>(&'a self) -> RcuReadGuard<'a, P> {
        proof {
            use_type_invariant(self);
        }
        RcuReadGuard(self.0.read(Tracked(session)))
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuOption<P> {
    /// Creates a nullable RCU primitive.
    #[inline]
    pub fn new(pointer: Option<P>) -> Self {
        if let Some(pointer) = pointer {
            Self(
                #[verus_spec(with Ghost(true))]
                RcuInner::new(pointer),
            )
        } else {
            Self(RcuInner::new_none())
        }
    }

    /// Creates an empty nullable RCU primitive.
    #[inline(always)]
    pub const fn new_none() -> Self {
        Self(RcuInner::new_none())
    }

    /// Replaces the current pointer using a release swap.
    #[inline]
    #[verus_spec(
        with
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
        ensures
            final(session).wf(),
            final(session).scheduler() == old(session).scheduler(),
            final(session).cpu() == old(session).cpu(),
            final(session).quiescent_generation() == old(session).quiescent_generation(),
            final(session).available_fractions() == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth(),
    )]
    pub fn update(&self, new_ptr: Option<P>) {
        proof {
            use_type_invariant(self);
        }
        self.0.update(new_ptr, Tracked(session));
    }

    /// Starts a read-side critical section and acquires the current pointer.
    #[inline]
    #[verus_spec(res =>
        with
            Tracked(session): Tracked<&'a mut RunningTaskContext>,
        requires
            old(session).wf(),
            old(session).available_fractions() > 1,
    )]
    pub fn read<'a>(&'a self) -> RcuOptionReadGuard<'a, P> {
        proof {
            use_type_invariant(self);
        }
        RcuOptionReadGuard(self.0.read(Tracked(session)))
    }

    #[inline]
    #[verus_spec(
        with
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
        ensures
            final(session).wf(),
            final(session).scheduler() == old(session).scheduler(),
            final(session).cpu() == old(session).cpu(),
            final(session).quiescent_generation() == old(session).quiescent_generation(),
            final(session).available_fractions() == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth(),
    )]
    pub fn read_with<'a, A: InAtomicMode>(&'a self, guard: &'a A) -> Option<
        <P as NonNullPtrRef<'a>>::Ref,
    > where P: NonNullPtrRef<'a> {
        proof {
            use_type_invariant(self);
        }
        self.0.read_with(guard, Tracked(session))
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuReadGuard<'_, P> {
    #[inline]
    pub fn drop(self) {
    }

    #[inline]
    pub fn get<'a>(&'a self) -> <P as NonNullPtrRef<'a>>::Ref where P: NonNullPtrRef<'a> {
        proof {
            use_type_invariant(self);
        }
        let res = self.0.get();
        res.unwrap()
    }

    /// Tries to replace the pointer using AcqRel/Acquire CAS.
    #[inline]
    pub fn compare_exchange(self, new_ptr: P) -> Result<(), P> {
        proof {
            use_type_invariant(&self);
        }
        self.0.compare_exchange(Some(new_ptr)).map_err(
            |err|
                requires
                    err is Some,
                { err.unwrap() },
        )
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuOptionReadGuard<'_, P> {
    #[inline]
    pub fn drop(self) {
    }

    #[inline]
    pub fn get<'a>(&'a self) -> Option<<P as NonNullPtrRef<'a>>::Ref> where P: NonNullPtrRef<'a> {
        self.0.get()
    }

    #[inline]
    pub fn is_none(&self) -> bool {
        self.0.obj_ptr.is_null()
    }

    /// Tries to replace the pointer using AcqRel/Acquire CAS.
    #[inline]
    pub fn compare_exchange(self, new_ptr: Option<P>) -> Result<(), Option<P>> {
        proof {
            use_type_invariant(&self);
        }
        self.0.compare_exchange(new_ptr)
    }
}

/// A wrapper whose destructor will eventually be delayed until after an RCU
/// grace period.
///
/// The delayed-drop path is deliberately not restored in this first weak-memory
/// cut; `__mod.rs` contains the old callback-monitor reference.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RcuDrop<T: Send + 'static> {
    value: ManuallyDrop<T>,
}

impl<T: Send + 'static> View for RcuDrop<T> {
    type V = T;

    closed spec fn view(&self) -> T {
        self.value@
    }
}

#[verus_verify]
impl<T: Send + 'static> RcuDrop<T> {
    #[inline]
    #[verus_spec(res =>
        ensures
            res@ == value,
    )]
    pub fn new(value: T) -> Self {
        Self { value: ManuallyDrop::new(value) }
    }
}

#[verus_verify]
impl<T: Send + 'static> Deref for RcuDrop<T> {
    type Target = T;

    #[inline]
    #[verus_spec(res =>
        ensures
            *res == self@,
    )]
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

/// Finishes a grace period on the current CPU.
///
#[verus_spec(
    with
        Tracked(session): Tracked<&mut RunningTaskContext>,
    requires
        old(session).wf(),
        old(session).is_quiescent(),
    ensures
        final(session).wf(),
        final(session).is_quiescent(),
        final(session).task() == old(session).task(),
        final(session).scheduler() == old(session).scheduler(),
        final(session).cpu() == old(session).cpu(),
        final(session).session_id() == old(session).session_id(),
        old(session).quiescent_generation() <= final(session).quiescent_generation(),
        final(session).quiescent_generation() <= old(session).quiescent_generation() + 1,
        final(session).available_fractions() == old(session).available_fractions(),
        final(session).preempt_depth() == old(session).preempt_depth(),
)]
pub unsafe fn finish_grace_period() {
    if let Some(monitor) = RCU_MONITOR.get() {
        unsafe {
            #[verus_spec(with Tracked(session))]
            monitor.finish_grace_period();
        }
    }
}

pub fn init() {
    RCU_MONITOR.init(monitor::RcuMonitor::new_data());
}

} // verus!
verus! {

impl<P: NonNullPtr> RcuInner<P> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

impl<P: NonNullPtr> Rcu<P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& !self.0.is_nullable()
    }
}

impl<P: NonNullPtr> RcuOption<P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& self.0.is_nullable()
    }
}

impl<'a, P: NonNullPtr> RcuReadGuard<'a, P> {
    /// Relates this guard to the task session that supplied its weak-memory
    /// view. Consuming operations require the same session.
    pub closed spec fn matches_context(self, session: RunningTaskContext) -> bool {
        self.0.matches_context(session)
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& !self.0.rcu.is_nullable()
        &&& self.0.is_active()
    }
}

impl<'a, P: NonNullPtr> RcuOptionReadGuard<'a, P> {
    /// Relates this guard to the task session that supplied its weak-memory
    /// view. Consuming operations require the same session.
    pub closed spec fn matches_context(self, session: RunningTaskContext) -> bool {
        self.0.matches_context(session)
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& self.0.rcu.is_nullable()
        &&& self.0.is_active()
    }
}

impl<'a, P: NonNullPtr> RcuReadGuardInner<'a, P> {
    pub closed spec fn is_active(self) -> bool {
        self.proof_active
    }

    pub closed spec fn has_stored_context(self) -> bool {
        self.tracked_session@ is Some
    }

    pub closed spec fn stored_context(self) -> RunningTaskContext
        recommends
            self.has_stored_context(),
    {
        *self.tracked_session@->Some_0
    }

    closed spec fn guard_token(self) -> rcu_cpu_spec::CpuRcuReadGuardToken<
        <P as NonNullPtr>::Target,
    >
        recommends
            self.tracked_guard@ is Some,
    {
        self.tracked_guard@->Some_0
    }

    closed spec fn matches_context(self, session: RunningTaskContext) -> bool {
        &&& self.proof_active
        &&& self.tracked_guard@ is Some
        &&& self._inner_guard.matches_context(session)
        &&& self.guard_token().participant_id() == session.rcu_participant_id()
        &&& self.guard_token().cpu() == session.cpu()
        &&& self.guard_token().generation() == session.rcu_generation()
        &&& self.guard_token().reader_context() == (rcu_spec::RcuReaderContext {
            scheduler: session.scheduler(),
            task: session.task(),
            session: session.session_id(),
            cpu: session.cpu(),
            generation: session.rcu_generation(),
        })
    }

    proof fn lemma_matches_context_preserved(
        &self,
        before: RunningTaskContext,
        tracked after: &RunningTaskContext,
    )
        requires
            self.matches_context(before),
            after.wf(),
            after.task() == before.task(),
            after.scheduler() == before.scheduler(),
            after.cpu() == before.cpu(),
            after.session_id() == before.session_id(),
            after.quiescent_generation() == before.quiescent_generation(),
            after.available_fractions() == before.available_fractions(),
            after.preempt_depth() == before.preempt_depth(),
            after.rcu_participant_id() == before.rcu_participant_id(),
            after.rcu_generation() == before.rcu_generation(),
        ensures
            self.matches_context(*after),
    {
        self._inner_guard.lemma_matches_context_preserved(before, after);
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.rcu.type_inv()
        &&& !self.rcu.is_nullable() ==> !self.obj_ptr.is_null()
        &&& self.proof_active == (self.tracked_guard@ is Some)
        &&& self.proof_active ==> self.tracked_session@ is Some
        &&& self.tracked_session@ is Some ==> self.stored_context().wf()
        &&& self.proof_active ==> {
            &&& self._inner_guard.has_resource()
            &&& self.guard_token().wf()
            &&& self.guard_token().domain() == self.rcu.ptr.constant().domain
            &&& self.guard_token().root() == self.rcu.ptr.id()
            &&& self.guard_token().reader_registry() == self.rcu.ptr.constant().reader_registry
            &&& self.guard_token().retire_observation_registry()
                == self.rcu.ptr.constant().retire_observation_registry
            &&& self.matches_context(self.stored_context())
            &&& self.guard_token().reader_fragment().fraction()
                == self.stored_context().rcu_fraction()
            &&& match self.tracked_info@ {
                None => self.obj_ptr.is_null(),
                Some(info) => {
                    &&& !self.obj_ptr.is_null()
                    &&& info.wf()
                    &&& info.domain() == self.guard_token().domain()
                    &&& equal(info.ptr(), self.obj_ptr)
                    &&& !self.guard_token().expired().contains(info.obj())
                    &&& self.guard_token().protects(info.addr(), info.obj())
                },
            }
        }
    }
}

impl<P: NonNullPtr + Send> Inv for Rcu<P> {
    closed spec fn inv(self) -> bool {
        self.type_inv()
    }
}

} // verus!
