// SPDX-License-Identifier: MPL-2.0
//! Read-copy update (RCU).
//!
//! This is the new weak-memory RCU skeleton. The previous SC proof-oriented
//! implementation is kept in `__mod.rs` as reference and is not compiled.
//!
//! # Verification model
//!
//! The executable RCU API is built on Verus' native IRC11 weak-memory model.
//! The atomic root pointer is a trusted executable `AtomicPtr` adapter, while
//! proofs use native `AtomicPointsTo`, `AtomicHistory`, and operation relations.
//! Weak atomic operations borrow the unique native `ViewSeen` from the current
//! task's `RunningTaskContext`; RCU never mints a fresh per-operation view and
//! therefore preserves observations across RCU operations and publication.
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
//! Executable callbacks use
//! `vstd_extra::raw_callback::RawCallbackWithProof<RcuReclaimPermit>`. The raw
//! representation stores a thin data pointer plus a monomorphized runner
//! pointer, while its type requires the monitor's linear reclaim permit at
//! invocation. The RCU monitor wraps it in `monitor::RcuCallback`, which can
//! only be constructed from a `RcuCallbackSafety` certificate. This prevents
//! the proof layer from treating an arbitrary type-erased callback as a safe
//! reclamation callback or dropping the completion proof at the erasure
//! boundary.
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
//! Delayed reclamation is connected to the weak-memory proof. The weak atomic
//! invariant retains the current registration together with
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
//! removal invariant would contradict the load timestamp. The guarded load
//! also splits a physical read lease from `P::Permission`; `get()` borrows that
//! lease to derive `P::RefPermission`, with no pointer-permission assumption.
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
//! Before invoking a callback, its reclaim permit excludes every active lease
//! for the retired allocation. Reclamation then recovers the complete
//! `P::Permission` from the root invariant and passes it to the typed callback.
//! Two language-integration boundaries remain explicit: the legacy
//! `read_with()` compatibility API uses `assume_shared_ref`, while new callers
//! can use `read_with_guard()` to retain the physical lease in a verified read
//! guard. Verified callers use the consuming guard `drop()` method because
//! Verus cannot yet attach this invariant-opening transition to Rust's implicit
//! `Drop::drop(&mut self)`. Runtime destruction still restores the executable
//! preemption counter through `DisabledPreemptGuard`.
use alloc::boxed::Box;
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref, ptr::NonNull};

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd_extra::prelude::*;
use vstd_extra::raw_callback::{RawCallbackContextWithProof, RawCallbackWithProof};

use crate::{
    specs::{
        mm::cpu::online_cpus,
        sync::{
            rcu as rcu_spec, rcu_cpu as rcu_cpu_spec,
            weak_memory::{
                LinkedListRetiredChild, RcuRetiredRootObject, RcuRootAtomicInv,
                RcuRootAtomicInvariant, RcuRootAtomicState, RcuWeakAtomicPtr,
                RegisteredLinkedListWeakAtomicLink,
            },
        },
        task::InAtomicMode,
    },
    sync::Once,
    task::{DisabledPreemptGuard, RunningTaskContext, disable_preempt_in_context},
};
use vstd_extra::atomic_irc11::{ThreadViewOrder, ViewSeen};

use non_null::{NonNullPtr, NonNullPtrRef};
use rcu_spec::RcuRootOwnershipPredicate;

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

/// Concrete linked-list atomic whose pointee ownership is a real smart-pointer
/// permission understood by [`NonNullPtrRef`].
type RcuLinkedListAtomicLink<P> = RegisteredLinkedListWeakAtomicLink<
    <P as NonNullPtr>::Permission,
    RcuPointerOwnership<P>,
>;

/// One loaded internal child together with its physical RCU read lease.
///
/// This is the linked-list counterpart of [`RcuReadGuardInner`].  In
/// particular, [`Self::get`] derives `P::RefPermission` from the lease and
/// invokes the same verified `raw_as_ref` boundary as a direct-root read.
struct LinkedListChildReadGuard<'a, P> where P: NonNullPtr<Target = rcu_spec::LinkedListNode> {
    obj_ptr: *mut rcu_spec::LinkedListNode,
    link: &'a RcuLinkedListAtomicLink<P>,
    proof_active: bool,
    tracked_guard: Tracked<Option<rcu_cpu_spec::CpuRcuReadGuardToken<rcu_spec::LinkedListNode>>>,
    tracked_child: Tracked<Option<rcu_spec::RcuProtectedPtr<rcu_spec::LinkedListNode>>>,
    tracked_lease: Tracked<Option<rcu_cpu_spec::RcuRootReadLease<P::Permission>>>,
    tracked_observation: Tracked<Option<rcu_spec::LinkedListLinkObservation>>,
}

impl<'a, P> LinkedListChildReadGuard<'a, P> where P: NonNullPtr<Target = rcu_spec::LinkedListNode> {
    #[verifier::type_invariant]
    closed spec fn type_inv(&self) -> bool {
        &&& self.link.well_formed()
        &&& self.link.no_reclaimed_targets()
        &&& self.proof_active ==> {
            &&& self.tracked_guard@ is Some
            &&& self.tracked_observation@ is Some
            &&& self.tracked_guard@->Some_0.wf()
            &&& self.tracked_guard@->Some_0.scheduler() == self.link.constant().scheduler
            &&& self.tracked_guard@->Some_0.domain() == self.link.constant().domain
            &&& self.tracked_guard@->Some_0.root() == self.link.constant().root
            &&& self.tracked_guard@->Some_0.retire_observation_registry()
                == self.link.constant().retire_observation_registry
            &&& self.tracked_observation@->Some_0.registry()
                == self.link.constant().timestamp_registry
            &&& self.tracked_observation@->Some_0.native_registry()
                == self.link.constant().native_observation_registry
            &&& self.tracked_observation@->Some_0.loc() == self.link.native_loc()
            &&& self.tracked_guard@->Some_0.paper_guard().seen_at(self.link.constant().source_obj)
                == self.tracked_observation@->Some_0.index()
            &&& (self.tracked_child@ is Some) == (self.obj_ptr.addr() != 0)
            &&& (self.tracked_lease@ is Some) == (self.obj_ptr.addr() != 0)
            &&& match (self.tracked_child@, self.tracked_lease@) {
                (None, None) => self.obj_ptr.addr() == 0,
                (Some(child), Some(lease)) => {
                    &&& equal(child.ptr(), self.obj_ptr)
                    &&& self.link.registered_targets().contains_pair(child.obj(), child.ptr())
                    &&& self.link.target_lifecycles().contains_key(child.obj())
                    &&& !self.link.target_phase(child.obj()).is_reclaimed()
                    &&& child.protected_by(self.tracked_guard@->Some_0.paper_guard())
                    &&& lease.key() == child.obj()
                    &&& lease.active_registry() == self.link.constant().active_lease_registry
                    &&& lease.participant_id() == self.tracked_guard@->Some_0.participant_id()
                    &&& lease.reader_fraction()
                        == self.tracked_guard@->Some_0.reader_fragment().fraction()
                    &&& lease.domain() == self.tracked_guard@->Some_0.domain()
                    &&& lease.root() == self.tracked_guard@->Some_0.root()
                    &&& lease.reader_context() == self.tracked_guard@->Some_0.reader_context()
                    &&& lease.start_view() == self.tracked_guard@->Some_0.start_view()
                    &&& lease.protected_addr() == child.ptr().addr()
                    &&& RcuPointerOwnership::<P>::owns(child.ptr(), lease.resource())
                },
                _ => false,
            }
        }
    }

    /// Loads an internal child and retains both its traversal witness and its
    /// physical lease. `previous` may be supplied to repeat a load from the
    /// same source without resetting the dense traversal view. The retained
    /// observation is certified by the link's native-view registry and stays
    /// valid as the atomic history grows.
    fn load(
        link: &'a RcuLinkedListAtomicLink<P>,
        Tracked(guard): Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<rcu_spec::LinkedListNode>>,
        Tracked(from): Tracked<&mut rcu_spec::RcuProtectedPtr<rcu_spec::LinkedListNode>>,
        Tracked(previous): Tracked<Option<&rcu_spec::LinkedListLinkObservation>>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: Self)
        requires
            link.well_formed(),
            link.no_reclaimed_targets(),
            guard.wf(),
            guard.scheduler() == link.constant().scheduler,
            guard.domain() == link.constant().domain,
            guard.root() == link.constant().root,
            guard.retire_observation_registry() == link.constant().retire_observation_registry,
            online_cpus().contains(guard.cpu()),
            guard.seen_removed().removed == Set::<nat>::empty(),
            match previous {
                None => guard.paper_guard().seen_at(link.constant().source_obj) == 0,
                Some(observation) => {
                    &&& observation.registry() == link.constant().timestamp_registry
                    &&& observation.native_registry() == link.constant().native_observation_registry
                    &&& observation.loc() == link.native_loc()
                    &&& old(tv)@.contains(observation.view())
                    &&& guard.paper_guard().seen_at(link.constant().source_obj)
                        == observation.index()
                },
            },
            old(from).protected_by(guard.paper_guard()),
            old(from).ptr() == link.constant().source,
            old(from).obj() == link.constant().source_obj,
        ensures
            res.type_inv(),
            res.proof_active,
            old(tv)@.spec_le(final(tv)@),
            final(from).ptr() == link.constant().source,
            final(from).obj() == link.constant().source_obj,
    {
        let (
            obj_ptr,
            _timestamp,
            _index,
            Tracked(guard),
            Tracked(child),
            Tracked(lease),
            Tracked(observation),
        ) = link.load_acquire_and_lease_cpu(
            Tracked(guard),
            Tracked(from),
            Tracked(previous),
            Tracked(tv),
        );
        proof {
            match (&child, &lease) {
                (Some(loaded_child), None) => {
                    assert(loaded_child.obj() != link.constant().source_obj);
                    assert(link.registered_targets().dom().remove(
                        link.constant().source_obj,
                    ).contains(loaded_child.obj()));
                    assert(!link.target_phase(loaded_child.obj()).is_reclaimed());
                    assert(false);
                },
                _ => {},
            }
        }
        let res = Self {
            obj_ptr,
            link,
            proof_active: true,
            tracked_guard: Tracked(Some(guard)),
            tracked_child: Tracked(child),
            tracked_lease: Tracked(lease),
            tracked_observation: Tracked(Some(observation)),
        };
        proof {
            assert(res.type_inv());
        }
        res
    }

    /// Obtains the smart pointer's real shared-reference representation from
    /// the internal child's physical lease.
    fn get<'b>(&'b self) -> Option<<P as NonNullPtrRef<'b>>::Ref> where P: NonNullPtrRef<'b>
        requires
            self.proof_active,
    {
        proof {
            use_type_invariant(self);
            reveal(LinkedListChildReadGuard::type_inv);
            if self.obj_ptr.addr() != 0 {
                assert(self.tracked_lease@ is Some);
                assert(RcuPointerOwnership::<P>::owns(
                    self.obj_ptr,
                    self.tracked_lease@->Some_0.resource(),
                ));
                assert(P::ptr_perm_match(self.obj_ptr, self.tracked_lease@->Some_0.resource()));
                assert(self.tracked_lease@->Some_0.resource().inv());
            }
        }
        NonNull::new(self.obj_ptr).map(
            |ptr|
                requires
                    self.tracked_lease@ is Some,
                    P::ptr_perm_match(ptr.view_ptr_mut(), self.tracked_lease@->Some_0.resource()),
                {
                    proof_decl! {
                        let tracked lease = self.tracked_lease.tracked_borrow();
                        let tracked ref_perm = P::borrow_perm_as_ref_perm(lease.borrow());
                    }
                    unsafe { P::raw_as_ref(ptr, Tracked(ref_perm)) }
                },
        )
    }

    /// Returns the physical lease, the traversal witness, and the updated CPU
    /// guard so the caller may continue traversing.
    fn finish(self, Tracked(tv): Tracked<&mut ViewSeen>) -> (res: Tracked<
        (
            rcu_cpu_spec::CpuRcuReadGuardToken<rcu_spec::LinkedListNode>,
            Option<rcu_spec::RcuProtectedPtr<rcu_spec::LinkedListNode>>,
            rcu_spec::LinkedListLinkObservation,
        ),
    >)
        requires
            self.type_inv(),
            self.proof_active,
            self.link.no_reclaimed_targets(),
        ensures
            old(tv)@.spec_le(final(tv)@),
            res@.0.wf(),
            res@.0.paper_guard().seen_at(self.link.constant().source_obj) == res@.2.index(),
            res@.2.registry() == self.link.constant().timestamp_registry,
            res@.2.native_registry() == self.link.constant().native_observation_registry,
            res@.2.loc() == self.link.native_loc(),
            (res@.1 is Some) == (self.obj_ptr.addr() != 0),
    {
        let mut this = self;
        proof {
            use_type_invariant(&this);
            reveal(LinkedListChildReadGuard::type_inv);
        }
        this.proof_active = false;
        proof_decl! {
            let tracked guard = this.tracked_guard.borrow_mut().tracked_take();
            let tracked mut child = None;
            vstd::modes::tracked_swap(this.tracked_child.borrow_mut(), &mut child);
            let tracked mut lease = None;
            vstd::modes::tracked_swap(this.tracked_lease.borrow_mut(), &mut lease);
            let tracked observation = this.tracked_observation.borrow_mut().tracked_take();
        }
        let Tracked(guard) = this.link.return_registered_lease_cpu(
            Tracked(lease),
            Tracked(guard),
            Tracked(tv),
        );
        Tracked((guard, child, observation))
    }
}

impl<'a> LinkedListChildReadGuard<'a, Box<rcu_spec::LinkedListNode>> {
    /// Concrete acceptance path: turn the boxed child's leased
    /// `RefPermission` into an actual Rust shared reference and dereference
    /// the node allocation.
    fn deref_box_child<'b>(&'b self) -> Option<&'b rcu_spec::LinkedListNode>
        requires
            self.proof_active,
    {
        self.get().map(|child| child.deref_target())
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
    tracked_lease: Tracked<Option<rcu_cpu_spec::RcuRootReadLease<<P as NonNullPtr>::Permission>>>,
    tracked_session: Tracked<Option<&'a mut RunningTaskContext>>,
}

/// Sized callback payload that retains the physical ownership of one detached
/// RCU object until the monitor executes its callback.
struct RcuDropCallbackContext<P: NonNullPtr + Send> {
    pointer: NonNull<<P as NonNullPtr>::Target>,
    tracked_object: Tracked<rcu_spec::RcuObjectId<<P as NonNullPtr>::Target>>,
    tracked_claim: Tracked<rcu_cpu_spec::RcuReclaimClaim<<P as NonNullPtr>::Target>>,
    ghost_removal: Ghost<rcu_spec::RcuRemovalObservation>,
    ghost_retire_observation_registry: Ghost<Loc>,
    ghost_scheduler: Ghost<Loc>,
    tracked_root_inv: Tracked<
        &'static RcuRootAtomicInvariant<
            <P as NonNullPtr>::Target,
            <P as NonNullPtr>::Permission,
            RcuPointerOwnership<P>,
        >,
    >,
}

/// Type-erased callback payload for an internal linked-list child.
///
/// The callback owns the entire link wrapper after unlink/retire.  This gives
/// it exclusive access to the link's phase token and physical permission pool
/// when the monitor eventually supplies a reclaim permit.
struct LinkedListDropCallbackContext<P> where
    P: NonNullPtr<Target = rcu_spec::LinkedListNode> + Send,
 {
    pointer: NonNull<rcu_spec::LinkedListNode>,
    link: RcuLinkedListAtomicLink<P>,
    ghost_target_obj: Ghost<nat>,
    tracked_object: Tracked<rcu_spec::RcuObjectId<rcu_spec::LinkedListNode>>,
    tracked_claim: Tracked<rcu_cpu_spec::RcuReclaimClaim<rcu_spec::LinkedListNode>>,
    ghost_removal: Ghost<rcu_spec::RcuRemovalObservation>,
    ghost_retire_observation_registry: Ghost<Loc>,
    ghost_scheduler: Ghost<Loc>,
}

// SAFETY: the context owns the detached `P` allocation and the unique link
// wrapper that protects its proof-only permission pool. No borrowed runtime
// state crosses into the monitor queue.
#[verifier::external]
unsafe impl<P> Send for LinkedListDropCallbackContext<P> where
    P: NonNullPtr<Target = rcu_spec::LinkedListNode> + Send,
 {

}

impl<P> LinkedListDropCallbackContext<P> where
    P: NonNullPtr<Target = rcu_spec::LinkedListNode> + Send,
 {
    pub closed spec fn permit_matches(&self, permit: monitor::RcuReclaimPermit) -> bool {
        &&& permit.wf()
        &&& permit.callback().domain == self.tracked_object@.domain()
        &&& permit.callback().obj == self.tracked_object@.obj()
        &&& permit.callback().removal == self.ghost_removal@
        &&& permit.callback().retire_observation_registry == self.ghost_retire_observation_registry@
        &&& permit.callback().scheduler == self.ghost_scheduler@
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.link.well_formed()
        &&& self.link.registered_targets().contains_pair(
            self.ghost_target_obj@,
            self.pointer.view_ptr_mut(),
        )
        &&& self.link.target_lifecycles().contains_key(self.ghost_target_obj@)
        &&& (self.link.target_phase(self.ghost_target_obj@).is_retired() || self.link.target_phase(
            self.ghost_target_obj@,
        ).is_reclaimed())
        &&& self.tracked_object@.wf()
        &&& equal(self.tracked_object@.ptr(), self.pointer.view_ptr_mut())
        &&& self.tracked_object@.domain() == self.link.constant().domain
        &&& self.tracked_object@.obj() == self.ghost_target_obj@
        &&& self.ghost_scheduler@ == self.link.constant().scheduler
        &&& match self.link.target_phase(self.ghost_target_obj@) {
            crate::specs::sync::weak_memory::LinkedListChildPhase::Retired { index: _, removal }
            | crate::specs::sync::weak_memory::LinkedListChildPhase::Reclaimed {
                index: _,
                removal,
            } => self.ghost_removal@ == removal,
            _ => false,
        }
        &&& self.ghost_removal@.root == self.link.constant().root
        &&& self.ghost_retire_observation_registry@
            == self.link.constant().retire_observation_registry
        &&& self.link.target_phase(self.ghost_target_obj@).is_retired()
        &&& self.tracked_claim@.registry() == self.link.constant().reclaim_registry
        &&& self.tracked_claim@.obj() == self.tracked_object@.obj()
        &&& self.tracked_claim@.is_pending()
        &&& equal(self.tracked_claim@.ptr(), self.pointer.view_ptr_mut())
    }
}

impl<P> RawCallbackContextWithProof<monitor::RcuReclaimPermit> for LinkedListDropCallbackContext<
    P,
> where P: NonNullPtr<Target = rcu_spec::LinkedListNode> + Send {
    open spec fn call_requires(&self, permit: monitor::RcuReclaimPermit) -> bool {
        self.permit_matches(permit)
    }

    fn run(self, Tracked(permit): Tracked<monitor::RcuReclaimPermit>) {
        let Tracked(credit) = vstd::invariant::create_open_invariant_credit();
        proof_decl! {
            let tracked permission;
            let tracked completed;
        }
        proof {
            use_type_invariant(&self);
            use_type_invariant(&permit);
            reveal(LinkedListDropCallbackContext::type_inv);
            permit.lemma_authorizes_callback();
            let ghost callback = permit.callback();
            assert(self.permit_matches(permit));
            assert(permit.authorizes(callback));
            assert(self.link.target_phase(self.ghost_target_obj@).is_retired());
            completed = permit.tracked_into_reclaimed_witness(callback);
            assert(completed.wf());
            assert(completed.scheduler() == self.link.constant().scheduler);
            assert(completed.record() == callback.retired_record());
            assert(completed.record().domain == self.link.constant().domain);
            assert(completed.record().obj == self.ghost_target_obj@);
            assert(completed.record().retire_observation_registry
                == self.link.constant().retire_observation_registry);
            assert(completed.record().removal == self.link.target_phase(
                self.ghost_target_obj@,
            )->Retired_removal);
        }
        let LinkedListDropCallbackContext {
            pointer,
            mut link,
            ghost_target_obj,
            tracked_object: _,
            tracked_claim,
            ghost_removal: _,
            ghost_retire_observation_registry: _,
            ghost_scheduler: _,
        } = self;
        proof {
            permission =
            link.tracked_reclaim_retired_target(
                pointer.as_ptr(),
                ghost_target_obj@,
                tracked_claim.get(),
                completed,
                credit,
            );
            assert(RcuPointerOwnership::<P>::owns(pointer.as_ptr(), permission));
            assert(P::ptr_perm_match(pointer.as_ptr(), permission));
            assert(permission.inv());
        }
        let _pointer = unsafe { P::from_raw(pointer, Tracked(permission)) };
    }
}

// SAFETY: the callback consumes the same owning pointer type `P` that was
// accepted by the RCU cell. The tracked permission has no runtime payload.
#[verifier::external]
unsafe impl<P: NonNullPtr + Send> Send for RcuDropCallbackContext<P> {

}

impl<P: NonNullPtr + Send> RawCallbackContextWithProof<
    monitor::RcuReclaimPermit,
> for RcuDropCallbackContext<P> {
    open spec fn call_requires(&self, permit: monitor::RcuReclaimPermit) -> bool {
        self.permit_matches(permit)
    }

    fn run(self, Tracked(permit): Tracked<monitor::RcuReclaimPermit>) {
        let pointer = self.pointer;
        let Tracked(credit) = vstd::invariant::create_open_invariant_credit();
        proof_decl! {
            let tracked permission;
        }
        proof {
            use_type_invariant(&self);
            use_type_invariant(&permit);
            reveal(RcuDropCallbackContext::type_inv);
            permit.lemma_authorizes_callback();
            let tracked root_inv = self.tracked_root_inv.get();
            let ghost callback = permit.callback();
            assert(self.permit_matches(permit));
            assert(permit.authorizes(callback));
            vstd::invariant::open_atomic_invariant_in_proof!(credit => root_inv => state => {
                assert(RcuRootAtomicInv::<RcuPointerOwnership<P>>::inv(
                    root_inv.constant(),
                    state,
                ));
                crate::specs::sync::weak_memory::lemma_root_atomic_permission_facts::<
                    <P as NonNullPtr>::Target,
                    <P as NonNullPtr>::Permission,
                    RcuPointerOwnership<P>,
                >(root_inv.constant(), &state);
                assert(rcu_spec::RcuOwnedWeakAtomicInv::<
                    rcu_spec::UnitRcuRootOwnership,
                >::inv(root_inv.constant(), (state.points_to, state.root)));
                assert(state.permissions.wf());
                assert(callback.scheduler == state.permissions.scheduler());
                assert(callback.domain == state.permissions.domain());
                assert(callback.retire_observation_registry
                    == state.permissions.retire_observation_registry());
                assert(callback.removal.root == state.permissions.root());
                state.permissions.lemma_active_registry_projection();
                let ghost permissions_before_exclusion = state.permissions;
                let ghost registry_before_exclusion = state.permissions.registry();
                assert forall|lease_id: nat|
                    state.permissions.active_ids().contains(lease_id)
                        && state.permissions.active_record(lease_id).key() == callback.obj
                    implies {
                        let witness = state.permissions.active_record(lease_id).witness();
                        &&& witness.wf()
                        &&& witness.protected().obj() == callback.obj
                        &&& witness.reader().cpu() == witness.paper_guard().reader().cpu
                        &&& permit.reports().contains_key(witness.reader().cpu())
                        &&& callback.scheduler == witness.binding().registry()
                        &&& callback.domain == witness.paper_guard().domain()
                        &&& callback.retire_observation_registry
                            == witness.paper_guard().retire_observation_registry()
                        &&& callback.removal.root == witness.paper_guard().root()
                    } by {
                    assert(state.permissions.active_ids().contains(lease_id));
                    assert(state.permissions.wf());
                    let witness = state.permissions.active_record(lease_id).witness();
                    assert(witness.wf());
                    assert(witness.reader().cpu() == witness.paper_guard().reader().cpu);
                    assert(online_cpus().contains(witness.reader().cpu()));
                    assert(permit.reports().dom() == online_cpus());
                    assert(permit.reports().contains_key(witness.reader().cpu()));
                    assert(state.permissions.active_record(lease_id).key()
                        == witness.protected().obj());
                    assert(witness.protected().obj() == callback.obj);
                    assert(callback.scheduler == witness.binding().registry());
                    assert(callback.domain == witness.paper_guard().domain());
                    assert(callback.retire_observation_registry
                        == witness.paper_guard().retire_observation_registry());
                    assert(callback.removal.root == witness.paper_guard().root());
                };
                {
                    let tracked registry = state.permissions.tracked_registry_mut();
                    assert(*registry == registry_before_exclusion);
                    assert forall|lease_id: nat|
                        (*registry).active_ids().contains(lease_id)
                            && (*registry).active_record(lease_id).key() == callback.obj
                        implies {
                            let witness = (*registry).active_record(lease_id).witness();
                            &&& witness.wf()
                            &&& witness.protected().obj() == callback.obj
                            &&& witness.reader().cpu() == witness.paper_guard().reader().cpu
                            &&& permit.reports().contains_key(witness.reader().cpu())
                            &&& callback.scheduler == witness.binding().registry()
                            &&& callback.domain == witness.paper_guard().domain()
                            &&& callback.retire_observation_registry
                                == witness.paper_guard().retire_observation_registry()
                            &&& callback.removal.root == witness.paper_guard().root()
                        } by {};
                    permit.tracked_excludes_active_leases(callback, registry);
                }
                assert(state.permissions == permissions_before_exclusion);
                assert(state.permissions.wf());
                let tracked completed = permit.tracked_into_reclaimed_witness(callback);
                assert(completed.scheduler() == state.permissions.scheduler());
                assert(completed.record() == callback.retired_record());
                assert(completed.record().domain == state.permissions.domain());
                assert(completed.record().retire_observation_registry
                    == state.permissions.retire_observation_registry());
                assert(completed.record().removal.root == state.permissions.root());
                {
                    let tracked retired_fact = completed.tracked_retired_fact();
                    state.root.lemma_retired_fact_agrees(retired_fact);
                }
                assert(state.root.removals().contains_pair(
                    callback.obj,
                    callback.removal,
                ));
                state.permissions.lemma_all_unretired_domains();
                let ghost before = state.permissions;
                assert(before.reclaim_registry() == root_inv.constant().0.reclaim_registry);
                assert(before.unretired_claims().dom()
                    == match state.root.current_registration() {
                        Some(registration) => Set::empty().insert(registration.0.obj()),
                        None => Set::empty(),
                    });
                assert forall|obj: nat| #[trigger]
                    state.root.removals().contains_key(obj) implies
                        !before.has_unretired_claim(obj) by {};
                state.permissions.lemma_contains_iff_key(self.tracked_claim@.obj());
                permission = state.permissions.tracked_reclaim(
                    self.tracked_claim.get(),
                    completed,
                );
                assert(before.contains(callback.obj));
                assert(before.keys().contains(callback.obj));
                assert(before.reclaim_states()[callback.obj] is Some);
                assert(before.reclaim_states()[callback.obj]->Some_0 == pointer.as_ptr());
                assert(RcuPointerOwnership::<P>::owns(pointer.as_ptr(), permission));
                assert(P::ptr_perm_match(pointer.as_ptr(), permission));
                assert(permission.inv());
                state.permissions.lemma_all_live_reclaim_states();
                state.permissions.lemma_all_unretired_domains();
                assert(state.permissions.allocations() == state.root.infos().dom());
                assert forall|obj: nat| #[trigger]
                    state.permissions.keys().contains(obj) implies {
                        &&& state.permissions.contains(obj)
                        &&& state.permissions.allocations().contains(obj)
                        &&& state.permissions.reclaim_states().dom().contains(obj)
                        &&& state.root.infos().contains_key(obj)
                        &&& state.permissions.reclaim_states()[obj] is Some
                        &&& state.permissions.reclaim_states()[obj]->Some_0
                            == state.root.infos()[obj].ptr()
                        &&& RcuPointerOwnership::<P>::owns(
                            state.permissions.reclaim_states()[obj]->Some_0,
                            state.permissions.ownership(obj),
                        )
                    } by {
                    assert(obj != callback.obj);
                    assert(before.keys().contains(obj));
                    assert(before.contains(obj));
                    assert(state.permissions.ownership(obj) == before.ownership(obj));
                    assert(state.permissions.reclaim_states()[obj]
                        == before.reclaim_states()[obj]);
                };
                assert(state.permissions.unretired_claims() == before.unretired_claims());
                assert(state.permissions.unretired_claims().dom()
                    == match state.root.current_registration() {
                        Some(registration) => Set::empty().insert(registration.0.obj()),
                        None => Set::empty(),
                    });
                assert forall|obj: nat| #[trigger]
                    state.root.removals().contains_key(obj) implies
                        !state.permissions.has_unretired_claim(obj) by {
                    assert(!before.has_unretired_claim(obj));
                    assert(before.has_unretired_claim(obj)
                        == before.unretired_claims().dom().contains(obj));
                    assert(state.permissions.has_unretired_claim(obj)
                        == state.permissions.unretired_claims().dom().contains(obj));
                    assert(state.permissions.has_unretired_claim(obj)
                        == before.has_unretired_claim(obj));
                };
                assert forall|obj: nat| #[trigger]
                    state.permissions.reclaimed().contains_key(obj) implies {
                        &&& state.root.removals().contains_key(obj)
                        &&& state.permissions.reclaimed()[obj].record().removal
                            == state.root.removals()[obj]
                    } by {
                    if obj == callback.obj {
                        assert(state.permissions.reclaimed()[obj].record()
                            == callback.retired_record());
                        assert(state.root.removals()[obj] == callback.removal);
                    } else {
                        assert(before.reclaimed().contains_key(obj));
                        assert(state.permissions.reclaimed()[obj] == before.reclaimed()[obj]);
                    }
                };
                assert(state.permissions.scheduler() == root_inv.constant().0.scheduler);
                assert(state.permissions.domain() == root_inv.constant().0.domain);
                assert(state.permissions.root() == root_inv.constant().0.domain);
                assert(state.permissions.retire_observation_registry()
                    == root_inv.constant().0.retire_observation_registry);
                assert(state.permissions.reclaim_registry() == before.reclaim_registry());
                assert(state.permissions.reclaim_registry()
                    == root_inv.constant().0.reclaim_registry);
                assert(state.permissions.active_lease_registry()
                    == root_inv.constant().0.active_lease_registry);
                assert(rcu_spec::RcuOwnedWeakAtomicInv::<
                    rcu_spec::UnitRcuRootOwnership,
                >::inv(root_inv.constant(), (state.points_to, state.root)));
                crate::specs::sync::weak_memory::lemma_build_root_atomic_inv::<
                    <P as NonNullPtr>::Target,
                    <P as NonNullPtr>::Permission,
                    RcuPointerOwnership<P>,
                >(
                    root_inv.constant(),
                    &state,
                );
            });
        }
        let _pointer = unsafe { P::from_raw(pointer, Tracked(permission)) };
    }
}

impl<P: NonNullPtr + Send> RcuDropCallbackContext<P> {
    pub closed spec fn permit_matches(&self, permit: monitor::RcuReclaimPermit) -> bool {
        &&& permit.wf()
        &&& permit.callback().domain == self.tracked_object@.domain()
        &&& permit.callback().obj == self.tracked_object@.obj()
        &&& permit.callback().removal == self.ghost_removal@
        &&& permit.callback().retire_observation_registry == self.ghost_retire_observation_registry@
        &&& permit.callback().scheduler == self.ghost_scheduler@
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.tracked_object@.wf()
        &&& equal(self.tracked_object@.ptr(), self.pointer.view_ptr_mut())
        &&& self.tracked_claim@.obj() == self.tracked_object@.obj()
        &&& self.tracked_claim@.is_pending()
        &&& equal(self.tracked_claim@.ptr(), self.pointer.view_ptr_mut())
        &&& self.tracked_object@.domain() == self.tracked_root_inv@.constant().0.domain
        &&& self.tracked_claim@.registry() == self.tracked_root_inv@.constant().0.reclaim_registry
        &&& self.ghost_scheduler@ == self.tracked_root_inv@.constant().0.scheduler
        &&& self.ghost_removal@.root == self.tracked_root_inv@.constant().0.domain
        &&& self.ghost_retire_observation_registry@
            == self.tracked_root_inv@.constant().0.retire_observation_registry
    }
}

/// Erases a detached owned object into an executable callback payload.
///
/// This function does not certify or enqueue the callback. Those operations
/// still require `RcuRetired` and a monitor grace-period certificate.
fn callback_from_detached<P: NonNullPtr + Send>(
    pointer: *mut <P as NonNullPtr>::Target,
    Tracked(owned): Tracked<RcuRetiredRootObject<<P as NonNullPtr>::Target>>,
    Tracked(root_inv): Tracked<
        &'static RcuRootAtomicInvariant<
            <P as NonNullPtr>::Target,
            <P as NonNullPtr>::Permission,
            RcuPointerOwnership<P>,
        >,
    >,
) -> (res: (RawCallbackWithProof<monitor::RcuReclaimPermit>, Tracked<rcu_spec::RcuCallbackSafety>))
    requires
        !pointer.is_null(),
        equal(owned.ptr(), pointer),
        equal(owned.object().ptr(), pointer),
        owned.object().domain() == root_inv.constant().0.domain,
        owned.claim().registry() == root_inv.constant().0.reclaim_registry,
        owned.retired().removal().root == root_inv.constant().0.domain,
        owned.retired().retire_observation_registry()
            == root_inv.constant().0.retire_observation_registry,
    ensures
        res.1@.removal() == owned.retired().removal(),
        forall|permit: monitor::RcuReclaimPermit|
            permit.wf() && permit.callback().domain == res.1@.domain() && permit.callback().obj
                == res.1@.obj() && permit.callback().removal == res.1@.removal()
                && permit.callback().retire_observation_registry
                == res.1@.retire_observation_registry() && permit.callback().scheduler
                == root_inv.constant().0.scheduler ==> res.0.call_requires(permit),
{
    proof {
        use_type_invariant(&owned);
    }
    proof_decl! {
        let tracked (object, retired, claim) = owned.tracked_into_parts();
        let tracked cert = rcu_spec::certify_callback_from_retired(&object, retired);
    }
    proof {
        assert(object.domain() == root_inv.constant().0.domain);
        assert(claim.registry() == root_inv.constant().0.reclaim_registry);
        assert(cert.removal().root == root_inv.constant().0.domain);
        assert(cert.retire_observation_registry()
            == root_inv.constant().0.retire_observation_registry);
    }
    let pointer = unsafe { NonNull::new_unchecked(pointer) };
    proof {
        assert(object.wf());
        assert(equal(object.ptr(), pointer.view_ptr_mut()));
        assert(claim.obj() == object.obj());
        assert(claim.is_pending());
        assert(equal(claim.ptr(), pointer.view_ptr_mut()));
        assert(object.domain() == root_inv.constant().0.domain);
        assert(claim.registry() == root_inv.constant().0.reclaim_registry);
        assert(root_inv.constant().0.scheduler == root_inv.constant().0.scheduler);
        assert(cert.removal().root == root_inv.constant().0.domain);
        assert(cert.retire_observation_registry()
            == root_inv.constant().0.retire_observation_registry);
    }
    let context = RcuDropCallbackContext::<P> {
        pointer,
        tracked_object: Tracked(object),
        tracked_claim: Tracked(claim),
        ghost_removal: Ghost(cert.removal()),
        ghost_retire_observation_registry: Ghost(cert.retire_observation_registry()),
        ghost_scheduler: Ghost(root_inv.constant().0.scheduler),
        tracked_root_inv: Tracked(root_inv),
    };
    proof {
        use_type_invariant(&context);
    }
    (RawCallbackWithProof::new(context), Tracked(cert))
}

/// Erases a retired internal child into the real monitor callback pipeline.
/// The link moves into the callback context, so the successful callback is the
/// only code that can change its phase to `Reclaimed` and recover `P`'s full
/// physical permission.
fn callback_from_linked_list_child<P>(
    link: RcuLinkedListAtomicLink<P>,
    target: *mut rcu_spec::LinkedListNode,
    Ghost(target_obj): Ghost<nat>,
    Tracked(retired): Tracked<LinkedListRetiredChild>,
) -> (res: (
    RawCallbackWithProof<monitor::RcuReclaimPermit>,
    Tracked<rcu_spec::RcuCallbackSafety>,
)) where P: NonNullPtr<Target = rcu_spec::LinkedListNode> + Send
    requires
        link.well_formed(),
        link.registered_targets().contains_pair(target_obj, target),
        link.target_lifecycles().contains_key(target_obj),
        link.target_phase(target_obj).is_retired(),
        retired.object().wf(),
        retired.object().domain() == link.constant().domain,
        retired.object().obj() == target_obj,
        equal(retired.object().ptr(), target),
        retired.claim().registry() == link.constant().reclaim_registry,
        retired.claim().obj() == target_obj,
        retired.claim().is_pending(),
        equal(retired.claim().ptr(), target),
        retired.retired().removal() == link.target_phase(target_obj)->Retired_removal,
        link.target_phase(target_obj)->Retired_removal.root == link.constant().root,
        retired.retired().retire_observation_registry()
            == link.constant().retire_observation_registry,
    ensures
        res.1@.domain() == link.constant().domain,
        res.1@.obj() == target_obj,
        res.1@.removal() == link.target_phase(target_obj)->Retired_removal,
        res.1@.retire_observation_registry() == link.constant().retire_observation_registry,
        forall|permit: monitor::RcuReclaimPermit|
            permit.wf() && permit.callback().domain == res.1@.domain() && permit.callback().obj
                == res.1@.obj() && permit.callback().removal == res.1@.removal()
                && permit.callback().retire_observation_registry
                == res.1@.retire_observation_registry() && permit.callback().scheduler
                == link.constant().scheduler ==> res.0.call_requires(permit),
{
    proof_decl! {
        let tracked (object, cert, claim) = retired.tracked_certify_callback();
    }
    proof {
        object.lemma_wf_facts();
        assert(link.well_formed());
        assert(target.addr() != 0);
    }
    let pointer = unsafe { NonNull::new_unchecked(target) };
    proof {
        assert(equal(pointer.view_ptr_mut(), target));
        assert(object.wf());
        assert(link.target_phase(target_obj) is Retired);
        assert(equal(object.ptr(), pointer.view_ptr_mut()));
        assert(object.domain() == link.constant().domain);
        assert(object.obj() == target_obj);
        assert(claim.registry() == link.constant().reclaim_registry);
        assert(claim.obj() == object.obj());
        assert(claim.is_pending());
        assert(equal(claim.ptr(), pointer.view_ptr_mut()));
        assert(cert.removal() == link.target_phase(target_obj)->Retired_removal);
        assert(cert.removal().root == link.constant().root);
        assert(cert.retire_observation_registry() == link.constant().retire_observation_registry);
    }
    let ghost scheduler = link.constant().scheduler;
    let context = LinkedListDropCallbackContext::<P> {
        pointer,
        link,
        ghost_target_obj: Ghost(target_obj),
        tracked_object: Tracked(object),
        tracked_claim: Tracked(claim),
        ghost_removal: Ghost(cert.removal()),
        ghost_retire_observation_registry: Ghost(cert.retire_observation_registry()),
        ghost_scheduler: Ghost(scheduler),
    };
    proof {
        use_type_invariant(&context);
    }
    (RawCallbackWithProof::new(context), Tracked(cert))
}

/// Schedules one retired internal child on the existing `call_rcu` monitor
/// path. This is intentionally kept private to the linked-list acceptance
/// case until a production data-structure adapter chooses its public API.
fn after_grace_period_linked_list_child<P>(
    link: RcuLinkedListAtomicLink<P>,
    target: *mut rcu_spec::LinkedListNode,
    Ghost(target_obj): Ghost<nat>,
    Tracked(retired): Tracked<LinkedListRetiredChild>,
    Tracked(session): Tracked<&mut RunningTaskContext>,
) where P: NonNullPtr<Target = rcu_spec::LinkedListNode> + Send
    requires
        old(session).wf(),
        old(session).scheduler() == rcu_spec::rcu_scheduler(),
        link.well_formed(),
        link.constant().scheduler == old(session).scheduler(),
        link.registered_targets().contains_pair(target_obj, target),
        link.target_lifecycles().contains_key(target_obj),
        link.target_phase(target_obj).is_retired(),
        retired.object().wf(),
        retired.object().domain() == link.constant().domain,
        retired.object().obj() == target_obj,
        equal(retired.object().ptr(), target),
        retired.claim().registry() == link.constant().reclaim_registry,
        retired.claim().obj() == target_obj,
        retired.claim().is_pending(),
        equal(retired.claim().ptr(), target),
        retired.retired().removal() == link.target_phase(target_obj)->Retired_removal,
        link.target_phase(target_obj)->Retired_removal.root == link.constant().root,
        retired.retired().removal().observed_by(old(session).irc11_view()),
        retired.retired().retire_observation_registry()
            == link.constant().retire_observation_registry,
    ensures
        final(session).wf(),
        final(session).task() == old(session).task(),
        final(session).scheduler() == old(session).scheduler(),
        final(session).cpu() == old(session).cpu(),
        final(session).session_id() == old(session).session_id(),
        final(session).quiescent_generation() == old(session).quiescent_generation(),
        final(session).available_fractions() == old(session).available_fractions(),
        final(session).preempt_depth() == old(session).preempt_depth(),
        final(session).rcu_participant_id() == old(session).rcu_participant_id(),
        final(session).rcu_generation() == old(session).rcu_generation(),
        final(session).rcu_participant_view() == old(session).rcu_participant_view(),
        final(session).rcu_fraction() == old(session).rcu_fraction(),
{
    let (callback, cert) = callback_from_linked_list_child::<P>(
        link,
        target,
        Ghost(target_obj),
        Tracked(retired),
    );
    if let Some(monitor) = RCU_MONITOR.get() {
        #[verus_spec(with Tracked(session))]
        monitor.after_grace_period(callback, cert);
    }
}

impl<P: NonNullPtr> RcuInner<P> {
    closed spec fn is_nullable(self) -> bool {
        self.ghost_nullable@
    }

    closed spec fn wf(self) -> bool {
        &&& self.ptr.well_formed()
        &&& self.ptr.constant().nullable == self.ghost_nullable@
        &&& self.ptr.constant().scheduler == rcu_spec::rcu_scheduler()
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
            res.ptr.constant().scheduler == rcu_spec::rcu_scheduler(),
    {
        let ptr = RcuAtomicPtr::<P>::new(
            Ghost(true),
            Ghost(rcu_spec::rcu_scheduler()),
            core::ptr::null_mut(),
            Tracked(None),
        );
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
            res.ptr.constant().scheduler == rcu_spec::rcu_scheduler(),
    )]
    fn new(pointer: P) -> Self {
        let (raw, Tracked(perm)) = P::into_raw(pointer);
        let raw_ptr = raw.as_ptr();
        proof {
            assert(!raw_ptr.is_null());
        }
        let ptr = RcuAtomicPtr::<P>::new(
            Ghost(nullable),
            Ghost(rcu_spec::rcu_scheduler()),
            raw_ptr,
            Tracked(Some(perm)),
        );
        Self {
            ptr,
            ghost_nullable: Ghost(nullable),
            _marker: PhantomData::<*const <P as NonNullPtr>::Target>,
        }
    }

    #[inline(always)]
    fn load_ptr_acquire(&self, Tracked(tv): Tracked<&mut ViewSeen>) -> (res: (
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
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: (
        *mut <P as NonNullPtr>::Target,
        Tracked<Option<rcu_spec::RcuBlockInfo<<P as NonNullPtr>::Target>>>,
        Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<<P as NonNullPtr>::Target>>,
        Tracked<Option<rcu_cpu_spec::RcuRootReadLease<<P as NonNullPtr>::Permission>>>,
    ))
        requires
            self.type_inv(),
            cpu_reader.wf(),
            online_cpus().contains(cpu_reader.cpu()),
            reader.cpu == cpu_reader.cpu(),
            reader.generation == cpu_reader.generation(),
            binding.registry() == reader.scheduler,
            reader.scheduler == self.ptr.constant().scheduler,
            binding.cpu() == cpu_reader.cpu(),
            binding.locals_key().len() == 1,
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
            res.2@.scheduler() == binding.registry(),
            res.2@.domain() == self.ptr.constant().domain,
            res.2@.reader_registry() == self.ptr.constant().reader_registry,
            res.2@.retire_observation_registry() == self.ptr.constant().retire_observation_registry,
            res.2@.root() == self.ptr.id(),
            res.2@.reader_context() == reader,
            match (res.1@, res.3@) {
                (None, None) => {
                    &&& res.0.is_null()
                    &&& res.2@.reader_fragment() == cpu_reader
                },
                (Some(info), Some(lease)) => {
                    &&& !res.0.is_null()
                    &&& info.wf()
                    &&& info.domain() == res.2@.domain()
                    &&& equal(info.ptr(), res.0)
                    &&& !res.2@.expired().contains(info.obj())
                    &&& !res.2@.seen_removed().removed.contains(info.obj())
                    &&& res.2@.protects(info.addr(), info.obj())
                    &&& res.2@.reader_fragment().fraction() == cpu_reader.fraction() / 2real
                    &&& lease.key() == info.obj()
                    &&& lease.active_registry() == self.ptr.constant().active_lease_registry
                    &&& lease.participant_id() == res.2@.participant_id()
                    &&& lease.reader_fraction() == res.2@.reader_fragment().fraction()
                    &&& lease.domain() == res.2@.domain()
                    &&& lease.root() == res.2@.root()
                    &&& lease.reader_context() == res.2@.reader_context()
                    &&& lease.start_view() == res.2@.start_view()
                    &&& lease.protected_addr() == info.addr()
                    &&& RcuPointerOwnership::<P>::owns(res.0, lease.resource())
                },
                _ => false,
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
        (res.0, res.3, res.4, res.5)
    }

    #[inline(always)]
    fn swap_ptr_release(
        &self,
        new_ptr: *mut <P as NonNullPtr>::Target,
        Tracked(ownership): Tracked<Option<<P as NonNullPtr>::Permission>>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: (
        *mut <P as NonNullPtr>::Target,
        Tracked<Option<RcuRetiredRootObject<<P as NonNullPtr>::Target>>>,
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
            res.1@ is Some ==> res.1@->Some_0.object().domain() == self.ptr.constant().domain,
            res.1@ is Some ==> equal(res.1@->Some_0.object().ptr(), res.0),
            res.1@ is Some ==> equal(res.1@->Some_0.ptr(), res.0),
            res.1@ is Some ==> res.1@->Some_0.retired().removal().observed_by(final(tv)@),
            res.1@ is Some ==> res.1@->Some_0.claim().obj() == res.1@->Some_0.obj(),
            res.1@ is Some ==> res.1@->Some_0.claim().registry()
                == self.ptr.constant().reclaim_registry,
            res.1@ is Some ==> res.1@->Some_0.retired().removal().root
                == self.ptr.constant().domain,
            res.1@ is Some ==> res.1@->Some_0.retired().retire_observation_registry()
                == self.ptr.constant().retire_observation_registry,
    {
        proof {
            assert(self.ptr.constant().nullable == self.is_nullable());
            assert(self.ptr.constant().nullable || !new_ptr.is_null());
        }
        let res = self.ptr.swap_release_rcu(new_ptr, Tracked(ownership), Tracked(tv));
        proof {
            if res.1@ is Some {
                assert(res.1@->Some_0.object().domain() == self.ptr.constant().domain);
                assert(res.1@->Some_0.retired().removal().root == self.ptr.constant().domain);
            }
        }
        res
    }

    fn update(&self, new_ptr: Option<P>, Tracked(session): Tracked<&mut RunningTaskContext>)
        requires
            self.type_inv(),
            self.is_nullable() || new_ptr is Some,
            old(session).wf(),
            old(session).scheduler() == self.ptr.constant().scheduler,
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
                let tracked tv = session.tracked_borrow_irc11_view_mut();
            }
            self.swap_ptr_release(raw, Tracked(perm), Tracked(tv))
        };
        if !old_raw.is_null() {
            proof_decl! {
                let tracked detached = detached.tracked_unwrap();
                let tracked root_inv = self.ptr.tracked_atomic_inv();
            }
            let (callback, cert) = callback_from_detached::<P>(
                old_raw,
                Tracked(detached),
                Tracked(root_inv),
            );
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
            old(session).scheduler() == self.ptr.constant().scheduler,
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
            session.lemma_cpu_online();
            assert(session.rcu_participant_id() == context_before_disable.rcu_participant_id());
            assert(session.rcu_generation() == context_before_disable.rcu_generation());
            assert(session.rcu_participant_view() == context_before_disable.rcu_participant_view());
            assert(context_before_reader.wf());
            assert(context_before_reader.rcu_participant_view().spec_le(
                context_before_reader.irc11_view(),
            ));
            assert(cpu_reader.participant_view() == context_before_reader.rcu_participant_view());
            assert(session.view() == context_before_reader.view());
            assert(cpu_reader.participant_view().spec_le(session.irc11_view()));
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
            let tracked tv = DisabledPreemptGuard::tracked_borrow_irc11_view_mut_from_context(
                session,
                &inner_guard,
            );
        }
        let (obj_ptr, tracked_info, tracked_guard, tracked_lease) = self.load_ptr_acquire_guarded(
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
            assert(tracked_guard@.reader_context() == (rcu_spec::RcuReaderContext {
                scheduler: session.scheduler(),
                task: session.task(),
                session: session.session_id(),
                cpu: session.cpu(),
                generation: session.rcu_generation(),
            }));
            match (tracked_info@, tracked_lease@) {
                (None, None) => {
                    assert(obj_ptr.is_null());
                    assert(tracked_guard@.reader_fragment() == cpu_reader);
                    assert(tracked_guard@.reader_fragment().fraction() == session.rcu_fraction());
                },
                (Some(info), Some(lease)) => {
                    assert(!obj_ptr.is_null());
                    assert(info.wf());
                    assert(info.domain() == tracked_guard@.domain());
                    assert(equal(info.ptr(), obj_ptr));
                    assert(!tracked_guard@.expired().contains(info.obj()));
                    assert(!tracked_guard@.seen_removed().removed.contains(info.obj()));
                    assert(tracked_guard@.protects(info.addr(), info.obj()));
                    assert(tracked_guard@.reader_fragment().fraction() == session.rcu_fraction()
                        / 2real);
                    assert(lease.key() == info.obj());
                    assert(lease.participant_id() == tracked_guard@.participant_id());
                    assert(lease.reader_fraction() == tracked_guard@.reader_fragment().fraction());
                    assert(lease.domain() == tracked_guard@.domain());
                    assert(lease.root() == tracked_guard@.root());
                    assert(lease.reader_context() == tracked_guard@.reader_context());
                    assert(lease.start_view() == tracked_guard@.start_view());
                    assert(lease.protected_addr() == info.addr());
                    assert(RcuPointerOwnership::<P>::owns(obj_ptr, lease.resource()));
                },
                _ => assert(false),
            }
        }
        let res = RcuReadGuardInner {
            obj_ptr,
            rcu: self,
            proof_active: true,
            _inner_guard: inner_guard,
            tracked_info,
            tracked_guard: Tracked(Some(tracked_guard.get())),
            tracked_lease,
            tracked_session: Tracked(Some(session)),
        };
        proof {
            let ghost stored_context = *res.tracked_session@->Some_0;
            assert(res._inner_guard.matches_context(stored_context));
            assert(res.guard_token().participant_id() == stored_context.rcu_participant_id());
            assert(res.guard_token().cpu() == stored_context.cpu());
            assert(res.guard_token().generation() == stored_context.rcu_generation());
            match res.tracked_info@ {
                None => assert(res.guard_token().reader_fragment().fraction()
                    == stored_context.rcu_fraction()),
                Some(_) => assert(res.guard_token().reader_fragment().fraction() * 2real
                    == stored_context.rcu_fraction()),
            }
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
fn take_reader_state<'a, T, O>(
    proof_active: &mut bool,
    Tracked(guard_slot): Tracked<&mut Tracked<Option<rcu_cpu_spec::CpuRcuReadGuardToken<T>>>>,
    Tracked(lease_slot): Tracked<&mut Tracked<Option<rcu_cpu_spec::RcuRootReadLease<O>>>>,
    Tracked(session_slot): Tracked<&mut Tracked<Option<&'a mut RunningTaskContext>>>,
) -> (res: Tracked<
    (
        rcu_cpu_spec::CpuRcuReadGuardToken<T>,
        Option<rcu_cpu_spec::RcuRootReadLease<O>>,
        &'a mut RunningTaskContext,
    ),
>)
    requires
        *old(proof_active),
        old(guard_slot)@ is Some,
        old(session_slot)@ is Some,
    ensures
        !*final(proof_active),
        final(guard_slot)@ is None,
        final(lease_slot)@ is None,
        final(session_slot)@ is None,
        res@.0 == old(guard_slot)@->Some_0,
        res@.1 == old(lease_slot)@,
        equal(*res@.2, *old(session_slot)@->Some_0),
    opens_invariants none
    no_unwind
{
    proof_decl! {
        let tracked guard = guard_slot.borrow_mut().tracked_take();
        let tracked mut lease = None;
        vstd::modes::tracked_swap(lease_slot.borrow_mut(), &mut lease);
        let tracked session = session_slot.borrow_mut().tracked_take();
    }
        * proof_active = false;
    Tracked((guard, lease, session))
}

/// Completes `Guard -> Inactive` and returns both reader fractions.
fn finish_reader_state<'a, P: NonNullPtr>(
    rcu: &RcuInner<P>,
    inner_guard: &mut DisabledPreemptGuard,
    Tracked(guard): Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<<P as NonNullPtr>::Target>>,
    Tracked(lease): Tracked<Option<rcu_cpu_spec::RcuRootReadLease<<P as NonNullPtr>::Permission>>>,
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
        match lease {
            None => guard.reader_fragment().fraction() == old(session).rcu_fraction(),
            Some(lease) => {
                &&& lease.active_registry() == rcu.ptr.constant().active_lease_registry
                &&& lease.participant_id() == guard.participant_id()
                &&& lease.reader_fraction() == guard.reader_fragment().fraction()
                &&& lease.domain() == guard.domain()
                &&& lease.root() == guard.root()
                &&& lease.reader_context() == guard.reader_context()
                &&& lease.start_view() == guard.start_view()
                &&& guard.protects(lease.protected_addr(), lease.key())
                &&& guard.reader_fragment().fraction() * 2real == old(session).rcu_fraction()
            },
        },
    ensures
        !final(inner_guard).has_resource(),
        (*res@).wf(),
        (*res@).task() == old(session).task(),
        (*res@).scheduler() == old(session).scheduler(),
        (*res@).cpu() == old(session).cpu(),
        old(session).view().spec_le((*res@).view()),
        (*res@).session_id() == old(session).session_id(),
        (*res@).quiescent_generation() == old(session).quiescent_generation(),
        (*res@).available_fractions() == old(session).available_fractions() + 1,
        (*res@).preempt_depth() + 1 == old(session).preempt_depth(),
        (*res@).rcu_participant_id() == old(session).rcu_participant_id(),
        (*res@).rcu_generation() == old(session).rcu_generation(),
        (*res@).rcu_participant_view() == old(session).rcu_participant_view(),
        (*res@).rcu_fraction() == old(session).rcu_fraction() * 2real,
    no_unwind
{
    let ghost context_at_entry = *session;
    proof_decl! {
        let tracked tv = DisabledPreemptGuard::tracked_borrow_irc11_view_mut_from_context(
            session,
            inner_guard,
        );
    }
    let Tracked(guard) = rcu.ptr.return_cpu_rcu_read_lease(
        Tracked(lease),
        Tracked(guard),
        Tracked(tv),
    );
    proof {
        assert(guard.reader_fragment().fraction() == session.rcu_fraction());
        assert(context_at_entry.view().spec_le(session.view()));
    }
    let ghost context_before_stop = *session;
    let Tracked(cpu_reader) = rcu.ptr.stop_cpu_rcu_reader(Tracked(guard));
    proof {
        inner_guard.lemma_matches_context_depth(session);
        session.tracked_stop_rcu_reader(cpu_reader);
        assert(session.view() == context_before_stop.view());
        inner_guard.lemma_matches_context_preserved(context_before_stop, session);
        inner_guard.lemma_matches_context_depth(session);
    }
    let ghost context_before_release = *session;
    inner_guard.release_in_place_to_context(Tracked(session));
    proof {
        assert(context_before_release.view() == context_before_stop.view());
        assert(session.view() == context_before_release.view());
        assert(context_at_entry.view().spec_le(session.view()));
    }
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
            let tracked tv = session.tracked_borrow_irc11_view_mut();
        }
        let (obj_ptr, _tracked_info) = self.load_ptr_acquire(Tracked(tv));
        if obj_ptr.is_null() {
            return None;
        }
        // SAFETY:
        // 1. This pointer is not NULL.
        // 2. The `_guard` guarantees atomic mode for the duration of lifetime
        //    `'a`, the pointer is valid because other writers won't release the
        //    allocation until this task passes the quiescent state.

        NonNull::new(obj_ptr).map(|ptr| unsafe { assume_shared_ref::<P>(ptr) })
    }
}

#[verus_verify]
impl<'a, P: NonNullPtr + Send> RcuReadGuardInner<'a, P> {
    #[inline]
    #[verus_spec(res =>
        requires
            self.proof_active,
        ensures
            !self.rcu.is_nullable() ==> res is Some,
    )]
    fn get<'b>(&'b self) -> Option<<P as NonNullPtrRef<'b>>::Ref> where P: NonNullPtrRef<'b> {
        proof {
            use_type_invariant(self);
            reveal(RcuReadGuardInner::type_inv);
            if !self.obj_ptr.is_null() {
                match self.tracked_info@ {
                    None => assert(false),
                    Some(info) => {
                        assert(self.tracked_lease@ is Some);
                        assert(RcuPointerOwnership::<P>::owns(
                            self.obj_ptr,
                            self.tracked_lease@->Some_0.resource(),
                        ));
                        assert(P::ptr_perm_match(
                            self.obj_ptr,
                            self.tracked_lease@->Some_0.resource(),
                        ));
                        assert(self.tracked_lease@->Some_0.resource().inv());
                    },
                }
            }
        }
        let res = NonNull::new(self.obj_ptr).map(
            |ptr|
                requires
                    self.tracked_lease@ is Some,
                    P::ptr_perm_match(ptr.view_ptr_mut(), self.tracked_lease@->Some_0.resource()),
                {
                    proof_decl! {
                        let tracked lease = self.tracked_lease.tracked_borrow();
                        let tracked ref_perm = P::borrow_perm_as_ref_perm(lease.borrow());
                    }
                    unsafe { P::raw_as_ref(ptr, Tracked(ref_perm)) }
                },
        );
        proof {
            if !self.rcu.is_nullable() {
                assert(!self.obj_ptr.is_null());
                assert(res is Some);
            }
        }
        res
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
        let tracked_state = take_reader_state::<
            <P as NonNullPtr>::Target,
            <P as NonNullPtr>::Permission,
        >(
            &mut this.proof_active,
            Tracked(&mut this.tracked_guard),
            Tracked(&mut this.tracked_lease),
            Tracked(&mut this.tracked_session),
        );
        proof_decl! {
            let tracked (guard, lease, session) = tracked_state.get();
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
                let tracked tv = DisabledPreemptGuard::tracked_borrow_irc11_view_mut_from_context(
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
                        let tracked root_inv = rcu.ptr.tracked_atomic_inv();
                    }
                    let (callback, cert) = callback_from_detached::<P>(
                        old_raw,
                        Tracked(detached),
                        Tracked(root_inv),
                    );
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
            Tracked(lease),
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

impl<'a, P: NonNullPtr> RcuReadGuardInner<'a, P> {
    fn finish(self)
        no_unwind
    {
        let mut this = self;
        proof {
            use_type_invariant(&this);
        }
        if this.proof_active {
            let tracked_state = take_reader_state::<
                <P as NonNullPtr>::Target,
                <P as NonNullPtr>::Permission,
            >(
                &mut this.proof_active,
                Tracked(&mut this.tracked_guard),
                Tracked(&mut this.tracked_lease),
                Tracked(&mut this.tracked_session),
            );
            proof_decl! {
                let tracked (guard, lease, session) = tracked_state.get();
            }
            let Tracked(session) = finish_reader_state(
                this.rcu,
                &mut this._inner_guard,
                Tracked(guard),
                Tracked(lease),
                Tracked(session),
            );
            let ghost restored = *session;
            restore_reader_session(
                Tracked(&mut this.tracked_session),
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
            old(session).scheduler() == rcu_spec::rcu_scheduler(),
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
            old(session).scheduler() == rcu_spec::rcu_scheduler(),
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
            old(session).scheduler() == rcu_spec::rcu_scheduler(),
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
            old(session).scheduler() == rcu_spec::rcu_scheduler(),
            old(session).available_fractions() > 1,
    )]
    pub fn read<'a>(&'a self) -> RcuOptionReadGuard<'a, P> {
        proof {
            use_type_invariant(self);
        }
        RcuOptionReadGuard(self.0.read(Tracked(session)))
    }

    /// Acquires the current pointer while an external atomic-mode guard is live.
    ///
    /// Unlike the legacy [`Self::read_with`] compatibility API, this method
    /// returns an RCU read guard that retains the loaded allocation's physical
    /// read lease. Call [`RcuOptionReadGuard::get`] to borrow the pointer and
    /// consume [`RcuOptionReadGuard::drop`] before the external guard expires.
    /// The returned guard owns a nested preemption-disable scope, so its lease
    /// protocol does not rely on an unverified projection from `InAtomicMode`.
    #[inline]
    #[verus_spec(res =>
        with
            Tracked(session): Tracked<&'a mut RunningTaskContext>,
        requires
            old(session).wf(),
            old(session).scheduler() == rcu_spec::rcu_scheduler(),
            old(session).available_fractions() > 1,
    )]
    pub fn read_with_guard<'a, A: InAtomicMode>(&'a self, _guard: &'a A) -> RcuOptionReadGuard<
        'a,
        P,
    > {
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
        self.0.finish();
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
        self.0.finish();
    }

    #[inline]
    pub fn get<'a>(&'a self) -> Option<<P as NonNullPtrRef<'a>>::Ref> where P: NonNullPtrRef<'a> {
        proof {
            use_type_invariant(self);
        }
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
        old(session).scheduler() == rcu_spec::rcu_scheduler(),
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
// Verus requires trait destructors to open no invariants. The verified API uses
// the consuming `Rcu(Read|OptionRead)Guard::drop` methods above; runtime builds
// retain ordinary Rust destruction, after which the embedded preemption guard
// performs the executable counter decrement.
#[cfg(not(verus_keep_ghost))]
impl<'a, P: NonNullPtr> Drop for RcuReadGuardInner<'a, P> {
    fn drop(&mut self) {}
}

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
        &&& self.proof_active ==> ((self.tracked_info@ is Some) == (self.tracked_lease@ is Some))
        &&& self.tracked_session@ is Some ==> self.stored_context().wf()
        &&& self.proof_active ==> {
            &&& self._inner_guard.has_resource()
            &&& self.stored_context().scheduler() == self.rcu.ptr.constant().scheduler
            &&& self.guard_token().wf()
            &&& self.guard_token().domain() == self.rcu.ptr.constant().domain
            &&& self.guard_token().root() == self.rcu.ptr.id()
            &&& self.guard_token().reader_registry() == self.rcu.ptr.constant().reader_registry
            &&& self.guard_token().retire_observation_registry()
                == self.rcu.ptr.constant().retire_observation_registry
            &&& self.matches_context(self.stored_context())
            &&& match self.tracked_info@ {
                None => {
                    &&& self.obj_ptr.is_null()
                    &&& self.tracked_lease@ is None
                    &&& self.guard_token().reader_fragment().fraction()
                        == self.stored_context().rcu_fraction()
                },
                Some(info) => {
                    &&& self.tracked_lease@ is Some
                    &&& !self.obj_ptr.is_null()
                    &&& info.wf()
                    &&& info.domain() == self.guard_token().domain()
                    &&& equal(info.ptr(), self.obj_ptr)
                    &&& !self.guard_token().expired().contains(info.obj())
                    &&& !self.guard_token().seen_removed().removed.contains(info.obj())
                    &&& self.guard_token().protects(info.addr(), info.obj())
                    &&& self.guard_token().reader_fragment().fraction() * 2real
                        == self.stored_context().rcu_fraction()
                    &&& self.tracked_lease@->Some_0.key() == info.obj()
                    &&& self.tracked_lease@->Some_0.active_registry()
                        == self.rcu.ptr.constant().active_lease_registry
                    &&& self.tracked_lease@->Some_0.participant_id()
                        == self.guard_token().participant_id()
                    &&& self.tracked_lease@->Some_0.reader_fraction()
                        == self.guard_token().reader_fragment().fraction()
                    &&& self.tracked_lease@->Some_0.domain() == self.guard_token().domain()
                    &&& self.tracked_lease@->Some_0.root() == self.guard_token().root()
                    &&& self.tracked_lease@->Some_0.reader_context()
                        == self.guard_token().reader_context()
                    &&& self.tracked_lease@->Some_0.start_view() == self.guard_token().start_view()
                    &&& self.tracked_lease@->Some_0.protected_addr() == info.addr()
                    &&& RcuPointerOwnership::<P>::owns(
                        self.obj_ptr,
                        self.tracked_lease@->Some_0.resource(),
                    )
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
