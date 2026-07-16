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
//! identity. `Rcu` roots are non-null in every message, while `RcuOption` roots
//! may contain null messages without allocation IDs. Physical `P::Permission`,
//! reader permissions, traversal snapshots, and reclamation are modeled
//! separately in [`specs::sync::rcu`] and are being connected incrementally.
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
//!   `RcuCallbackSummary { domain, obj, retire_epoch }`, which is what the
//!   monitor stores next to a type-erased executable callback.
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
//! under the monitor lock, produces a `CompletedGracePeriod` certificate, and
//! executes exactly that batch outside the lock.
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
//! remaining boundary is concrete: executable preemption guards do not yet own
//! the domain's `Inactive/Guard` reader token. Fresh stores and successful CAS
//! operations now produce `RcuRegistration`, but `RcuInner` does not yet retain
//! that resource together with `P::Permission` or route the replaced object's
//! retire permission into the monitor. For now, `RcuDrop<T>` preserves the
//! public wrapper API.
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref, ptr::NonNull};

use vstd::prelude::*;
use vstd_extra::prelude::*;

use crate::{
    specs::{
        sync::{
            rcu as rcu_spec,
            weak_memory::{ThreadView, WeakAtomicPtr},
        },
        task::InAtomicMode,
    },
    task::{DisabledPreemptGuard, RunningTaskContext, disable_preempt_in_context},
};

use non_null::{NonNullPtr, NonNullPtrRef};

pub mod monitor;
pub mod non_null;

verus! {

broadcast use vstd_extra::external::nonnull::group_nonull_axioms;

/// The weak-memory atomic slot used by RCU.
///
/// `bool` is the constant key: `true` means the public cell may contain null
/// (`RcuOption`), and `false` means the public cell is non-null (`Rcu`).  The
/// RCU-specific predicate requires non-null `Rcu` cells to contain only
/// non-null history messages. Its publication registry also assigns every
/// non-null message a domain-local allocation identity, matching the paper's
/// distinction between physical addresses and allocation IDs.
type RcuAtomicPtr<P> = WeakAtomicPtr<
    <P as NonNullPtr>::Target,
    bool,
    rcu_spec::RcuRootGhost,
    rcu_spec::RcuWeakAtomicInv,
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
    _inner_guard: DisabledPreemptGuard,
}

impl<P: NonNullPtr> RcuInner<P> {
    closed spec fn is_nullable(self) -> bool {
        self.ghost_nullable@
    }

    closed spec fn wf(self) -> bool {
        &&& self.ptr.well_formed()
        &&& self.ptr.constant() == self.ghost_nullable@
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
            // TODO: retain this beside the initial `P::Permission`.
            let tracked (root_ghost, _registration) = rcu_spec::RcuRootGhost::tracked_initial(
                core::ptr::null_mut::<<P as NonNullPtr>::Target>(),
            );
        }
        let ptr = WeakAtomicPtr::new(Ghost(true), core::ptr::null_mut(), Tracked(root_ghost));
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
        let (raw, Tracked(_perm)) = P::into_raw(pointer);
        let raw_ptr = raw.as_ptr();
        proof {
            assert(!raw_ptr.is_null());
        }
        proof_decl! {
            // TODO: retain this beside the initial `P::Permission`.
            let tracked (root_ghost, _registration) =
                rcu_spec::RcuRootGhost::tracked_initial(raw_ptr);
        }
        let ptr = WeakAtomicPtr::new(Ghost(nullable), raw_ptr, Tracked(root_ghost));
        Self {
            ptr,
            ghost_nullable: Ghost(nullable),
            _marker: PhantomData::<*const <P as NonNullPtr>::Target>,
        }
    }

    #[inline(always)]
    fn load_ptr_acquire(&self, Tracked(tv): Tracked<&mut ThreadView>) -> (res:
        *mut <P as NonNullPtr>::Target)
        requires
            self.type_inv(),
        ensures
            !self.is_nullable() ==> !res.is_null(),
    {
        proof {
            assert(self.ptr.constant() == self.is_nullable());
        }
        let res = self.ptr.load_acquire_rcu(Tracked(tv));
        proof {
            if !self.is_nullable() {
                assert(!self.ptr.constant());
                assert(!res.0.is_null());
            }
        }
        res.0
    }

    #[inline(always)]
    fn store_ptr_release(
        &self,
        new_ptr: *mut <P as NonNullPtr>::Target,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: Tracked<Option<rcu_spec::RcuRegistration<<P as NonNullPtr>::Target>>>)
        requires
            self.type_inv(),
            self.is_nullable() || !new_ptr.is_null(),
        ensures
            (res@ is Some) == !new_ptr.is_null(),
            res@ is Some ==> res@->Some_0.0.ptr() == new_ptr,
    {
        proof {
            assert(self.ptr.constant() == self.is_nullable());
            assert(self.ptr.constant() || !new_ptr.is_null());
        }
        self.ptr.store_release_rcu(new_ptr, Tracked(tv))
    }

    fn update(&self, new_ptr: Option<P>, Tracked(session): Tracked<&mut RunningTaskContext>)
        requires
            self.type_inv(),
            self.is_nullable() || new_ptr is Some,
            old(session).wf(),
        ensures
            final(session).wf(),
            final(session).task() == old(session).task(),
            final(session).session_id() == old(session).session_id(),
            final(session).available_fractions() == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth(),
    {
        proof_decl! {
            let ghost new_ptr_is_some = new_ptr is Some;
        }
        let (raw, Tracked(_perm)) = if let Some(new_ptr) = new_ptr {
            let (ptr, Tracked(perm)) = P::into_raw(new_ptr);
            (ptr.as_ptr(), Tracked(Some(perm)))
        } else {
            (core::ptr::null_mut(), Tracked(None))
        };

        proof_decl! {
            let tracked tv = session.tracked_borrow_thread_view_mut();
        }
        proof {
            if !self.is_nullable() {
                assert(new_ptr_is_some);
            }
            assert(self.is_nullable() || !raw.is_null());
        }
        // TODO: retain the registration with `perm` until this object is detached.
        let Tracked(_registration) = self.store_ptr_release(raw, Tracked(tv));
    }

    fn read(&self, Tracked(session): Tracked<&mut RunningTaskContext>) -> (res: RcuReadGuardInner<
        '_,
        P,
    >)
        requires
            self.type_inv(),
            old(session).wf(),
            old(session).available_fractions() > 1,
        ensures
            res.type_inv(),
            res.rcu.is_nullable() == self.is_nullable(),
            final(session).wf(),
            final(session).available_fractions() + 1 == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth() + 1,
            res.matches_context(*final(session)),
    {
        let inner_guard = disable_preempt_in_context(Tracked(session));
        proof_decl! {
            let tracked tv = DisabledPreemptGuard::tracked_borrow_thread_view_mut_from_context(
                session,
                &inner_guard,
            );
        }
        let obj_ptr = self.load_ptr_acquire(Tracked(tv));
        RcuReadGuardInner { obj_ptr, rcu: self, _inner_guard: inner_guard }
    }

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
            final(session).available_fractions() == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth(),
    {
        proof_decl! {
            let tracked tv = session.tracked_borrow_thread_view_mut();
        }
        let obj_ptr = self.load_ptr_acquire(Tracked(tv));
        NonNull::new(obj_ptr).map(|ptr| unsafe { assume_shared_ref::<P>(ptr) })
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
        res
    }

    fn compare_exchange(
        self,
        new_ptr: Option<P>,
        Tracked(session): Tracked<&mut RunningTaskContext>,
    ) -> (res: Result<(), Option<P>>)
        requires
            self.rcu.is_nullable() || new_ptr is Some,
            old(session).wf(),
            self.matches_context(*old(session)),
        ensures
            new_ptr is Some && res is Err ==> res->Err_0 is Some,
            final(session).wf(),
            final(session).task() == old(session).task(),
            final(session).session_id() == old(session).session_id(),
            final(session).available_fractions() == old(session).available_fractions() + 1,
            final(session).preempt_depth() + 1 == old(session).preempt_depth(),
    {
        let expected = self.obj_ptr;
        let rcu = self.rcu;

        proof {
            use_type_invariant(&self);
        }

        proof_decl! {
            let ghost new_ptr_is_some = new_ptr is Some;
            let tracked tv = DisabledPreemptGuard::tracked_borrow_thread_view_mut_from_context(
                session,
                &self._inner_guard,
            );
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
        }

        proof {
            assert(rcu.ptr.constant() == rcu.is_nullable());
            assert(rcu.ptr.constant() || !new_raw.is_null());
        }
        let cas_res = rcu.ptr.compare_exchange_acqrel_acquire_rcu(expected, new_raw, Tracked(tv));
        // A successful CAS must route this registration into the ownership map.
        let Tracked(_registration) = cas_res.2;

        let res = match cas_res.0 {
            Result::Ok(_) => Ok(()),
            Result::Err(_) => {
                if let Some(new_nonnull) = NonNull::new(new_raw) {
                    proof_decl! {
                        let tracked perm = new_perm.tracked_unwrap();
                    }
                    Err(Some(unsafe { P::from_raw(new_nonnull, Tracked(perm)) }))
                } else {
                    Err(None)
                }
            },
        };
        proof {
            self._inner_guard.lemma_matches_context_depth(session);
        }
        self._inner_guard.release_to_context(Tracked(session));
        res
    }

    #[inline]
    fn drop(self, Tracked(session): Tracked<&mut RunningTaskContext>)
        requires
            old(session).wf(),
            self.matches_context(*old(session)),
        ensures
            final(session).wf(),
            final(session).task() == old(session).task(),
            final(session).view() == old(session).view(),
            final(session).session_id() == old(session).session_id(),
            final(session).available_fractions() == old(session).available_fractions() + 1,
            final(session).preempt_depth() + 1 == old(session).preempt_depth(),
    {
        proof {
            self._inner_guard.lemma_matches_context_depth(session);
        }
        self._inner_guard.release_to_context(Tracked(session));
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

    /// Replaces the current pointer with `new_ptr` using a release store.
    #[inline]
    #[verus_spec(
        with
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
        ensures
            final(session).wf(),
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
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
            old(session).available_fractions() > 1,
        ensures
            final(session).wf(),
            final(session).available_fractions() + 1 == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth() + 1,
            res.matches_context(*final(session)),
    )]
    pub fn read(&self) -> RcuReadGuard<'_, P> {
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

    /// Replaces the current pointer using a release store.
    #[inline]
    #[verus_spec(
        with
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
        ensures
            final(session).wf(),
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
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
            old(session).available_fractions() > 1,
        ensures
            final(session).wf(),
            final(session).available_fractions() + 1 == old(session).available_fractions(),
            final(session).preempt_depth() == old(session).preempt_depth() + 1,
            res.matches_context(*final(session)),
    )]
    pub fn read(&self) -> RcuOptionReadGuard<'_, P> {
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
    #[verus_spec(
        with
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
            self.matches_context(*old(session)),
        ensures
            final(session).wf(),
            final(session).available_fractions() == old(session).available_fractions() + 1,
            final(session).preempt_depth() + 1 == old(session).preempt_depth(),
    )]
    pub fn drop(self) {
        self.0.drop(Tracked(session));
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
    #[verus_spec(
        with
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
            self.matches_context(*old(session)),
        ensures
            final(session).wf(),
            final(session).available_fractions() == old(session).available_fractions() + 1,
            final(session).preempt_depth() + 1 == old(session).preempt_depth(),
    )]
    pub fn compare_exchange(self, new_ptr: P) -> Result<(), P> {
        self.0.compare_exchange(Some(new_ptr), Tracked(session)).map_err(
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
    #[verus_spec(
        with
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
            self.matches_context(*old(session)),
        ensures
            final(session).wf(),
            final(session).available_fractions() == old(session).available_fractions() + 1,
            final(session).preempt_depth() + 1 == old(session).preempt_depth(),
    )]
    pub fn drop(self) {
        self.0.drop(Tracked(session));
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
    #[verus_spec(
        with
            Tracked(session): Tracked<&mut RunningTaskContext>,
        requires
            old(session).wf(),
            self.matches_context(*old(session)),
        ensures
            final(session).wf(),
            final(session).available_fractions() == old(session).available_fractions() + 1,
            final(session).preempt_depth() + 1 == old(session).preempt_depth(),
    )]
    pub fn compare_exchange(self, new_ptr: Option<P>) -> Result<(), Option<P>> {
        proof {
            use_type_invariant(&self);
        }
        self.0.compare_exchange(new_ptr, Tracked(session))
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
/// No-op until the weak-memory monitor/reclamation path is rebuilt.
pub unsafe fn finish_grace_period() {
}

pub fn init() {
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
    }
}

impl<'a, P: NonNullPtr> RcuReadGuardInner<'a, P> {
    closed spec fn matches_context(self, session: RunningTaskContext) -> bool {
        self._inner_guard.matches_context(session)
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.rcu.type_inv()
        &&& !self.rcu.is_nullable() ==> !self.obj_ptr.is_null()
    }
}

impl<P: NonNullPtr + Send> Inv for Rcu<P> {
    closed spec fn inv(self) -> bool {
        self.type_inv()
    }
}

} // verus!
