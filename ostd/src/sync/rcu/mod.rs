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
//! relaxed/acquire loads and CAS operations.
//!
//! The current root-pointer invariant is intentionally small: `Rcu` roots are
//! non-null in every atomic-history message, while `RcuOption` roots may be
//! null. Ownership, reader permissions, traversal snapshots, and reclamation are
//! modeled separately in [`specs::sync::rcu`] and are being connected
//! incrementally.
//!
//! The traversal layer follows the paper's shape:
//!
//! - [`RcuReadGuardToken<T>`] represents a read-side critical section together
//!   with its `SeenRemoved(D, LV)` observation.
//! - [`RcuProtectedPtr<T>`] records that a typed pointer is protected by that
//!   guard and has not been observed removed.
//! - [`RcuBaseRetirePerm<T>`] becomes [`RcuRetirePerm<T>`] only after the caller has
//!   observed enough traversal state to prove the retired object is in the
//!   removed set.
//! - `RcuCallbackSafety` compresses that typed retire proof into an erased
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
//! incomplete grace period. The next step is to implement
//! `set_monitoring`/`finish_grace_period` against this invariant and to prove
//! callback execution only after the relevant grace period has completed.
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
//! Delayed reclamation is still being wired into the weak-memory proof. For now,
//! `RcuDrop<T>` preserves the public wrapper API, while the monitor/callback
//! path carries the new proof summary and safety certificate skeleton.
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
    task::{DisabledPreemptGuard, disable_preempt},
};

use non_null::{NonNullPtr, NonNullPtrRef};

pub mod non_null;
pub mod monitor;

verus! {

broadcast use vstd_extra::external::nonnull::group_nonull_axioms;

/// The weak-memory atomic slot used by RCU.
///
/// `bool` is the constant key: `true` means the public cell may contain null
/// (`RcuOption`), and `false` means the public cell is non-null (`Rcu`).  The
/// ghost state is still empty for this cut, but the predicate is now
/// RCU-specific: non-null `Rcu` cells require every atomic-history message to
/// contain a non-null pointer. Later revisions should extend the ghost state to
/// carry read permissions, retired pools, and traversal snapshots.
type RcuAtomicPtr<P> = WeakAtomicPtr<
    <P as NonNullPtr>::Target,
    bool,
    (),
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
    /// Thread-local weak-memory view for this read-side critical section.
    ///
    /// For now this only records the load/CAS view effects of the RCU pointer
    /// itself. Traversal-safe RCU should later expose this to the paper-style
    /// `SeenRemoved(D, LV)` proof layer in `specs::sync::rcu`.
    view: Tracked<ThreadView>,
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
        let ptr = WeakAtomicPtr::new(Ghost(true), core::ptr::null_mut(), Tracked(()));
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
        let ptr = WeakAtomicPtr::new(Ghost(nullable), raw_ptr, Tracked(()));
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
    )
        requires
            self.type_inv(),
            self.is_nullable() || !new_ptr.is_null(),
    {
        proof {
            assert(self.ptr.constant() == self.is_nullable());
            assert(self.ptr.constant() || !new_ptr.is_null());
        }
        self.ptr.store_release_rcu(new_ptr, Tracked(tv));
    }

    #[verus_spec(
        requires
            self.type_inv(),
            self.is_nullable() || new_ptr is Some,
    )]
    fn update(&self, new_ptr: Option<P>) {
        proof_decl! {
            let ghost new_ptr_is_some = new_ptr is Some;
        }
        let (raw, Tracked(_perm)) = if let Some(new_ptr) = new_ptr {
            let (ptr, Tracked(perm)) = P::into_raw(new_ptr);
            (ptr.as_ptr(), Tracked(Some(perm)))
        } else {
            (core::ptr::null_mut(), Tracked(None))
        };

        // TODO: A freshly minted empty view makes this release store publish no
        // prior observations, so in the model it degrades to relaxed-strength
        // publication. This is sound (the empty view is the weakest token) but
        // lossy; switch to a per-task/per-CPU view once task-attached ghost
        // state is available.
        proof_decl! {
            let tracked mut tv = ThreadView::new();
        }
        proof {
            if !self.is_nullable() {
                assert(new_ptr_is_some);
            }
            assert(self.is_nullable() || !raw.is_null());
        }
        self.store_ptr_release(raw, Tracked(&mut tv));
    }

    #[verus_spec(res =>
        requires
            self.type_inv(),
        ensures
            res.type_inv(),
            res.rcu.is_nullable() == self.is_nullable(),
    )]
    fn read(&self) -> RcuReadGuardInner<'_, P> {
        let inner_guard = disable_preempt();
        // TODO: The guard's view starts empty instead of inheriting the
        // thread's accumulated view; sound but forgets prior observations.
        // Replace with a per-task/per-CPU view once available.
        proof_decl! {
            let tracked mut tv = ThreadView::new();
        }
        let obj_ptr = self.load_ptr_acquire(Tracked(&mut tv));
        RcuReadGuardInner { obj_ptr, rcu: self, _inner_guard: inner_guard, view: Tracked(tv) }
    }

    #[inline]
    #[verus_spec(
        requires
            self.type_inv(),
    )]
    pub fn read_with<'a, A: InAtomicMode>(&'a self, _guard: &'a A) -> Option<
        <P as NonNullPtrRef<'a>>::Ref,
    > where P: NonNullPtrRef<'a> {
        // TODO: Same as `read`: a fresh empty view forgets the thread's prior
        // observations; replace with a per-task/per-CPU view once available.
        proof_decl! {
            let tracked mut tv = ThreadView::new();
        }
        let obj_ptr = self.load_ptr_acquire(Tracked(&mut tv));
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

    #[verus_spec(res =>
        requires
            self.rcu.is_nullable() || new_ptr is Some,
        ensures
            new_ptr is Some && res is Err ==> res->Err_0 is Some,
    )]
    fn compare_exchange(self, new_ptr: Option<P>) -> Result<(), Option<P>> {
        let expected = self.obj_ptr;
        let rcu = self.rcu;

        proof {
            use_type_invariant(&self);
        }

        proof_decl! {
            let tracked mut tv = self.view.get();
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
        }

        proof {
            assert(rcu.ptr.constant() == rcu.is_nullable());
            assert(rcu.ptr.constant() || !new_raw.is_null());
        }
        let res = rcu.ptr.compare_exchange_acqrel_acquire_rcu(expected, new_raw, Tracked(&mut tv));

        match res.0 {
            Result::Ok(_) => Ok(()),
            Result::Err(_) => {
                let Some(new_nonnull) = NonNull::new(new_raw) else {
                    return Err(None);
                };
                proof_decl! {
                    let tracked perm = new_perm.tracked_unwrap();
                }
                Err(Some(unsafe { P::from_raw(new_nonnull, Tracked(perm)) }))
            },
        }
    }

    #[inline]
    fn drop(self) {
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
    pub fn update(&self, new_ptr: P) {
        proof {
            use_type_invariant(self);
        }
        self.0.update(Some(new_ptr));
    }

    /// Starts a read-side critical section and acquires the current pointer.
    #[inline]
    pub fn read(&self) -> RcuReadGuard<'_, P> {
        proof {
            use_type_invariant(self);
        }
        RcuReadGuard(self.0.read())
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
    pub fn update(&self, new_ptr: Option<P>) {
        proof {
            use_type_invariant(self);
        }
        self.0.update(new_ptr);
    }

    /// Starts a read-side critical section and acquires the current pointer.
    #[inline]
    pub fn read(&self) -> RcuOptionReadGuard<'_, P> {
        proof {
            use_type_invariant(self);
        }
        RcuOptionReadGuard(self.0.read())
    }

    #[inline]
    pub fn read_with<'a, A: InAtomicMode>(&'a self, guard: &'a A) -> Option<
        <P as NonNullPtrRef<'a>>::Ref,
    > where P: NonNullPtrRef<'a> {
        proof {
            use_type_invariant(self);
        }
        self.0.read_with(guard)
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuReadGuard<'_, P> {
    #[inline]
    pub fn drop(self) {
        self.0.drop();
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
        self.0.drop();
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
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& !self.0.rcu.is_nullable()
    }
}

impl<'a, P: NonNullPtr> RcuOptionReadGuard<'a, P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& self.0.rcu.is_nullable()
    }
}

impl<'a, P: NonNullPtr> RcuReadGuardInner<'a, P> {
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
