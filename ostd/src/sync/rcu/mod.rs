// SPDX-License-Identifier: MPL-2.0
//! Read-copy update (RCU).
//!
//! # Note
//!
//! Currently this RCU model assumes a sequential consistency (SC) memory model.
//! We may explore weak memory models in the future.
use core::{marker::PhantomData, ptr::NonNull};

use monitor::{RcuMonitor, RcuMonitorOwner, RcuMonitorPred};
use non_null::{NonNullPtr, NonNullPtrRef};
use vstd::{atomic_ghost::AtomicPtr, atomic_with_ghost, modes::tracked_static_ref, prelude::*};
use vstd_extra::{
    prelude::*,
    resource::ghost_resource::{count::Count, tokens::CountResource},
};

pub mod non_null;

mod monitor;

use crate::specs::task::InAtomicMode;
use crate::task::{disable_preempt, DisabledPreemptGuard};

use super::Once;

verus! {

broadcast use vstd_extra::external::nonnull::group_nonull_axioms;
// Verification-only budget for splitting read-side ghost tokens.
//
// This is not a runtime reader counter and does not model an overflow condition
// in the RCU implementation. It is a temporary bounded approximation needed by
// `CountResource`; the final RCU proof should discharge the admission assumption
// with an unbounded ghost registry or a CPU/epoch-based sharding model.

const RCU_READER_SLOTS: u64 = 1u64 << 60;

type RcuReadPool<P> = CountResource<<P as NonNullPtr>::Permission, RCU_READER_SLOTS>;

type RcuReadToken<P> = Count<<P as NonNullPtr>::Permission, RCU_READER_SLOTS>;

exec static RCU_MONITOR: Once<RcuMonitor, RcuMonitorOwner, RcuMonitorPred>
    ensures
        RCU_MONITOR.wf(),
        RCU_MONITOR.inv() == RcuMonitorPred,
{
    Once::new(Ghost(RcuMonitorPred))
}

pub fn init() {
    RCU_MONITOR.init(RcuMonitor::new_data());
}

/// A Read-Copy Update (RCU) cell for sharing a pointer between threads.
///
/// The pointer should be a non-null pointer with type `P`, which implements
/// [`NonNullPtr`]. For example, `P` can be `Box<T>` or `Arc<T>`.
///
/// # Overview
///
/// Read-Copy-Update (RCU) is a synchronization mechanism designed for high-
/// performance, low-latency read operations in concurrent systems. It allows
/// multiple readers to access shared data simultaneously without contention,
/// while writers can update the data safely in a way that does not disrupt
/// ongoing reads. RCU is particularly suited for situations where reads are
/// far more frequent than writes.
///
/// The original design and implementation of RCU is described in paper _The
/// Read-Copy-Update Mechanism for Supporting Real-Time Applications on Shared-
/// Memory Multiprocessor Systems with Linux_ published on IBM Systems Journal
/// 47.2 (2008).
///
/// # Examples
///
/// ```
/// use ostd::sync::Rcu;
///
/// let rcu = Rcu::new(Box::new(42));
///
/// let rcu_guard = rcu.read();
///
/// assert_eq!(*rcu_guard, Some(&42));
///
/// rcu_guard.compare_exchange(Box::new(43)).unwrap();
///
/// let rcu_guard = rcu.read();
///
/// assert_eq!(*rcu_guard, Some(&43));
/// ```
pub struct Rcu<P: NonNullPtr>(RcuInner<P>);

/// A Read-Copy Update (RCU) cell for sharing a _nullable_ pointer.
///
/// This is a variant of [`Rcu`] that allows the contained pointer to be null.
/// So that it can implement `Rcu<Option<P>>` where `P` is not a nullable
/// pointer. It is the same as [`Rcu`] in other aspects.
///
/// # Examples
///
/// ```
/// use ostd::sync::RcuOption;
///
/// static RCU: RcuOption<Box<usize>> = RcuOption::new_none();
///
/// assert!(RCU.read().is_none());
///
/// RCU.update(Box::new(42));
///
/// // Read the data protected by RCU
/// {
///     let rcu_guard = RCU.read().try_get().unwrap();
///     assert_eq!(*rcu_guard, 42);
/// }
///
/// // Update the data protected by RCU
/// {
///     let rcu_guard = RCU.read().try_get().unwrap();
///
///     rcu_guard.compare_exchange(Box::new(43)).unwrap();
///
///     let rcu_guard = RCU.read().try_get().unwrap();
///     assert_eq!(*rcu_guard, 43);
/// }
/// ```
pub struct RcuOption<P: NonNullPtr>(RcuInner<P>);

struct_with_invariants! {
/// The inner implementation of both [`Rcu`] and [`RcuOption`].
struct RcuInner<P: NonNullPtr> {
        nullable: Ghost<bool>,
        ptr: AtomicPtr<
            <P as NonNullPtr>::Target,
            _,
            Option<RcuReadPool<P>>,
            _,
        >,
    // We want to implement Send and Sync explicitly.
    // Having a pointer field prevents them from being implemented
    // automatically by the compiler.
    _marker: PhantomData<P>,
}

closed spec fn wf(self) -> bool {
        invariant on ptr with (nullable, _marker) is (
            v: *mut <P as NonNullPtr>::Target,
            g: Option<RcuReadPool<P>>,
        ) {
            match g {
                Some(perm) => {
                    &&& v@.addr != 0
                    &&& P::ptr_perm_match(nonnull_from_ptr_mut_spec(v), perm@)
                    &&& perm@.inv()
                    &&& perm.wf()
                },
                None => nullable@ && v@.addr == 0,
            }
    }
}
}

/// The inner implementation of both [`RcuReadGuard`] and [`RcuOptionReadGuard`].
struct RcuReadGuardInner<'a, P: NonNullPtr> {
    obj_ptr: *mut <P as NonNullPtr>::Target,
    rcu: &'a RcuInner<P>,
    _inner_guard: DisabledPreemptGuard,
    ref_perm: Tracked<Option<RcuReadToken<P>>>,
}

/// A guard that allows access to the pointed data protected by a [`Rcu`].
#[clippy::has_significant_drop]
#[must_use]
pub struct RcuReadGuard<'a, P: NonNullPtr>(RcuReadGuardInner<'a, P>);

/// A guard that allows access to the pointed data protected by a [`RcuOption`].
#[clippy::has_significant_drop]
#[must_use]
pub struct RcuOptionReadGuard<'a, P: NonNullPtr>(RcuReadGuardInner<'a, P>);

// SAFETY: It is apparent that if `P` is `Send`, then `Rcu<P>` is `Send`.
#[verifier::external]
unsafe impl<P: NonNullPtr> Send for RcuInner<P> where P: Send {

}

// SAFETY: To implement `Sync` for `Rcu<P>`, we need to meet two conditions:
//  1. `P` must be `Sync` because `Rcu::get` allows concurrent access.
//  2. `P` must be `Send` because `Rcu::update` may obtain an object
//     of `P` created on another thread.
#[verifier::external]
unsafe impl<P: NonNullPtr> Sync for RcuInner<P> where P: Send + Sync {

}

impl<P: NonNullPtr> RcuInner<P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

impl<P: NonNullPtr> RcuOption<P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& self.0.nullable@
    }
}

impl<P: NonNullPtr> Rcu<P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& !self.0.nullable@
    }
}

impl<'a, P: NonNullPtr> RcuReadGuard<'a, P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& !self.0.rcu.nullable@
        &&& self.0.ref_perm@ is Some
    }
}

impl<'a, P: NonNullPtr> RcuOptionReadGuard<'a, P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& self.0.rcu.nullable@
    }
}

impl<'a, P: NonNullPtr> RcuReadGuardInner<'a, P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        match self.ref_perm@ {
            Some(perm) => {
                &&& self.obj_ptr@.addr != 0
                &&& P::ptr_perm_match(nonnull_from_ptr_mut_spec(self.obj_ptr), perm.resource())
                &&& perm.resource().inv()
                &&& perm.frac() == 1
            },
            None => self.obj_ptr@.addr == 0,
        }
    }
}

impl<P: NonNullPtr + Send> Inv for Rcu<P> {
    closed spec fn inv(self) -> bool {
        self.type_inv()
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuOption<P> {
    /// Creates a new RCU primitive with the given pointer.
    #[inline]
    #[verus_spec]
    pub fn new(ptr: Option<P>) -> Self {
        // Need to open type invariant.
        // if let Some(pointer) = pointer {
        //     Self(RcuInner::new(pointer))
        // } else {
        //     Self(RcuInner::new_none())
        // }
        let inner = match ptr {
            Some(ptr) => { proof_with!(Ghost(true)); RcuInner::new(ptr) },
            None => RcuInner::new_none(),
        };

        proof {
            use_type_invariant(&inner);
        }

        Self(inner)
    }

    /// Creates a new RCU primitive that contains nothing.
    ///
    /// This is a constant equivalence to [`RcuOption::new(None)`].
    #[inline(always)]
    pub const fn new_none() -> Self {
        let inner = RcuInner::new_none();

        proof {
            use_type_invariant(&inner);
        }

        Self(inner)
    }

    /// Replaces the current pointer with a null pointer.
    ///
    /// This function updates the pointer to the new pointer regardless of the
    /// original pointer. If the original pointer is not NULL, it will be
    /// dropped after the grace period.
    ///
    /// Oftentimes this function is not recommended unless you have
    /// synchronized writes with locks. Otherwise, you can use [`Self::read`]
    /// and then [`RcuOptionReadGuard::compare_exchange`] to update the pointer.
    #[inline]
    pub fn update(&self, new_ptr: Option<P>) {
        proof {
            use_type_invariant(self);
        }
        self.0.update(new_ptr);
    }

    /// Retrieves a read guard for the RCU primitive.
    ///
    /// The guard allows read access to the data protected by RCU, as well
    /// as the ability to do compare-and-exchange.
    ///
    /// The contained pointer can be NULL and you can only get a reference
    /// (if checked non-NULL) via [`RcuOptionReadGuard::get`].
    #[inline]
    pub fn read(&self) -> RcuOptionReadGuard<'_, P> {
        let inner = self.0.read();
        proof {
            use_type_invariant(self);
            assert(inner.rcu.nullable@);
        }
        RcuOptionReadGuard(inner)
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> Rcu<P> {
    /// Creates a new RCU primitive with the given pointer `pointer`.
    #[inline(always)]
    #[verus_spec]
    pub fn new(pointer: P) -> Self {
        proof_with!(Ghost(false));
        let inner = RcuInner::new(pointer);
        proof {
            use_type_invariant(&inner);
        }

        Self(inner)
    }

    /// Replaces the current pointer with a null pointer.
    ///
    /// This function updates the pointer to the new pointer regardless of the
    /// original pointer. The original pointer will be dropped after the grace
    /// period.
    ///
    /// Oftentimes this function is not recommended unless you have serialized
    /// writes with locks. Otherwise, you can use [`Self::read`] and then
    /// [`RcuReadGuard::compare_exchange`] to update the pointer.
    #[inline]
    pub fn update(&self, new_ptr: P) {
        self.0.update(Some(new_ptr));
    }

    /// Retrieves a read guard for the RCU primitive.
    ///
    /// The guard allows read access to the data protected by RCU, as well
    /// as the ability to do compare-and-exchange.
    #[inline]
    pub fn read(&self) -> RcuReadGuard<'_, P> {
        let inner = self.0.read();
        proof {
            use_type_invariant(self);
            assert(!inner.rcu.nullable@);
            assert(inner.ref_perm@ is Some);
        }
        RcuReadGuard(inner)
    }
    // #[inline]
    // pub fn read_with<'a, G: AsAtomicModeGuard + ?Sized>(&'a self, guard: &'a G) -> P::Ref<'a> where
    //     P: NonNullPtrRef<'a>,
    // {
    //     self.0.read_with(guard.as_atomic_mode_guard()).unwrap()
    // }

}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuInner<P> {
    #[inline(always)]
    // #[verus_spec]
    const fn new_none() -> (res: Self)
        ensures
            res.nullable@,
    {
        Self {
            nullable: Ghost(true),
            ptr: AtomicPtr::new(
                Ghost((Ghost(true), PhantomData)),
                core::ptr::null_mut(),
                Tracked(None),
            ),
            _marker: PhantomData,
        }
    }

    /// Creates a new RCU primitive with the given pointer `pointer`.
    #[inline(always)]
    #[verus_spec(r =>
        with
            Ghost(nullable): Ghost<bool>,
        ensures
            r.type_inv(),
            r.nullable@ == nullable,
    )]
    fn new(pointer: P) -> Self {
        let (ptr, Tracked(ptr_perm)) = <P as NonNullPtr>::into_raw(pointer);
        let marker = PhantomData;
        proof {
            assert(nonnull_from_ptr_mut_spec(ptr.as_ptr()) == ptr);
            assert(ptr.as_ptr()@.addr != 0);
            assert(P::ptr_perm_match(nonnull_from_ptr_mut_spec(ptr.as_ptr()), ptr_perm));
            assert(ptr_perm.inv());
        }
        proof_decl! {
            let tracked ptr_perm = CountResource::alloc(ptr_perm);
        }
        let ptr = AtomicPtr::new(
            Ghost((Ghost(nullable), marker)),
            ptr.as_ptr(),
            Tracked(Some(ptr_perm)),
        );
        Self { nullable: Ghost(nullable), ptr, _marker: marker }
    }

    #[verus_spec(
        requires
            self.nullable@ || new_ptr is Some,
    )]
    fn update(&self, new_ptr: Option<P>) {
        let (new_raw_ptr, Tracked(new_perm)) = match new_ptr {
            Some(new_ptr) => {
                let (ptr, Tracked(perm)) = <P as NonNullPtr>::into_raw(new_ptr);
                proof {
                    assert(nonnull_from_ptr_mut_spec(ptr.as_ptr()) == ptr);
                    assert(ptr.as_ptr()@.addr != 0);
                    assert(P::ptr_perm_match(nonnull_from_ptr_mut_spec(ptr.as_ptr()), perm));
                    assert(perm.inv());
                }
                (ptr.as_ptr(), Tracked(Some(perm)))
            },
            None => {
                proof {
                    assert(self.nullable@);
                }
                (core::ptr::null_mut(), Tracked(None))
            },
        };

        proof_decl! {
            let tracked mut old_perm: Option<RcuReadPool<P>> = None;
        }
        proof {
            use_type_invariant(self);
        }
        let old_raw_ptr =
            atomic_with_ghost! {
            self.ptr => swap(new_raw_ptr);
            update _prev -> next;
            returning old_raw_ptr;
            ghost g => {
                old_perm = g;
                g = match new_perm {
                    Some(perm) => Some(CountResource::alloc(perm)),
                    None => None,
                };
                assert(next == new_raw_ptr);
                match &g {
                    Some(perm) => {
                        assert(next@.addr != 0);
                        assert(P::ptr_perm_match(nonnull_from_ptr_mut_spec(next), perm@));
                        assert(perm@.inv());
                        assert(perm.wf());
                        assert(perm.not_empty());
                    },
                    None => {
                        assert(self.nullable@);
                        assert(next@.addr == 0);
                    },
                }
            }
        };

        if let Some(p) = NonNull::new(old_raw_ptr) {
            // SAFETY:
            // 1. The pointer was previously returned by `into_raw`.
            // 2. The pointer is removed from the RCU slot so that no one will
            //    use it after the end of the current grace period. The removal
            //    is done atomically, so it will only be dropped once.
            // unsafe { delay_drop::<P>(p) };
        }
    }

    #[verus_spec(obj_ptr =>
        with
            -> ref_perm: Tracked<Option<RcuReadToken<P>>>,
        ensures
            !self.nullable@ ==> ref_perm@ is Some,
            match ref_perm@ {
                Some(perm) => {
                    &&& obj_ptr@.addr != 0
                    &&& P::ptr_perm_match(nonnull_from_ptr_mut_spec(obj_ptr), perm.resource())
                    &&& perm.resource().inv()
                    &&& perm.frac() == 1
                },
                None => obj_ptr@.addr == 0,
            },
    )]
    fn load_read_token(&self) -> *mut <P as NonNullPtr>::Target {
        proof_decl! {
            let tracked mut ref_perm: Option<RcuReadToken<P>> = None;
        }
        proof {
            use_type_invariant(self);
        }
        let obj_ptr =
            atomic_with_ghost! {
            self.ptr => load();
            update prev -> _next;
            returning loaded;
            ghost g => {
                if g is Some {
                    let tracked mut perm = g.tracked_unwrap();
                        assert(loaded == prev);
                        assert(loaded@.addr != 0);
                        assert(P::ptr_perm_match(nonnull_from_ptr_mut_spec(loaded), perm@));
                        assert(perm@.inv());
                    let ghost perm_snapshot = perm@;

                    // Verification-only admission for the bounded read-token pool.
                    // This is not a runtime reader limit; it only reflects that
                    // `CountResource` uses a Rust const-generic `u64` budget rather
                    // than an unbounded mathematical `nat`.
                    assume(perm.not_empty());
                    assume(1 < perm.frac());
                    let tracked token = perm.split_one();
                    assert(perm@ == perm_snapshot);
                    assert(token.resource() == perm_snapshot);
                    assert(P::ptr_perm_match(nonnull_from_ptr_mut_spec(loaded), token.resource()));
                    assert(token.resource().inv());
                    assert(token.frac() == 1);
                    ref_perm = Some(token);
                    assert(P::ptr_perm_match(nonnull_from_ptr_mut_spec(loaded), perm@));
                    assert(perm@.inv());
                    assert(perm.wf());
                    g = Some(perm);
                } else {
                    assert(self.nullable@);
                    assert(loaded@.addr == 0);
                }
            }
        };
        proof {
            match &ref_perm {
                Some(perm) => {
                    assert(P::ptr_perm_match(nonnull_from_ptr_mut_spec(obj_ptr), perm.resource()));
                    assert(perm.resource().inv());
                    assert(perm.frac() == 1);
                },
                None => {
                    assert(self.nullable@);
                    assert(obj_ptr@.addr == 0);
                },
            }
        }
        proof_with! { |= Tracked(ref_perm) }
        obj_ptr
    }

    #[verus_spec(r =>
        ensures
            r.rcu.nullable@ == self.nullable@,
            !self.nullable@ ==> r.ref_perm@ is Some,
    )]
    fn read(&self) -> RcuReadGuardInner<'_, P> {
        let guard = disable_preempt();
        proof_decl! {
            let tracked mut ref_perm: Option<RcuReadToken<P>> = None;
        }
        let obj_ptr = #[verus_spec(with => Tracked(ref_perm))]
        self.load_read_token();
        proof {
            if !self.nullable@ {
                assert(ref_perm is Some);
            }
        }
        RcuReadGuardInner { obj_ptr, rcu: self, _inner_guard: guard, ref_perm: Tracked(ref_perm) }
    }

    #[verus_spec]
    pub fn read_with<'a, A: InAtomicMode>(
        &'a self,
        _guard: &'a A,  // &'a dyn InAtomicMode is not well-supported in Verus.
    ) -> Option<<P as NonNullPtrRef<'a>>::Ref> where P: NonNullPtrRef<'a> {
        proof_decl! {
            let tracked mut ref_perm: Option<RcuReadToken<P>> = None;
        }
        let obj_ptr = #[verus_spec(with => Tracked(ref_perm))]
        self.load_read_token();
        let Some(ptr) = NonNull::new(obj_ptr) else {
            return None;
        };
        proof {
            assert(nonnull_new_spec(obj_ptr) == Some(ptr));
            assert(ptr == nonnull_from_ptr_mut_spec(obj_ptr));
        }
        proof_decl! {
            // `read_with` returns only the reference and has no guard object to
            // store the read token. For this temporary skeleton, leak the
            // verification-only token so the returned ref can borrow it for
            // `'a`. The final RCU proof should attach this token to the
            // atomic-mode/CPU epoch state instead.
            let tracked ref_perm = ref_perm.tracked_unwrap();
            let tracked ref_perm = tracked_static_ref(ref_perm);
            let tracked ref_perm: <P as NonNullPtrRef<'a>>::RefPermission =
                P::borrow_perm_as_ref_perm(ref_perm.borrow());
        }
        proof {
            assert(P::ptr_perm_match(ptr, P::ref_perm_view_permission(ref_perm)));
            assert(ref_perm.inv());
        }
        // SAFETY:
        // 1. This pointer is not NULL.
        // 2. The `_guard` guarantees atomic mode for the duration of lifetime
        //    `'a`, the pointer is valid because other writers won't release the
        //    allocation until this task passes the quiescent state.
        Some(unsafe { P::raw_as_ref(ptr, Tracked(ref_perm)) })
    }
}

#[verus_verify]
impl<'a, P: NonNullPtr + Send> RcuReadGuardInner<'a, P> {
    #[inline]
    #[verus_spec(r =>
        ensures
            self.ref_perm@ is Some ==> r is Some,
    )]
    fn get<'b>(&'b self) -> Option<<P as NonNullPtrRef<'b>>::Ref>
        where P: NonNullPtrRef<'b>
    {
        // SAFETY: The guard ensures that `P` will not be dropped. Thus, `P`
        // outlives the lifetime of `&self`. Additionally, during this period,
        // it is impossible to create a mutable reference to `P`.
        let Some(ptr) = NonNull::new(self.obj_ptr) else {
            proof {
                use_type_invariant(self);
                assert(nonnull_new_spec(self.obj_ptr) is None);
                assert(self.obj_ptr@.addr == 0);
                assert(self.ref_perm@ is None);
            }
            return None;
        };

        proof {
            use_type_invariant(self);
            assert(nonnull_new_spec(self.obj_ptr) == Some(ptr));
            assert(ptr == nonnull_from_ptr_mut_spec(self.obj_ptr));
        }
        proof_decl! {
            let tracked ref_perm: <P as NonNullPtrRef<'b>>::RefPermission =
                match self.ref_perm.borrow() {
                    Some(perm) => P::borrow_perm_as_ref_perm(perm.borrow()),
                    None => proof_from_false(),
                };
        }
        proof {
            assert(P::ptr_perm_match(ptr, P::ref_perm_view_permission(ref_perm)));
            assert(ref_perm.inv());
        }

        Some(unsafe { P::raw_as_ref(ptr, Tracked(ref_perm)) })
    }

    #[verus_spec(r =>
        requires
            self.rcu.nullable@ || new_ptr is Some,
        ensures
            new_ptr is Some && r is Err ==> r->Err_0 is Some,
    )]
    fn compare_exchange(self, new_ptr: Option<P>) -> Result<(), Option<P>> {
        proof_decl! {
            let ghost new_ptr_is_some = new_ptr is Some;
        }
        let (new_raw_ptr, Tracked(new_perm)) = match new_ptr {
            Some(new_ptr) => {
                let (ptr, Tracked(perm)) = <P as NonNullPtr>::into_raw(new_ptr);
                proof {
                    assert(nonnull_from_ptr_mut_spec(ptr.as_ptr()) == ptr);
                    assert(ptr.as_ptr()@.addr != 0);
                    assert(P::ptr_perm_match(nonnull_from_ptr_mut_spec(ptr.as_ptr()), perm));
                    assert(perm.inv());
                    assert(new_ptr_is_some);
                }
                (ptr.as_ptr(), Tracked(Some(perm)))
            },
            None => {
                proof {
                    assert(!new_ptr_is_some);
                    assert(self.rcu.nullable@);
                }
                (core::ptr::null_mut(), Tracked(None))
            },
        };
        proof {
            if new_ptr_is_some {
                assert(new_raw_ptr@.addr != 0);
            }
        }

        proof_decl! {
            let tracked mut old_perm: Option<RcuReadPool<P>> = None;
            let tracked mut err_new_perm: Option<Option<<P as NonNullPtr>::Permission>> = None;
        }
        proof {
            use_type_invariant(self.rcu);
        }
        let res =
            atomic_with_ghost! {
            self.rcu.ptr => compare_exchange(self.obj_ptr, new_raw_ptr);
            update _prev -> next;
            returning res;
            ghost g => {
                if res is Ok {
                    old_perm = g;
                    g = match new_perm {
                        Some(perm) => Some(CountResource::alloc(perm)),
                        None => None,
                    };
                    assert(next == new_raw_ptr);
                    match &g {
                        Some(perm) => {
                            assert(next@.addr != 0);
                            assert(P::ptr_perm_match(nonnull_from_ptr_mut_spec(next), perm@));
                            assert(perm@.inv());
                            assert(perm.wf());
                            assert(perm.not_empty());
                        },
                        None => {
                            assert(self.rcu.nullable@);
                            assert(next@.addr == 0);
                        },
                    }
                } else {
                    err_new_perm = Some(new_perm);
                }
            }
        };
        if res.is_ok() {
            if let Some(p) = NonNull::new(self.obj_ptr) {
                // SAFETY:
                // 1. The pointer was previously returned by `into_raw`.
                // 2. The pointer is removed from the RCU slot so that no one will
                //    use it after the end of the current grace period. The removal
                //    is done atomically, so it will only be dropped once.
                // unsafe { delay_drop::<P>(p) };
            }
            Ok(())
        } else {
            let Some(new_nonnull) = NonNull::new(new_raw_ptr) else {
                proof {
                    assert(nonnull_new_spec(new_raw_ptr) is None);
                    assert(new_raw_ptr@.addr == 0);
                    assert(!new_ptr_is_some);
                    assert(!(new_ptr is Some));
                }
                return Err(None);
            };
            proof {
                assert(nonnull_new_spec(new_raw_ptr) == Some(new_nonnull));
                assert(new_nonnull == nonnull_from_ptr_mut_spec(new_raw_ptr));
            }
            proof_decl! {
                let tracked new_perm = err_new_perm.tracked_unwrap().tracked_unwrap();
            }
            proof {
                assert(P::ptr_perm_match(new_nonnull, new_perm));
                assert(new_perm.inv());
            }
            // SAFETY:
            // 1. It was previously returned by `into_raw`.
            // 2. The `compare_exchange` fails so the pointer will not
            //    be used by other threads via reading the RCU primitive.
            Err(Some(unsafe { <P as NonNullPtr>::from_raw(new_nonnull, Tracked(new_perm)) }))
        }
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuReadGuard<'_, P> {
    /// Gets the reference of the protected data.
    #[inline]
    pub fn get<'a>(&'a self) -> <P as NonNullPtrRef<'a>>::Ref where P: NonNullPtrRef<'a> {
        let res = self.0.get();
        proof {
            use_type_invariant(self);
            assert(self.0.ref_perm@ is Some);
            assert(res is Some);
        }
        res.unwrap()
    }

    /// Tries to replace the already read pointer with a new pointer.
    ///
    /// If another thread has updated the pointer after the read, this
    /// function will fail, and returns the given pointer back. Otherwise,
    /// it will replace the pointer with the new one and drop the old pointer
    /// after the grace period.
    ///
    /// If spinning on [`Rcu::read`] and this function, it is recommended
    /// to relax the CPU or yield the task on failure. Otherwise contention
    /// will occur.
    ///
    /// This API does not help to avoid
    /// [the ABA problem](https://en.wikipedia.org/wiki/ABA_problem).
    #[inline]
    pub fn compare_exchange(self, new_ptr: P) -> Result<(), P> {
        match self.0.compare_exchange(Some(new_ptr)) {
            Ok(()) => Ok(()),
            Err(err) => {
                proof {
                    assert(err is Some);
                }
                Err(err.unwrap())
            },
        }
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuOptionReadGuard<'_, P> {
    #[inline]
    pub fn get<'a>(&'a self) -> Option<<P as NonNullPtrRef<'a>>::Ref> where P: NonNullPtrRef<'a> {
        self.0.get()
    }

    #[inline]
    pub fn is_none(&self) -> bool {
        self.0.obj_ptr.is_null()
    }

    #[inline]
    pub fn compare_exchange(self, new_ptr: Option<P>) -> Result<(), Option<P>> {
        proof {
            use_type_invariant(&self);
        }
        self.0.compare_exchange(new_ptr)
    }
}

} // verus!
/* use core::{
    marker::PhantomData,
    mem::ManuallyDrop,
    ops::Deref,
    ptr::NonNull,
    sync::atomic::{
        AtomicPtr,
        Ordering::{AcqRel, Acquire},
    },
};

use non_null::NonNullPtr;
use spin::once::Once;

use self::monitor::RcuMonitor;
use crate::task::{
    atomic_mode::{AsAtomicModeGuard, InAtomicMode},
    disable_preempt, DisabledPreemptGuard,
};

mod monitor;*/
/*

impl<P: NonNullPtr + Send> RcuInner<P> {


    fn new(pointer: P) -> Self {
        let ptr = <P as NonNullPtr>::into_raw(pointer).as_ptr();
        let ptr = AtomicPtr::new(ptr);
        Self {
            ptr,
            _marker: PhantomData,
        }
    }

    fn update(&self, new_ptr: Option<P>) {
        let new_ptr = if let Some(new_ptr) = new_ptr {
            <P as NonNullPtr>::into_raw(new_ptr).as_ptr()
        } else {
            core::ptr::null_mut()
        };

        let old_raw_ptr = self.ptr.swap(new_ptr, AcqRel);

        if let Some(p) = NonNull::new(old_raw_ptr) {
            // SAFETY:
            // 1. The pointer was previously returned by `into_raw`.
            // 2. The pointer is removed from the RCU slot so that no one will
            //    use it after the end of the current grace period. The removal
            //    is done atomically, so it will only be dropped once.
            unsafe { delay_drop::<P>(p) };
        }
    }

    fn read(&self) -> RcuReadGuardInner<'_, P> {
        let guard = disable_preempt();
        RcuReadGuardInner {
            obj_ptr: self.ptr.load(Acquire),
            rcu: self,
            _inner_guard: guard,
        }
    }

    fn read_with<'a>(&'a self, _guard: &'a dyn InAtomicMode) -> Option<P::Ref<'a>> {
        let obj_ptr = self.ptr.load(Acquire);
        if obj_ptr.is_null() {
            return None;
        }
        // SAFETY:
        // 1. This pointer is not NULL.
        // 2. The `_guard` guarantees atomic mode for the duration of lifetime
        //    `'a`, the pointer is valid because other writers won't release the
        //    allocation until this task passes the quiescent state.
        NonNull::new(obj_ptr).map(|ptr| unsafe { P::raw_as_ref(ptr) })
    }
}

impl<P: NonNullPtr> Drop for RcuInner<P> {
    fn drop(&mut self) {
        let ptr = self.ptr.load(Acquire);
        if let Some(p) = NonNull::new(ptr) {
            // SAFETY: It was previously returned by `into_raw` when creating
            // the RCU primitive.
            let pointer = unsafe { <P as NonNullPtr>::from_raw(p) };
            // It is OK not to delay the drop because the RCU primitive is
            // owned by nobody else.
            drop(pointer);
        }
    }
}



impl<P: NonNullPtr + Send> RcuReadGuardInner<'_, P> {
    fn get(&self) -> Option<P::Ref<'_>> {
        // SAFETY: The guard ensures that `P` will not be dropped. Thus, `P`
        // outlives the lifetime of `&self`. Additionally, during this period,
        // it is impossible to create a mutable reference to `P`.
        NonNull::new(self.obj_ptr).map(|ptr| unsafe { P::raw_as_ref(ptr) })
    }

    fn compare_exchange(self, new_ptr: Option<P>) -> Result<(), Option<P>> {
        let new_ptr = if let Some(new_ptr) = new_ptr {
            <P as NonNullPtr>::into_raw(new_ptr).as_ptr()
        } else {
            core::ptr::null_mut()
        };

        if self
            .rcu
            .ptr
            .compare_exchange(self.obj_ptr, new_ptr, AcqRel, Acquire)
            .is_err()
        {
            let Some(new_ptr) = NonNull::new(new_ptr) else {
                return Err(None);
            };
            // SAFETY:
            // 1. It was previously returned by `into_raw`.
            // 2. The `compare_exchange` fails so the pointer will not
            //    be used by other threads via reading the RCU primitive.
            return Err(Some(unsafe { <P as NonNullPtr>::from_raw(new_ptr) }));
        }

        if let Some(p) = NonNull::new(self.obj_ptr) {
            // SAFETY:
            // 1. The pointer was previously returned by `into_raw`.
            // 2. The pointer is removed from the RCU slot so that no one will
            //    use it after the end of the current grace period. The removal
            //    is done atomically, so it will only be dropped once.
            unsafe { delay_drop::<P>(p) };
        }

        Ok(())
    }
}

impl<P: NonNullPtr + Send> Rcu<P> {
    /// Creates a new RCU primitive with the given pointer.
    pub fn new(pointer: P) -> Self {
        Self(RcuInner::new(pointer))
    }

    /// Replaces the current pointer with a null pointer.
    ///
    /// This function updates the pointer to the new pointer regardless of the
    /// original pointer. The original pointer will be dropped after the grace
    /// period.
    ///
    /// Oftentimes this function is not recommended unless you have serialized
    /// writes with locks. Otherwise, you can use [`Self::read`] and then
    /// [`RcuReadGuard::compare_exchange`] to update the pointer.
    pub fn update(&self, new_ptr: P) {
        self.0.update(Some(new_ptr));
    }

    /// Retrieves a read guard for the RCU primitive.
    ///
    /// The guard allows read access to the data protected by RCU, as well
    /// as the ability to do compare-and-exchange.
    pub fn read(&self) -> RcuReadGuard<'_, P> {
        RcuReadGuard(self.0.read())
    }

    /// Reads the RCU-protected value in an atomic mode.
    ///
    /// The RCU mechanism protects reads ([`Self::read`]) by entering an
    /// atomic mode. If we are already in an atomic mode, this function can
    /// reduce the overhead of disabling preemption again.
    ///
    /// Unlike [`Self::read`], this function does not return a read guard, so
    /// you cannot use [`RcuReadGuard::compare_exchange`] to synchronize the
    /// writers. You may do it via a [`super::SpinLock`].
    pub fn read_with<'a, G: AsAtomicModeGuard + ?Sized>(&'a self, guard: &'a G) -> P::Ref<'a> {
        self.0.read_with(guard.as_atomic_mode_guard()).unwrap()
    }
}

impl<P: NonNullPtr + Send> RcuOption<P> {
    /// Creates a new RCU primitive with the given pointer.
    pub fn new(pointer: Option<P>) -> Self {
        if let Some(pointer) = pointer {
            Self(RcuInner::new(pointer))
        } else {
            Self(RcuInner::new_none())
        }
    }

    /// Creates a new RCU primitive that contains nothing.
    ///
    /// This is a constant equivalence to [`RcuOption::new(None)`].
    pub const fn new_none() -> Self {
        Self(RcuInner::new_none())
    }

    /// Replaces the current pointer with a null pointer.
    ///
    /// This function updates the pointer to the new pointer regardless of the
    /// original pointer. If the original pointer is not NULL, it will be
    /// dropped after the grace period.
    ///
    /// Oftentimes this function is not recommended unless you have
    /// synchronized writes with locks. Otherwise, you can use [`Self::read`]
    /// and then [`RcuOptionReadGuard::compare_exchange`] to update the pointer.
    pub fn update(&self, new_ptr: Option<P>) {
        self.0.update(new_ptr);
    }

    /// Retrieves a read guard for the RCU primitive.
    ///
    /// The guard allows read access to the data protected by RCU, as well
    /// as the ability to do compare-and-exchange.
    ///
    /// The contained pointer can be NULL and you can only get a reference
    /// (if checked non-NULL) via [`RcuOptionReadGuard::get`].
    pub fn read(&self) -> RcuOptionReadGuard<'_, P> {
        RcuOptionReadGuard(self.0.read())
    }

    /// Reads the RCU-protected value in an atomic mode.
    ///
    /// The RCU mechanism protects reads ([`Self::read`]) by entering an
    /// atomic mode. If we are already in an atomic mode, this function can
    /// reduce the overhead of disabling preemption again.
    ///
    /// Unlike [`Self::read`], this function does not return a read guard, so
    /// you cannot use [`RcuOptionReadGuard::compare_exchange`] to synchronize the
    /// writers. You may do it via a [`super::SpinLock`].
    pub fn read_with<'a, G: AsAtomicModeGuard + ?Sized>(
        &'a self,
        guard: &'a G,
    ) -> Option<P::Ref<'a>> {
        self.0.read_with(guard.as_atomic_mode_guard())
    }
}

impl<P: NonNullPtr + Send> RcuReadGuard<'_, P> {
    /// Gets the reference of the protected data.
    pub fn get(&self) -> P::Ref<'_> {
        self.0.get().unwrap()
    }

    /// Tries to replace the already read pointer with a new pointer.
    ///
    /// If another thread has updated the pointer after the read, this
    /// function will fail, and returns the given pointer back. Otherwise,
    /// it will replace the pointer with the new one and drop the old pointer
    /// after the grace period.
    ///
    /// If spinning on [`Rcu::read`] and this function, it is recommended
    /// to relax the CPU or yield the task on failure. Otherwise contention
    /// will occur.
    ///
    /// This API does not help to avoid
    /// [the ABA problem](https://en.wikipedia.org/wiki/ABA_problem).
    pub fn compare_exchange(self, new_ptr: P) -> Result<(), P> {
        self.0
            .compare_exchange(Some(new_ptr))
            .map_err(|err| err.unwrap())
    }
}

impl<P: NonNullPtr + Send> RcuOptionReadGuard<'_, P> {
    /// Gets the reference of the protected data.
    ///
    /// If the RCU primitive protects nothing, this function returns `None`.
    pub fn get(&self) -> Option<P::Ref<'_>> {
        self.0.get()
    }

    /// Returns if the RCU primitive protects nothing when [`Rcu::read`] happens.
    pub fn is_none(&self) -> bool {
        self.0.obj_ptr.is_null()
    }

    /// Tries to replace the already read pointer with a new pointer
    /// (or none).
    ///
    /// If another thread has updated the pointer after the read, this
    /// function will fail, and returns the given pointer back. Otherwise,
    /// it will replace the pointer with the new one and drop the old pointer
    /// after the grace period.
    ///
    /// If spinning on [`RcuOption::read`] and this function, it is recommended
    /// to relax the CPU or yield the task on failure. Otherwise contention
    /// will occur.
    ///
    /// This API does not help to avoid
    /// [the ABA problem](https://en.wikipedia.org/wiki/ABA_problem).
    pub fn compare_exchange(self, new_ptr: Option<P>) -> Result<(), Option<P>> {
        self.0.compare_exchange(new_ptr)
    }
}

/// Delays the dropping of a [`NonNullPtr`] after the RCU grace period.
///
/// This is internally needed for implementing [`Rcu`] and [`RcuOption`]
/// because we cannot alias a [`Box`]. Restoring `P` and use [`RcuDrop`] for it
/// can lead to multiple [`Box`]es simultaneously pointing to the same
/// content.
///
/// # Safety
///
/// The pointer must be previously returned by `into_raw`, will not be used
/// after the end of the current grace period, and will only be dropped once.
///
/// [`Box`]: alloc::boxed::Box
unsafe fn delay_drop<P: NonNullPtr + Send>(pointer: NonNull<<P as NonNullPtr>::Target>) {
    struct ForceSend<P: NonNullPtr + Send>(NonNull<<P as NonNullPtr>::Target>);
    // SAFETY: Sending a raw pointer to another task is safe as long as
    // the pointer access in another task is safe (guaranteed by the trait
    // bound `P: Send`).
    unsafe impl<P: NonNullPtr + Send> Send for ForceSend<P> {}

    let pointer: ForceSend<P> = ForceSend(pointer);

    let rcu_monitor = RCU_MONITOR.get().unwrap();
    rcu_monitor.after_grace_period(move || {
        // This is necessary to make the Rust compiler to move the entire
        // `ForceSend` structure into the closure.
        let pointer = pointer;

        // SAFETY:
        // 1. The pointer was previously returned by `into_raw`.
        // 2. The pointer won't be used anymore since the grace period has
        //    finished and this is the only time the pointer gets dropped.
        let p = unsafe { <P as NonNullPtr>::from_raw(pointer.0) };
        drop(p);
    });
}

/// A wrapper to delay calling destructor of `T` after the RCU grace period.
///
/// Upon dropping this structure, a callback will be registered to the global
/// RCU monitor and the destructor of `T` will be delayed until the callback.
///
/// [`RcuDrop<T>`] is guaranteed to have the same layout as `T`. You can also
/// access the inner value safely via [`RcuDrop<T>`].
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct RcuDrop<T: Send + 'static> {
    value: ManuallyDrop<T>,
}

impl<T: Send + 'static> RcuDrop<T> {
    /// Creates a new [`RcuDrop`] instance that delays the dropping of `value`.
    pub fn new(value: T) -> Self {
        Self {
            value: ManuallyDrop::new(value),
        }
    }
}

impl<T: Send + 'static> Deref for RcuDrop<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T: Send + 'static> Drop for RcuDrop<T> {
    fn drop(&mut self) {
        // SAFETY: The `ManuallyDrop` will not be used after this point.
        let taken = unsafe { ManuallyDrop::take(&mut self.value) };
        let rcu_monitor = RCU_MONITOR.get().unwrap();
        rcu_monitor.after_grace_period(|| {
            drop(taken);
        });
    }
}

/// Finishes the current grace period.
///
/// This function is called when the current grace period on current CPU is
/// finished. If this CPU is the last CPU to finish the current grace period,
/// it takes all the current callbacks and invokes them.
///
/// # Safety
///
/// The caller must ensure that this CPU is not executing in a RCU read-side
/// critical section.
pub unsafe fn finish_grace_period() {
    let rcu_monitor = RCU_MONITOR.get().unwrap();
    // SAFETY: The caller ensures safety.
    unsafe {
        rcu_monitor.finish_grace_period();
    }
}

static RCU_MONITOR: Once<RcuMonitor> = Once::new();

pub fn init() {
    RCU_MONITOR.call_once(RcuMonitor::new);
}
*/
