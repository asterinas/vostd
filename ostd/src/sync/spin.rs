// SPDX-License-Identifier: MPL-2.0
use vstd::atomic_ghost::*;
use vstd::cell::{self, pcell::*};
use vstd::modes::*;
use vstd::prelude::*;
use vstd_extra::prelude::*;

use alloc::sync::Arc;
use core::{
    cell::UnsafeCell,
    fmt,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    //    sync::atomic::{AtomicBool, Ordering},
};

use super::{guard::SpinGuardian, LocalIrqDisabled /*, PreemptDisabled*/};
//use crate::task::atomic_mode::AsAtomicModeGuard;

verus! {
    broadcast use group_deref_spec;
}

/// A spin lock.
///
/// # Guard behavior
///
/// The type `G' specifies the guard behavior of the spin lock. While holding the lock,
/// - if `G` is [`PreemptDisabled`], preemption is disabled;
/// - if `G` is [`LocalIrqDisabled`], local IRQs are disabled.
///
/// The `G` can also be provided by other crates other than ostd,
/// if it behaves similar like [`PreemptDisabled`] or [`LocalIrqDisabled`].
///
/// The guard behavior can be temporarily upgraded from [`PreemptDisabled`] to
/// [`LocalIrqDisabled`] using the [`disable_irq`] method.
///
/// # Verified Properties
/// ## Verification Design
/// To verify the correctness of spin lock, we use a ghost permission (i.e., not present in executable Rust). Only the owner of this permission can access the protected data in the cell.
/// When [`lock`] or [`try_lock`] succeeds, the ghost permission is transferred to the lock guard and given to the user for accessing the protected data.
/// When the lock guard is dropped, the ghost permission is transferred back to the spin lock.
///
/// [`disable_irq`]: Self::disable_irq
/// [`lock`]: Self::lock
/// [`try_lock`]: Self::try_lock
///
/// ## Invariant
/// The `SpinLock` is internally represented by a struct `SpinLockInner` that contains an `AtomicBool` and a `PCell` to hold the protected data. 
/// We present its formally verified version and invariant below. 
/// 
/// The `lock` field is extended with a [`PointsTo<T>`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/pcell/struct.PointsTo.html)
/// ghost permission to track the ownership of the protected data. This ghost permission is also checked by Rust's ownership and borrowing rules and cannot be duplicated, 
/// thereby ensuring exclusive access to the protected data.
/// The `val` field is a [`PCell<T>`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/pcell/struct.PCell.html), which behaves like [`UnsafeCell<T>`](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html) used in the Asterinas mainline, but
/// only allows verified access through the ghost permission.
/// 
/// When the internal `AtomicBool` is `true`, the permission has been transferred to a `SpinLockGuard` and no one else can acquire the lock. 
/// When it is `false`, the permission to access the `PCell<T>` is stored in the lock, and it must match the `val`'s id.
/// ```rust
/// struct_with_invariants! {
/// struct SpinLockInner<T> {
///    lock: AtomicBool<_,Option<PointsTo<T>>,_>,
///    val: PCell<T>,
/// }
///
/// closed spec fn wf(self) -> bool {
///    invariant on lock with (val) is (v:bool, g:Option<PointsTo<T>>) {
///        match g {
///            None => v == true,
///            Some(perm) => perm.id() == val.id() && !v
///        }
///    }
/// }
/// }
/// ```
/// 
/// *Note*: The invariant is encapsulated in [`type_inv`] using the [`#[verifier::type_invariant]`](https://verus-lang.github.io/verus/guide/reference-type-invariants.html?highlight=type_#declaring-a-type-invariant) mechanism. 
/// It internally holds at all steps during the method executions and is **NOT** exposed in the public APIs' pre- and post-conditions.
/// 
/// ## Safety
/// There are no data races.
///
/// ## Functional Correctness
/// - At most one user can hold the lock at the same time.
/// 
/// [`type_inv`]: Self::type_inv
#[repr(transparent)]
#[verus_verify]
//pub struct SpinLock<T: ?Sized, G = PreemptDisabled> {
pub struct SpinLock<T, G> {
    phantom: PhantomData<G>,
    /// Only the last field of a struct may have a dynamically sized type.
    /// That's why SpinLockInner is put in the last field.
    inner: SpinLockInner<T>,
}

verus! {

struct_with_invariants! {
struct SpinLockInner<T> {
    lock: AtomicBool<_,Option<PointsTo<T>>,_>,
    val: PCell<T>, //TODO: Waiting the new PCell that supports ?Sized
    //val: UnsafeCell<T>,
}

closed spec fn wf(self) -> bool {
    invariant on lock with (val) is (v:bool, g:Option<PointsTo<T>>) {
        match g {
            None => v == true,
            Some(perm) => perm.id() == val.id() && !v
        }
    }
}
}

impl<T> SpinLockInner<T>
{
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool{
        self.wf()
    }
}

#[verus_verify]
impl<T, G> SpinLock<T, G> {
    /// Creates a new spin lock.
    ///
    /// # Verified Properties
    /// ## Safety
    /// This function is written in safe Rust and there is no undefined behavior.
    /// ## Preconditions
    /// None.
    /// ## Postconditions
    /// - The function will not panic.
    /// - The created spin lock satisfies the invariant.
    pub const fn new(val: T) -> Self
    {
        let (val, Tracked(perm)) = PCell::new(val);
        let lock_inner = SpinLockInner {
            lock: AtomicBool::new(Ghost(val),false,Tracked(Some(perm))),
            //val: UnsafeCell::new(val),
            val: val,
        };
        Self {
            phantom: PhantomData,
            inner: lock_inner,
        }
    }
}

verus!{}
impl<T,G> SpinLock<T,G>
{
    /// Returns the unique [`CellId`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/struct.CellId.html) of the internal `PCell<T>`.
    pub closed spec fn cell_id(self) -> cell::CellId {
        self.inner.val.id()
    }

    /// Encapsulates the invariant described in the *Invariant* section of [`SpinLock`].
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool{
        self.inner.type_inv()
    }
}
}

/*
impl<T: ?Sized> SpinLock<T, PreemptDisabled> {
    /// Converts the guard behavior from disabling preemption to disabling IRQs.
    pub fn disable_irq(&self) -> &SpinLock<T, LocalIrqDisabled> {
        let ptr = self as *const SpinLock<T, PreemptDisabled>;
        let ptr = ptr as *const SpinLock<T, LocalIrqDisabled>;
        // SAFETY:
        // 1. The types `SpinLock<T, PreemptDisabled>`, `SpinLockInner<T>` and `SpinLock<T,
        //    IrqDisabled>` have the same memory layout guaranteed by `#[repr(transparent)]`.
        // 2. The specified memory location can be borrowed as an immutable reference for the
        //    specified lifetime.
        unsafe { &*ptr }
    }
}*/

verus! {
//impl<T: ?Sized, G: SpinGuardian> SpinLock<T, G> {
impl<T, G: SpinGuardian> SpinLock<T, G> {

    /// Acquires the spin lock.
    ///
    /// # Verified Properties
    /// ## Safety
    /// There are no data races. The lock ensures exclusive access to the protected data.
    /// ## Preconditions
    /// None. (The invariant of `SpinLock` always holds internally.)
    /// ## Postconditions
    /// The returned `SpinLockGuard` satisfies its type invariant:
    /// - An exclusive permission to access the protected data is held by the guard.
    /// - The guard's permission matches the lock's internal cell ID.
    /// ## Key Verification Step
    /// When the internal atomic compare-and-exchange operation in `acquire_lock` succeeds,
    /// the ghost permission is simultaneously extracted from the lock.
    /// ```rust
    /// atomic_with_ghost!  {
    ///    self.inner.lock => compare_exchange(false, true);
    ///    returning res;
    ///    ghost cell_perm => {
    ///     // Extract the ghost permission when the lock is successfully acquired   
    ///     if res is Ok {
    ///            tracked_swap(&mut perm, &mut cell_perm);
    ///        }
    ///    }
    ///}.is_ok()
    /// ```
    #[verus_spec]
    pub fn lock(&self) -> SpinLockGuard<T, G> {
        // Notice the guard must be created before acquiring the lock.
        proof!{ use_type_invariant(self);}
        proof_decl!{
            let tracked mut perm: PointsTo<T> = arbitrary_cell_pointsto();
        }
        let inner_guard = G::guard();
        proof_with! {=> Tracked(perm)}
        self.acquire_lock();
        SpinLockGuard_ {
            lock: self,
            guard: inner_guard,
            v_perm: Tracked(perm),
        }
    }

    /// Acquires the spin lock through an [`Arc`].
    ///
    /// The method is similar to [`lock`], but it doesn't have the requirement
    /// for compile-time checked lifetimes of the lock guard.
    ///
    /// [`lock`]: Self::lock
    ///
    /// # Verified Properties
    /// Same as [`lock`].
    #[verus_spec]
    pub fn lock_arc(self: &Arc<Self>) -> ArcSpinLockGuard<T, G> {
        proof!{ use_type_invariant(self);}
        proof_decl!{
            let tracked mut perm: PointsTo<T> = arbitrary_cell_pointsto();
        }
        let inner_guard = G::guard();
        proof_with! {=> Tracked(perm)}
        self.acquire_lock();
        proof!{
            assert(perm.id() == (*self.clone().deref_spec()).cell_id());
        }
        SpinLockGuard_ {
            lock: self.clone(),
            guard: inner_guard,
            v_perm: Tracked(perm),
        }
    }

    /// Tries acquiring the spin lock immediately.
    ///
    /// # Verified Properties
    /// ## Safety
    /// There are no data races. The lock ensures exclusive access to the protected data.
    /// ## Preconditions
    /// None. (The invariant of `SpinLock` always holds internally.)
    /// ## Postconditions
    /// If `Some(guard)` is returned, it satisfies its type invariant:
    /// - An exclusive permission to access the protected data is held by the guard.
    /// - The guard's permission matches the lock's internal cell ID.
    #[verus_spec]
    pub fn try_lock(&self) -> Option<SpinLockGuard<T, G>> {
        let inner_guard = G::guard();
        proof_decl!{
            let tracked mut perm: Option<PointsTo<T>> = None;
        }
        if #[verus_spec(with => Tracked(perm))] self.try_acquire_lock() {
            let lock_guard = SpinLockGuard_ {
                lock: self,
                guard: inner_guard,
                v_perm: Tracked(perm.tracked_unwrap()),
            };
            return Some(lock_guard);
        }
        None
    }

    /*
    /// Returns a mutable reference to the underlying data.
    ///
    /// This method is zero-cost: By holding a mutable reference to the lock, the compiler has
    /// already statically guaranteed that access to the data is exclusive.
    pub fn get_mut(&mut self) -> &mut T {
        self.inner.val.get_mut()
    }*/

    /// Acquires the spin lock, otherwise busy waiting
    #[verus_spec(ret =>
        with
            -> perm: Tracked<PointsTo<T>>,
        ensures
            perm@.id() == self.inner.val.id(),
            )]
    #[verifier::exec_allows_no_decreases_clause]
    fn acquire_lock(&self) {
        proof_decl!{
            let tracked mut perm: Option<PointsTo<T>> = None;
        }
        proof!{ use_type_invariant(self);}
        #[verus_spec(
            invariant self.type_inv(),
        )]
        while !#[verus_spec(with => Tracked(perm))]self.try_acquire_lock() {
            core::hint::spin_loop();
        }

        proof_decl!{
            let tracked mut perm = perm.tracked_unwrap();
        }
        // VERUS LIMITATION： Explicit return value to bind the ghost permission return value
        #[verus_spec(with |= Tracked(perm))]
        ()
    }

    #[verus_spec(ret =>
        with
            -> perm: Tracked<Option<PointsTo<T>>>,
        ensures
            ret && perm@ is Some && perm@ -> Some_0.id() == self.inner.val.id() || !ret && perm@ is None,
            )]
    fn try_acquire_lock(&self) -> bool {
        /*self.inner
            .lock
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()*/
        proof_decl!{
            let tracked mut perm: Option<PointsTo<T>> = None;
        }
        proof!{ use_type_invariant(self);}
        proof_with!{ |= Tracked(perm)}
        atomic_with_ghost!  {
            self.inner.lock => compare_exchange(false, true);
            returning res;
            ghost cell_perm => {
                if res is Ok {
                    tracked_swap(&mut perm, &mut cell_perm);
                }
            }
        }.is_ok()
    }

    /// *Note*: This is **NOT** an OSTD API. It is only an example to show the doc generation output with the `#[verus_spec]` macro.
    /// It will be removed after [our PR](https://github.com/verus-lang/verus/pull/2132) about `#[verus_spec]` doc generation is merged into Verus mainline.
    #[verus_spec(ret =>
        with
            ghost_in1: Tracked<int>,
            ghost_in2: Tracked<int>,
            ->
            ghost_out: Ghost<(int,int)>,
        requires
            ghost_in1@ >= 0,
        ensures
            ghost_out@.0 == ghost_in1@,
            ret == 0,
    )]
    pub fn spec_with_example(&self) -> u32 {
        proof_decl!{
            let ghost mut out: (int,int) = (0,0);
        }
        proof!{
            out.0 = ghost_in1@;
            out.1 = ghost_in2@;
        }
        proof_with!{|= Ghost(out)}
        0
    }

    /*
    fn release_lock(&self) {
        self.inner.lock.store(false, Ordering::Release);
    }
    */
}
}

/*
impl<T: ?Sized + fmt::Debug, G> fmt::Debug for SpinLock<T, G> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.inner.val, f)
    }
}

// SAFETY: Only a single lock holder is permitted to access the inner data of Spinlock.
unsafe impl<T: ?Sized + Send, G> Send for SpinLock<T, G> {}
unsafe impl<T: ?Sized + Send, G> Sync for SpinLock<T, G> {}
*/
/// A guard that provides exclusive access to the data protected by a [`SpinLock`].
///
/// # Verified Properties
/// ## Verification Design
/// The guard is extended with a ghost permission field `v_perm` that
/// holds the ghost permission ([`PointsTo<T>`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/pcell/struct.PointsTo.html))
/// This permission grants exclusive ownership of the protected data and enables verified access to the `PCell<T>`.
///
/// 
/// ## Invariant
/// The guard maintains a type invariant ensuring that its ghost permission's ID matches
/// the lock's internal cell ID. This guarantees that the permission corresponds to the
/// correct protected data.
/// 
/// ```rust
/// #[verifier::type_invariant]
///    spec fn type_inv(self) -> bool{
///        self.lock.deref_spec().cell_id() == self.v_perm@.id()
///    }
/// ```
/// 
/// *Note*: The invariant is encapsulated using the [`#[verifier::type_invariant]`](https://verus-lang.github.io/verus/guide/reference-type-invariants.html?highlight=type_#declaring-a-type-invariant) mechanism. 
/// It internally holds at all steps during the method executions and is **NOT** exposed in the public APIs' pre- and post-conditions.
pub type SpinLockGuard<'a, T, G> = SpinLockGuard_<T, &'a SpinLock<T, G>, G>;
/// A guard that provides exclusive access to the data protected by a `Arc<SpinLock>`.
pub type ArcSpinLockGuard<T, G> = SpinLockGuard_<T, Arc<SpinLock<T, G>>, G>;

/// The guard of a spin lock.
#[clippy::has_significant_drop]
#[must_use]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
#[verus_verify]
pub struct SpinLockGuard_<T /*: ?Sized*/, R: Deref<Target = SpinLock<T, G>>, G: SpinGuardian> {
    guard: G::Guard,
    lock: R,
    v_perm: Tracked<PointsTo<T>>, //Ghost permission for verification
}

verus! {
impl<T, R: Deref<Target = SpinLock<T, G>>, G: SpinGuardian> SpinLockGuard_<T, R, G>
{
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool{
        self.lock.deref_spec().cell_id() == self.v_perm@.id()
    }
}
}
/*
impl<T: ?Sized, R: Deref<Target = SpinLock<T, G>>, G: SpinGuardian> AsAtomicModeGuard
    for SpinLockGuard_<T, R, G>
{
    fn as_atomic_mode_guard(&self) -> &dyn crate::task::atomic_mode::InAtomicMode {
        self.guard.as_atomic_mode_guard()
    }
}

impl<T: ?Sized, R: Deref<Target = SpinLock<T, G>>, G: SpinGuardian> Deref
    for SpinLockGuard_<T, R, G>
{
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.lock.inner.val.get() }
    }
}

impl<T: ?Sized, R: Deref<Target = SpinLock<T, G>>, G: SpinGuardian> DerefMut
    for SpinLockGuard_<T, R, G>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.lock.inner.val.get() }
    }
}

impl<T: ?Sized, R: Deref<Target = SpinLock<T, G>>, G: SpinGuardian> Drop
    for SpinLockGuard_<T, R, G>
{
    fn drop(&mut self) {
        self.lock.release_lock();
    }
}

impl<T: ?Sized + fmt::Debug, R: Deref<Target = SpinLock<T, G>>, G: SpinGuardian> fmt::Debug
    for SpinLockGuard_<T, R, G>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}*/

/*
impl<T: ?Sized, R: Deref<Target = SpinLock<T, G>>, G: SpinGuardian> !Send
    for SpinLockGuard_<T, R, G>
{
}

// SAFETY: `SpinLockGuard_` can be shared between tasks/threads in same CPU.
// As `lock()` is only called when there are no race conditions caused by interrupts.
unsafe impl<T: ?Sized + Sync, R: Deref<Target = SpinLock<T, G>> + Sync, G: SpinGuardian> Sync
    for SpinLockGuard_<T, R, G>
{
}
*/
