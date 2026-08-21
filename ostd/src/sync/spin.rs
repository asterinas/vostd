// SPDX-License-Identifier: MPL-2.0
use vstd::atomic_ghost::*;
use vstd::cell::{self, pcell::*};
use vstd::prelude::*;
use vstd_extra::prelude::*;

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

/// A user-supplied invariant for data protected by a [`SpinLock`].
///
/// `State` is tracked state transferred together with the permission for the
/// protected value. The invariant is required to hold
/// while the state is stored in an unlocked spin lock. A lock guard may
/// temporarily break it, but must restore it before returning the state when
/// the guard is dropped.
pub trait SpinLockPredicate<T>: Sized {
    /// Immutable ghost data fixed when a spin lock is created.
    type Constant;

    /// Tracked state used to relate the protected value to external ghost
    /// state.
    type State;

    /// The relation that must hold between the protected value and its tracked
    /// state while the spin lock is unlocked.
    spec fn inv(constant: Self::Constant, value: T, state: Self::State) -> bool;
}

/// A spin-lock invariant that imposes no condition on the protected value.
///
/// This predicate allows existing `SpinLock` users to opt out of a custom
/// invariant.
pub struct TrivialSpinLockPredicate;

impl<T> SpinLockPredicate<T> for TrivialSpinLockPredicate {
    type Constant = ();
    type State = ();

    open spec fn inv(_constant: (), _value: T, _state: ()) -> bool {
        true
    }
}

/// The tracked resources transferred from the unlocked spin lock to its guard
/// when the lock is acquired, and returned to the lock when the guard is dropped.
tracked struct SpinLockResource<T, P: SpinLockPredicate<T>> {
    tracked perm: PointsTo<T>,
    tracked state: P::State,
}

impl<T, P: SpinLockPredicate<T>> SpinLockResource<T, P> {
    pub closed spec fn cell_id(self) -> cell::CellId {
        self.perm.id()
    }

    pub closed spec fn value(self) -> T {
        *self.perm.value()
    }

    pub closed spec fn predicate_state(self) -> P::State {
        self.state
    }
}

/// The following structs adapt [`SpinLockPredicate`] to [`AtomicBool`]'s invariant by pairing the
/// protected [`PCell`]'s id with the user-supplied predicate constant. The atomic predicate
/// ensures that the stored [`PointsTo`] permission belongs to that cell and satisfies the user
/// invariant. Atomic operations may update the lock bit and tracked resource, while this paired
/// constant remains fixed for the lifetime of the [`AtomicBool`].
ghost struct SpinLockConstant<C> {
    cell_id: cell::CellId,
    user_constant: C,
}

impl<C> SpinLockConstant<C> {
    pub closed spec fn cell_id(self) -> cell::CellId {
        self.cell_id
    }

    pub closed spec fn user_constant(self) -> C {
        self.user_constant
    }
}

struct SpinLockAtomicPredicate<T, P: SpinLockPredicate<T>> {
    phantom: PhantomData<(T, P)>,
}

impl<T, P: SpinLockPredicate<T>>
    AtomicInvariantPredicate<
        SpinLockConstant<P::Constant>,
        bool,
        Option<SpinLockResource<T, P>>,
    > for SpinLockAtomicPredicate<T, P>
{
    open spec fn atomic_inv(
        constant: SpinLockConstant<P::Constant>,
        locked: bool,
        resource: Option<SpinLockResource<T, P>>,
    ) -> bool {
        match resource {
            None => locked,
            Some(resource) => {
                &&& !locked
                &&& resource.cell_id() == constant.cell_id()
                &&& P::inv(
                    constant.user_constant(),
                    resource.value(),
                    resource.predicate_state(),
                )
            }
        }
    }
}

} // verus!

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
/// [`disable_irq`]: Self::disable_irq
///
/// # Verified Properties
/// ## Verification Design
/// To verify the correctness of spin lock, we use a ghost permission (i.e., not present in executable Rust). Only the owner of this permission can access the protected data in the cell.
/// When [`lock`] or [`try_lock`] succeeds, the ghost permission is transferred to the lock guard and given to the user for accessing the protected data.
/// When the lock guard is dropped, the ghost permission is transferred back to the spin lock.
///
/// [`lock`]: Self::lock
/// [`try_lock`]: Self::try_lock
///
/// ## Invariant
/// The `SpinLock` is internally represented by a struct `SpinLockInner` that contains an `AtomicBool` and a `PCell` to hold the protected data.
/// We present its formally verified version and invariant below.
///
/// The `lock` field is extended with a [`PointsTo<T>`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/pcell/struct.PointsTo.html)
/// ghost permission and the state associated with a user-supplied [`SpinLockPredicate`].
/// These tracked resources are also checked by Rust's ownership and borrowing rules and cannot be
/// duplicated, thereby ensuring exclusive access to the protected data and predicate state.
/// The `val` field is a [`PCell<T>`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/pcell/struct.PCell.html), which behaves like [`UnsafeCell<T>`](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html) used in the Asterinas mainline, but
/// only allows verified access through the ghost permission.
///
/// When the internal `AtomicBool` is `true`, both resources have been transferred to a
/// `SpinLockGuard`, so the user predicate may temporarily be broken. When it is `false`, both
/// resources are stored in the lock, the permission must match the `val`'s ID, and the user
/// predicate must hold.
/// ```rust
/// struct SpinLockInner<T, P: SpinLockPredicate<T>> {
///    lock: AtomicBool<
///        SpinLockConstant<P::Constant>,
///        Option<SpinLockResource<T, P>>,
///        SpinLockAtomicPredicate<T, P>,
///    >,
///    val: PCell<T>,
/// }
///
/// closed spec fn wf(self) -> bool {
///    self.lock.well_formed()
///        && self.lock.constant().cell_id() == self.val.id()
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
pub struct SpinLock<T, G, P: SpinLockPredicate<T> = TrivialSpinLockPredicate> {
    phantom: PhantomData<G>,
    /// Only the last field of a struct may have a dynamically sized type.
    /// That's why SpinLockInner is put in the last field.
    inner: SpinLockInner<T, P>,
}

#[verus_verify]
struct SpinLockInner<T, P: SpinLockPredicate<T>> {
    lock: AtomicBool<
        SpinLockConstant<P::Constant>,
        Option<SpinLockResource<T, P>>,
        SpinLockAtomicPredicate<T, P>,
    >,
    val: PCell<T>, //TODO: Waiting the new PCell that supports ?Sized
                   //val: UnsafeCell<T>,
}

verus! {
impl<T, P: SpinLockPredicate<T>> SpinLockInner<T, P>
{
    closed spec fn wf(self) -> bool {
        &&& self.lock.well_formed()
        &&& self.lock.constant().cell_id() == self.val.id()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool{
        self.wf()
    }
}

impl<T, G> SpinLock<T, G, TrivialSpinLockPredicate> {
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
        Self::new_with_pred(val, Ghost(()), Tracked(()))
    }
}

impl<T, G, P: SpinLockPredicate<T>> SpinLock<T, G, P> {
    /// Creates a spin lock with a user-supplied invariant and its initial
    /// tracked state.
    pub const fn new_with_pred(
        val: T,
        Ghost(user_constant): Ghost<P::Constant>,
        Tracked(state): Tracked<P::State>,
    ) -> (res: Self)
        requires
            P::inv(user_constant, val, state),
        ensures
            res.constant() == user_constant,
    {
        let (val, Tracked(perm)) = PCell::new(val);
        let ghost constant = SpinLockConstant { cell_id: val.id(), user_constant };
        let tracked resource = SpinLockResource { perm, state };
        let lock_inner = SpinLockInner {
            lock: AtomicBool::<
                SpinLockConstant<P::Constant>,
                Option<SpinLockResource<T, P>>,
                SpinLockAtomicPredicate<T, P>,
            >::new(
                Ghost(constant),
                false,
                Tracked(Some(resource)),
            ),
            //val: UnsafeCell::new(val),
            val: val,
        };
        Self {
            phantom: PhantomData,
            inner: lock_inner,
        }
    }
}

impl<T, G, P: SpinLockPredicate<T>> SpinLock<T, G, P>
{
    /// Returns the unique [`CellId`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/struct.CellId.html) of the internal `PCell<T>`.
    pub closed spec fn cell_id(self) -> cell::CellId {
        self.inner.val.id()
    }

    /// The immutable user constant associated with the spin-lock predicate.
    pub closed spec fn constant(self) -> P::Constant {
        self.inner.lock.constant().user_constant()
    }

    /// Public well-formedness predicate for external wrappers.
    pub closed spec fn wf(self) -> bool {
        self.type_inv()
    }

    /// Encapsulates the invariant described in the *Invariant* section of [`SpinLock`].
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool{
        self.inner.type_inv()
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

#[verus_verify]
impl<T /*: ?Sized */, G: SpinGuardian, P: SpinLockPredicate<T>> SpinLock<T, G, P> {
    /// Acquires the spin lock.
    ///
    /// # Verified Properties
    /// ## Safety
    /// There are no data races. The lock ensures exclusive access to the protected data.
    /// ## Preconditions
    /// None. (The invariant of `SpinLock` always holds internally.)
    /// ## Postconditions
    /// The returned `SpinLockGuard` satisfies its type invariant and the user-supplied predicate:
    /// - An exclusive permission to access the protected data is held by the guard.
    /// - The guard's permission matches the lock's internal cell ID.
    /// - The protected value and tracked predicate state satisfy the predicate.
    /// ## Key Verification Step
    /// When the internal atomic compare-and-exchange operation in `acquire_lock` succeeds,
    /// the ghost permission and predicate state are simultaneously extracted from the lock.
    /// ```rust
    /// atomic_with_ghost!  {
    ///    self.inner.lock => compare_exchange(false, true);
    ///    returning res;
    ///    ghost lock_resource => {
    ///     // Extract the resources when the lock is successfully acquired.
    ///     if res is Ok {
    ///            resource = Some(lock_resource.tracked_take());
    ///        }
    ///    }
    ///}.is_ok()
    /// ```
    #[verus_spec(ret =>
        ensures
            ret.constant() == self.constant(),
            ret.predicate_inv(),
    )]
    pub fn lock(&self) -> SpinLockGuard<'_, T, G, P> {
        // Notice the guard must be created before acquiring the lock.
        proof!{ use_type_invariant(self);}
        proof_decl!{
            let tracked resource: SpinLockResource<T, P>;
        }
        let inner_guard = G::guard();
        proof_with! {=> Tracked(resource)}
        self.acquire_lock();
        proof_decl! {
            let tracked SpinLockResource { perm, state } = resource;
        }
        SpinLockGuard {
            lock: self,
            guard: inner_guard,
            tracked_perm: Tracked(perm),
            tracked_state: Tracked(Some(state)),
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
    #[verus_spec(ret =>
        ensures
            ret is Some ==> {
                &&& ret->0.constant() == self.constant()
                &&& ret->0.predicate_inv()
            },
    )]
    pub fn try_lock(&self) -> Option<SpinLockGuard<'_, T, G, P>> {
        let inner_guard = G::guard();
        proof_decl!{
            let tracked mut resource: Option<SpinLockResource<T, P>> = None;
        }
        if #[verus_spec(with => Tracked(resource))] self.try_acquire_lock() {
            proof_decl! {
                let tracked SpinLockResource { perm, state } = resource.tracked_unwrap();
            }
            let lock_guard = SpinLockGuard {
                lock: self,
                guard: inner_guard,
                tracked_perm: Tracked(perm),
                tracked_state: Tracked(Some(state)),
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
            -> resource: Tracked<SpinLockResource<T, P>>,
        ensures
            resource@.perm.id() == self.inner.val.id(),
            P::inv(self.constant(), resource@.value(), resource@.predicate_state()),
            )]
    #[verifier::exec_allows_no_decreases_clause]
    fn acquire_lock(&self) {
        proof_decl!{
            let tracked mut resource: Option<SpinLockResource<T, P>> = None;
        }
        proof!{ use_type_invariant(self);}
        #[verus_spec(
            invariant self.type_inv(),
        )]
        while !#[verus_spec(with => Tracked(resource))]self.try_acquire_lock() {
            core::hint::spin_loop();
        }

        proof_decl!{
            let tracked resource = resource.tracked_unwrap();
        }
        // VERUS LIMITATION： Explicit return value to bind the ghost permission return value
        #[verus_spec(with |= Tracked(resource))]
        ()
    }

    #[verus_spec(ret =>
        with
            -> resource: Tracked<Option<SpinLockResource<T, P>>>,
        ensures
            ret ==> {
                &&& resource@ is Some
                &&& resource@->0.perm.id() == self.inner.val.id()
                &&& P::inv(
                    self.constant(),
                    resource@->0.value(),
                    resource@->0.predicate_state(),
                )
            },
            !ret ==> resource@ is None,
            )]
    fn try_acquire_lock(&self) -> bool {
        /*self.inner
            .lock
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()*/
        proof_decl!{
            let tracked mut resource: Option<SpinLockResource<T, P>> = None;
        }
        proof!{ use_type_invariant(self);}
        proof_with!{ |= Tracked(resource)}
        atomic_with_ghost!  {
            self.inner.lock => compare_exchange(false, true);
            returning res;
            ghost lock_resource => {
                if res is Ok {
                    resource = Some(lock_resource.tracked_take());
                }
            }
        }.is_ok()
    }

    #[verus_spec(
        with
            Tracked(resource): Tracked<SpinLockResource<T, P>>,
        requires
            resource.perm.id() == self.inner.val.id(),
            P::inv(self.constant(), resource.value(), resource.predicate_state()),
    )]
    fn release_lock(&self) {
        proof!{
            use_type_invariant(self);
        }
        //self.inner.lock.store(false, Ordering::Release);
        atomic_with_ghost!{
            self.inner.lock => store(false);
            ghost lock_resource => {
                lock_resource = Some(resource);
            }
        }
    }
}
}

/*
impl<T: ?Sized + fmt::Debug, G> fmt::Debug for SpinLock<T, G> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.inner.val, f)
    }
}*/

// SAFETY: Only a single lock holder is permitted to access the inner data of Spinlock.
#[verifier::external]
unsafe impl<T: Send, G, P: SpinLockPredicate<T>> Send for SpinLock<T, G, P> {}
#[verifier::external]
unsafe impl<T: Send, G, P: SpinLockPredicate<T>> Sync for SpinLock<T, G, P> {}

/// A guard that provides exclusive access to the data protected by a [`SpinLock`].
///
/// # Verified Properties
/// ## Verification Design
/// The guard is extended with tracked fields holding both the ghost permission
/// ([`PointsTo<T>`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/pcell/struct.PointsTo.html))
/// and the user-supplied predicate state. The permission grants exclusive ownership of the
/// protected data and enables verified access to the `PCell<T>`.
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
///        self.lock.cell_id() == self.tracked_perm@.id()
///    }
/// ```
///
/// *Note*: The invariant is encapsulated using the [`#[verifier::type_invariant]`](https://verus-lang.github.io/verus/guide/reference-type-invariants.html?highlight=type_#declaring-a-type-invariant) mechanism.
/// It internally holds at all steps during the method executions and is **NOT** exposed in the public APIs' pre- and post-conditions.
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
#[clippy::has_significant_drop]
#[must_use]
#[verus_verify]
pub struct SpinLockGuard<
    'a,
    T, /*: ?Sized*/
    G: SpinGuardian,
    P: SpinLockPredicate<T> = TrivialSpinLockPredicate,
> {
    guard: G::Guard,
    lock: &'a SpinLock<T, G, P>,
    /// Ghost permission for the protected value.
    tracked_perm: Tracked<PointsTo<T>>,
    /// User-supplied predicate state.
    tracked_state: Tracked<Option<P::State>>,
}

verus! {
impl<'a, T, G: SpinGuardian, P: SpinLockPredicate<T>> SpinLockGuard<'a, T, G, P>
{
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool{
        self.lock.cell_id() == self.tracked_perm@.id()
    }

    /// The value stored in the lock.
    pub closed spec fn value(self) -> T {
        *self.tracked_perm@.value()
    }

    /// The tracked state used by the user-supplied predicate.
    pub closed spec fn predicate_state(self) -> P::State
        recommends
            self.has_predicate_state(),
    {
        self.tracked_state@->0
    }

    /// Whether the guard currently owns its predicate state.
    pub closed spec fn has_predicate_state(self) -> bool {
        self.tracked_state@ is Some
    }

    /// The immutable user constant associated with the guarded spin lock.
    pub closed spec fn constant(self) -> P::Constant {
        self.lock.constant()
    }

    /// Whether the user-supplied invariant currently holds.
    pub open spec fn predicate_inv(self) -> bool {
        &&& self.has_predicate_state()
        &&& P::inv(self.constant(), self.value(), self.predicate_state())
    }

    /// The value stored in the lock. It is an alias of `Self::value`.
    pub open spec fn view(self) -> T {
        self.value()
    }

    /// Temporarily takes ownership of the user-supplied predicate state.
    #[verus_spec(ret =>
        with
            -> state: Tracked<P::State>,
        requires
            old(self).has_predicate_state(),
        ensures
            state@ == old(self).predicate_state(),
            !final(self).has_predicate_state(),
            final(self).value() == old(self).value(),
            final(self).constant() == old(self).constant(),
    )]
    pub fn take_predicate_state(&mut self) {
        proof! {
            use_type_invariant(&*self);
        }
        proof_decl! {
            let tracked state = OptionAdditionalFns::tracked_take(&mut *self.tracked_state);
        }
        #[verus_spec(with |= Tracked(state))]
        ()
    }

    /// Returns the user-supplied predicate state to the guard.
    #[verus_spec(
        with
            Tracked(state): Tracked<P::State>,
        requires
            !old(self).has_predicate_state(),
        ensures
            final(self).has_predicate_state(),
            final(self).predicate_state() == state,
            final(self).value() == old(self).value(),
            final(self).constant() == old(self).constant(),
    )]
    pub fn put_predicate_state(&mut self) {
        proof! {
            use_type_invariant(&*self);
            *self.tracked_state = Some(state);
        }
    }
}
/*
impl<T: ?Sized, G: SpinGuardian> AsAtomicModeGuard for SpinLockGuard<'_, T, G> {
    fn as_atomic_mode_guard(&self) -> &dyn crate::task::atomic_mode::InAtomicMode {
        self.guard.as_atomic_mode_guard()
    }
}*/

// FIXME: fix when verus attribute syntax supports Tracked.
#[verus_verify]
impl<T: /*?Sized*/, G: SpinGuardian, P: SpinLockPredicate<T>> Deref
    for SpinLockGuard<'_, T, G, P>
{
    type Target = T;

    #[verus_spec(returns self.view())]
    fn deref(&self) -> &T {
        proof_decl! {
            let tracked read_perm = self.tracked_perm.borrow();
        }
        proof!{
            use_type_invariant(self);
        }
        // unsafe { &*self.lock.inner.val.get() }
        // The internal implementation of `PCell<T>::borrow` is exactly unsafe { &(*(*self.ucell).get()) },
        // and here we verify that we have the permission to call `borrow`.
        self.lock.inner.val.borrow(Tracked(read_perm))
    }
}


#[verus_verify]
impl<T: /* ?Sized */, G: SpinGuardian, P: SpinLockPredicate<T>> DerefMut
    for SpinLockGuard<'_, T, G, P>
{
    #[verus_spec(ret =>
        ensures
            final(self).view() == *final(ret),
            old(self).view() == *ret,
            final(self).has_predicate_state() == old(self).has_predicate_state(),
            old(self).has_predicate_state() ==> final(self).predicate_state()
                == old(self).predicate_state(),
            final(self).constant() == old(self).constant(),
    )]
    fn deref_mut(&mut self) -> &mut Self::Target
    {
        proof!{
            use_type_invariant(&*self);
        }
        // unsafe { &mut *self.lock.inner.val.get() }
        self.lock.inner.val.borrow_mut(Tracked(&mut *self.tracked_perm))
    }
}
}

/* impl<T: ?Sized, G: SpinGuardian> Drop for SpinLockGuard<'_, T, G> {
    fn drop(&mut self) {
        self.lock.release_lock();
    }
}
*/

#[verus_verify]
impl<'a, T /*:?Sized */, G: SpinGuardian, P: SpinLockPredicate<T>> SpinLockGuard<'a, T, G, P> {
    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    #[verus_spec(
        requires
            self.predicate_inv(),
    )]
    pub fn drop(self) {
        proof! {use_type_invariant(&self);}
        proof_decl! {
            let tracked perm = self.tracked_perm.get();
            let tracked state = self.tracked_state.get().tracked_unwrap();
            let tracked resource = SpinLockResource { perm, state };
        }
        proof_with!(Tracked(resource));
        self.lock.release_lock();
    }
}

/* impl<T: ?Sized + fmt::Debug, G: SpinGuardian> fmt::Debug for SpinLockGuard<'_, T, G> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}*/

#[verus_verify]
impl<T: ?Sized, G: SpinGuardian, P: SpinLockPredicate<T>> !Send for SpinLockGuard<'_, T, G, P> {}

#[verifier::external]
// SAFETY: `SpinLockGuard` can be shared between tasks/threads in same CPU.
// As `lock()` is only called when there are no race conditions caused by interrupts.
unsafe impl<T: Sync, G: SpinGuardian, P: SpinLockPredicate<T>> Sync for SpinLockGuard<'_, T, G, P> {}
