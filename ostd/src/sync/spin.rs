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

/// The tracked resources transferred from the unlocked spin lock to its guard
/// when the lock is acquired, and returned to the lock when the guard is dropped.
tracked struct SpinLockResource<T, I: ResourceInvariant<T>> {
    perm: PointsTo<T>,
    resource: I::Resource,
}

impl<T, I: ResourceInvariant<T>> SpinLockResource<T, I> {
    pub closed spec fn cell_id(self) -> cell::CellId {
        self.perm.id()
    }

    pub closed spec fn value(self) -> T {
        *self.perm.value()
    }

    pub closed spec fn resource(self) -> I::Resource {
        self.resource
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
/// # Verified properties
///
/// ## Ownership model
///
/// The `lock` field extends [`AtomicBool`] with a [`PointsTo<T>`] permission and a user-supplied
/// tracked resource. These two resources are bundled in `SpinLockResource` and stored as the
/// atomic ghost state while the lock is available:
///
/// ```rust
/// tracked struct SpinLockResource<T, I: ResourceInvariant<T>> {
///     perm: PointsTo<T>,
///     resource: I::Resource,
/// }
///
/// struct SpinLockInner<T, I: ResourceInvariant<T>> {
///     lock: AtomicBool<_, Option<SpinLockResource<T, I>>, _>,
///     val: PCell<T>,
///     ghost_resource_constant: Ghost<<I as ResourceInvariant<T>>::Constant>,
/// }
/// ```
///
/// When the lock bit is `false`, the atomic ghost state is `Some`, the permission refers to `val`,
/// and the protected value satisfies the user [`ResourceInvariant`]. Acquiring the lock changes
/// the bit to `true` and transfers the complete `SpinLockResource` to the guard, leaving `None` in
/// the atomic ghost state. Releasing the guard restores the resource invariant and returns the
/// bundle to the lock.
///
/// The immutable resource constant remains available through `ghost_resource_constant` even while the
/// tracked resource is owned by a guard. The complete relationship is encapsulated as a Verus type
/// invariant; public operations expose only the permissions and resource-invariant facts needed
/// by their callers.
///
/// ## Safety
/// There are no data races.
///
/// ## Functional Correctness
/// - At most one user can hold the lock at the same time.
#[repr(transparent)]
#[verus_verify]
//pub struct SpinLock<T: ?Sized, G = PreemptDisabled> {
pub struct SpinLock<T, G, I: ResourceInvariant<T> = TrivialResourceInvariant> {
    phantom: PhantomData<G>,
    /// Only the last field of a struct may have a dynamically sized type.
    /// That's why SpinLockInner is put in the last field.
    inner: SpinLockInner<T, I>,
}

struct_with_invariants! {
struct SpinLockInner<T, I: ResourceInvariant<T>> {
    lock: AtomicBool<_, Option<SpinLockResource<T, I>>, _>,
    val: PCell<T>, //TODO: Waiting the new PCell that supports ?Sized
                   //val: UnsafeCell<T>,
    ghost_resource_constant: Ghost<<I as ResourceInvariant<T>>::Constant>,
}

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        invariant on lock with (val, ghost_resource_constant)
            is (locked: bool, resource: Option<SpinLockResource<T, I>>)
        {
            match resource {
                None => locked,
                Some(resource) => {
                    &&& !locked
                    &&& resource.cell_id() == val.id()
                    &&& I::inv(
                        ghost_resource_constant@,
                        resource.value(),
                        resource.resource(),
                    )
                }
            }
        }
    }
}

verus! {

impl<T, G, I: ResourceInvariant<T>> SpinLock<T, G, I> {
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
    pub const fn new(
        val: T,
        Ghost(user_constant): Ghost<I::Constant>,
        Tracked(user_resource): Tracked<I::Resource>,
    ) -> (res: Self)
        requires
            I::inv(user_constant, val, user_resource),
        ensures
            res.constant() == user_constant,
    {
        let (val, Tracked(perm)) = PCell::new(val);
        let tracked resource = SpinLockResource { perm, resource: user_resource };
        let lock_inner = SpinLockInner {
            lock: AtomicBool::new(
                Ghost((val, Ghost(user_constant))),
                false,
                Tracked(Some(resource)),
            ),
            //val: UnsafeCell::new(val),
            val: val,
            ghost_resource_constant: Ghost(user_constant),
        };
        Self {
            phantom: PhantomData,
            inner: lock_inner,
        }
    }
}

}

verus! {

impl<T, G, I: ResourceInvariant<T>> SpinLock<T, G, I>
{
    /// Returns the unique [`CellId`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/struct.CellId.html) of the internal `PCell<T>`.
    pub closed spec fn cell_id(self) -> cell::CellId {
        self.inner.val.id()
    }

    /// The immutable constant associated with the resource invariant.
    pub closed spec fn constant(self) -> I::Constant {
        self.inner.ghost_resource_constant@
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
impl<T /*: ?Sized */, G: SpinGuardian, I: ResourceInvariant<T>> SpinLock<T, G, I> {
    /// Acquires the spin lock.
    ///
    /// # Verified Properties
    /// ## Safety
    /// There are no data races. The lock ensures exclusive access to the protected data.
    /// ## Preconditions
    /// None. (The invariant of `SpinLock` always holds internally.)
    /// ## Postconditions
    /// The returned `SpinLockGuard` satisfies its type invariant and the user-supplied resource
    /// invariant:
    /// - An exclusive permission to access the protected data is held by the guard.
    /// - The guard's permission matches the lock's internal cell ID.
    /// - The protected value and tracked resource satisfy the resource invariant.
    /// ## Key Verification Step
    /// When the internal atomic compare-and-exchange operation in `acquire_lock` succeeds,
    /// the ghost permission and user resource are simultaneously extracted from the lock.
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
            ret.resource_inv(),
    )]
    pub fn lock(&self) -> SpinLockGuard<'_, T, G, I> {
        // Notice the guard must be created before acquiring the lock.
        proof!{ use_type_invariant(self);}
        proof_decl!{
            let tracked resource: SpinLockResource<T, I>;
        }
        let inner_guard = G::guard();
        proof_with! {=> Tracked(resource)}
        self.acquire_lock();
        proof_decl! {
            let tracked SpinLockResource { perm, resource: user_resource } = resource;
        }
        SpinLockGuard {
            lock: self,
            guard: inner_guard,
            tracked_perm: Tracked(perm),
            tracked_resource: Tracked(Some(user_resource)),
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
                &&& ret->0.resource_inv()
            },
    )]
    pub fn try_lock(&self) -> Option<SpinLockGuard<'_, T, G, I>> {
        let inner_guard = G::guard();
        proof_decl!{
            let tracked mut resource: Option<SpinLockResource<T, I>> = None;
        }
        if #[verus_spec(with => Tracked(resource))] self.try_acquire_lock() {
            proof_decl! {
                let tracked SpinLockResource { perm, resource: user_resource } =
                    resource.tracked_unwrap();
            }
            let lock_guard = SpinLockGuard {
                lock: self,
                guard: inner_guard,
                tracked_perm: Tracked(perm),
                tracked_resource: Tracked(Some(user_resource)),
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
            -> resource: Tracked<SpinLockResource<T, I>>,
        ensures
            resource@.perm.id() == self.inner.val.id(),
            I::inv(self.constant(), resource@.value(), resource@.resource()),
            )]
    #[verifier::exec_allows_no_decreases_clause]
    fn acquire_lock(&self) {
        proof_decl!{
            let tracked mut resource: Option<SpinLockResource<T, I>> = None;
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
            -> resource: Tracked<Option<SpinLockResource<T, I>>>,
        ensures
            ret ==> {
                &&& resource@ is Some
                &&& resource@->0.perm.id() == self.inner.val.id()
                &&& I::inv(
                    self.constant(),
                    resource@->0.value(),
                    resource@->0.resource(),
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
            let tracked mut resource: Option<SpinLockResource<T, I>> = None;
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
            Tracked(resource): Tracked<SpinLockResource<T, I>>,
        requires
            resource.perm.id() == self.inner.val.id(),
            I::inv(self.constant(), resource.value(), resource.resource()),
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
unsafe impl<T: Send, G, I: ResourceInvariant<T>> Send for SpinLock<T, G, I> where I::Resource: Send {}
#[verifier::external]
unsafe impl<T: Send, G, I: ResourceInvariant<T>> Sync for SpinLock<T, G, I> where I::Resource: Send {}

/// A guard that provides exclusive access to the data protected by a [`SpinLock`].
///
/// # Verified Properties
/// ## Verification Design
/// The guard is extended with tracked fields holding both the ghost permission
/// ([`PointsTo<T>`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/pcell/struct.PointsTo.html))
/// and the user-supplied tracked resource. The permission grants exclusive ownership of the
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
    I: ResourceInvariant<T> = TrivialResourceInvariant,
> {
    guard: G::Guard,
    lock: &'a SpinLock<T, G, I>,
    /// Ghost permission for the protected value.
    tracked_perm: Tracked<PointsTo<T>>,
    /// User-supplied tracked resource.
    tracked_resource: Tracked<Option<I::Resource>>,
}

verus! {
impl<'a, T, G: SpinGuardian, I: ResourceInvariant<T>> SpinLockGuard<'a, T, G, I>
{
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool{
        self.lock.cell_id() == self.tracked_perm@.id()
    }

    /// The value stored in the lock.
    pub closed spec fn value(self) -> T {
        *self.tracked_perm@.value()
    }

    /// The tracked resource associated with the protected value.
    pub closed spec fn resource(self) -> I::Resource
        recommends
            self.has_resource(),
    {
        self.tracked_resource@->0
    }

    /// Whether the guard currently owns the user-supplied resource.
    pub closed spec fn has_resource(self) -> bool {
        self.tracked_resource@ is Some
    }

    /// The immutable user constant associated with the guarded spin lock.
    pub closed spec fn constant(self) -> I::Constant {
        self.lock.constant()
    }

    /// Whether the user-supplied invariant currently holds.
    pub open spec fn resource_inv(self) -> bool {
        &&& self.has_resource()
        &&& I::inv(self.constant(), self.value(), self.resource())
    }

    /// The value stored in the lock. It is an alias of `Self::value`.
    pub open spec fn view(self) -> T {
        self.value()
    }

    /// Temporarily takes ownership of the user-supplied tracked resource.
    #[verus_spec(ret =>
        with
            -> resource: Tracked<I::Resource>,
        requires
            old(self).has_resource(),
        ensures
            resource@ == old(self).resource(),
            !final(self).has_resource(),
            final(self).value() == old(self).value(),
            final(self).constant() == old(self).constant(),
    )]
    pub fn take_resource(&mut self) {
        proof! {
            use_type_invariant(&*self);
        }
        proof_decl! {
            let tracked resource = OptionAdditionalFns::tracked_take(&mut *self.tracked_resource);
        }
        #[verus_spec(with |= Tracked(resource))]
        ()
    }

    /// Returns the user-supplied tracked resource to the guard.
    #[verus_spec(
        with
            Tracked(resource): Tracked<I::Resource>,
        requires
            !old(self).has_resource(),
        ensures
            final(self).has_resource(),
            final(self).resource() == resource,
            final(self).value() == old(self).value(),
            final(self).constant() == old(self).constant(),
    )]
    pub fn put_resource(&mut self) {
        proof! {
            use_type_invariant(&*self);
            *self.tracked_resource = Some(resource);
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
impl<T: /*?Sized*/, G: SpinGuardian, I: ResourceInvariant<T>> Deref
    for SpinLockGuard<'_, T, G, I>
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
impl<T: /* ?Sized */, G: SpinGuardian, I: ResourceInvariant<T>> DerefMut
    for SpinLockGuard<'_, T, G, I>
{
    #[verus_spec(ret =>
        ensures
            final(self).view() == *final(ret),
            old(self).view() == *ret,
            final(self).has_resource() == old(self).has_resource(),
            old(self).has_resource() ==> final(self).resource() == old(self).resource(),
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
impl<'a, T /*:?Sized */, G: SpinGuardian, I: ResourceInvariant<T>> SpinLockGuard<'a, T, G, I> {
    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    #[verus_spec(
        requires
            self.resource_inv(),
    )]
    pub fn drop(self) {
        proof! {use_type_invariant(&self);}
        proof_decl! {
            let tracked perm = self.tracked_perm.get();
            let tracked user_resource = self.tracked_resource.get().tracked_unwrap();
            let tracked resource = SpinLockResource { perm, resource: user_resource };
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
impl<T: ?Sized, G: SpinGuardian, I: ResourceInvariant<T>> !Send for SpinLockGuard<'_, T, G, I> {}

#[verifier::external]
// SAFETY: `SpinLockGuard` can be shared between tasks/threads in same CPU.
// As `lock()` is only called when there are no race conditions caused by interrupts.
unsafe impl<T: Sync, G: SpinGuardian, I: ResourceInvariant<T>> Sync for SpinLockGuard<'_, T, G, I> {}
