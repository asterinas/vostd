// SPDX-License-Identifier: MPL-2.0
//! Read-copy update (RCU).
//!
//! # Note
//!
//! Currently this RCU model assumes a sequential consistency (SC) memory model.
//! We may explore weak memory models in the future.
#[cfg(feature = "irc11")]
use vstd::thread_view::Objective;
use vstd::{
    atomic_ghost::AtomicPtr,
    atomic_with_ghost,
    map::Map,
    modes::tracked_static_ref,
    prelude::*,
    resource::{
        Loc,
        frac_opt::Frac,
        set::{GhostPersistentSingleton, GhostPersistentSubset, GhostSetAuth},
    },
};
use vstd_extra::{once::Once, prelude::*};

use core::{
    marker::PhantomData, mem::ManuallyDrop, ops::Deref,
    ptr::NonNull,
    /*
    sync::atomic::{
            AtomicPtr,
            Ordering::{AcqRel, Acquire},
        },
    */
};

use non_null::NonNullPtr;
// use spin::once::Once;

use self::monitor::{RcuMonitor, RcuMonitorInvariant, RcuMonitorPred};
use crate::task::{
    DisabledPreemptGuard,
    atomic_mode::{/*AsAtomicModeGuard, */ InAtomicMode},
    disable_preempt,
};

mod monitor;
pub mod non_null;

verus! {

broadcast use vstd_extra::external::nonnull::group_nonull_axioms;

/// Read permissions for one published object.
///
/// Fractions are real-valued, so every read can split another share without a
/// reader budget.
type RcuReadPool<P> = Frac<<P as NonNullPtr>::Permission>;

/// One reader's share of a pool and a persistent witness that the pool is
/// registered in its RCU cell.
tracked struct RcuReadToken<P: NonNullPtr> {
    tracked perm: RcuReadPool<P>,
    tracked registered: GhostPersistentSingleton<Loc>,
}

type RcuRetiredEntry<P> = (Ghost<*mut <P as NonNullPtr>::Target>, RcuReadPool<P>);

/// Called by `drop` of the read guard to track the retired read permissions.
type RcuRetiredPools<P> = Map<Loc, RcuRetiredEntry<P>>;

type RcuReturnedTokens<P> = Map<Loc, RcuReadToken<P>>;

tracked struct RcuPtrGhost<P: NonNullPtr> {
    tracked current: Option<RcuReadPool<P>>,
    tracked retired: RcuRetiredPools<P>,
    tracked returned: RcuReturnedTokens<P>,
    /// Ids of every pool this cell has published.
    tracked registry: GhostSetAuth<Loc>,
    /// A duplicable copy of `registry` used to hand out reader witnesses.
    tracked registered: GhostPersistentSubset<Loc>,
}

impl<P: NonNullPtr> RcuReadToken<P> {
    spec fn id(self) -> Loc {
        self.perm.id()
    }

    spec fn resource(self) -> <P as NonNullPtr>::Permission {
        self.perm.resource()
    }

    spec fn frac(self) -> real {
        self.perm.frac()
    }

    /// The token is registered in the registry `registry`.
    spec fn registered_in(self, registry: Loc) -> bool {
        &&& self.registered.id() == registry
        &&& self.registered@ == self.id()
    }

    proof fn tracked_borrow(tracked &self) -> (tracked res: &<P as NonNullPtr>::Permission)
        ensures
            *res == self.resource(),
    {
        self.perm.borrow()
    }
}

impl<P: NonNullPtr> RcuPtrGhost<P> {
    proof fn tracked_empty() -> (tracked res: Self)
        ensures
            res.current is None,
            res.retired.is_empty(),
            res.returned.is_empty(),
            res.registry_inv(),
    {
        let tracked (registry, subset) = GhostSetAuth::new(Set::empty());
        let tracked registered = subset.persist();
        RcuPtrGhost {
            current: None,
            retired: Map::tracked_empty(),
            returned: Map::tracked_empty(),
            registry,
            registered,
        }
    }

    /// Every registered pool is still the current pool or a retired pool.
    spec fn registry_inv(self) -> bool {
        &&& self.registered.id() == self.registry.id()
        &&& self.registered@ == self.registry@
        &&& self.current matches Some(pool) ==> self.registry@.contains(pool.id())
        &&& forall|id: Loc| #[trigger]
            self.registry@.contains(id) ==> self.retired.contains_key(id) || (
            self.current matches Some(pool) && pool.id() == id)
    }

    /// Publishes `perm` in a fresh pool and records the pool in the registry.
    proof fn tracked_alloc_pool(
        tracked &mut self,
        tracked perm: <P as NonNullPtr>::Permission,
    ) -> (tracked pool: RcuReadPool<P>)
        requires
            old(self).registry_inv(),
            retired_pools_inv::<P>(old(self).retired),
        ensures
            pool.resource() == perm,
            pool.frac() == 1real,
            final(self).current == old(self).current,
            final(self).retired == old(self).retired,
            final(self).returned == old(self).returned,
            final(self).registry.id() == old(self).registry.id(),
            final(self).registered.id() == old(self).registered.id(),
            final(self).registry@ == old(self).registry@.insert(pool.id()),
            final(self).registered@ == final(self).registry@,
    {
        let tracked mut pool = Frac::new(perm);
        if self.registry@.contains(pool.id()) {
            // A fresh full pool cannot share its id with a live pool.
            if self.retired.contains_key(pool.id()) {
                let tracked existing = self.retired.tracked_borrow(pool.id());
                existing.1.bounded();
                pool.bounded_with(&existing.1);
            } else {
                let tracked existing = self.current.tracked_borrow();
                existing.bounded();
                pool.bounded_with(existing);
            }
        }
        let tracked singleton = self.registry.insert(pool.id());
        self.registered.combine_points_to(singleton.persist());
        pool
    }

    /// Retires the current pool, published at `prev`, and publishes `new_perm`.
    proof fn tracked_replace(
        tracked &mut self,
        prev: *mut <P as NonNullPtr>::Target,
        tracked new_perm: Option<<P as NonNullPtr>::Permission>,
    )
        requires
            old(self).registry_inv(),
            retired_pools_inv::<P>(old(self).retired),
            old(self).current matches Some(pool) ==> {
                &&& !prev.is_null()
                &&& P::ptr_perm_match(prev, pool.resource())
                &&& pool.resource().inv()
            },
        ensures
            final(self).registry_inv(),
            retired_pools_inv::<P>(final(self).retired),
            final(self).returned == old(self).returned,
            final(self).registry.id() == old(self).registry.id(),
            match new_perm {
                Some(perm) => final(self).current matches Some(pool) && pool.resource() == perm,
                None => final(self).current is None,
            },
    {
        if self.current is Some {
            let tracked pool = self.current.tracked_take();
            let ghost id = pool.id();
            if self.retired.contains_key(id) {
                let tracked (ptr, mut retired_pool) = self.retired.tracked_remove(id);
                retired_pool.combine(pool);
                self.retired.tracked_insert(id, (ptr, retired_pool));
            } else {
                self.retired.tracked_insert(id, (Ghost(prev), pool));
            }
        }
        if new_perm is Some {
            let tracked pool = self.tracked_alloc_pool(new_perm.tracked_unwrap());
            self.current = Some(pool);
        }
    }

    /// Returns a witness that `id` is registered.
    proof fn tracked_witness(tracked &self, id: Loc) -> (tracked res: GhostPersistentSingleton<Loc>)
        requires
            self.registry_inv(),
            self.registry@.contains(id),
        ensures
            res.id() == self.registry.id(),
            res@ == id,
    {
        let tracked mut copy = self.registered.duplicate();
        copy.split_singleton(id)
    }

    /// Returns a reader token to its pool.
    proof fn tracked_return_token(tracked &mut self, tracked token: RcuReadToken<P>)
        requires
            old(self).registry_inv(),
            retired_pools_inv::<P>(old(self).retired),
            token.registered_in(old(self).registry.id()),
        ensures
            final(self).registry_inv(),
            retired_pools_inv::<P>(final(self).retired),
            final(self).registry.id() == old(self).registry.id(),
            final(self).returned == old(self).returned,
            final(self).current is Some <==> old(self).current is Some,
            final(self).current matches Some(pool) ==> pool.resource() == old(
                self,
            ).current->0.resource(),
    {
        let tracked RcuReadToken { perm, registered } = token;
        let ghost id = perm.id();
        registered.agree(&self.registry);
        if self.retired.contains_key(id) {
            let tracked (ptr, mut pool) = self.retired.tracked_remove(id);
            pool.combine(perm);
            self.retired.tracked_insert(id, (ptr, pool));
        } else {
            let tracked mut pool = self.current.tracked_take();
            pool.combine(perm);
            self.current = Some(pool);
        }
    }
}

// This authority contains allocation ownership and bookkeeping only. Raw
// addresses do not carry the pointee's subjective weak-memory observations.
#[cfg(feature = "irc11")]
unsafe impl<P: NonNullPtr> Objective for RcuPtrGhost<P> {

}

closed spec fn retired_pools_inv<P: NonNullPtr>(retired: RcuRetiredPools<P>) -> bool {
    forall|id: Loc| #[trigger]
        retired.contains_key(id) ==> {
            let entry = retired[id];
            &&& !(entry.0@).is_null()
            &&& entry.1.id() == id
            &&& P::ptr_perm_match(entry.0@, entry.1.resource())
            &&& entry.1.resource().inv()
        }
}

closed spec fn returned_tokens_inv<P: NonNullPtr>(returned: RcuReturnedTokens<P>) -> bool {
    forall|id: Loc| #[trigger]
        returned.contains_key(id) ==> {
            let token = returned[id];
            &&& token.id() == id
            &&& token.resource().inv()
            &&& token.frac() > 0real
        }
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

/// A guard that allows access to the pointed data protected by a [`Rcu`].
#[clippy::has_significant_drop]
#[must_use]
pub struct RcuReadGuard<'a, P: NonNullPtr>(RcuReadGuardInner<'a, P>);

/// A Read-Copy Update (RCU) cell for sharing a _ghost_nullable_ pointer.
///
/// This is a variant of [`Rcu`] that allows the contained pointer to be null.
/// So that it can implement `Rcu<Option<P>>` where `P` is not a ghost_nullable
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

/// A guard that allows access to the pointed data protected by a [`RcuOption`].
#[clippy::has_significant_drop]
#[must_use]
pub struct RcuOptionReadGuard<'a, P: NonNullPtr>(RcuReadGuardInner<'a, P>);

struct_with_invariants! {
/// The inner implementation of both [`Rcu`] and [`RcuOption`].
struct RcuInner<P: NonNullPtr> {
    ptr: AtomicPtr<<P as NonNullPtr>::Target,_,RcuPtrGhost<P>,_>,
    // We want to implement Send and Sync explicitly.
    // Having a pointer field prevents them from being implemented
    // automatically by the compiler.
    _marker: PhantomData<*const <P as NonNullPtr>::Target>,
    ghost_nullable: Ghost<bool>,
    pool_registry: Ghost<Loc>,
}

closed spec fn wf(self) -> bool {
    invariant on ptr with (ghost_nullable, _marker, pool_registry) is (
        v: *mut <P as NonNullPtr>::Target,
        g: RcuPtrGhost<P>,
    ) {
        &&& retired_pools_inv::<P>(g.retired)
        &&& returned_tokens_inv::<P>(g.returned)
        &&& g.registry_inv()
        &&& g.registry.id() == pool_registry@
        &&& match g.current {
            Some(perm) => {
                &&& !v.is_null()
                &&& P::ptr_perm_match(v, perm.resource())
                &&& perm.resource().inv()
            },
            None => ghost_nullable@ && v.is_null(),
        }
    }
}
}
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
    /// Whether the contained pointer can be null. Used to distinguish `Rcu` and `RcuOption`.
    pub closed spec fn is_nullable(self) -> bool {
        self.ghost_nullable@
    }

    /// The registry that records every pool published by this cell.
    closed spec fn registry_id(self) -> Loc {
        self.pool_registry@
    }
}

impl<P: NonNullPtr + Send> RcuInner<P> {
    #[inline(always)]
    const fn new_none() -> (res: Self)
        ensures
            res.is_nullable(),
            res.wf(),
    {
        let tracked ptr_ghost = RcuPtrGhost::<P>::tracked_empty();
        let ghost pool_registry = ptr_ghost.registry.id();
        Self {
            ptr: AtomicPtr::new(
                Ghost(
                    (
                        Ghost(true),
                        PhantomData::<*const <P as NonNullPtr>::Target>,
                        Ghost(pool_registry),
                    ),
                ),
                core::ptr::null_mut(),
                Tracked(ptr_ghost),
            ),
            _marker: PhantomData::<*const <P as NonNullPtr>::Target>,
            ghost_nullable: Ghost(true),
            pool_registry: Ghost(pool_registry),
        }
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuInner<P> {
    /// Creates a new RCU primitive with the given pointer `pointer`.
    #[inline(always)]
    #[verus_spec(r =>
        with
            Ghost(ghost_nullable): Ghost<bool>,
        requires
            pointer.inv(),
        ensures
            r.type_inv(),
            r.is_nullable() == ghost_nullable,
    )]
    fn new(pointer: P) -> Self {
        // let ptr = <P as NonNullPtr>::into_raw(pointer).as_ptr();
        let (ptr, Tracked(ptr_perm)) = <P as NonNullPtr>::into_raw(pointer);
        let ptr = ptr.as_ptr();
        proof_decl! {
            let tracked mut ptr_ghost = RcuPtrGhost::<P>::tracked_empty();
            let tracked pool = ptr_ghost.tracked_alloc_pool(ptr_perm);
            let ghost pool_registry = ptr_ghost.registry.id();
        }
        proof {
            ptr_ghost.current = Some(pool);
        }

        let ptr = AtomicPtr::new(
            Ghost((Ghost(ghost_nullable), PhantomData, Ghost(pool_registry))),
            ptr,
            Tracked(ptr_ghost),
        );
        Self {
            ptr,
            _marker: PhantomData,
            ghost_nullable: Ghost(ghost_nullable),
            pool_registry: Ghost(pool_registry),
        }
    }

    #[verus_spec(
        requires
            self.is_nullable() || new_ptr is Some,
            new_ptr.inv(),
    )]
    fn update(&self, new_ptr: Option<P>) {
        let (new_ptr, Tracked(new_perm)) = if let Some(new_ptr) = new_ptr {
            //  <P as NonNullPtr>::into_raw(new_ptr).as_ptr()
            let (ptr, Tracked(perm)) = <P as NonNullPtr>::into_raw(new_ptr);
            let ptr = ptr.as_ptr();
            (ptr, Tracked(Some(perm)))
        } else {
            (core::ptr::null_mut(), Tracked(None))
        };

        proof {
            use_type_invariant(self);
        }
        let old_raw_ptr =
            atomic_with_ghost! {
            self.ptr => swap(new_ptr);
            update prev -> next;
            ghost g => {
                g.tracked_replace(prev, new_perm);
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
            -> tracked_ref_perm: Tracked<Option<RcuReadToken<P>>>,
        ensures
            !self.is_nullable() ==> tracked_ref_perm@ is Some,
            match tracked_ref_perm@ {
                Some(perm) => {
                    &&& !obj_ptr.is_null()
                    &&& P::ptr_perm_match(obj_ptr, perm.resource())
                    &&& perm.resource().inv()
                    &&& perm.registered_in(self.registry_id())
                },
                None => obj_ptr.is_null(),
            },
    )]
    fn load_read_token(&self) -> *mut <P as NonNullPtr>::Target {
        proof_decl! {
            let tracked mut tracked_ref_perm: Option<RcuReadToken<P>> = None;
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
                if g.current is Some {
                    let tracked registered = g.tracked_witness(g.current->0.id());
                    let tracked mut pool = g.current.tracked_take();
                    let tracked perm = pool.split();
                    tracked_ref_perm = Some(RcuReadToken { perm, registered });
                    g.current = Some(pool);
                }
            }
        };
        proof_with! { |= Tracked(tracked_ref_perm) }
        obj_ptr
    }

    #[verus_spec(r =>
        ensures
            r.type_inv(),
            r.rcu.is_nullable() == self.is_nullable(),
            !self.is_nullable() ==> r.tracked_ref_perm@ is Some,
    )]
    fn read(&self) -> RcuReadGuardInner<'_, P> {
        let guard = disable_preempt();
        proof_decl! {
            let tracked mut tracked_ref_perm: Option<RcuReadToken<P>> = None;
        }
        let obj_ptr = #[verus_spec(with => Tracked(tracked_ref_perm))]
        self.load_read_token();
        RcuReadGuardInner {
            obj_ptr,
            rcu: self,
            _inner_guard: guard,
            tracked_ref_perm: Tracked(tracked_ref_perm),
        }
    }

    #[verus_spec(r => ensures r.inv())]
    pub fn read_with<'a>(&'a self, _guard: &'a dyn InAtomicMode) -> Option<P::Ref<'a>> {
        proof_decl! {
            let tracked mut tracked_ref_perm: Option<RcuReadToken<P>> = None;
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
            let tracked tracked_ref_perm: P::RefPermission<'a> =
                P::tracked_borrow_perm_as_ref_perm(tracked_ref_perm.tracked_borrow());
        }
        // SAFETY:
        // 1. This pointer is not NULL.
        // 2. The `_guard` guarantees atomic mode for the duration of lifetime
        //    `'a`, the pointer is valid because other writers won't release the
        //    allocation until this task passes the quiescent state.
        NonNull::new(obj_ptr).map(
            |ptr| -> (reference: P::Ref<'a>)
                requires
                    P::ptr_perm_match(ptr.as_ptr(), P::ref_perm_view_permission(tracked_ref_perm)),
                    tracked_ref_perm.inv(),
                ensures
                    reference.inv(),
                {
                    unsafe { P::raw_as_ref(ptr, Tracked(tracked_ref_perm)) }
                },
        )
    }
}

/*
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
*/

/// The inner implementation of both [`RcuReadGuard`] and [`RcuOptionReadGuard`].
struct RcuReadGuardInner<'a, P: NonNullPtr> {
    obj_ptr: *mut <P as NonNullPtr>::Target,
    rcu: &'a RcuInner<P>,
    _inner_guard: DisabledPreemptGuard,
    tracked_ref_perm: Tracked<Option<RcuReadToken<P>>>,
}

#[verus_verify]
impl<'a, P: NonNullPtr + Send> RcuReadGuardInner<'a, P> {
    #[inline]
    #[verus_spec(r =>
        ensures
            self.tracked_ref_perm@ is Some ==> r is Some,
            r.inv(),
    )]
    fn get<'b>(&'b self) -> Option<P::Ref<'b>> {
        proof {
            use_type_invariant(self);
        }

        // SAFETY: The guard ensures that `P` will not be dropped. Thus, `P`
        // outlives the lifetime of `&self`. Additionally, during this period,
        // it is impossible to create a mutable reference to `P`.
        NonNull::new(self.obj_ptr).map(
            |ptr| -> (reference: P::Ref<'b>)
                requires
                    self.tracked_ref_perm@ is Some,
                    P::ptr_perm_match(ptr.as_ptr(), self.tracked_ref_perm->0.resource()),
                    self.tracked_ref_perm->0.resource().inv(),
                ensures
                    reference.inv(),
                {
                    unsafe {
                        P::raw_as_ref(
                            ptr,
                            Tracked(
                                P::tracked_borrow_perm_as_ref_perm(
                                    self.tracked_ref_perm.tracked_borrow().tracked_borrow(),
                                ),
                            ),
                        )
                    }
                },
        )
    }

    #[verus_spec(r =>
        requires
            self.rcu.is_nullable() || new_ptr is Some,
            new_ptr.inv(),
        ensures
            new_ptr is Some && r is Err ==> r->Err_0 is Some,
            r matches Err(pointer) ==> pointer.inv(),
    )]
    fn compare_exchange(self, new_ptr: Option<P>) -> Result<(), Option<P>> {
        let obj_ptr = self.obj_ptr;
        proof {
            use_type_invariant(&self);
            use_type_invariant(self.rcu);
        }
        proof_decl! {
            let tracked mut tracked_ref_perm = self.tracked_ref_perm.get();
            let tracked mut err_new_perm: Option<Option<<P as NonNullPtr>::Permission>> = None;
        }
        let (new_ptr, Tracked(new_perm)) = if let Some(new_ptr) = new_ptr {
            // <P as NonNullPtr>::into_raw(new_ptr).as_ptr()
            let (ptr, Tracked(perm)) = <P as NonNullPtr>::into_raw(new_ptr);
            (ptr.as_ptr(), Tracked(Some(perm)))
        } else {
            (core::ptr::null_mut(), Tracked(None))
        };
        let res =
            atomic_with_ghost! {
            self.rcu.ptr => compare_exchange(obj_ptr, new_ptr);
            update _prev -> next;
            returning res;
            ghost g => {
                if res is Ok {
                    g.tracked_replace(_prev, new_perm);
                } else {
                    err_new_perm = Some(new_perm);
                }
                if tracked_ref_perm is Some {
                    g.tracked_return_token(tracked_ref_perm.tracked_unwrap());
                }
            }
        };
        if res.is_ok() {
            if let Some(p) = NonNull::new(obj_ptr) {
                // SAFETY:
                // 1. The pointer was previously returned by `into_raw`.
                // 2. The pointer is removed from the RCU slot so that no one will
                //    use it after the end of the current grace period. The removal
                //    is done atomically, so it will only be dropped once.
                // unsafe { delay_drop::<P>(p) };
            }
            Ok(())
        } else {
            let Some(new_nonnull) = NonNull::new(new_ptr) else {
                return Err(None);
            };
            proof_decl! {
                let tracked new_perm = err_new_perm.tracked_unwrap().tracked_unwrap();
            }
            // SAFETY:
            // 1. It was previously returned by `into_raw`.
            // 2. The `compare_exchange` fails so the pointer will not
            //    be used by other threads via reading the RCU primitive.
            Err(Some(unsafe { <P as NonNullPtr>::from_raw(new_nonnull, Tracked(new_perm)) }))
        }
    }

    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    #[inline]
    #[verus_spec]
    fn drop(self) {
        let rcu = self.rcu;
        let obj_ptr = self.obj_ptr;
        proof {
            use_type_invariant(&self);
            use_type_invariant(rcu);
        }
        proof_decl! {
            let tracked mut tracked_ref_perm = self.tracked_ref_perm.get();
        }
        atomic_with_ghost! {
            rcu.ptr => load();
            update prev -> _next;
            returning _loaded;
            ghost g => {
                if tracked_ref_perm is Some {
                    g.tracked_return_token(tracked_ref_perm.tracked_unwrap());
                }
            }
        };
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> Rcu<P> {
    /// Creates a new RCU primitive with the given pointer `pointer`.
    #[verus_spec(requires pointer.inv())]
    pub fn new(pointer: P) -> Self {
        Self(
            #[verus_spec(with Ghost(false))]
            RcuInner::new(pointer),
        )
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
    #[verus_spec(requires new_ptr.inv())]
    pub fn update(&self, new_ptr: P) {
        self.0.update(Some(new_ptr));
    }

    /// Retrieves a read guard for the RCU primitive.
    ///
    /// The guard allows read access to the data protected by RCU, as well
    /// as the ability to do compare-and-exchange.
    #[inline]
    pub fn read(&self) -> RcuReadGuard<'_, P> {
        proof {
            use_type_invariant(self);
        }
        RcuReadGuard(self.0.read())
    }
    // #[inline]
    // pub fn read_with<'a, G: AsAtomicModeGuard + ?Sized>(&'a self, guard: &'a G) -> P::Ref<'a> where
    //     P: NonNullPtr,
    // {
    //     self.0.read_with(guard.as_atomic_mode_guard()).unwrap()
    // }

}

impl<P: NonNullPtr + Send> RcuOption<P> {
    /// Creates a new RCU primitive that contains nothing.
    ///
    /// This is a constant equivalence to [`RcuOption::new(None)`].
    #[inline(always)]
    pub const fn new_none() -> Self {
        Self(RcuInner::new_none())
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuOption<P> {
    /// Creates a new RCU primitive with the given pointer.
    #[verus_spec(requires pointer.inv())]
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
    #[verus_spec(requires new_ptr.inv())]
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
        proof {
            use_type_invariant(self);
        }
        RcuOptionReadGuard(self.0.read())
    }
}

#[verus_verify]
impl<P: NonNullPtr + Send> RcuReadGuard<'_, P> {
    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    #[inline]
    pub fn drop(self) {
        self.0.drop();
    }

    /// Gets the reference of the protected data.
    #[inline]
    #[verus_spec(r => ensures r.inv())]
    pub fn get<'a>(&'a self) -> P::Ref<'a> {
        proof {
            use_type_invariant(self);
        }
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
    #[inline]
    #[verus_spec(r =>
        requires new_ptr.inv(),
        ensures r matches Err(pointer) ==> pointer.inv(),
    )]
    pub fn compare_exchange(self, new_ptr: P) -> Result<(), P> {
        self.0.compare_exchange(Some(new_ptr)).map_err(
            |err| -> (pointer: P)
                requires
                    err is Some,
                    err.inv(),
                ensures
                    pointer.inv(),
                { err.unwrap() },
        )
    }
}

/*
impl<P: NonNullPtr> AsAtomicModeGuard for RcuReadGuard<'_, P> {
    fn as_atomic_mode_guard(&self) -> &dyn InAtomicMode {
        self.0.inner_guard.as_atomic_mode_guard()
    }
}*/

#[verus_verify]
impl<P: NonNullPtr + Send> RcuOptionReadGuard<'_, P> {
    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    #[inline]
    pub fn drop(self) {
        self.0.drop();
    }

    #[inline]
    #[verus_spec(r => ensures r.inv())]
    pub fn get<'a>(&'a self) -> Option<P::Ref<'a>> {
        self.0.get()
    }

    #[inline]
    pub fn is_none(&self) -> bool {
        self.0.obj_ptr.is_null()
    }

    #[inline]
    #[verus_spec(r =>
        requires new_ptr.inv(),
        ensures r matches Err(pointer) ==> pointer.inv(),
    )]
    pub fn compare_exchange(self, new_ptr: Option<P>) -> Result<(), Option<P>> {
        proof {
            use_type_invariant(&self);
        }
        self.0.compare_exchange(new_ptr)
    }
}

/*
impl<P: NonNullPtr> AsAtomicModeGuard for RcuOptionReadGuard<'_, P> {
    fn as_atomic_mode_guard(&self) -> &dyn InAtomicMode {
        self.0.inner_guard.as_atomic_mode_guard()
    }
}
*/

/*
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
} */

/// A wrapper to delay calling destructor of `T` after the RCU grace period.
///
/// Upon dropping this structure, a callback will be registered to the global
/// RCU monitor and the destructor of `T` will be delayed until the callback.
///
/// [`RcuDrop<T>`] is guaranteed to have the same layout as `T`. You can also
/// access the inner value safely via [`RcuDrop<T>`].
#[verifier::allow(autoderive_clone_without_spec)]
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
    /// Creates a new [`RcuDrop<T>`] that wraps the given value.
    #[inline]
    #[verus_spec(r =>
        ensures
            r@ == value,
    )]
    pub fn new(value: T) -> Self {
        Self { value: ManuallyDrop::new(value) }
    }/*
    /// Extracts the value from the `RcuDrop` container.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the returned value will be dropped after
    /// all the threads cannot access it anymore. Specifically, dropping it
    /// after the RCU grace period is guaranteed to be safe.
    ///
    /// Note that panic unwinding may cause the returned value to be dropped
    /// immediately, which is not sound. Therefore, the caller must forget the
    /// [`PanicGuard`] after it ensures that the value will be dropped at the
    /// correct time.
    pub(crate) unsafe fn into_inner(slot: RcuDrop<T>) -> (T, PanicGuard) {
        let mut slot = ManuallyDrop::new(slot);
        let panic_guard = PanicGuard::new();
        // SAFETY: The `slot` will not be used after this point.
        let val = unsafe { ManuallyDrop::take(&mut slot.value) };
        (val, panic_guard)
    }
    */

}

#[verus_verify]
impl<T: Send + 'static> Deref for RcuDrop<T> {
    type Target = T;

    #[verus_spec(r =>
        ensures
            *r == self@,
    )]
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

/*
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
pub(crate) unsafe fn finish_grace_period() {
    let rcu_monitor = RCU_MONITOR.get().unwrap();
    // SAFETY: The caller ensures safety.
    unsafe {
        rcu_monitor.finish_grace_period();
    }
}

*/

exec static RCU_MONITOR: Once<RcuMonitor, RcuMonitorInvariant, RcuMonitorPred>
    ensures
        RCU_MONITOR.wf(),
        RCU_MONITOR.inv() == RcuMonitorPred,
{
    Once::new(Ghost(RcuMonitorPred))
}

pub(super) fn init() {
    RCU_MONITOR.init(RcuMonitor::new_data());
}

} // verus!
verus! {

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
        &&& self.0.is_nullable()
    }
}

impl<P: NonNullPtr> Rcu<P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& !self.0.is_nullable()
    }
}

impl<'a, P: NonNullPtr> RcuReadGuard<'a, P> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.0.type_inv()
        &&& !self.0.rcu.is_nullable()
        &&& self.0.tracked_ref_perm@ is Some
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
        match self.tracked_ref_perm@ {
            Some(perm) => {
                &&& !self.obj_ptr.is_null()
                &&& P::ptr_perm_match(self.obj_ptr, perm.resource())
                &&& perm.resource().inv()
                &&& perm.registered_in(self.rcu.registry_id())
            },
            None => self.obj_ptr.is_null(),
        }
    }
}

impl<P: NonNullPtr + Send> Inv for Rcu<P> {
    closed spec fn inv(self) -> bool {
        self.type_inv()
    }
}

} // verus!
