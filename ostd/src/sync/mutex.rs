// SPDX-License-Identifier: MPL-2.0
use vstd::atomic_ghost::*;
use vstd::cell::{self, pcell::*};
use vstd::prelude::*;
use vstd_extra::resource::ghost_resource::excl::*;

use alloc::sync::Arc;
use core::{
    cell::UnsafeCell,
    fmt,
    ops::{Deref, DerefMut},
    sync::atomic::Ordering,
};

use super::WaitQueue;

verus! {

tracked struct MutexPerms<T> {
    cell_perm: Option<PointsTo<T>>,
    guard_token: Option<UniqueToken>,
}

struct_with_invariants! {

/// A mutex with waitqueue.
pub struct Mutex<T  /* : ?Sized */ > {
    lock: AtomicBool<_, MutexPerms<T>, _>,
    queue: WaitQueue,
    // val: UnsafeCell<T>,
    val: PCell<T>,
}

closed spec fn wf(self) -> bool {
    invariant on lock with (val) is (v: bool, g: MutexPerms<T>) {
        let active_guard = g.guard_token is None;
        &&& v <==> active_guard
        &&& active_guard <==> g.cell_perm is None
        &&& g.cell_perm is Some ==> g.cell_perm->Some_0.id() == val.id()
        &&& g.guard_token is Some ==> g.guard_token->Some_0.wf()
    }
}
}

impl<T> Mutex<T> {
    pub closed spec fn cell_id(self) -> cell::CellId {
        self.val.id()
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    /// Creates a new mutex.
    pub const fn new(val: T) -> (r: Self)
        ensures
            r.type_inv(),
    {
        let (val, Tracked(perm)) = PCell::new(val);
        proof_decl! {
            let tracked guard_token = UniqueToken::alloc(());
        }
        Self {
            lock: AtomicBool::new(
                Ghost(val),
                false,
                Tracked(MutexPerms { cell_perm: Some(perm), guard_token: Some(guard_token) }),
            ),
            queue: WaitQueue::new(),
            val: val,
        }
    }
}

impl<T  /* : ?Sized */ > Mutex<T> {
    /// Acquires the mutex.
    ///
    /// This method runs in a block way until the mutex can be acquired.
    #[track_caller]
    #[verifier::external_body]
    pub fn lock(&self) -> MutexGuard<T> {
        self.queue.wait_until(|| self.try_lock())
    }

    /// Acquires the mutex through an [`Arc`].
    ///
    /// The method is similar to [`lock`], but it doesn't have the requirement
    /// for compile-time checked lifetimes of the mutex guard.
    ///
    /// [`lock`]: Self::lock
    #[track_caller]
    #[verifier::external_body]
    pub fn lock_arc(self: &Arc<Self>) -> ArcMutexGuard<T> {
        self.queue.wait_until(|| self.try_lock_arc())
    }

    /// Tries Acquire the mutex immediately.
    #[verus_spec]
    pub fn try_lock(&self) -> Option<MutexGuard<T>> {
        // Cannot be reduced to `then_some`, or the possible dropping of the temporary
        // guard will cause an unexpected unlock.
        // SAFETY: The lock is successfully acquired when creating the guard.
        proof_decl! {
            let tracked mut locked_state: Option<(PointsTo<T>, UniqueToken)> = None;
        }
        if #[verus_spec(with => Tracked(locked_state))] self.acquire_lock() {
            proof_decl! {
                let tracked (perm, guard_token) = locked_state.tracked_unwrap();
            }
            Some(unsafe {
                MutexGuard::new(
                    self,
                    Tracked(perm),
                    Tracked(guard_token),
                )
            })
        } else {
            None
        }
    }

    /// Tries acquire the mutex through an [`Arc`].
    ///
    /// The method is similar to [`try_lock`], but it doesn't have the requirement
    /// for compile-time checked lifetimes of the mutex guard.
    ///
    /// [`try_lock`]: Self::try_lock
    #[verus_spec]
    pub fn try_lock_arc(self: &Arc<Self>) -> Option<ArcMutexGuard<T>> {
        proof_decl! {
            let tracked mut locked_state: Option<(PointsTo<T>, UniqueToken)> = None;
        }
        if #[verus_spec(with => Tracked(locked_state))] self.acquire_lock() {
            proof_decl! {
                let tracked (perm, guard_token) = locked_state.tracked_unwrap();
            }
            Some(ArcMutexGuard {
                mutex: self.clone(),
                v_perm: Tracked(perm),
                v_guard_token: Tracked(guard_token),
            })
        } else {
            None
        }
    }

    /* /// Returns a mutable reference to the underlying data.
    ///
    /// This method is zero-cost: By holding a mutable reference to the lock, the compiler has
    /// already statically guaranteed that access to the data is exclusive.
    #[verifier::external_body]
    pub fn get_mut(&mut self) -> &mut T {
        self.val.get_mut()
    } */

    /// Releases the mutex and wake up one thread which is blocked on this mutex.
    #[verifier::external_body]
    fn unlock(&self) {
        self.release_lock();
        self.queue.wake_one();
    }

    #[verus_spec(ret =>
        with
            -> locked_state: Tracked<Option<(PointsTo<T>, UniqueToken)>>,
        ensures
            ret ==> locked_state@ is Some && locked_state@->Some_0.0.id() == self.cell_id(),
            !ret ==> locked_state@ is None,
    )]
    fn acquire_lock(&self) -> bool {
        proof_decl! {
            let tracked mut locked_state: Option<(PointsTo<T>, UniqueToken)> = None;
        }
        proof! {
            use_type_invariant(self);
        }
        proof_with! { |= Tracked(locked_state) }
        atomic_with_ghost! {
            self.lock => compare_exchange(false, true);
            returning res;
            ghost perms => {
                if res is Ok {
                    let tracked perm = perms.cell_perm.tracked_take();
                    let tracked guard_token = perms.guard_token.tracked_take();
                    locked_state = Some((perm, guard_token));
                }
            }
        }.is_ok()
    }

    #[verus_spec(
        with
            Tracked(perm): Tracked<PointsTo<T>>,
            Tracked(guard_token): Tracked<UniqueToken>,
        requires
            perm.id() == self.cell_id(),
            guard_token.wf(),
    )]
    fn release_lock(&self) {
        proof! {
            use_type_invariant(self);
        }
        atomic_with_ghost! {
            self.lock => store(false);
            ghost perms => {
                perms = MutexPerms { cell_perm: Some(perm), guard_token: Some(guard_token) };
            }
        }
    }
}

/* impl<T: /* ?Sized +  */fmt::Debug> fmt::Debug for Mutex<T> {
    #[verifier::external_body]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.val, f)
    }
}

unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}
unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {} */

#[verifier::reject_recursive_types(T)]
#[clippy::has_significant_drop]
#[must_use]
pub struct MutexGuard<'a, T  /* : ?Sized */ > {
    mutex: &'a Mutex<T>,
    v_perm: Tracked<PointsTo<T>>,
    v_guard_token: Tracked<UniqueToken>,
}

impl<'a, T  /* : ?Sized */ > MutexGuard<'a, T> {
    /// # Safety
    ///
    /// The caller must ensure that the given reference of [`Mutex`] lock has been successfully acquired
    /// in the current context. When the created [`MutexGuard`] is dropped, it will unlock the [`Mutex`].
    unsafe fn new(
        mutex: &'a Mutex<T>,
        Tracked(perm): Tracked<PointsTo<T>>,
        Tracked(guard_token): Tracked<UniqueToken>,
    ) -> (r: MutexGuard<'a, T>)
        requires
            perm.id() == mutex.cell_id(),
        ensures
            r.type_inv(),
    {
        MutexGuard { mutex, v_perm: Tracked(perm), v_guard_token: Tracked(guard_token) }
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.v_perm@.id() == self.mutex.cell_id()
    }
}

/// An guard that provides exclusive access to the data protected by a `Arc<Mutex>`.
#[verifier::reject_recursive_types(T)]
#[clippy::has_significant_drop]
#[must_use]
pub struct ArcMutexGuard<T  /* : ?Sized */ > {
    mutex: Arc<Mutex<T>>,
    v_perm: Tracked<PointsTo<T>>,
    v_guard_token: Tracked<UniqueToken>,
}

impl<T> ArcMutexGuard<T> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.v_perm@.id() == self.mutex.cell_id()
    }
}

/* impl<T/* : ?Sized */> Deref for MutexGuard<'_, T> {
    type Target = T;

    #[verifier::external_body]
    fn deref(&self) -> &Self::Target {
        // unsafe { &*self.mutex.val.get() }
        self.mutex.val.borrow(Tracked(read_perm))
    }
}

impl<T/* : ?Sized */> DerefMut for MutexGuard<'_, T> {
    #[verifier::external_body]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.mutex.val.get() }
    }
} */

impl<T  /* : ?Sized */ > Drop for MutexGuard<'_, T> {
    #[verifier::external_body]
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        self.mutex.unlock();
    }
}

impl<T> Drop for ArcMutexGuard<T> {
    #[verifier::external_body]
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        self.mutex.unlock();
    }
}

/* impl<T: /* ?Sized + */ fmt::Debug> fmt::Debug for MutexGuard<'_, T> {
    #[verifier::external_body]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
} */

impl<T  /* : ?Sized */ > !Send for MutexGuard<'_, T> {}

impl<T> !Send for ArcMutexGuard<T> {}

// unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}
impl<'a, T  /* : ?Sized */ > MutexGuard<'a, T> {
    #[verifier::external_body]
    pub fn get_lock(guard: &MutexGuard<'a, T>) -> &'a Mutex<T> {
        guard.mutex
    }
}

} // verus!
#[cfg(ktest)]
mod test {
    use super::*;
    use crate::prelude::*;

    // A regression test for a bug fixed in [#1279](https://github.com/asterinas/asterinas/pull/1279).
    #[ktest]
    fn test_mutex_try_lock_does_not_unlock() {
        let lock = Mutex::new(0);
        assert!(!lock.lock.load(Ordering::Relaxed));

        // A successful lock
        let guard1 = lock.lock();
        assert!(lock.lock.load(Ordering::Relaxed));

        // A failed `try_lock` won't drop the lock
        assert!(lock.try_lock().is_none());
        assert!(lock.lock.load(Ordering::Relaxed));

        // Ensure the lock is held until here
        drop(guard1);
    }
}
