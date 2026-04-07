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

struct_with_invariants! {

/// A mutex with waitqueue.
pub struct Mutex<T  /* : ?Sized */ > {
    lock: AtomicBool<_, Option<PointsTo<T>>, _>,
    queue: WaitQueue,
    // val: UnsafeCell<T>,
    val: PCell<T>,
}

closed spec fn wf(self) -> bool {
    invariant on lock with (val) is (v: bool, g: Option<PointsTo<T>>) {
        let active_guard = g is None;
        &&& v <==> active_guard
        &&& g is Some ==> g->Some_0.id() == val.id()
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
    pub const fn new(val: T) -> Self {
        let (val, Tracked(perm)) = PCell::new(val);
        Self {
            lock: AtomicBool::new(
                Ghost(val),
                false,
                Tracked(Some(perm)),
            ),
            queue: WaitQueue::new(),
            val: val,
        }
    }
}

#[verus_verify]
impl<T  /* : ?Sized */ > Mutex<T> {
    /// Acquires the mutex.
    ///
    /// This method runs in a block way until the mutex can be acquired.
    #[track_caller]
    pub fn lock(&self) -> MutexGuard<'_, T> {
        self.queue.wait_until(|| self.try_lock())
    }

    /// Tries to acquire the mutex immediately.
    #[verus_spec]
    pub fn try_lock(&self) -> Option<MutexGuard<T>> {
        // Cannot be reduced to `then_some`, or the possible dropping of the temporary
        // guard will cause an unexpected unlock.
        // SAFETY: The lock is successfully acquired when creating the guard.
        proof_decl! {
            let tracked mut locked_state: Option<PointsTo<T>> = None;
        }
        {#[verus_spec(with => Tracked(locked_state))] self.acquire_lock()}.then(
            || requires 
                locked_state is Some,
                locked_state -> Some_0.id() == self.cell_id(),
                {unsafe { proof_with!{Tracked(locked_state.tracked_unwrap())};
                            MutexGuard::new(self) }})
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
    #[verus_spec(
        with
            Tracked(perm): Tracked<PointsTo<T>>,
        requires
            perm.id() == self.cell_id(),
    )]
    fn unlock(&self)
    {
        proof_with!(Tracked(perm));
        self.release_lock();
        self.queue.wake_one();
    }

    #[verus_spec(ret =>
        with
            -> locked_state: Tracked<Option<PointsTo<T>>>,
        ensures
            ret ==> locked_state@ is Some && locked_state@->Some_0.id() == self.cell_id(),
            !ret ==> locked_state@ is None,
    )]
    fn acquire_lock(&self) -> bool {
        proof_decl! {
            let tracked mut locked_state: Option<PointsTo<T>> = None;
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
                    let tracked perm = perms.tracked_take();
                    locked_state = Some(perm);
                }
            }
        }.is_ok()
    }

    #[verus_spec(
        with
            Tracked(perm): Tracked<PointsTo<T>>,
        requires
            perm.id() == self.cell_id(),
    )]
    fn release_lock(&self)
    {
        proof! {
            use_type_invariant(self);
        }
        atomic_with_ghost! {
            self.lock => store(false);
            ghost perms => {
                perms = Some(perm);
            }
        }
    }
}

/* impl<T: /* ?Sized +  */fmt::Debug> fmt::Debug for Mutex<T> {
    #[verifier::external_body]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.val, f)
    }
} */
#[verifier::external]
unsafe impl<T: /*?Sized + */Send> Send for Mutex<T> {}
#[verifier::external]
unsafe impl<T: /*?Sized + */Send> Sync for Mutex<T> {}

/// A guard that provides exclusive access to the data protected by a [`Mutex`].
#[verifier::reject_recursive_types(T)]
#[clippy::has_significant_drop]
#[must_use]
#[verus_verify]
pub struct MutexGuard<'a, T  /* : ?Sized */ > {
    mutex: &'a Mutex<T>,
    #[cfg(verus_keep_ghost_body)]
    v_perm: Tracked<PointsTo<T>>,
}

impl<'a, T  /* : ?Sized */ > MutexGuard<'a, T> {
    /// # Safety
    ///
    /// The caller must ensure that the given reference of [`Mutex`] lock has been successfully acquired
    /// in the current context. When the created [`MutexGuard`] is dropped, it will unlock the [`Mutex`].
    #[verus_spec(ret =>
        with
            Tracked(perm): Tracked<PointsTo<T>>,
        requires
            perm.id() == mutex.cell_id(),
    )]
    unsafe fn new(mutex: &'a Mutex<T>) -> (r: MutexGuard<'a, T>)
    {
        proof_with!{v_perm: Tracked(perm)}
        MutexGuard { mutex }
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.v_perm@.id() == self.mutex.cell_id()
    }

    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for
    /// `Drop` is incomplete for now.
    #[verus_spec]
    pub fn drop(self) {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(&*self.mutex);
        }
        proof_with!{self.v_perm}
        self.mutex.release_lock();
        self.mutex.queue.wake_one();
    }
}

impl<T/* : ?Sized */> Deref for MutexGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        proof! {
            use_type_invariant(self);
        }
        // unsafe { &*self.mutex.val.get() }
        self.mutex.val.borrow(Tracked(self.v_perm.borrow()))
    }
}

/* impl<T/* : ?Sized */> DerefMut for MutexGuard<'_, T> {
    #[verifier::external_body]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.mutex.val.get() }
    }
} */

/* impl<T  /* : ?Sized */ > Drop for MutexGuard<'_, T> {
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        self.mutex.unlock(Tracked(perm));
    }
} */

/* impl<T: /* ?Sized + */ fmt::Debug> fmt::Debug for MutexGuard<'_, T> {
    #[verifier::external_body]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
} */

impl<T  /* : ?Sized */ > !Send for MutexGuard<'_, T> {}

// unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}
impl<'a, T  /* : ?Sized */ > MutexGuard<'a, T> {
    /// Returns the [`Mutex`] associated with this guard.
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
