use std::cell::Cell;

use vstd::prelude::*;
use vstd::cell::*;

verus! {

// TODO: Implement the queue spinlock protocol.
/// A lock body for a queue spinlock.
///
/// Each memory location that is shared between CPUs must have a unique
/// instance of this type.
#[repr(C)]
// TODO: Implement
#[verifier::external_body]
pub struct LockBody {
    // val: u32,
    locked: Cell<bool>,
}

// TODO: Implement Sync
// SAFETY: The structure will be used for synchronization by design.
// unsafe impl Sync for LockBody {}
// TODO: Implement Send
// SAFETY: When sending a lock body there will be no shared references to it.
// So there's no race that could happen.
// unsafe impl Send for LockBody {}
impl LockBody {
    /// Create a new queued spinlock, which is unlocked.
    // TODO: Implement
    #[verifier::external_body]
    pub(crate) const fn new() -> Self {
        // Self {
        //     val: ManuallyDrop::new(UnsafeCell::new(0)),
        // }
        Self { locked: Cell::new(false) }
    }

    /// Create a new queued spinlock, which is locked.
    ///
    /// To use it, the caller must subsequently call `unlock` to release the
    /// lock for others.
    // TODO: Implement
    #[verifier::external_body]
    pub(crate) const fn new_locked() -> Self {
        // Self {
        //     val: ManuallyDrop::new(UnsafeCell::new(Self::LOCKED_VAL)),
        // }
        Self { locked: Cell::new(true) }
    }

    /// Try to lock the queued spinlock.
    ///
    /// If the lock is acquired successfully, return an acquired guard.
    /// Otherwise, return a guard that haven't acquired the lock.
    ///
    /// If it returns an acquired guard the critical section can commence.
    pub(crate) fn try_lock(&self) -> bool {
        self.try_lock_impl().is_ok()
    }

    /// Unlock the queued spin-lock.
    ///
    /// This function will release the lock and allow other CPUs to acquire the
    /// lock. Call this function after the critical section is finished.
    ///
    /// # Safety
    ///
    /// The caller must ensure the following properties:
    ///  - The lock is pinned after any one acquired it and before every one
    ///    unlocks it (i.e. no lock-stealing).
    ///  - The lock was acquired by the current CPU for once and not unlocked.
    ///  - preemption is disabled after the current CPU acquired the lock.
    // TODO: Implement
    #[verifier::external_body]
    pub(crate) fn unlock(&self) {
        // // 0,0,1 -> 0,0,0
        // unsafe {
        //     intrinsics::atomic_store_release(self.locked_ptr(), 0);
        // }
        // TODO: Implement unlock
        self.locked.set(false);
    }

    /// Lock the queued spinlock.
    ///
    /// This function will spin until the lock is acquired. When the function
    /// returns, the critical section can commence.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the current task is pinned to the current
    /// CPU.
    pub(crate) unsafe fn lock(&self) {
        // (queue tail, pending bit, lock value)
        //
        //              fast     :    slow                                  :    unlock
        //                       :                                          :
        // uncontended  (0,0,0) -:--> (0,0,1) ------------------------------:--> (*,*,0)
        //                       :       | ^--------.------.             /  :
        //                       :       v           \      \            |  :
        // pending               :    (0,1,1) +--> (0,1,0)   \           |  :
        //                       :       | ^--'              |           |  :
        //                       :       v                   |           |  :
        // uncontended           :    (n,x,y) +--> (n,0,0) --'           |  :
        //   queue               :       | ^--'                          |  :
        //                       :       v                               |  :
        // contended             :    (*,x,y) +--> (*,0,0) ---> (*,0,1) -'  :
        //   queue               :         ^--'                             :
        match self.try_lock_impl() {
            Ok(()) => {},
            Err(val) => {
                // Slow path. There are pending spinners or queued spinners.
                self.lock_slow(val);
            },
        }
    }

    #[verifier::external_body]
    /// Acquire the spinlock in a slow path.
    fn lock_slow(&self, mut lock_val: u32) {
        // TODO: Implement lock_slow
        self.locked.set(true);
    }

    /// Try to lock the spinlock in an optimistic path.
    ///
    /// If the lock is acquired successfully, return `Ok(())`. Otherwise, return
    /// `Err(prev_val)`.
    // TODO: Implement try_lock_impl
    #[verifier::external_body]
    fn try_lock_impl(&self) -> Result<(), u32> {
        unimplemented!()
    }

    /// Acquire the spinlock in a very-slow path.
    ///
    /// If we cannot lock optimistically (likely due to contention), we enqueue
    /// ourselves and spin on local MCS nodes.
    // TODO: Implement
    #[verifier::external_body]
    fn lock_enqueue(&self) {
        unimplemented!()
    }

    // TODO: Implement
    #[verifier::external_body]
    fn val_ptr(&self) -> *mut u32 {
        unimplemented!()
    }

    // TODO: Implement
    #[verifier::external_body]
    fn locked_ptr(&self) -> *mut u8 {
        unimplemented!()
    }

    // TODO: Implement
    #[verifier::external_body]
    fn pending_ptr(&self) -> *mut u8 {
        unimplemented!()
    }

    // TODO: Implement
    #[verifier::external_body]
    fn tail_ptr(&self) -> *mut u16 {
        unimplemented!()
    }

    // TODO: Implement
    #[verifier::external_body]
    fn locked_pending_ptr(&self) -> *mut u16 {
        unimplemented!()
    }
}

} // verus!
