// SPDX-License-Identifier: MPL-2.0
use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd_extra::prelude::*;

use alloc::sync::Arc;
//use core::sync::atomic::{fence, AtomicUsize, Ordering};

use super::{PreemptDisabled, RwLock, RwLockReadGuard, RwLockWriteGuard};

verus! {

/// A reference-counting pointer with read-write capabilities.
///
/// This is essentially `Arc<RwLock<T>>`, so it can provide read-write capabilities through
/// [`RwArc::read`] and [`RwArc::write`].
///
/// In addition, this allows to derive another reference-counting pointer with read-only
/// capabilities ([`RoArc`]) via [`RwArc::clone_ro`].
///
/// The purpose of having this type is to allow lockless (read) access to the underlying data when
/// there is only one [`RwArc`] instance for the particular allocation (note that there can be any
/// number of [`RoArc`] instances for that allocation). See the [`RwArc::get`] method for more
/// details.
pub struct RwArc<T>(Arc<Inner<T>>);

/// A reference-counting pointer with read-only capabilities.
///
/// This type can be created from an existing [`RwArc`] using its [`RwArc::clone_ro`] method. See
/// the type and method documentation for more details.
pub struct RoArc<T>(Arc<Inner<T>>);

struct_with_invariants!{
struct Inner<T> {
    data: RwLock<T, PreemptDisabled>,
    num_rw: AtomicUsize<_,int,_>,
}

closed spec fn wf(&self) -> bool {
  invariant on num_rw with (data) is (v:usize, g:int) {
    v == g
  }
}
}

impl<T> RwArc<T> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.0.wf()
        &&& self.0.num_rw.well_formed()
    }
}

impl<T> RwArc<T> {
    /// Creates a new `RwArc<T>`.
    pub fn new(data: T) -> (r: Self)
        ensures
            r.wf(),
    {
        //let inner = Inner { data: RwLock::new(data), num_rw: AtomicUsize::new(1) };
        let data = RwLock::new(data);
        let inner = Inner { data, num_rw: AtomicUsize::new(Ghost(data), 1, Tracked(1int)) };
        Self(Arc::new(inner))
    }

    /// Acquires the read lock for immutable access.
    pub fn read(&self) -> RwLockReadGuard<'_, T, PreemptDisabled> {
        self.0.data.read()
    }

    /// Acquires the write lock for mutable access.
    pub fn write(&self) -> RwLockWriteGuard<'_, T, PreemptDisabled> {
        self.0.data.write()
    }

    /*
    /// Returns an immutable reference if no other `RwArc` points to the same allocation.
    ///
    /// This method is cheap because it does not acquire a lock.
    ///
    /// It's still sound because:
    /// - The mutable reference to `self` and the condition ensure that we are exclusively
    ///   accessing the unique `RwArc` instance for the particular allocation.
    /// - There may be any number of [`RoArc`]s pointing to the same allocation, but they may only
    ///   produce immutable references to the underlying data.
    #[verifier::external_body]
    pub fn get(&mut self) -> Option<&T> {
        if self.0.num_rw.load(Ordering::Relaxed) > 1 {
            return None;
        }
        // This will synchronize with `RwArc::drop` to make sure its changes are visible to us.

        fence(Ordering::Acquire);

        let data_ptr = self.0.data.as_ptr();

        // SAFETY: The data is valid. During the lifetime, no one will be able to create a mutable
        // reference to the data, so it's okay to create an immutable reference like the one below.
        Some(unsafe { &*data_ptr })
    }
    */
    /// Clones a [`RoArc`] that points to the same allocation.
    pub fn clone_ro(&self) -> RoArc<T> {
        RoArc(self.0.clone())
    }
}

#[verus_verify]
impl<T> Clone for RwArc<T> {
    #[verus_spec]
    fn clone(&self) -> Self
        returns
            self,
    {
        proof!{
            use_type_invariant(self);
        }
        let inner = self.0.clone();
        // Note that overflowing the counter will make it unsound. But not to worry: the above
        // `Arc::clone` must have already aborted the kernel before this happens.
        // inner.num_rw.fetch_add(1, Ordering::Relaxed);
        atomic_with_ghost! {
            inner.num_rw => fetch_add(1);
            ghost g => {
                assume(g < usize::MAX);
                g = g + 1;
            }
        };

        Self(inner)
    }
}

/*
impl<T> Drop for RwArc<T> {
    #[verifier::external_body]
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        self.0.num_rw.fetch_sub(1, Ordering::Release);
    }
}*/

impl<T: Clone> RwArc<T> {
    /// Returns the contained value by cloning it.
    pub fn get_cloned(&self) -> T {
        let guard = self.read();
        guard.clone()
    }
}

impl<T> RoArc<T> {
    /// Acquires the read lock for immutable access.
    pub fn read(&self) -> RwLockReadGuard<'_, T, PreemptDisabled> {
        self.0.data.read()
    }
}

} // verus!
#[cfg(ktest)]
mod test {
    use super::*;
    use crate::prelude::*;

    #[ktest]
    fn lockless_get() {
        let mut rw1 = RwArc::new(1u32);
        assert_eq!(rw1.get(), Some(1).as_ref());

        let _ro = rw1.clone_ro();
        assert_eq!(rw1.get(), Some(1).as_ref());

        let rw2 = rw1.clone();
        assert_eq!(rw1.get(), None);

        drop(rw2);
        assert_eq!(rw1.get(), Some(1).as_ref());
    }
}
