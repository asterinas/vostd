use vstd::prelude::*;
use vstd_extra::array_ptr::{self, ArrayPtr, PointsToArray};

use core::mem::MaybeUninit;

verus! {

/// A trait for Plain Old Data (POD) types.
pub trait Pod: Copy + Sized {
    /// Creates a new instance of Pod type that is filled with zeroes.
    #[verifier::external_body]
    fn new_zeroed() -> Self {
        // SAFETY. An all-zero value of `T: Pod` is always valid.
        unsafe { core::mem::zeroed() }
    }

    /// Creates a new instance of Pod type with uninitialized content.
    #[verifier::external_body]
    fn new_uninit() -> Self {
        // SAFETY. A value of `T: Pod` can have arbitrary bits.
        #[allow(clippy::uninit_assumed_init)]
        unsafe { MaybeUninit::uninit().assume_init() }
    }

    /// As a slice of bytes.
    #[verifier::external_body]
    fn as_bytes<const N: usize>(&self) -> (slice: (
        ArrayPtr<u8, N>,
        Tracked<&array_ptr::PointsTo<u8, N>>,
    ))
        ensures
            slice.1@.value().len() == core::mem::size_of::<Self>(),
            slice.1@.wf(),
            slice.0.addr() == slice.1@.addr(),
    {
        let ptr = self as *const Self as *const u8;

        (ArrayPtr::from_addr(ptr as usize), Tracked::assume_new())
    }

    /// As a mutable slice of bytes.
    ///
    /// Note that this does not create the permission to mutate the Pod value as
    /// mutable reference is not yet supported in Verus.
    ///
    /// Instead, the caller must uphold a separate permission to mutate the Pod value.
    #[verifier::external_body]
    fn as_bytes_mut(&mut self) -> (r: (usize, usize))
        ensures
            r.1 == core::mem::size_of::<Self>(),
    {
        let ptr = self as *mut Self as usize;
        let len = core::mem::size_of::<Self>();

        (ptr, len)
    }
}

/// A marker trait for POD types that can be read or written with one instruction.
///
/// We currently rely on this trait to ensure that the memory operation created by
/// [`core::ptr::read_volatile`] and [`core::ptr::write_volatile`] doesn't tear. However, the Rust documentation
/// makes no such guarantee, and even the wording in the LLVM LangRef is ambiguous.
///
/// At this point, we can only _hope_ that this doesn't break in future versions of the Rust or
/// LLVM compilers. However, this is unlikely to happen in practice, since the Linux kernel also
/// uses "volatile" semantics to implement `READ_ONCE`/`WRITE_ONCE`.
pub trait PodOnce: Pod {

}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "riscv64",
    target_arch = "loongarch64",
))]
#[verusfmt::skip]
mod pod_once_impls {
    use super::PodOnce;

    // impl PodOnce for u8 {}
    // impl PodOnce for u16 {}
    // impl PodOnce for u32 {}
    // impl PodOnce for u64 {}
    // impl PodOnce for usize {}
    // impl PodOnce for i8 {}
    // impl PodOnce for i16 {}
    // impl PodOnce for i32 {}
    // impl PodOnce for i64 {}
    // impl PodOnce for isize {}

    /// Checks whether the memory operation created by [`core::ptr::read_volatile`] and
    /// [`core::ptr::write_volatile`] doesn't tear.
    ///
    /// Note that the Rust documentation makes no such guarantee, and even the wording in the LLVM
    /// LangRef is ambiguous. But this is unlikely to break in practice because the Linux kernel
    /// also uses "volatile" semantics to implement `READ_ONCE`/`WRITE_ONCE`.
    ///
    /// # Verified Properties
    /// ## Postconditions
    /// Returns `true` if and only if the memory operation created by [`core::ptr::read_volatile`] and
    /// [`core::ptr::write_volatile`] doesn't tear for type `T` (size <= 8 bytes).
    pub(super) const fn is_non_tearing<T: PodOnce>() -> bool
        returns
            core::mem::size_of::<T>() == 1
            || core::mem::size_of::<T>() == 2
            || core::mem::size_of::<T>() == 4
            || core::mem::size_of::<T>() == 8,
    {
        let size = core::mem::size_of::<T>();
        size == 1 || size == 2 || size == 4 || size == 8
    }
}

} // verus!
