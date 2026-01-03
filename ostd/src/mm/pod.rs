use vstd::prelude::*;
use vstd_extra::{
    array_ptr::{self, PointsToArray},
    prelude::ArrayPtr,
};

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
    ///
    /// This seems a bit awkward if we try to use `arrayptr` and then making a mutable
    /// reference from it as verus cannot do it now.
    #[verifier::external_body]
    fn as_bytes_mut(&mut self) -> (r: (*mut u8, usize))
        ensures
            r.1 == core::mem::size_of::<Self>(),
    {
        let ptr = self as *mut Self as *mut u8;
        let len = core::mem::size_of::<Self>();
        // unsafe { core::slice::from_raw_parts_mut(ptr, len) }
        (ptr, len)
    }
}

/// A marker trait for POD types that can be read or written with one instruction.
///
/// We currently rely on this trait to ensure that the memory operation created by
/// `ptr::read_volatile` and `ptr::write_volatile` doesn't tear. However, the Rust documentation
/// makes no such guarantee, and even the wording in the LLVM LangRef is ambiguous.
///
/// At this point, we can only _hope_ that this doesn't break in future versions of the Rust or
/// LLVM compilers. However, this is unlikely to happen in practice, since the Linux kernel also
/// uses "volatile" semantics to implement `READ_ONCE`/`WRITE_ONCE`.
pub trait PodOnce: Pod {

}

} // verus!

