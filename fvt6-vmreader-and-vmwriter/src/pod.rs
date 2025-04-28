use vstd::prelude::*;

use core::mem::MaybeUninit;

verus! {

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
    fn as_bytes(&self) -> (slice: &[u8])
        ensures
            slice.len() == core::mem::size_of::<Self>(),
    {
        let ptr = self as *const Self as *const u8;
        let len = core::mem::size_of::<Self>();
        unsafe { core::slice::from_raw_parts(ptr, len) }
    }

    /// As a mutable slice of bytes.
    #[verifier::external_body]
    fn as_bytes_mut(&mut self) -> (*mut u8, usize) {
        let ptr = self as *mut Self as *mut u8;
        let len = core::mem::size_of::<Self>();
        // unsafe { core::slice::from_raw_parts_mut(ptr, len) }
        (ptr, len)
    }
}

#[verifier::external]
pub fn as_bytes_mut_ex<T: Pod>(val: &mut T) -> &mut [u8] {
    let ptr = val as *mut T as *mut u8;
    let len = core::mem::size_of::<T>();
    unsafe { core::slice::from_raw_parts_mut(ptr, len) }
}

pub open spec fn pod_size_spec<T: Pod>() -> usize {
    core::mem::size_of::<T>()
}

pub open spec fn pod_pnt_is_aligned<T: Pod>(pnt: *const u8) -> bool {
    (pnt as usize) % pod_size_spec::<T>() == 0
}

pub open spec fn pod_mem_space_is_aligned<T: Pod>(avail: int) -> bool {
    avail % pod_size_spec::<T>() as int == 0
}

} // verus!
