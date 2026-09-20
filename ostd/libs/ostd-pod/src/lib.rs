//! This crate defines a marker trait for plain old data (POD).
#![no_std]

use vstd::prelude::*;
use vstd_extra::array_ptr::{self, ArrayPtr};

use core::mem::MaybeUninit;

verus! {

/// A marker trait for plain old data (POD).
///
/// A POD type `T:Pod` supports converting to and from arbitrary
/// `mem::size_of::<T>()` bytes _safely_.
/// For example, simple primitive types like `u8` and `i16`
/// are POD types. But perhaps surprisingly, `bool` is not POD
/// because Rust compiler makes implicit assumption that
/// a byte of `bool` has a value of either `0` or `1`.
/// Interpreting a byte of value `3` has a `bool` value has
/// undefined behavior.
///
/// # Safety
///
/// Marking a non-POD type as POD may cause undefined behaviors.
pub unsafe trait Pod: Copy + Sized {
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
        unsafe {
            MaybeUninit::uninit().assume_init()
        }
    }

    /// Creates a new instance from the given bytes.
    #[verus_spec(
        requires
            bytes@.len() >= core::mem::size_of::<Self>(),
        returns
            from_bytes_spec::<Self>(bytes@),
    )]
    fn from_bytes(bytes: &[u8]) -> Self {
        let mut new_self = Self::new_uninit();
        let copy_len = new_self.as_bytes().len();
        new_self.as_bytes_mut().copy_from_slice(&bytes[..copy_len]);
        proof {
            assert(new_self == decode_pod::<Self>(
                bytes@[0..core::mem::size_of::<Self>()],
            ));
        }
        new_self
    }

    /// As a slice of bytes.
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r.len() == core::mem::size_of::<Self>(),
            r@ == pod_bytes(*self),
    )]
    fn as_bytes(&self) -> &[u8] {
        let ptr = self as *const Self as *const u8;
        let len = core::mem::size_of::<Self>();
        unsafe { core::slice::from_raw_parts(ptr, len) }
    }

    /// As a mutable slice of bytes.
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r.len() == core::mem::size_of::<Self>(),
            final(r)@ == pod_bytes(*final(self)),
            *final(self) == decode_pod::<Self>(final(r)@),
    )]
    fn as_bytes_mut(&mut self) -> &mut [u8] {
        let ptr = self as *mut Self as *mut u8;
        let len = core::mem::size_of::<Self>();
        unsafe { core::slice::from_raw_parts_mut(ptr, len) }
    }
}

/// The value decoded from the first `size_of::<T>()` input bytes.
pub open spec fn from_bytes_spec<T>(bytes: Seq<u8>) -> T {
    decode_pod::<T>(bytes[0..core::mem::size_of::<T>()])
}

/// Spec function: the byte representation of a [`Pod`] value.
///
/// This is uninterpreted — the actual byte mapping depends on `T`'s layout
/// (endianness, padding, etc.) which we don't model. Callers use this to
/// relate writes and reads of the same value through memory.
pub uninterp spec fn pod_bytes<T>(val: T) -> Seq<u8>;

/// The Pod value whose byte representation equals `bytes` (when one exists).
///
/// Defined via `choose`; if no Pod value maps to `bytes`, the result is
/// arbitrary. Callers should obtain the relevant existence fact from a checked
/// byte conversion before relying on the returned value.
pub open spec fn decode_pod<T>(bytes: Seq<u8>) -> T {
    choose|val: T| pod_bytes::<T>(val) == bytes
}

macro_rules! impl_pod_for {
    ($($pod_ty:ty),*) => {
        $(unsafe impl Pod for $pod_ty {})*
    };
}
// impl Pod for primitive types
impl_pod_for!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, isize, usize);
// impl Pod for array
unsafe impl<T: Pod, const N: usize> Pod for [T; N] {}

} // verus!

#[cfg(feature = "derive")]
pub use ostd_pod_derive::*;
