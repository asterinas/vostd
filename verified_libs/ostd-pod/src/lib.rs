//! This crate defines a marker trait for plain old data (POD).
#![no_std]

use vstd::prelude::*;
use vstd_extra::array_ptr::{self, ArrayPtr, PointsToArray};

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
        unsafe { MaybeUninit::uninit().assume_init() }
    }

    /// As an immutable slice of bytes.
    #[verifier::external_body]
    fn as_bytes(&self) -> (r: &[u8])
        ensures
            r.len() == core::mem::size_of::<Self>(),
    {
        let ptr = self as *const Self as *const u8;
        let len = core::mem::size_of::<Self>();

        unsafe { core::slice::from_raw_parts(ptr, len) }
    }

    /// As a mutable slice of bytes.
    #[verifier::external_body]
    fn as_bytes_mut(&mut self) -> (r: &mut [u8])
        ensures
            r.len() == core::mem::size_of::<Self>(),
    {
        let ptr = self as *mut Self as *mut u8;
        let len = core::mem::size_of::<Self>();

        unsafe { core::slice::from_raw_parts_mut(ptr, len) }
    }

    /// As a slice of bytes via an [`ArrayPtr`] (with a tracked permission).
    ///
    /// This is the verus-flavored variant; the raw `&[u8]` view is [`Self::as_bytes`].
    #[verifier::external_body]
    fn as_array_ptr_bytes<const N: usize>(&self) -> (slice: (
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
}

/// Spec function: the byte representation of a [`Pod`] value.
///
/// This is uninterpreted — the actual byte mapping depends on `T`'s layout
/// (endianness, padding, etc.) which we don't model. Callers use this to
/// relate writes and reads of the same value through memory.
pub uninterp spec fn pod_bytes<T: Pod>(val: T) -> Seq<u8>;

/// Axiom: the byte representation of a `T: Pod` value has length `size_of::<T>()`.
pub broadcast axiom fn axiom_pod_bytes_len<T: Pod>(val: T)
    ensures
        #[trigger] pod_bytes(val).len() == core::mem::size_of::<T>(),
;

/// Axiom: [`pod_bytes`] is injective — equal byte sequences come from equal values.
///
/// `T: Pod` has a well-defined byte layout (no padding for `repr(C)` primitives),
/// so the byte sequence uniquely determines the value.
pub broadcast axiom fn axiom_pod_bytes_injective<T: Pod>(v1: T, v2: T)
    ensures
        #[trigger] pod_bytes(v1) == #[trigger] pod_bytes(v2) ==> v1 == v2,
;

/// The Pod value whose byte representation equals `bytes` (when one exists).
///
/// Defined via `choose` over the injective [`pod_bytes`]; if no Pod value
/// maps to `bytes`, the result is arbitrary. Callers should establish
/// existence before relying on the returned value.
pub open spec fn decode_pod<T: Pod>(bytes: Seq<u8>) -> T {
    choose|v: T| pod_bytes::<T>(v) == bytes
}

/// Round-trip: `decode_pod(pod_bytes(v)) == v` by injectivity.
pub broadcast proof fn lemma_decode_pod_inverse<T: Pod>(v: T)
    ensures
        #[trigger] decode_pod::<T>(pod_bytes::<T>(v)) == v,
{
    let bytes = pod_bytes::<T>(v);
    let chosen: T = choose|w: T| pod_bytes::<T>(w) == bytes;
    assert(pod_bytes::<T>(chosen) == bytes);
    broadcast use axiom_pod_bytes_injective;

}

macro_rules! impl_pod_for {
    ($($pod_ty:ty),*) => {
        $(unsafe impl Pod for $pod_ty {})*
    };
}

// impl Pod for primitive types
impl_pod_for!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, isize, usize);

// impl Pod for array
unsafe impl<T: Pod, const N: usize> Pod for [T; N] {

}

} // verus!
