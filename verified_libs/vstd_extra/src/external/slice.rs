use core::ops::Range;
use vstd::prelude::*;

verus! {

/// Rust 1.100.0, library/core/src/convert/mod.rs: AsMut<[T]> for [T]
/// returns `self`. The reborrow preserves the entire slice on return and
/// propagates all subsequent mutations back to the receiver without panicking.
pub assume_specification<T>[ <[T] as core::convert::AsMut<[T]>>::as_mut ](slice: &mut [T]) -> (ret:
    &mut [T])
    ensures
        ret@ == old(slice)@,
        final(slice)@ == final(ret)@,
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(as_ptr_spec)]
pub assume_specification<T>[ <[T]>::as_ptr ](s: &[T]) -> (r: *const T)
    ensures
        r == as_ptr_spec(s),
    no_unwind
;

pub uninterp spec fn as_ptr_spec<T>(s: &[T]) -> *const T;

pub uninterp spec fn as_mut_ptr_spec<T>(s: &mut [T]) -> *mut T;

pub assume_specification<T>[ <[T]>::as_mut_ptr ](s: &mut [T]) -> (r: *mut T)
    ensures
        r == as_mut_ptr_spec(s),
    no_unwind
;

/// AXIOM: A slice's one-past-the-end byte address fits in `usize`.
///
/// Rust guarantees that any valid slice's memory range lies within the
/// addressable address space, so `as_ptr(s) as usize + s.len() * size_of::<T>()`
/// never overflows. We package this as a `usize`-level fact for `T = u8` (the
/// common case for byte-slice plumbing); other element types can use it after
/// multiplying by `size_of::<T>()`.
pub broadcast axiom fn axiom_slice_addr_no_overflow(s: &[u8])
    ensures
        #[trigger] (as_ptr_spec(s) as usize) + s.len() <= usize::MAX,
;

/// AXIOM: Any valid Rust slice has a non-null data pointer.
///
/// Rust guarantees that a slice reference's backing pointer is always non-null
/// (dangling non-null for empty or zero-sized slices).
pub broadcast axiom fn axiom_slice_as_ptr_nonnull<T>(s: &[T])
    ensures
        (#[trigger] s.as_ptr()).addr() != 0,
;

/// Spec for `core::slice::from_raw_parts`. We promise only that the resulting
/// slice has the requested length and that the call does not unwind.
/// The caller must uphold Rust's safety contract.
pub assume_specification<'a, T>[ core::slice::from_raw_parts::<'a, T> ](
    data: *const T,
    len: usize,
) -> (ret: &'a [T])
    ensures
        ret.len() == len,
    no_unwind
;

/// Spec for `core::slice::from_raw_parts_mut`. As above.
pub assume_specification<'a, T>[ core::slice::from_raw_parts_mut::<'a, T> ](
    data: *mut T,
    len: usize,
) -> (ret: &'a mut [T])
    ensures
        ret.len() == len,
    no_unwind
;

/// Fills every element with a clone of `value`; the length is unchanged.
///
/// Fills in place with no allocation, so there is no input-dependent panic; a panicking
/// `T::clone` is assumed away by `cloned`.
pub assume_specification<T: Clone>[ <[T]>::fill ](s: &mut [T], value: T)
    ensures
        final(s)@.len() == old(s)@.len(),
        forall|i: int|
            #![trigger final(s)@[i]]
            0 <= i < final(s)@.len() ==> cloned::<T>(value, final(s)@[i]),
;

} // verus!
