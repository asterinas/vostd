use core::ops::Range;
use vstd::prelude::*;

verus! {

#[verifier::when_used_as_spec(as_ptr_spec)]
pub assume_specification<T>[ <[T]>::as_ptr ](s: &[T]) -> (r: *const T)
    ensures
        r == as_ptr_spec(s),
;

pub uninterp spec fn as_ptr_spec<T>(s: &[T]) -> *const T;

pub uninterp spec fn as_mut_ptr_spec<T>(s: &mut [T]) -> *mut T;

pub assume_specification<T>[ <[T]>::as_mut_ptr ](s: &mut [T]) -> (r: *mut T)
    ensures
        r == as_mut_ptr_spec(s),
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

/// Spec for `core::slice::from_raw_parts`. We promise only that the resulting
/// slice has the requested length; soundness for the memory aliased lives in
/// the `unsafe` contract upheld by the caller.
pub assume_specification<'a, T>[ core::slice::from_raw_parts::<'a, T> ](
    data: *const T,
    len: usize,
) -> (ret: &'a [T])
    ensures
        ret.len() == len,
;

/// Spec for `core::slice::from_raw_parts_mut`. As above.
pub assume_specification<'a, T>[ core::slice::from_raw_parts_mut::<'a, T> ](
    data: *mut T,
    len: usize,
) -> (ret: &'a mut [T])
    ensures
        ret.len() == len,
;

} // verus!
