use core::marker::PointeeSized;
use core::num::NonZero;
use core::ptr::NonNull;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use crate::external::nonzero::*;

verus! {
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(T)]
#[verifier::external_body]
pub struct ExNonNull<T: PointeeSized>(NonNull<T>);

pub trait NonNullAdditionalFns<T: PointeeSized> {
    // The model for NonNull<T> is *mut T, so that we can reuse the existing pointer infrastructure.
    // See https://doc.rust-lang.org/stable/std/ptr/struct.NonNull.html.
    spec fn view_ptr_mut(self) -> *mut T;

    spec fn cast_spec<U>(self) -> NonNull<U>;

    spec fn dangling_spec() -> NonNull<T>;

    proof fn lemma_addr_is_nonnull(self)
        ensures
            self.view_ptr_mut()@.addr != 0,;
        
}

impl<T: PointeeSized> NonNullAdditionalFns<T> for NonNull<T> {
    uninterp spec fn view_ptr_mut(self) -> *mut T; 

    uninterp spec fn cast_spec<U>(self) -> NonNull<U>;

    uninterp spec fn dangling_spec() -> NonNull<T>;

    axiom fn lemma_addr_is_nonnull(self);
}

#[inline(always)]
pub open spec fn nonnull_view_ptr_mut_wrapper<T: PointeeSized>(ptr: NonNull<T>) -> *mut T {
    ptr.view_ptr_mut()
}

#[inline(always)]
pub open spec fn nonnull_cast_spec_wrapper<T: PointeeSized, U>(ptr: NonNull<T>) -> NonNull<U> {
    ptr.cast_spec::<U>()
}


pub assume_specification<T: PointeeSized>[ NonNull::new_unchecked ](ptr: *mut T) -> (ret: NonNull<
    T,
>)
    requires
        ptr@.addr != 0,
    ensures
        ret.view_ptr_mut() == ptr,
;

#[verifier::when_used_as_spec(nonnull_view_ptr_mut_wrapper)]
pub assume_specification<T: PointeeSized>[ NonNull::as_ptr ](ptr: NonNull<T>) -> (ret: *mut T)
    ensures
        ret@.addr != 0,
        ptr.view_ptr_mut() == ret,
;

#[verifier::when_used_as_spec(nonnull_cast_spec_wrapper)]
pub assume_specification<T: PointeeSized, U>[ NonNull::<T>::cast::<U> ](
    ptr: NonNull<T>,
) -> (ret: NonNull<U>)
    ensures
        ret.view_ptr_mut() == ptr.view_ptr_mut() as *mut U,
    returns
        ptr.cast_spec::<U>(),
;

/// FIXME: Better specification that captures the effect of the mapping function `f` on the pointer's address, instead of just saying the metadata and provenance are unchanged.
pub assume_specification<T: PointeeSized, F: FnOnce(NonZero<usize>) -> NonZero<usize>> [ NonNull::<T>::map_addr ](
    ptr: NonNull<T>,
    f: F,
) -> (ret: NonNull<T>)
    ensures
        ret.view_ptr_mut()@.metadata == ptr.view_ptr_mut()@.metadata,
        ret.view_ptr_mut()@.provenance == ptr.view_ptr_mut()@.provenance,
;

// Specification for NonNull::dangling(), uninterpreted because the ptr only has to satisfy the alignment requirement.
// See https://doc.rust-lang.org/stable/std/ptr/struct.NonNull.html#method.dangling.
pub uninterp spec fn nonnull_dangling_spec<T>() -> NonNull<T>;

#[verifier::when_used_as_spec(nonnull_dangling_spec)]
pub assume_specification<T>[ NonNull::dangling ]() -> (ret: NonNull<T>)
    ensures
        ret.view_ptr_mut()@.addr as nat % align_of::<T>() as nat == 0,
        ret.view_ptr_mut()@.provenance == Provenance::null(),
    returns
        nonnull_dangling_spec::<T>(),
;

} // verus!
