use std::marker::PointeeSized;
use std::ptr::NonNull;
use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(T)]
#[verifier::external_body]
pub struct ExNonNull<T: PointeeSized>(NonNull<T>);

// The model for NonNull<T> is *mut T, so we can reuse the existing pointer specs.
// See https://doc.rust-lang.org/stable/std/ptr/struct.NonNull.html.
pub uninterp spec fn ptr_mut_from_nonull<T: PointeeSized>(ptr: NonNull<T>) -> *mut T;

// This is the type invariant, the address (represented by the View of *mut T)) is not zero.
pub broadcast axiom fn axiom_nonull_is_nonnull<T: PointeeSized>(ptr: NonNull<T>)
    ensures
        (#[trigger]ptr_mut_from_nonull(ptr))@.addr != 0,
;

// Inverse function:
// Constructing NonNull<T> from the *mut T model.
pub uninterp spec fn nonnull_from_ptr_mut<T: PointeeSized>(ptr: *mut T) -> NonNull<T>;

pub broadcast axiom fn axiom_ptr_mut_from_nonull_eq<T: PointeeSized>(ptr: NonNull<T>)
    ensures
        nonnull_from_ptr_mut(#[trigger] ptr_mut_from_nonull(ptr)) == ptr,
;

pub broadcast axiom fn axiom_nonull_from_ptr_mut_eq<T: PointeeSized>(ptr: *mut T)
    requires
        ptr@.addr != 0,
    ensures
        ptr_mut_from_nonull(#[trigger] nonnull_from_ptr_mut(ptr)) == ptr,
;

pub assume_specification<T: PointeeSized>[ NonNull::new_unchecked ](ptr: *mut T) -> NonNull<T>
    requires
        ptr@.addr != 0,
    returns
        nonnull_from_ptr_mut(ptr),
;

pub assume_specification<T: PointeeSized>[ NonNull::as_ptr ](_0: NonNull<T>) -> (ret: *mut T)
    ensures
        ret@.addr != 0,
    returns
        ptr_mut_from_nonull(_0),
;
    

// Specification for NonNull::dangling(), uninterptred because the ptr only has to satisfy the alignment requirement.
// See https://doc.rust-lang.org/stable/std/ptr/struct.NonNull.html#method.dangling.
pub uninterp spec fn nonnull_dangling_spec<T>() -> NonNull<T>;

pub assume_specification<T>[ NonNull::dangling ]() -> (ret: NonNull<T>)
    ensures
        ptr_mut_from_nonull(ret)@.addr as nat % align_of::<T>() as nat == 0,
    returns
        nonnull_dangling_spec::<T>(),
;

pub broadcast group group_nonnull{
    axiom_nonull_is_nonnull,
    axiom_ptr_mut_from_nonull_eq,
    axiom_nonull_from_ptr_mut_eq,
}

} // verus!
