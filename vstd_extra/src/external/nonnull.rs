use core::marker::PointeeSized;
use core::ptr::NonNull;
use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(T)]
#[verifier::external_body]
pub struct ExNonNull<T: PointeeSized>(NonNull<T>);

// The model for NonNull<T> is *mut T, so we can reuse the existing pointer specs.
// See https://doc.rust-lang.org/stable/std/ptr/struct.NonNull.html.
pub uninterp spec fn nonnull_view<T: PointeeSized>(ptr: NonNull<T>) -> *mut T;

// This is the type invariant, the address (represented by the View of *mut T)) is not zero.
pub broadcast axiom fn axiom_nonnull_is_nonnull<T: PointeeSized>(ptr: NonNull<T>)
    ensures
        (#[trigger] nonnull_view(ptr))@.addr != 0,
;

pub assume_specification<T: PointeeSized>[ NonNull::new_unchecked ](ptr: *mut T) -> (ret: NonNull<
    T,
>)
    requires
        ptr@.addr != 0,
    ensures
        nonnull_view(ret) == ptr,
;

pub assume_specification<T: PointeeSized>[ NonNull::as_ptr ](ptr: NonNull<T>) -> (ret: *mut T)
    ensures
        ret@.addr != 0,
        nonnull_view(ptr) == ret,
;

// Specification for NonNull::dangling(), uninterpreted because the ptr only has to satisfy the alignment requirement.
// See https://doc.rust-lang.org/stable/std/ptr/struct.NonNull.html#method.dangling.
pub uninterp spec fn nonnull_dangling_spec<T>() -> NonNull<T>;

pub assume_specification<T>[ NonNull::dangling ]() -> (ret: NonNull<T>)
    ensures
        nonnull_view(ret)@.addr as nat % align_of::<T>() as nat == 0,
    returns
        nonnull_dangling_spec::<T>(),
;

pub broadcast group group_nonnull {
    axiom_nonnull_is_nonnull,
}

} // verus!
