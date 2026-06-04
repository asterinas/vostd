use core::marker::PointeeSized;
use vstd::prelude::*;

verus! {

pub assume_specification<T: PointeeSized>[ <*const T>::map_addr ](
    ptr: *const T,
    f: impl FnOnce(usize) -> usize,
) -> (ret: *const T)
    requires
        f.requires((ptr@.addr,)),
    ensures
        ret@.metadata == ptr@.metadata,
        ret@.provenance == ptr@.provenance,
        f.ensures((ptr@.addr,), ret@.addr),
;

pub assume_specification<T: PointeeSized>[ <*mut T>::map_addr ](
    ptr: *mut T,
    f: impl FnOnce(usize) -> usize,
) -> (ret: *mut T)
    requires
        f.requires((ptr@.addr,)),
    ensures
        ret@.metadata == ptr@.metadata,
        ret@.provenance == ptr@.provenance,
        f.ensures((ptr@.addr,), ret@.addr),
;

#[verifier::inline]
pub open spec fn ptr_cast_spec<T: PointeeSized, U>(ptr: *const T) -> *const U {
    ptr as *const U
}

#[verifier::inline]
pub open spec fn ptr_mut_cast_spec<T: PointeeSized, U>(ptr: *mut T) -> *mut U {
    ptr as *mut U
}

#[verifier::inline]
pub open spec fn ptr_mut_cast_const_spec<T: PointeeSized>(ptr: *mut T) -> *const T {
    ptr as *const T
}

#[verifier::inline]
pub open spec fn ptr_cast_mut_spec<T: PointeeSized>(ptr: *const T) -> *mut T {
    ptr as *mut T
}

#[verifier::inline]
pub open spec fn ptr_is_null_spec<T: PointeeSized>(ptr: *const T) -> bool {
    ptr.addr() == 0
}

#[verifier::inline]
pub open spec fn ptr_mut_is_null_spec<T: PointeeSized>(ptr: *mut T) -> bool {
    ptr.addr() == 0
}

#[verifier::when_used_as_spec(ptr_cast_spec)]
pub assume_specification<T: PointeeSized, U>[ <*const T>::cast::<U> ](ptr: *const T) -> *const U
    returns
        ptr as *const U,
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(ptr_mut_cast_spec)]
pub assume_specification<T: PointeeSized, U>[ <*mut T>::cast::<U> ](ptr: *mut T) -> *mut U
    returns
        ptr as *mut U,
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(ptr_mut_cast_const_spec)]
pub assume_specification<T: PointeeSized>[ <*mut T>::cast_const ](ptr: *mut T) -> *const T
    returns
        ptr as *const T,
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(ptr_cast_mut_spec)]
pub assume_specification<T: PointeeSized>[ <*const T>::cast_mut ](ptr: *const T) -> *mut T
    returns
        ptr as *mut T,
    opens_invariants none
    no_unwind
;

/// [<*const T>::is_null](https://doc.rust-lang.org/std/primitive.pointer.html#method.is_null) only checks the raw data pointer.
#[verifier::when_used_as_spec(ptr_is_null_spec)]
pub assume_specification<T: PointeeSized>[ <*const T>::is_null ](ptr: *const T) -> bool
    returns
        ptr.addr() == 0,
    opens_invariants none
    no_unwind
;

/// [<*mut T>::is_null](https://doc.rust-lang.org/std/primitive.pointer.html#method.is_null) only checks the raw data pointer.
#[verifier::when_used_as_spec(ptr_mut_is_null_spec)]
pub assume_specification<T: PointeeSized>[ <*mut T>::is_null ](ptr: *mut T) -> bool
    returns
        ptr.addr() == 0,
    opens_invariants none
    no_unwind
;

} // verus!
