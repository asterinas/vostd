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

#[inline(always)]
pub open spec fn ptr_cast_spec<T: PointeeSized, U>(ptr: *const T) -> *const U {
    ptr as *const U
}

#[inline(always)]
pub open spec fn ptr_mut_cast_spec<T: PointeeSized, U>(ptr: *mut T) -> *mut U {
    ptr as *mut U
}

#[inline(always)]
pub open spec fn ptr_mut_cast_const_spec<T: PointeeSized>(ptr: *mut T) -> *const T {
    ptr as *const T
}

#[inline(always)]
pub open spec fn ptr_cast_mut_spec<T: PointeeSized>(ptr: *const T) -> *mut T {
    ptr as *mut T
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

} // verus!
