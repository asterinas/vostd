use core::marker::PointeeSized;
use vstd::{
    prelude::*,
    raw_ptr::{MemContents, PointsTo, PtrData, ptr_mut_from_data},
};

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

/// [`<*mut T>::is_aligned`](https://doc.rust-lang.org/std/primitive.pointer.html#method.is_aligned)
pub assume_specification<T>[ <*mut T>::is_aligned ](ptr: *mut T) -> bool
    returns
        ptr.addr() % core::mem::align_of::<T>() == 0,
    opens_invariants none
;

/// Models wrapping pointer addition.
#[verifier::inline]
pub open spec fn ptr_mut_add_spec<T: PointeeSized + Sized>(p: *mut T, count: usize) -> *mut T {
    ptr_mut_from_data(
        PtrData::<T> {
            addr: ((p.addr() + count * size_of::<T>()) % (usize::MAX as int + 1)) as usize,
            ..p@
        },
    )
}

} // verus!
/// Volatile read with optional Rust allocation permission.
///
/// # Safety
/// Classify the pointer correctly and uphold [`core::ptr::read_volatile`]'s requirements.
/* Trusted: extra permission arguments require wrappers.
 * Origin Rust: <none; new executable wrappers>
 */
#[verus_verify(external_body)]
#[verus_spec(ret =>
    with
        Ghost(is_rust_allocation): Ghost<bool>,
        Tracked(perm): Tracked<Option<&mut PointsTo<T>>>,
    requires
        ptr.addr() % align_of::<T>() == 0,
        is_rust_allocation ==> (perm matches Some(p) && {
            &&& p.ptr() == ptr
            &&& p.is_init()
        }),
        !is_rust_allocation ==> perm is None,
    ensures
        is_rust_allocation ==> (perm matches Some(p) && {
            &&& final(p).ptr() == ptr
            &&& final(p).is_uninit()
            &&& ret == p.value()
        }),
    opens_invariants none
    no_unwind when ptr.addr() % align_of::<T>() == 0
)]
pub unsafe fn read_volatile_wrapper<T>(ptr: *const T) -> T {
    // SAFETY: guaranteed by the caller.
    unsafe { core::ptr::read_volatile(ptr) }
}

/// Volatile write with optional Rust allocation permission.
///
/// # Safety
/// Classify the pointer correctly and uphold [`core::ptr::write_volatile`]'s requirements.
#[verus_verify(external_body)]
#[verus_spec(
    with
        Ghost(is_rust_allocation): Ghost<bool>,
        Tracked(perm): Tracked<Option<&mut PointsTo<T>>>,
    requires
        ptr.addr() % align_of::<T>() == 0,
        is_rust_allocation ==> (perm matches Some(p) && p.ptr() == ptr),
        !is_rust_allocation ==> perm is None,
    ensures
        is_rust_allocation ==> (perm matches Some(p) && {
            &&& final(p).ptr() == ptr
            &&& final(p).opt_value() == MemContents::Init(value)
        }),
    opens_invariants none
    no_unwind when ptr.addr() % align_of::<T>() == 0
)]
pub unsafe fn write_volatile_wrapper<T>(ptr: *mut T, value: T) {
    // SAFETY: guaranteed by the caller.
    unsafe { core::ptr::write_volatile(ptr, value) }
}

/// Temporary xAPIC workaround until vstd supports `wrapping_add`. Do not reuse elsewhere.
///
/// # Safety
/// Uphold `pointer::add`'s allocation and arithmetic requirements.
#[verus_verify(external_body)]
#[verus_spec(
    requires
        p.addr() + count * size_of::<T>() <= usize::MAX,
        count * size_of::<T>() <= isize::MAX,
    returns ptr_mut_add_spec(p, count),
    opens_invariants none
    no_unwind when p.addr() + count * size_of::<T>() <= usize::MAX
        && count * size_of::<T>() <= isize::MAX
)]
pub unsafe fn ptr_mut_add<T>(p: *mut T, count: usize) -> *mut T {
    // SAFETY: guaranteed by the caller.
    unsafe { p.add(count) }
}
