use core::marker::PointeeSized;
use core::num::NonZeroUsize;
use core::ptr::NonNull;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::std_specs::{cmp::*, nonzero::*, ptr::*};

verus! {

/// Rust 1.99.1 core/src/ptr/non_null.rs: equality delegates to raw-pointer equality.
pub assume_specification<T: PointeeSized>[ <NonNull<T> as core::cmp::PartialEq>::eq ](
    left: &NonNull<T>,
    right: &NonNull<T>,
) -> (ret: bool)
    ensures
        call_ensures(<*mut T as core::cmp::PartialEq>::eq, (&left.as_ptr(), &right.as_ptr()), ret),
;

pub trait NonNullAdditionalFns<T: PointeeSized> {
    /// Specification for `NonNull::cast`.
    spec fn cast_spec<U>(self) -> NonNull<U>;

    /// Specification for `NonNull::dangling()`.
    spec fn dangling_spec() -> NonNull<T>;

    spec fn addr_spec(self) -> NonZeroUsize;
}

impl<T: PointeeSized> NonNullAdditionalFns<T> for NonNull<T> {
    uninterp spec fn cast_spec<U>(self) -> NonNull<U>;

    uninterp spec fn dangling_spec() -> NonNull<T>;

    open spec fn addr_spec(self) -> NonZeroUsize {
        nonzero_from_primitive(self.as_ptr().addr())
    }
}

/// Relates the nonzero address model to the standard raw-pointer accessor.
pub broadcast proof fn lemma_addr_view_eq_as_ptr<T: PointeeSized>(ptr: NonNull<T>)
    ensures
        (#[trigger] ptr.addr_spec()).view() == ptr.as_ptr().addr(),
{
    broadcast use axiom_nonzero_from_primitive_view_eq;

    axiom_nonnull_addr_nonzero(ptr);
}

#[verifier::inline]
pub open spec fn nonnull_addr_spec_wrapper<T: PointeeSized>(ptr: NonNull<T>) -> NonZeroUsize {
    ptr.addr_spec()
}

/// Trusted model of Rust 1.99.1's `core/src/ptr/non_null.rs::NonNull::addr`:
/// returns the nonzero address of the underlying pointer.
#[verifier::when_used_as_spec(nonnull_addr_spec_wrapper)]
pub assume_specification<T: PointeeSized>[ NonNull::<T>::addr ](ptr: NonNull<T>) -> NonZeroUsize
    returns
        ptr.addr_spec(),
    opens_invariants none
    no_unwind
;

/// Trusted model of Rust 1.99.1's `core/src/ptr/non_null.rs::NonNull::map_addr`:
/// calls `f` on the address and preserves the pointer's metadata and provenance.
pub assume_specification<T: PointeeSized>[ NonNull::<T>::map_addr ](
    ptr: NonNull<T>,
    f: impl FnOnce(NonZeroUsize) -> NonZeroUsize,
) -> (ret: NonNull<T>)
    requires
        f.requires((ptr.addr_spec(),)),
    ensures
        ret.as_ptr()@.metadata == ptr.as_ptr()@.metadata,
        ret.as_ptr()@.provenance == ptr.as_ptr()@.provenance,
        f.ensures((ptr.addr_spec(),), ret.addr_spec()),
;

#[verifier::inline]
pub open spec fn nonnull_cast_spec_wrapper<T: PointeeSized, U>(ptr: NonNull<T>) -> NonNull<U> {
    ptr.cast_spec::<U>()
}

/// An uninterpreted specification that constructs a `NonNull<T>` from a raw pointer.
pub uninterp spec fn nonnull_from_ptr_mut_spec<T: PointeeSized>(ptr: *mut T) -> NonNull<T>;

#[verifier::inline]
pub open spec fn nonnull_new_spec<T: PointeeSized>(ptr: *mut T) -> Option<NonNull<T>> {
    if ptr.is_null() {
        None
    } else {
        Some(nonnull_from_ptr_mut_spec(ptr))
    }
}

/// The view of a `NonNull<T>` constructed from `*mut T` should be exactly that `*mut T`.
pub broadcast axiom fn axiom_nonnull_from_ptr_mut_spec_eq<T: PointeeSized>(ptr: *mut T)
    requires
        !ptr.is_null(),
    ensures
        (#[trigger] nonnull_from_ptr_mut_spec(ptr)).as_ptr() == ptr,
;

/// The `NonNull` constructed from the view of a `NonNull<T>` should be exactly that `NonNull<T>`.
/// Implies that `a.as_ptr() == b.as_ptr() ==> a == b`.
pub broadcast axiom fn axiom_view_ptr_mut_eq<T: PointeeSized>(a: NonNull<T>)
    ensures
        nonnull_from_ptr_mut_spec(#[trigger] a.as_ptr()) == a,
;

/// The semantic of casting a `NonNull<T>` should be the same as casting the underlying raw pointer
/// (including the address, metadata, and provenance).
pub broadcast axiom fn axiom_cast_spec_eq<T: PointeeSized, U>(ptr: NonNull<T>)
    ensures
        ((#[trigger] ptr.cast_spec::<U>())).as_ptr() == ptr.as_ptr() as *mut U,
;

#[verifier::when_used_as_spec(nonnull_cast_spec_wrapper)]
pub assume_specification<T: PointeeSized, U>[ NonNull::<T>::cast::<U> ](ptr: NonNull<T>) -> (ret:
    NonNull<U>)
    ensures
        ret.as_ptr() == ptr.as_ptr() as *mut U,
    returns
        ptr.cast_spec::<U>(),
;

// Specification for NonNull::dangling(), uninterpreted because the ptr only has to satisfy the alignment requirement.
// See https://doc.rust-lang.org/stable/std/ptr/struct.NonNull.html#method.dangling.
pub uninterp spec fn nonnull_dangling_spec<T>() -> NonNull<T>;

#[verifier::when_used_as_spec(nonnull_dangling_spec)]
pub assume_specification<T>[ NonNull::dangling ]() -> (ret: NonNull<T>)
    ensures
        ret.as_ptr()@.addr as nat % align_of::<T>() as nat == 0,
        ret.as_ptr()@.provenance == Provenance::null(),
    returns
        nonnull_dangling_spec::<T>(),
;

#[verifier::inline]
pub open spec fn nonnull_with_addr_spec_wrapper<T: PointeeSized>(
    ptr: NonNull<T>,
    addr: NonZeroUsize,
) -> NonNull<T> {
    ptr.with_addr_spec(addr)
}

// To prevent circular dependency
pub trait NonNullAdditionalFnsMore<T>: NonNullAdditionalFns<T> where T: PointeeSized {
    spec fn with_addr_spec(self, addr: NonZeroUsize) -> NonNull<T>;
}

impl<T: PointeeSized> NonNullAdditionalFnsMore<T> for NonNull<T> {
    uninterp spec fn with_addr_spec(self, addr: NonZeroUsize) -> NonNull<T>;
}

pub axiom fn lemma_with_addr_properties<T: PointeeSized>(ptr: NonNull<T>, addr: NonZeroUsize)
    ensures
        ptr.with_addr_spec(addr).as_ptr()@.metadata == ptr.as_ptr()@.metadata,
        ptr.with_addr_spec(addr).as_ptr()@.provenance == ptr.as_ptr()@.provenance,
        ptr.with_addr_spec(addr).as_ptr()@.addr == addr.view(),
;

#[verifier::when_used_as_spec(nonnull_with_addr_spec_wrapper)]
pub assume_specification<T: PointeeSized>[ NonNull::<T>::with_addr ](
    ptr: NonNull<T>,
    addr: NonZeroUsize,
) -> NonNull<T>
    returns
        ptr.with_addr_spec(addr),
    opens_invariants none
    no_unwind
;

pub broadcast group group_nonull_axioms {
    axiom_nonnull_from_ptr_mut_spec_eq,
    axiom_cast_spec_eq,
    axiom_view_ptr_mut_eq,
    lemma_addr_view_eq_as_ptr,
    axiom_nonnull_addr_nonzero,
}

} // verus!
