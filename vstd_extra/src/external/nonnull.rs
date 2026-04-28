use super::nonzero::NonZeroUsize;
use core::marker::PointeeSized;
use core::num::NonZero;
use core::ptr::NonNull;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::std_specs::cmp::*;

verus! {

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(T)]
#[verifier::external_body]
pub struct ExNonNull<T: PointeeSized>(NonNull<T>);

pub trait NonNullAdditionalFns<T: PointeeSized> {
    // The model for NonNull<T> is *mut T, so that we can reuse the existing pointer infrastructure.
    // See https://doc.rust-lang.org/stable/std/ptr/struct.NonNull.html.
    spec fn view_ptr_mut(self) -> *mut T;

    /// Specification for `NonNull::cast`.
    spec fn cast_spec<U>(self) -> NonNull<U>;

    /// Specification for `NonNull::dangling()`.
    spec fn dangling_spec() -> NonNull<T>;

    /// Type invariant: the address of the pointer is non-null.
    broadcast proof fn lemma_addr_is_nonnull(self)
        ensures
            (#[trigger] self.view_ptr_mut())@.addr != 0,
    ;

    spec fn addr_spec(self) -> NonZeroUsize;

    broadcast proof fn lemma_addr_view_eq_view_ptr_mut(self)
        ensures
            (#[trigger] self.addr_spec()).view() == self.view_ptr_mut()@.addr,
    ;

    /// A wrapper of `NonNull::addr` in `std`, here we use our own `NonZeroUsize`
    fn addr_v(self) -> NonZeroUsize
        returns
            self.addr_spec(),
    ;
}

impl<T: PointeeSized> NonNullAdditionalFns<T> for NonNull<T> {
    uninterp spec fn view_ptr_mut(self) -> *mut T;

    uninterp spec fn cast_spec<U>(self) -> NonNull<U>;

    uninterp spec fn dangling_spec() -> NonNull<T>;

    axiom fn lemma_addr_is_nonnull(self);

    open spec fn addr_spec(self) -> NonZeroUsize {
        NonZeroUsize::nonzero_usize_from_usize(self.view_ptr_mut()@.addr)
    }

    axiom fn lemma_addr_view_eq_view_ptr_mut(self);

    #[verifier::external_body]
    #[verifier::when_used_as_spec(nonnull_addr_spec_wrapper)]
    fn addr_v(self) -> NonZeroUsize {
        unimplemented!()
    }
}

#[inline(always)]
pub open spec fn nonnull_addr_spec_wrapper<T: PointeeSized>(ptr: NonNull<T>) -> NonZeroUsize {
    ptr.addr_spec()
}

#[inline(always)]
pub open spec fn nonnull_view_ptr_mut_wrapper<T: PointeeSized>(ptr: NonNull<T>) -> *mut T {
    ptr.view_ptr_mut()
}

#[inline(always)]
pub open spec fn nonnull_cast_spec_wrapper<T: PointeeSized, U>(ptr: NonNull<T>) -> NonNull<U> {
    ptr.cast_spec::<U>()
}

/// An uninterpreted specification that constructs a `NonNull<T>` from a raw pointer.
pub uninterp spec fn nonnull_from_ptr_mut_spec<T: PointeeSized>(ptr: *mut T) -> NonNull<T>;

/// The view of a `NonNull<T>` constructed from `*mut T` should be exactly that `*mut T`.
pub broadcast axiom fn axiom_nonnull_from_ptr_mut_spec_eq<T: PointeeSized>(ptr: *mut T)
    requires
        ptr@.addr != 0,
    ensures
        (#[trigger] nonnull_from_ptr_mut_spec(ptr)).view_ptr_mut() == ptr,
;

/// The `NonNull` constructed from the view of a `NonNull<T>` should be exactly that `NonNull<T>`.
/// Implies that `a.view_ptr_mut() == b.view_ptr_mut() ==> a == b`.
pub broadcast axiom fn axiom_view_ptr_mut_eq<T: PointeeSized>(a: NonNull<T>)
    ensures
        nonnull_from_ptr_mut_spec(#[trigger] a.view_ptr_mut()) == a,
;

/// The semantic of casting a `NonNull<T>` should be the same as casting the underlying raw pointer
/// (including the address, metadata, and provenance).
pub broadcast axiom fn axiom_cast_spec_eq<T: PointeeSized, U>(ptr: NonNull<T>)
    ensures
        (#[trigger] ptr.cast_spec::<U>()).view_ptr_mut() == ptr.view_ptr_mut() as *mut U,
;

#[verifier::when_used_as_spec(nonnull_from_ptr_mut_spec)]
pub assume_specification<T: PointeeSized>[ NonNull::new_unchecked ](ptr: *mut T) -> (ret: NonNull<
    T,
>)
    requires
        ptr@.addr != 0,
    ensures
        ret.view_ptr_mut() == ptr,
    returns
        nonnull_from_ptr_mut_spec(ptr),
;

#[verifier::when_used_as_spec(nonnull_view_ptr_mut_wrapper)]
pub assume_specification<T: PointeeSized>[ NonNull::as_ptr ](ptr: NonNull<T>) -> (ret: *mut T)
    ensures
        ret@.addr != 0,
        ptr.view_ptr_mut() == ret,
;

#[verifier::when_used_as_spec(nonnull_cast_spec_wrapper)]
pub assume_specification<T: PointeeSized, U>[ NonNull::<T>::cast::<U> ](ptr: NonNull<T>) -> (ret:
    NonNull<U>)
    ensures
        ret.view_ptr_mut() == ptr.view_ptr_mut() as *mut U,
    returns
        ptr.cast_spec::<U>(),
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

#[inline(always)]
pub open spec fn nonnull_with_addr_spec_wrapper<T: PointeeSized>(
    ptr: NonNull<T>,
    addr: NonZeroUsize,
) -> NonNull<T> {
    ptr.with_addr_spec(addr)
}

// To prevent circular dependency
pub trait NonNullAdditionalFnsMore<T>: NonNullAdditionalFns<T> where T: PointeeSized {
    spec fn with_addr_spec(self, addr: NonZeroUsize) -> NonNull<T>;

    proof fn lemma_with_addr_properties(self, addr: NonZeroUsize)
        ensures
            self.with_addr_spec(addr).view_ptr_mut()@.metadata == self.view_ptr_mut()@.metadata,
            self.with_addr_spec(addr).view_ptr_mut()@.provenance == self.view_ptr_mut()@.provenance,
            self.with_addr_spec(addr).view_ptr_mut()@.addr == addr.view(),
    ;

    fn with_addr_v(self, addr: NonZeroUsize) -> (ret: NonNull<T>)
        returns
            self.with_addr_spec(addr),
    ;

    /// A wrapper of `NonNull::map_addr` in `std`, here we use our own `NonZeroUsize`
    fn map_addr_v<F: FnOnce(NonZeroUsize) -> NonZeroUsize>(self, f: F) -> (ret: NonNull<T>)
        requires
            f.requires((self.addr_spec(),)),
        ensures
            ret.view_ptr_mut()@.metadata == self.view_ptr_mut()@.metadata,
            ret.view_ptr_mut()@.provenance == self.view_ptr_mut()@.provenance,
            f.ensures((self.addr_spec(),), ret.addr_spec()),
    ;
}

impl<T: PointeeSized> NonNullAdditionalFnsMore<T> for NonNull<T> {
    #[verifier::external_body]
    fn map_addr_v<F: FnOnce(NonZeroUsize) -> NonZeroUsize>(self, f: F) -> (ret: NonNull<T>) {
        unimplemented!()
    }

    uninterp spec fn with_addr_spec(self, addr: NonZeroUsize) -> NonNull<T>;

    axiom fn lemma_with_addr_properties(self, addr: NonZeroUsize);

    #[verifier::external_body]
    #[verifier::when_used_as_spec(nonnull_with_addr_spec_wrapper)]
    fn with_addr_v(self, addr: NonZeroUsize) -> (ret: NonNull<T>) {
        unimplemented!()
    }
}

pub broadcast group group_nonull_axioms {
    axiom_nonnull_from_ptr_mut_spec_eq,
    axiom_cast_spec_eq,
    axiom_view_ptr_mut_eq,
    NonNullAdditionalFns::lemma_addr_view_eq_view_ptr_mut,
    NonNullAdditionalFns::lemma_addr_is_nonnull,
}

} // verus!
