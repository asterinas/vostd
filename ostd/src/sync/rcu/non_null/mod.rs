// SPDX-License-Identifier: MPL-2.0
//! This module provides a trait and some auxiliary types to help abstract and
//! work with non-null pointers.
use alloc::{boxed::Box, sync::Arc};
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd_extra::prelude::*;

mod either;

use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref, ptr::NonNull};

use crate::prelude::*;

verus! {

broadcast use {group_nonull_axioms, group_raw_ptr_axioms};
    
/// A trait that abstracts non-null pointers.
///
/// All common smart pointer types such as `Box<T>`,  `Arc<T>`, and `Weak<T>`
/// implement this trait as they can be converted to and from the raw pointer
/// type of `*const T`.
///
/// # Safety
///
/// This trait must be implemented correctly (according to the doc comments for
/// each method). Types like [`Rcu`] rely on this assumption to safely use the
/// raw pointers.
///
/// [`Rcu`]: super::Rcu
#[verus_verify]
pub unsafe trait NonNullPtr: Sized + 'static {
    /// The target type that this pointer refers to.
    // TODO: Support `Target: ?Sized`.
    type Target;

    // VERUS LIMITATION: Verus does not support generic associated type with lifetime yet, 
    // so we put all methods related to the Ref associated type in the `NonNullPtrRef` trait.
    /*/// A type that behaves just like a shared reference to the `NonNullPtr`.
    type Ref<'a>
    where
        Self: 'a;*/
        
    /// A verification-only permission type that represents the ownership of the memory managed by the pointer.
    type Permission: Inv;

    /// The power of two of the pointer alignment.
    const ALIGN_BITS: u32;

    /// Converts to a raw pointer.
    ///
    /// Each call to `into_raw` must be paired with a call to `from_raw`
    /// in order to avoid memory leakage.
    ///
    /// The lower [`Self::ALIGN_BITS`] of the raw pointer is guaranteed to
    /// be zero. In other words, the pointer is guaranteed to be aligned to
    /// `1 << Self::ALIGN_BITS`.
    /// VERUS LIMITATION: the #[verus_spec] attribute does not support `with` in trait yet.
    fn into_raw(self) -> ((res_ptr,perm): (NonNull<Self::Target>, Tracked<Self::Permission>))
        ensures
            Self::ptr_perm_match(res_ptr, perm@),
            self.rel_perm(perm@),
            perm@.inv(),
            res_ptr.view_ptr_mut().addr() % (1usize << Self::ALIGN_BITS) == 0,
    ;

    /// Converts back from a raw pointer.
    ///
    /// # Safety
    ///
    /// 1. The raw pointer must have been previously returned by a call to
    ///    `into_raw`.
    /// 2. The raw pointer must not be used after calling `from_raw`.
    ///
    /// Note that the second point is a hard requirement: Even if the
    /// resulting value has not (yet) been dropped, the pointer cannot be
    /// used because it may break Rust aliasing rules (e.g., `Box<T>`
    /// requires the pointer to be unique and thus _never_ aliased).
    /// VERIFICATION DESIGN: It's easy to verify the second point by consuming the permission produced by `into_raw`,
    /// so we can do nothing with the raw pointer because of the absence of permission.
    /// VERUS LIMITATION: the #[verus_spec] attribute does not support `with` in trait yet.
    unsafe fn from_raw(
        ptr: NonNull<Self::Target>,
        perm: Tracked<Self::Permission>,
    ) -> (ret: Self)
        requires
            Self::ptr_perm_match(ptr, perm@),
            perm@.inv(),
        ensures
            ret.rel_perm(perm@),
    ;

    /*/// Obtains a shared reference to the original pointer.
    ///
    /// # Safety
    ///
    /// The original pointer must outlive the lifetime parameter `'a`, and during `'a`
    /// no mutable references to the pointer will exist.
    //unsafe fn raw_as_ref<'a>(raw: NonNull<Self::Target>) -> Self::Ref<'a>;*/

    /*/// Converts a shared reference to a raw pointer.
    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> NonNull<Self::Target>;*/

    /// A specification function that constraints the nonnull pointer and the permission returned by `into_raw`.
    /// This design is to support the tagged pointer trick used in `Either`.
    spec fn ptr_perm_match(ptr: NonNull<Self::Target>, perm: Self::Permission) -> bool;

    /// A specification function that relates the original smart pointer and the permission.
    spec fn rel_perm(self, perm: Self::Permission) -> bool;

    /// The ALIGN_BITS must be less than usize::BITS.
    proof fn lemma_align_bits_range()
        ensures
            Self::ALIGN_BITS < usize::BITS,
    ;
}

/// The trait for the associated Ref type of `NonNullPtr`, which is separated from the `NonNullPtr` trait.
/// FIXME: This is a workaround for the lack of GAT with lifetime in Verus. We can merge this trait back to `NonNullPtr` 
/// once it is supported.
pub unsafe trait NonNullPtrRef<'a>: NonNullPtr {
    type Ref: 'a;

    /// A verification-only permission type that represents the reading permission of the memory managed by the pointer.
    type RefPermission: Inv;

    /// The RefPermission must be able to be viewed as the owned Permission.
    spec fn ref_perm_view_permission(perm: Self::RefPermission) -> Self::Permission;
    
    /// A specification function that relates the `Ref` type and the `RefPermission`.
    spec fn ref_rel_perm(r: Self::Ref, perm: Self::RefPermission) -> bool;

    /// The `RefPermission` must present the invariant of the `Permission`.
    proof fn lemma_ref_perm_inv_impl_perm_inv(perm: Self::RefPermission)
        requires
            perm.inv(),
        ensures
            Self::ref_perm_view_permission(perm).inv(),
    ;

    /// Obtains a shared reference to the original pointer.
    ///
    /// # Safety
    ///
    /// The original pointer must outlive the lifetime parameter `'a`, and during `'a`
    /// no mutable references to the pointer will exist.
    unsafe fn raw_as_ref(raw: NonNull<Self::Target>, perm: Tracked<Self::RefPermission>) -> (ret: Self::Ref)
        requires
            Self::ptr_perm_match(raw, Self::ref_perm_view_permission(perm@)),
            perm@.inv(),
        ensures
            Self::ref_rel_perm(ret, perm@),
    ;

    /// Converts a shared reference to a raw pointer.
    fn ref_as_raw(ptr_ref: Self::Ref) -> ((res_ptr, perm): (NonNull<Self::Target>, Tracked<Self::RefPermission>))
        ensures
            Self::ref_rel_perm(ptr_ref, perm@),
            Self::ptr_perm_match(res_ptr, Self::ref_perm_view_permission(perm@)),
            perm@.inv(),
            res_ptr.view_ptr_mut().addr() % (1usize << Self::ALIGN_BITS) == 0,
    ;
} 

/// A type that represents `&'a Box<T>`.
#[verus_verify]
#[derive(Debug)]
pub struct BoxRef<'a, T> {
    inner: *mut T,
    _marker: PhantomData<&'a T>,
    v_perm: Tracked<BoxPointsToRef<'a, T>>,
}

impl<'a, T> BoxRef<'a, T> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        &&& self.inner@.addr != 0
        &&& self.inner@.addr as int % vstd::layout::align_of::<T>() as int == 0
        &&& self.v_perm@@.ptr() == self.inner
        &&& self.v_perm@.inv()
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.inner
    }

    pub closed spec fn value(self) -> T {
        self.v_perm@@.value()
    }
}

/*
impl<T> Deref for BoxRef<'_, T> {
    type Target = Box<T>;

    fn deref(&self) -> &Self::Target {
        // SAFETY: A `Box<T>` is guaranteed to be represented by a single pointer [1] and a shared
        // reference to the `Box<T>` during the lifetime `'a` can be created according to the
        // safety requirements of `NonNullPtr::raw_as_ref`.
        //
        // [1]: https://doc.rust-lang.org/std/boxed/#memory-layout
        unsafe { core::mem::transmute(&self.inner) }
    }
}
*/

#[verus_verify]
impl<'a, T> BoxRef<'a, T> {
    /// Dereferences `self` to get a reference to `T` with the lifetime `'a`.
    #[verus_spec(ret => ensures *ret == self.value())]
    pub fn deref_target(&self) -> &'a T {
        proof!{
            use_type_invariant(self);
        }
        // [VERIFIED] SAFETY: The reference is created through `NonNullPtr::raw_as_ref`, hence
        // the original owned pointer and target must outlive the lifetime parameter `'a`,
        // and during `'a` no mutable references to the pointer will exist.
        
        // The function body of ptr_ref is exactly the same as `unsafe { &*(self.inner) }`
        //unsafe { &*(self.inner) }
        vstd::raw_ptr::ptr_ref(
            self.inner,
            Tracked(self.v_perm.borrow().tracked_borrow_points_to()),
        )
    }
}

unsafe impl<T: 'static> NonNullPtr for Box<T> {
    type Target = T;

    type Permission = BoxPointsTo<T>;

    /*type Ref<'a>
        = BoxRef<'a, T>
    where
        Self: 'a;*/

    #[verifier::external_body]
    const ALIGN_BITS: u32 = core::mem::align_of::<T>().trailing_zeros();

    #[verus_spec]
    fn into_raw(self) -> (NonNull<Self::Target>, Tracked<Self::Permission>) {
        proof_decl! {
            let tracked perm: (PointsTo<T>, Option<Dealloc>);
        }
        
        //let ptr = Box::into_raw(self);
        proof_with!(=> Tracked(perm));
        let ptr = box_into_raw(self);

        proof_decl!{
            let tracked box_points_to = BoxPointsTo {
                perm: PointsTowithDealloc::new(perm.0, perm.1),
            };
        }
        assume(ptr.addr() % (1usize << Self::ALIGN_BITS) == 0);
        
        // [VERIFIED] SAFETY: The pointer representing a `Box` can never be NULL.
        (unsafe { NonNull::new_unchecked(ptr) }, Tracked(box_points_to))
    }

    #[verus_spec]
    unsafe fn from_raw(
        ptr: NonNull<Self::Target>,
        Tracked(perm): Tracked<Self::Permission>,
    ) -> Self {
        proof_decl!{
            let tracked perm = perm.tracked_get_points_to_with_dealloc();
        }
        
        let ptr = ptr.as_ptr();

        // [VERIFIED] SAFETY: The safety is upheld by the caller.
        // unsafe { Box::from_raw(ptr) }
        unsafe { 
            proof_with!(Tracked(perm.points_to), Tracked(perm.dealloc));
            box_from_raw(ptr) 
        }
    }

    open spec fn ptr_perm_match(ptr: NonNull<Self::Target>, perm: Self::Permission) -> bool {
        ptr.view_ptr_mut() == perm.ptr()
    }

    open spec fn rel_perm(self, perm: Self::Permission) -> bool {
        perm.view_target() == *self
    }

    axiom fn lemma_align_bits_range();
}

unsafe impl<'a, T: 'static> NonNullPtrRef<'a> for Box<T> {
    type Ref = BoxRef<'a, T>;
    type RefPermission = BoxPointsToRef<'a, T>;

    open spec fn ref_perm_view_permission(perm: Self::RefPermission) -> Self::Permission {
        perm@
    }

    open spec fn ref_rel_perm(r: Self::Ref, perm: Self::RefPermission) -> bool {
        &&& r.value() == perm@.value()
        &&& r.ptr() == perm@.ptr()
    }

    proof fn lemma_ref_perm_inv_impl_perm_inv(perm: Self::RefPermission){}

    unsafe fn raw_as_ref(raw: NonNull<Self::Target>, perm: Tracked<Self::RefPermission>) -> Self::Ref {
        BoxRef { 
            inner: raw.as_ptr(), 
            _marker: PhantomData, 
            v_perm: perm 
        }
    }

    fn ref_as_raw(ptr_ref: Self::Ref) -> (NonNull<Self::Target>, Tracked<Self::RefPermission>) {
        proof!{
            use_type_invariant(&ptr_ref);
            assume(ptr_ref.ptr().addr() % (1usize << Self::ALIGN_BITS) == 0);
        }
        // [VERIFIED] SAFETY: The pointer representing a `Box` can never be NULL.
        (unsafe { NonNull::new_unchecked(ptr_ref.inner) }, ptr_ref.v_perm)
    }
}

/// A type that represents `&'a Arc<T>`.
/// 
/// Note there is no verification-only permission field, because `ArcRef` uses `Arc` instead of a raw pointer internally.
#[verus_verify]
#[derive(Debug)]
pub struct ArcRef<'a, T: 'static> {
    inner: ManuallyDrop<Arc<T>>,
    _marker: PhantomData<&'a Arc<T>>,
}

impl<T> View for ArcRef<'_, T> {
    type V = Arc<T>;

    closed spec fn view(&self) -> Arc<T> {
        self.inner@
    }
}

#[verus_verify]
impl<T> Deref for ArcRef<'_, T> {
    type Target = Arc<T>;

    #[verus_spec(ret =>
        ensures *ret == self@
    )]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[verus_verify]
impl<'a, T> ArcRef<'a, T> {
    /// Dereferences `self` to get a reference to `T` with the lifetime `'a`.
    /// VERUS LIMITATION: The code includes a cast from `&T` to `*const T`, which is not specified yet in Verus.
    /// This is also a nontrivial use case that extends the lifetime of the reference.
    #[verus_verify(external_body)]
    #[verus_spec(ret => ensures *ret == self@)]
    pub fn deref_target(&self) -> &'a T {
        // SAFETY: The reference is created through `NonNullPtr::raw_as_ref`, hence
        // the original owned pointer and target must outlive the lifetime parameter `'a`,
        // and during `'a` no mutable references to the pointer will exist.
        unsafe { &*(self.deref().deref() as *const T) }
    }
}

unsafe impl<T: 'static> NonNullPtr for Arc<T> {
    type Target = T;

    type Permission = ArcPointsTo<T>;

    /*
    type Ref<'a>
        = ArcRef<'a, T>
    where
        Self: 'a;*/
    
    #[verifier::external_body]
    const ALIGN_BITS: u32 = core::mem::align_of::<T>().trailing_zeros();

    #[verus_spec]
    fn into_raw(self) -> (NonNull<Self::Target>, Tracked<Self::Permission>) {
        proof_decl!{
            let tracked perm: ArcPointsTo<T>;
        }
        // let ptr = Arc::into_raw(self).cast_mut();
        let ptr = (#[verus_spec(with => Tracked(perm))] arc_into_raw(self)).cast_mut();
        assume(ptr.addr() % (1usize << Self::ALIGN_BITS) == 0);
        
        // [VERIFIED] SAFETY: The pointer representing an `Arc` can never be NULL.
        (unsafe { NonNull::new_unchecked(ptr) }, Tracked(perm))
    }

    unsafe fn from_raw(
        ptr: NonNull<Self::Target>,
        Tracked(perm): Tracked<Self::Permission>,
    ) -> Self {
        let ptr = ptr.as_ptr().cast_const();

        // [VERIFIED] SAFETY: The safety is upheld by the caller.
        // unsafe { Arc::from_raw(ptr) }
        unsafe { #[verus_spec(with Tracked(perm))] arc_from_raw(ptr) }
    }

    open spec fn ptr_perm_match(ptr: NonNull<Self::Target>, perm: Self::Permission) -> bool{
        ptr.view_ptr_mut() == perm.ptr()
    }

    open spec fn rel_perm(self, perm: Self::Permission) -> bool {
        perm.view_target() == *self
    }

    axiom fn lemma_align_bits_range();
}

unsafe impl<'a, T: 'static> NonNullPtrRef<'a> for Arc<T> {
    type Ref = ArcRef<'a, T>;
    type RefPermission = ArcPointsTo<T>;

    open spec fn ref_perm_view_permission(perm: Self::RefPermission) -> Self::Permission {
        perm
    }

    open spec fn ref_rel_perm(r: Self::Ref, perm: Self::RefPermission) -> bool {
        perm.view_target() == r@
    }

    proof fn lemma_ref_perm_inv_impl_perm_inv(perm: Self::RefPermission){}

    unsafe fn raw_as_ref(raw: NonNull<Self::Target>, perm: Tracked<Self::RefPermission>) -> Self::Ref {
        unsafe {
            ArcRef { 
                inner: ManuallyDrop::new(#[verus_spec(with perm)] arc_from_raw(raw.as_ptr())), 
                _marker: PhantomData 
            }
        }
    }

    fn ref_as_raw(ptr_ref: Self::Ref) -> (NonNull<Self::Target>, Tracked<Self::RefPermission>) {
        NonNullPtr::into_raw(ManuallyDrop::into_inner(ptr_ref.inner))
    }
}

} // verus!
