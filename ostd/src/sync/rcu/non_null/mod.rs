// SPDX-License-Identifier: MPL-2.0
//! This module provides a trait and some auxiliary types to help abstract and
//! work with non-null pointers.
use vstd::prelude::*;
use vstd_extra::prelude::*;
use alloc::{sync::Arc, boxed::Box};

//mod either;

use core::simd::ptr;
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref, ptr::NonNull};

use crate::prelude::*;

verus!{

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
pub unsafe trait NonNullPtr: Sized +'static {
    /// The target type that this pointer refers to.
    // TODO: Support `Target: ?Sized`.
    type Target;

    // VERUS LIMITATION: Cannot use associated type with lifetime yet.
    /*/// A type that behaves just like a shared reference to the `NonNullPtr`.
    type Ref<'a>
    where
        Self: 'a;*/ 

    // Verus LIMITATION: Cannot use `const` associated type yet.
    /// The power of two of the pointer alignment.
    // const ALIGN_BITS: u32; 
    fn ALIGN_BITS() -> u32;

    /// Converts to a raw pointer.
    ///
    /// Each call to `into_raw` must be paired with a call to `from_raw`
    /// in order to avoid memory leakage.
    ///
    /// The lower [`Self::ALIGN_BITS`] of the raw pointer is guaranteed to
    /// be zero. In other words, the pointer is guaranteed to be aligned to
    /// `1 << Self::ALIGN_BITS`.
    /// VERUS LIMITATION: the #[verus_spec] attribute does not support `with` in trait yet.
    /// SOUNDNESS: Considering also returning the Dealloc permission to ensure no memory leak.
    fn into_raw(self) -> (ret:(NonNull<Self::Target>, Tracked<SmartPtrPointsTo<Self::Target>>))
        ensures
            ptr_mut_from_nonull(ret.0) == self.ptr_mut_spec(),
            ptr_mut_from_nonull(ret.0) == ret.1@.ptr(),
            ret.1@.inv(),
            Self::match_points_to_type(ret.1@),
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
    /// SOUNDNESS: Considering consuming the Dealloc permission to ensure no double free.
    unsafe fn from_raw(ptr: NonNull<Self::Target>, perm: Tracked<SmartPtrPointsTo<Self::Target>>) -> (ret:Self)
        requires
            Self::match_points_to_type(perm@),
            ptr_mut_from_nonull(ptr) == perm@.ptr(),
            perm@.inv(),
        ensures
            ptr_mut_from_nonull(ptr) == ret.ptr_mut_spec(),
    ;

    // VERUS LIMITATION: Cannot use associated type with lifetime yet, will implement it as a free function for each type.
    /*/// Obtains a shared reference to the original pointer.
    ///
    /// # Safety
    ///
    /// The original pointer must outlive the lifetime parameter `'a`, and during `'a`
    /// no mutable references to the pointer will exist.
    //unsafe fn raw_as_ref<'a>(raw: NonNull<Self::Target>) -> Self::Ref<'a>;*/

    // VERUS LIMITATION: Cannot use associated type with lifetime yet, will implement it as a free function for each type.
    /*/// Converts a shared reference to a raw pointer.
    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> NonNull<Self::Target>;*/

    spec fn match_points_to_type(perm: SmartPtrPointsTo<Self::Target>) -> bool;

    // A uninterpreted spec function that returns the inner raw pointer.
    spec fn ptr_mut_spec(self) -> *mut Self::Target;
}

/// A type that represents `&'a Box<T>`.
#[verus_verify]
#[derive(Debug)]
pub struct BoxRef<'a, T> {
    inner: *mut T,
    _marker: PhantomData<&'a T>,
    v_perm: Tracked<&'a BoxPointsTo<T>>,
}

impl<'a, T> BoxRef<'a, T> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        &&& self.inner@.addr != 0
        &&& self.inner@.addr as int % vstd::layout::align_of::<T>() as int == 0
        &&& self.v_perm@.ptr() == self.inner
        &&& self.v_perm@.inv()
    }
    
    pub closed spec fn ptr(self) -> *mut T {
        self.inner
    }

    pub closed spec fn value(self) -> T {
        self.v_perm@.value()
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
        // [VERIFIED] SAFETY: The reference is created through `NonNullPtr::raw_as_ref`, hence
        // the original owned pointer and target must outlive the lifetime parameter `'a`,
        // and during `'a` no mutable references to the pointer will exist.
        
        let Tracked(perm) = self.v_perm;
        proof!{
            use_type_invariant(self);
        }
        //unsafe { &*(self.inner) }
        vstd::raw_ptr::ptr_ref(self.inner, Tracked(perm.tracked_borrow_points_to())) // The function body of ptr_ref is exactly the same as `unsafe { &*(self.inner) }`
    }
}

#[verus_verify]
unsafe impl<T: 'static> NonNullPtr for Box<T> {
    type Target = T;

    /*type Ref<'a>
        = BoxRef<'a, T>
    where
        Self: 'a;*/

    //const ALIGN_BITS: u32 = core::mem::align_of::<T>().trailing_zeros();
    #[verifier::external_body]
    fn ALIGN_BITS() -> u32 {
        core::mem::align_of::<T>().trailing_zeros()
    }

    fn into_raw(self) -> (NonNull<Self::Target>, Tracked<SmartPtrPointsTo<Self::Target>>) {
        //let ptr = Box::into_raw(self);
        let (ptr, Tracked(points_to), Tracked(dealloc)) = box_into_raw(self);
        proof_decl!{
            let tracked perm = SmartPtrPointsTo::new_box_points_to(points_to, dealloc);
        }
        // [VERIFIED] SAFETY: The pointer representing a `Box` can never be NULL. 
        (unsafe { NonNull::new_unchecked(ptr) }, Tracked(perm))
    }

    unsafe fn from_raw(ptr: NonNull<Self::Target>, Tracked(perm): Tracked<SmartPtrPointsTo<Self::Target>>) -> Self {
        proof_decl!{
            let tracked perm = perm.get_box_points_to().tracked_get_points_to_with_dealloc();
        }
        let ptr = ptr.as_ptr();
        
        // [VERIFIED] SAFETY: The safety is upheld by the caller.
        // unsafe { Box::from_raw(ptr) }
        unsafe { box_from_raw(ptr, Tracked(perm.points_to), Tracked(perm.dealloc)) }
    }

    /*unsafe fn raw_as_ref<'a>(raw: NonNull<Self::Target>) -> Self::Ref<'a> {
        BoxRef {
            inner: raw.as_ptr(),
            _marker: PhantomData,
        }
    }*/

    /*fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> NonNull<Self::Target> {
        // SAFETY: The pointer representing a `Box` can never be NULL.
        unsafe { NonNull::new_unchecked(ptr_ref.inner) }
    }*/

    open spec fn match_points_to_type(perm: SmartPtrPointsTo<Self::Target>) -> bool {
        perm is Box
    }

    open spec fn ptr_mut_spec(self) -> *mut Self::Target {
        box_pointer_spec(self)
    }
}

pub fn box_ref_as_raw<T: 'static>(ptr_ref: BoxRef<'_ ,T>) -> (ret:(NonNull<T>, Tracked<&BoxPointsTo<T>>)) 
    ensures
        ret.0 == nonnull_from_ptr_mut(ptr_ref.ptr()),
        ret.1@.ptr().addr() != 0,
        ret.1@.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
        ret.1@.ptr() == ptr_mut_from_nonull(ret.0),
        ret.1@.inv(),

{
    proof!{
        use_type_invariant(&ptr_ref);
    }
    // [VERIFIED] SAFETY: The pointer representing a `Box` can never be NULL.
    (unsafe { NonNull::new_unchecked(ptr_ref.inner) }, ptr_ref.v_perm)
} 

pub unsafe fn box_raw_as_ref<'a, T: 'static>(raw: NonNull<T>, perm: Tracked<&'a BoxPointsTo<T>>) -> BoxRef<'a, T>
    requires
        perm@.ptr() == ptr_mut_from_nonull(raw),
        perm@.inv(),
    {
        BoxRef {
            inner: raw.as_ptr(),
            _marker: PhantomData,
            v_perm: perm,
        }
    }

/// A type that represents `&'a Arc<T>`.
#[verus_verify]
#[derive(Debug)]
pub struct ArcRef<'a, T: 'static> {
    inner: ManuallyDrop<Arc<T>>,
    _marker: PhantomData<&'a Arc<T>>,
    // Note there is no permission field here, because `ArcRef` does not use a raw pointer directly.
}

impl<'a, T> ArcRef<'a, T> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        //&&& self.ptr() == self.v_perm@.ptr()
        //&&& self.v_perm@.inv()
        &&& self.ptr()@.addr != 0
        &&& self.ptr()@.addr as int % vstd::layout::align_of::<T>() as int == 0
    }

    pub open spec fn ptr(self) -> *const T {
        arc_pointer_spec(*self.deref_as_arc_spec())
    }
    
    pub closed spec fn deref_as_arc_spec(&self) -> &Arc<T> {
        &self.inner@
    }

    /// A workaround that Verus does not support implementing spec for Deref trait yet.
    pub broadcast axiom fn arcref_deref_spec_eq(self)
        ensures
            #[trigger] self.deref_as_arc_spec() == #[trigger] self.deref_spec(),
    ;
}

#[verus_verify]
impl<T> Deref for ArcRef<'_, T> {
    type Target = Arc<T>;

    #[verus_spec]
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
    #[verus_spec(ret => ensures *ret == *(self.deref_as_arc_spec()))]
    pub fn deref_target(&self) -> &'a T {
        // SAFETY: The reference is created through `NonNullPtr::raw_as_ref`, hence
        // the original owned pointer and target must outlive the lifetime parameter `'a`,
        // and during `'a` no mutable references to the pointer will exist.
        unsafe { &*(self.deref().deref() as *const T) }
    }
}

unsafe impl<T: 'static> NonNullPtr for Arc<T> {
    type Target = T;

    /* 
    type Ref<'a>
        = ArcRef<'a, T>
    where
        Self: 'a;*/

    //const ALIGN_BITS: u32 = core::mem::align_of::<T>().trailing_zeros();
    #[verifier::external_body]
    fn ALIGN_BITS() -> u32 {
        core::mem::align_of::<T>().trailing_zeros()
    }

    fn into_raw(self) -> (NonNull<Self::Target>, Tracked<SmartPtrPointsTo<Self::Target>>) {
        // let ptr = Arc::into_raw(self).cast_mut();
        let (ptr, Tracked(points_to)) = arc_into_raw(self);
        let ptr = ptr as *mut T;
        proof_decl!{
            let tracked perm = SmartPtrPointsTo::Arc(points_to);
        }
        // [VERIFIED] SAFETY: The pointer representing an `Arc` can never be NULL.
        (unsafe { NonNull::new_unchecked(ptr) }, Tracked(perm))
    }
    
    unsafe fn from_raw(ptr: NonNull<Self::Target>, Tracked(perm): Tracked<SmartPtrPointsTo<Self::Target>>) -> Self {
        proof_decl!{
            let tracked perm = perm.get_arc_points_to();
        }
        //let ptr = ptr.as_ptr().cast_const();
        let ptr = ptr.as_ptr() as *const T;

        // [VERIFIED] SAFETY: The safety is upheld by the caller.
        // unsafe { Arc::from_raw(ptr) }
        unsafe { arc_from_raw(ptr, Tracked(perm)) }
    }
    /*
    unsafe fn raw_as_ref<'a>(raw: NonNull<Self::Target>) -> Self::Ref<'a> {
        // SAFETY: The safety is upheld by the caller.
        unsafe {
            ArcRef {
                inner: ManuallyDrop::new(Arc::from_raw(raw.as_ptr())),
                _marker: PhantomData,
            }
        }
    }

    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> NonNull<Self::Target> {
        NonNullPtr::into_raw(ManuallyDrop::into_inner(ptr_ref.inner))
    }*/

    open spec fn match_points_to_type(perm: SmartPtrPointsTo<Self::Target>) -> bool {
        perm is Arc
    }

    open spec fn ptr_mut_spec(self) -> *mut Self::Target {
        arc_pointer_spec(self) as *mut Self::Target
    }
}

pub fn arc_ref_as_raw<T: 'static>(ptr_ref: ArcRef<'_ ,T>) -> (ret:(NonNull<T>, Tracked<ArcPointsTo<T>>)) 
    ensures
        ret.0 == nonnull_from_ptr_mut(ptr_ref.ptr() as *mut T),
        ret.1@.ptr().addr() != 0,
        ret.1@.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
        ret.1@.ptr() == ptr_mut_from_nonull(ret.0),
        ret.1@.inv(),
{
    proof!{
        use_type_invariant(&ptr_ref);
    }
    // NonNullPtr::into_raw(ManuallyDrop::into_inner(ptr_ref.inner))
    let (ptr, Tracked(perm)) = NonNullPtr::into_raw(ManuallyDrop::into_inner(ptr_ref.inner));
    (ptr, Tracked(perm.get_arc_points_to()))
}

pub unsafe fn arc_raw_as_ref<'a, T: 'static>(raw: NonNull<T>, perm: Tracked<ArcPointsTo<T>>) -> (ret: ArcRef<'a, T>)
    requires
        perm@.ptr() == ptr_mut_from_nonull(raw),
        perm@.inv(),
    ensures
        ret.ptr() == perm@.ptr(),
    {
        unsafe{
            ArcRef {
                inner: ManuallyDrop::new(arc_from_raw(raw.as_ptr(), perm)),
                _marker: PhantomData,
            }
        }
    }
}

verus!{
    broadcast use group_nonnull;
}