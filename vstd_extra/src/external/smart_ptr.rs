use std::sync::Arc;
use vstd::layout::valid_layout;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use crate::raw_ptr_extra::*;


verus!{
// VERUS LIMITATION: can not add ghost parameter in external specification yet, sp we wrap it in an exterbnal_body function
// The memory layout ensures that Box<T> has the following properties:
//  1. The pointer is aligned.
//  2. The pointer is non-null even for zero-sized types.
//  3. The pointer points to a valid value, whose layout is determined by Layout::for_value (exactly size_of::<T>() and align_of::<T>()).
// See https://doc.rust-lang.org/stable/std/boxed/index.html
// Its guarantee is actually much stronger than PointsTowithDealloc.inv().
#[verifier::external_body]
pub fn box_into_raw<T>(b: Box<T>) -> (ret: (*mut T, Tracked<PointsTo<T>>, Tracked<Option<Dealloc>>)) 
ensures
    ret.0 == ret.1@.ptr(),
    ret.1@.ptr().addr() != 0,
    ret.1@.is_init(),
    ret.1@.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
    match ret.2@ {
        Some(dealloc) => {
            &&& vstd::layout::size_of::<T>() > 0
            &&& dealloc.addr() == ret.1@.ptr().addr()
            &&& dealloc.size() == vstd::layout::size_of::<T>()
            &&& dealloc.align() == vstd::layout::align_of::<T>()
            &&& dealloc.provenance() == ret.1@.ptr()@.provenance
            &&& valid_layout(size_of::<T>(), align_of::<T>())
        },
        None => {
            &&& vstd::layout::size_of::<T>() == 0
        },
    },

{
    (Box::into_raw(b), Tracked::assume_new(), Tracked::assume_new())
}

#[verifier::external_body]
pub unsafe fn box_from_raw<T>(ptr: *mut T, tracked points_to: Tracked<PointsTo<T>>, tracked dealloc: Tracked<Option<Dealloc>>) -> (ret: Box<T>)
    requires
        ptr@.addr != 0,
        points_to@.ptr() == ptr,
        points_to@.is_init(),
        points_to@.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
        match dealloc@ {
            Some(dealloc) => {
                &&& vstd::layout::size_of::<T>() > 0
                &&& dealloc.addr() == ptr@.addr
                &&& dealloc.size() == vstd::layout::size_of::<T>()
                &&& dealloc.align() == vstd::layout::align_of::<T>()
                &&& dealloc.provenance() == ptr@.provenance
                &&& valid_layout(size_of::<T>(), align_of::<T>())
            },
            None => {
                &&& vstd::layout::size_of::<T>() == 0
            },
        },
    {
        unsafe { Box::from_raw(ptr) }
    }

// VERUS LIMITATION: can not add ghost parameter in external specification yet, sp we wrap it in an exterbnal_body function
// The memory layout ensures that Box<T> has the following properties:
//  1. The pointer is aligned.
//  2. The pointer is non-null even for zero-sized types.
//  3. The pointer points to a valid value, whose layout is determined by Layout::for_value (exactly size_of::<T>() and align_of::<T>()).
// See https://doc.rust-lang.org/stable/std/boxed/index.html
// Its guarantee is actually much stronger than PointsTowithDealloc.inv().
#[verifier::external_body]
pub fn arc_into_raw<T>(p: Arc<T>) -> (ret: (*const T, Tracked<PointsTo<T>>, Tracked<Option<Dealloc>>)) 
ensures
    ret.0 == ret.1@.ptr(),
    ret.1@.ptr().addr() != 0,
    ret.1@.is_init(),
    ret.1@.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
    match ret.2@ {
        Some(dealloc) => {
            &&& vstd::layout::size_of::<T>() > 0
            &&& dealloc.addr() == ret.1@.ptr().addr()
            &&& dealloc.size() == vstd::layout::size_of::<T>()
            &&& dealloc.align() == vstd::layout::align_of::<T>()
            &&& dealloc.provenance() == ret.1@.ptr()@.provenance
            &&& valid_layout(size_of::<T>(), align_of::<T>())
        },
        None => {
            &&& vstd::layout::size_of::<T>() == 0
        },
    },

{
    (Arc::into_raw(p), Tracked::assume_new(), Tracked::assume_new())
}

#[verifier::external_body]
/// According to the documentation, `[Arc::from_raw`](https://doc.rust-lang.org/std/sync/struct.Arc.html#method.from_raw) allows transmuting between different types as long as the pointer has the same size and alignment.
/// In verification this responsibility is dispatched to casting the PointsTo<T> appropriately, which is not handled here.
pub unsafe fn arc_from_raw<T>(ptr: *const T, tracked points_to: Tracked<PointsTo<T>>, tracked dealloc: Tracked<Option<Dealloc>>) -> (ret: Arc<T>)
    requires
        ptr@.addr != 0,
        points_to@.ptr() == ptr,
        points_to@.is_init(),
        points_to@.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
        match dealloc@ {
            Some(dealloc) => {
                &&& vstd::layout::size_of::<T>() > 0
                &&& dealloc.addr() == ptr@.addr
                &&& dealloc.size() == vstd::layout::size_of::<T>()
                &&& dealloc.align() == vstd::layout::align_of::<T>()
                &&& dealloc.provenance() == ptr@.provenance
                &&& valid_layout(size_of::<T>(), align_of::<T>())
            },
            None => {
                &&& vstd::layout::size_of::<T>() == 0
            },
        },
    {
        unsafe { Arc::from_raw(ptr) }
    }
}