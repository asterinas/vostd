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
}