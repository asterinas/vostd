use crate::ownership::*;
use crate::raw_ptr_extra::*;
use std::sync::Arc;
use vstd::layout::valid_layout;
use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

// The permssion to access memory given by the `into_raw` methods of smart pointers like `Box` and `Arc`.
/// For Box<T>, the `into_raw` method gives you the ownership of the memory
pub type BoxPointsTo<T> = PointsTowithDealloc<T>;

/// For Arc<T>, the `into_raw` method gives shared access to the memory, and the reference count is not decreased,
/// so the value will not be deallocated until we convert back to Arc<T> and drop it.
/// See https://doc.rust-lang.org/src/alloc/sync.rs.html#1480.
pub type ArcPointsTo<T> = &'static PointsTo<T>;

pub tracked enum SmartPtrPointsTo<T: 'static> {
    Box(BoxPointsTo<T>),
    Arc(ArcPointsTo<T>),
}

impl<T> Inv for SmartPtrPointsTo<T> {
    open spec fn inv(self) -> bool {
        match self {
            SmartPtrPointsTo::Box(b) => {
                &&& b.inv()
                &&& b.dealloc_aligned()
                &&& b.is_init()
            },
            SmartPtrPointsTo::Arc(a) => {
                &&& a.ptr().addr() != 0
                &&& a.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0
                &&& a.is_init()
            },
        }
    }
}

impl<T> SmartPtrPointsTo<T> {
    pub open spec fn ptr(self) -> *mut T {
        match self {
            SmartPtrPointsTo::Box(b) => b.ptr(),
            SmartPtrPointsTo::Arc(a) => a.ptr(),
        }
    }

    pub open spec fn addr(self) -> usize {
        self.ptr().addr()
    }

    pub open spec fn is_init(self) -> bool {
        match self {
            SmartPtrPointsTo::Box(b) => b.is_init(),
            SmartPtrPointsTo::Arc(a) => a.is_init(),
        }
    }

    pub open spec fn is_uninit(self) -> bool {
        match self {
            SmartPtrPointsTo::Box(b) => b.is_uninit(),
            SmartPtrPointsTo::Arc(a) => a.is_uninit(),
        }
    }

    pub proof fn get_box_points_to(tracked self) -> (tracked ret: BoxPointsTo<T>)
        requires
            self is Box,
        returns
            self->Box_0,
    {
        let tracked option_perm = match self {
            SmartPtrPointsTo::Box(p) => Some(p),
            _ => None,
        };
        option_perm.tracked_unwrap()
    }

    pub proof fn get_arc_points_to(tracked self) -> (tracked ret: ArcPointsTo<T>)
        requires
            self is Arc,
        returns
            self->Arc_0,
    {
        let tracked option_perm = match self {
            SmartPtrPointsTo::Arc(p) => Some(p),
            _ => None,
        };
        option_perm.tracked_unwrap()
    }
}

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
            None => { &&& vstd::layout::size_of::<T>() == 0 },
        },
{
    (Box::into_raw(b), Tracked::assume_new(), Tracked::assume_new())
}

#[verifier::external_body]
pub unsafe fn box_from_raw<T>(
    ptr: *mut T,
    tracked points_to: Tracked<PointsTo<T>>,
    tracked dealloc: Tracked<Option<Dealloc>>,
) -> (ret: Box<T>)
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
            None => { &&& vstd::layout::size_of::<T>() == 0 },
        },
{
    unsafe { Box::from_raw(ptr) }
}

// VERUS LIMITATION: can not add ghost parameter in external specification yet, sp we wrap it in an exterbnal_body function
// `Arc::into_raw` will not decrease the reference count, so the memory will keep valid until we convert back to Arc<T> and drop it.
#[verifier::external_body]
pub fn arc_into_raw<T>(p: Arc<T>) -> (ret: (*const T, Tracked<ArcPointsTo<T>>))
    ensures
        ret.0 == ret.1@.ptr(),
        ret.1@.ptr().addr() != 0,
        ret.1@.is_init(),
        ret.1@.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
{
    (Arc::into_raw(p), Tracked::assume_new())
}

#[verifier::external_body]
/// According to the documentation, `[Arc::from_raw`](https://doc.rust-lang.org/std/sync/struct.Arc.html#method.from_raw) allows transmuting between different types as long as the pointer has the same size and alignment.
/// In verification this responsibility is dispatched to casting the PointsTo<T> appropriately, which is not handled here.
pub unsafe fn arc_from_raw<T>(ptr: *const T, tracked points_to: Tracked<ArcPointsTo<T>>) -> (ret:
    Arc<T>)
    requires
        ptr@.addr != 0,
        points_to@.ptr() == ptr,
        points_to@.is_init(),
        points_to@.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
{
    unsafe { Arc::from_raw(ptr) }
}

} // verus!
