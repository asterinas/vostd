use crate::ownership::*;
use crate::raw_ptr_extra::*;
use std::sync::Arc;
use vstd::layout::valid_layout;
use vstd::prelude::*;
use vstd::raw_ptr::*;

// A unified interface for the raw ptr permission returned by `into_raw` methods of smart pointers like `Box` and `Arc`.
verus! {

// The permssion to access memory given by the `into_raw` methods of smart pointers like `Box` and `Arc`.
/// For `Box<T>`, the `into_raw` method gives you the ownership of the memory
pub tracked struct BoxPointsTo<T> {
    pub perm: PointsTowithDealloc<T>,
}

/// For `Arc<T>`, the `into_raw` method gives shared access to the memory, and the reference count is not decreased,
/// so the value will not be deallocated until we convert back to `Arc<T>` and drop it.
/// See <https://doc.rust-lang.org/src/alloc/sync.rs.html#1480>.
pub tracked struct ArcPointsTo<T: 'static> {
    pub perm: &'static PointsTo<T>,
}

pub tracked enum SmartPtrPointsTo<T: 'static> {
    Box(BoxPointsTo<T>),
    Arc(ArcPointsTo<T>),
}

impl<T> BoxPointsTo<T> {
    pub open spec fn perm(self) -> PointsTowithDealloc<T> {
        self.perm
    }

    pub open spec fn ptr(self) -> *mut T {
        self.perm.ptr()
    }

    pub open spec fn addr(self) -> usize {
        self.ptr().addr()
    }

    pub open spec fn is_uninit(self) -> bool {
        self.perm.is_uninit()
    }

    pub open spec fn is_init(self) -> bool {
        self.perm.is_init()
    }

    pub open spec fn value(self) -> T {
        self.perm.value()
    }

    pub proof fn tracked_get_points_to_with_dealloc(tracked self) -> (tracked ret:
        PointsTowithDealloc<T>)
        returns
            self.perm,
    {
        self.perm
    }

    pub proof fn tracked_borrow_points_to_with_dealloc(tracked &self) -> (tracked ret:
        &PointsTowithDealloc<T>)
        returns
            &self.perm,
    {
        &self.perm
    }

    pub proof fn tracked_get_points_to(tracked self) -> (tracked ret: PointsTo<T>)
        returns
            self.perm.points_to,
    {
        self.tracked_get_points_to_with_dealloc().tracked_get_points_to()
    }

    pub proof fn tracked_borrow_points_to(tracked &self) -> (tracked ret: &PointsTo<T>)
        returns
            &self.perm.points_to,
    {
        &self.tracked_borrow_points_to_with_dealloc().tracked_borrow_points_to()
    }
}

impl<T> ArcPointsTo<T> {
    pub open spec fn perm(self) -> &'static PointsTo<T> {
        self.perm
    }

    pub open spec fn ptr(self) -> *mut T {
        self.perm.ptr()
    }

    pub open spec fn addr(self) -> usize {
        self.ptr().addr()
    }

    pub open spec fn is_uninit(self) -> bool {
        self.perm.is_uninit()
    }

    pub open spec fn is_init(self) -> bool {
        self.perm.is_init()
    }

    pub open spec fn value(self) -> T {
        self.perm.value()
    }

    pub proof fn tracked_borrow_points_to(tracked &self) -> (tracked ret: &'static PointsTo<T>)
        returns
            self.perm,
    {
        self.perm
    }
}

impl<T> Inv for BoxPointsTo<T> {
    open spec fn inv(self) -> bool {
        &&& self.perm.inv()
        &&& self.perm.dealloc_aligned()
        &&& self.is_init()
    }
}

impl<T> Inv for ArcPointsTo<T> {
    open spec fn inv(self) -> bool {
        &&& self.addr() != 0
        &&& self.addr() as int % vstd::layout::align_of::<T>() as int == 0
        &&& self.is_init()
    }
}

impl<T> Inv for SmartPtrPointsTo<T> {
    open spec fn inv(self) -> bool {
        match self {
            SmartPtrPointsTo::Box(b) => { b.inv() },
            SmartPtrPointsTo::Arc(a) => { a.inv() },
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
        match self {
            SmartPtrPointsTo::Box(p) => p,
            _ => proof_from_false(),
        }
    }

    pub proof fn get_arc_points_to(tracked self) -> (tracked ret: ArcPointsTo<T>)
        requires
            self is Arc,
        returns
            self->Arc_0,
    {
        match self {
            SmartPtrPointsTo::Arc(p) => p,
            _ => proof_from_false(),
        }
    }

    pub proof fn new_box_points_to(
        tracked points_to: PointsTo<T>,
        tracked dealloc: Option<Dealloc>,
    ) -> (tracked ret: SmartPtrPointsTo<T>)
        requires
            points_to.is_init(),
            match dealloc {
                Some(dealloc) => {
                    &&& vstd::layout::size_of::<T>() > 0
                    &&& valid_layout(size_of::<T>(), dealloc.align() as usize)
                    &&& points_to.ptr().addr() == dealloc.addr()
                    &&& points_to.ptr()@.provenance == dealloc.provenance()
                    &&& dealloc.size() == vstd::layout::size_of::<T>()
                    &&& dealloc.align() == vstd::layout::align_of::<T>()
                },
                None => { vstd::layout::size_of::<T>() == 0 },
            },
        ensures
            ret.inv(),
            ret is Box,
        returns
            (SmartPtrPointsTo::Box(
                BoxPointsTo { perm: PointsTowithDealloc { points_to, dealloc } },
            )),
    {
        let tracked box_points_to = BoxPointsTo {
            perm: PointsTowithDealloc::new(points_to, dealloc),
        };
        SmartPtrPointsTo::Box(box_points_to)
    }

    pub proof fn new_arc_points_to(tracked points_to: &'static PointsTo<T>) -> (tracked ret:
        SmartPtrPointsTo<T>)
        requires
            points_to.is_init(),
            points_to.ptr().addr() != 0,
            points_to.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
        ensures
            ret.inv(),
            ret is Arc,
        returns
            (SmartPtrPointsTo::Arc(ArcPointsTo { perm: points_to })),
    {
        let tracked arc_points_to = ArcPointsTo { perm: points_to };
        SmartPtrPointsTo::Arc(arc_points_to)
    }
}

pub uninterp spec fn box_pointer_spec<T>(b: Box<T>) -> *mut T;

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
        ret.0 == box_pointer_spec(b),
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
    ensures
        box_pointer_spec(ret) == ptr,
{
    unsafe { Box::from_raw(ptr) }
}

pub uninterp spec fn arc_pointer_spec<T>(a: Arc<T>) -> *const T;

// VERUS LIMITATION: can not add ghost parameter in external specification yet, sp we wrap it in an exterbnal_body function
// `Arc::into_raw` will not decrease the reference count, so the memory will keep valid until we convert back to Arc<T> and drop it.
#[verifier::external_body]
pub fn arc_into_raw<T>(p: Arc<T>) -> (ret: (*const T, Tracked<ArcPointsTo<T>>))
    ensures
        ret.0 == arc_pointer_spec(p),
        ret.0 == ret.1@.ptr(),
        ret.1@.ptr().addr() != 0,
        ret.1@.is_init(),
        ret.1@.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
{
    (Arc::into_raw(p), Tracked::assume_new())
}

#[verifier::external_body]
/// According to the documentation, [`Arc::from_raw`](<https://doc.rust-lang.org/std/sync/struct.Arc.html#method.from_raw>) allows transmuting between different types as long as the pointer has the same size and alignment.
/// In verification this responsibility is dispatched to casting the `PointsTo<T>` appropriately, which is not handled here.
pub unsafe fn arc_from_raw<T>(ptr: *const T, tracked points_to: Tracked<ArcPointsTo<T>>) -> (ret:
    Arc<T>)
    requires
        ptr@.addr != 0,
        points_to@.ptr() == ptr,
        points_to@.is_init(),
        points_to@.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
    ensures
        arc_pointer_spec(ret) == ptr,
{
    unsafe { Arc::from_raw(ptr) }
}

} // verus!
