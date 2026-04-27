use crate::ownership::*;
use crate::raw_ptr_extra::*;
use alloc::sync::Arc;
use vstd::layout::valid_layout;
use vstd::prelude::*;
use vstd::raw_ptr::*;

// A unified interface for the raw ptr permission returned by `into_raw` methods of smart pointers like `Box` and `Arc`.
verus! {

/// A verification-only trait that abstracts the permission that tracks both the pointer and the value it points to.
pub trait PtrPointsToTrait {
    /// The type of the pointer.
    type Ptr;

    /// The type of the value that the pointer points to.
    type Target;

    spec fn ptr(self) -> *mut Self::Target;

    spec fn view_target(self) -> Self::Target;
}

impl<T> PtrPointsToTrait for BoxPointsTo<T> {
    type Ptr = Box<T>;

    type Target = T;

    open spec fn ptr(self) -> *mut T {
        self.perm.ptr()
    }

    open spec fn view_target(self) -> T {
        self.perm.value()
    }
}

impl<T> PtrPointsToTrait for ArcPointsTo<T> {
    type Ptr = Arc<T>;

    type Target = T;

    open spec fn ptr(self) -> *mut T {
        self.perm.ptr()
    }

    open spec fn view_target(self) -> T {
        self.perm.value()
    }
}

// The permission to access memory given by the `into_raw` methods of smart pointers like `Box` and `Arc`.
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
        &&& self.perm.is_init()
    }
}

impl<T> Inv for ArcPointsTo<T> {
    open spec fn inv(self) -> bool {
        &&& self.addr() != 0
        &&& self.addr() as int % vstd::layout::align_of::<T>() as int == 0
        &&& self.perm.is_init()
    }
}

/// A wrapper around `Box::into_raw` that also returns the permission to access the memory.
///
/// Soundness: it is unsound to create a `ptr` method for `Box<T>` that returns the raw pointer without the permission.
/// As Verus only compares the value of the `Box<T>` for equality, so the following code will be wrongly verified:
/// ```rust
/// let b1 = Box::new(1);
/// let b2 = Box::new(1);
/// assert(b1.ptr() == b2.ptr()); // this will be verified but is actually not true, as b1 and b2 are different allocations with different pointers.
/// ```
// VERUS LIMITATION: can not add ghost parameter in external specification yet, sp we wrap it in an external_body function
// The memory layout ensures that Box<T> has the following properties:
//  1. The pointer is aligned.
//  2. The pointer is non-null even for zero-sized types.
//  3. The pointer points to a valid value, whose layout is determined by Layout::for_value (exactly size_of::<T>() and align_of::<T>()).
// See https://doc.rust-lang.org/stable/std/boxed/index.html
// Its guarantee is actually much stronger than PointsTowithDealloc.inv().
#[verifier::external_body]
#[verus_spec(ret =>
    with
        -> perm: Tracked<(PointsTo<T>, Option<Dealloc>)>,
    ensures
        ret == perm@.0.ptr(),
        perm@.0.ptr().addr() != 0,
        perm@.0.is_init(),
        perm@.0.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
        perm@.0.value() == *b,
        match perm@.1 {
            Some(dealloc) => {
                &&& vstd::layout::size_of::<T>() > 0
                &&& dealloc.addr() == perm@.0.ptr().addr()
                &&& dealloc.size() == vstd::layout::size_of::<T>()
                &&& dealloc.align() == vstd::layout::align_of::<T>()
                &&& dealloc.provenance() == perm@.0.ptr()@.provenance
                &&& valid_layout(size_of::<T>(), align_of::<T>())
            },
            None => { &&& vstd::layout::size_of::<T>() == 0 },
        }
)]
pub fn box_into_raw<T>(b: Box<T>) -> *mut T {
    proof_with!(|= Tracked::assume_new());
    Box::into_raw(b)
}

#[verifier::external_body]
#[verus_spec(ret =>
    with
        Tracked(points_to): Tracked<PointsTo<T>>,
        Tracked(dealloc): Tracked<Option<Dealloc>>,
    requires
        ptr@.addr != 0,
        points_to.ptr() == ptr,
        points_to.is_init(),
        points_to.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
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
        *ret == points_to.value(),
    )]
pub unsafe fn box_from_raw<T>(ptr: *mut T) -> Box<T> {
    unsafe { Box::from_raw(ptr) }
}

/// A wrapper around `Arc::into_raw` that also returns the permission to access the memory.
///
/// Soundness: the soundness concern is similar to `box_into_raw`.
// VERUS LIMITATION: can not add ghost parameter in external specification yet, sp we wrap it in an external_body function
// `Arc::into_raw` will not decrease the reference count, so the memory will keep valid until we convert back to Arc<T> and drop it.
#[verifier::external_body]
#[verus_spec(ret =>
    with
        -> perm: Tracked<ArcPointsTo<T>>,
    ensures
        ret == perm@.ptr(),
        perm@.ptr().addr() != 0,
        perm@.is_init(),
        perm@.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
        perm@.value() == *p,
)]
pub fn arc_into_raw<T>(p: Arc<T>) -> *const T {
    proof_with!(|= Tracked::assume_new());
    Arc::into_raw(p)
}

/// According to the documentation, [`Arc::from_raw`](<https://doc.rust-lang.org/std/sync/struct.Arc.html#method.from_raw>) allows transmuting between different types as long as the pointer has the same size and alignment.
/// In verification this responsibility is dispatched to casting the `PointsTo<T>` appropriately, which is not handled here.
#[verifier::external_body]
#[verus_spec(ret =>
    with
        Tracked(points_to): Tracked<ArcPointsTo<T>>,
    requires
        ptr.addr() != 0,
        points_to.ptr() == ptr,
        points_to.is_init(),
        points_to.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0,
    ensures
        *ret == points_to.value(),
)]
pub unsafe fn arc_from_raw<T>(ptr: *const T) -> Arc<T> {
    unsafe { Arc::from_raw(ptr) }
}

} // verus!
