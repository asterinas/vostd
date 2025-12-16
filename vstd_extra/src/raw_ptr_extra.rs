use crate::ownership::*;
use vstd::layout::size_of as layout_size_of;
use vstd::layout::valid_layout;
use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

// Record Typed access permission along with Dealloc permission.
pub tracked struct PointsTowithDealloc<T> {
    pub tracked points_to: PointsTo<T>,
    pub tracked dealloc: Dealloc,
}

impl<T> Inv for PointsTowithDealloc<T> {
    open spec fn inv(self) -> bool {
        &&& self.points_to.ptr().addr() == self.dealloc.addr()
        &&& self.dealloc.size() == size_of::<
            T,
        >() as int
        // By definition in raw_ptr, the alignment of Dealloc is determined by alloc and it is not related to the alignment of T.
        // This alignment is to enable the conversion between PointsTo<T> and PoinstToRaw
        &&& self.points_to.ptr().addr() as int % align_of::<T>() as int == 0
        &&& valid_layout(size_of::<T>(), self.dealloc.align() as usize)
        &&& self.points_to.ptr()@.provenance == self.dealloc.provenance()
    }
}

impl<T> PointsTowithDealloc<T> {
    pub open spec fn addr(self) -> usize {
        self.points_to.ptr().addr()
    }

    pub open spec fn is_uninit(self) -> bool {
        self.points_to.is_uninit()
    }

    pub proof fn new(points_to: PointsTo<T>, dealloc: Dealloc) -> (ret: Self)
        requires
            valid_layout(size_of::<T>(), dealloc.align() as usize),
            points_to.ptr().addr() == dealloc.addr(),
            points_to.ptr()@.provenance == dealloc.provenance(),
            dealloc.size() == size_of::<T>() as int,
            points_to.ptr().addr() as int % align_of::<T>() as int == 0,
        ensures
            ret.inv(),
    {
        PointsTowithDealloc { points_to, dealloc }
    }

    pub proof fn into_raw(tracked self) -> (ret: (PointsToRaw, Dealloc))
        requires
            self.inv(),
            self.is_uninit(),
        ensures
            ret.1.addr() == self.addr(),
            ret.1.addr() as int % align_of::<T>() as int == 0,
            ret.1.size() == size_of::<T>() as int,
            ret.1.provenance() == ret.0.provenance(),
            ret.0.is_range(ret.1.addr() as int, size_of::<T>() as int),
    {
        let start = self.points_to.ptr().addr() as int;
        let tracked points_to_raw = self.points_to.into_raw();
        // PointsTo::into_raw ensures the range using vstd::layout::size_of, which returns int.
        // We need to show it matches core::mem::size_of::<T>() as int.
        assume(layout_size_of::<T>() == size_of::<T>() as int);
        assert(points_to_raw.is_range(start, size_of::<T>() as int));
        (points_to_raw, self.dealloc)
    }
}

} // verus!
