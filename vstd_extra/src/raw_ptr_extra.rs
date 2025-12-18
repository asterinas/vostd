use crate::ownership::*;
use vstd::layout::size_of as layout_size_of;
use vstd::layout::valid_layout;
use vstd::prelude::*;
use vstd::raw_ptr::*;

// NOTE: vstd::layout::size_of and size_of are actually two different functions,
// See: https://verus-lang.zulipchat.com/#narrow/channel/399078-help/topic/Multiple.20definitions.20of.20.60align_of.60.20and.20.60size_of.60.20in.20raw_ptr/with/563994445

verus! {

pub broadcast proof fn lemma_two_size_of_equal<T>()
    requires
        vstd::layout::size_of::<T>() <= usize::MAX,
    ensures
        #[trigger] vstd::layout::size_of::<T>() == size_of::<T>(),
{}

pub broadcast proof fn lemma_two_align_of_equal<T>()
    requires
        vstd::layout::align_of::<T>() <= usize::MAX,
    ensures
        #[trigger] vstd::layout::align_of::<T>() == align_of::<T>(),
{}

// Record Typed access permission along with Dealloc permission.
// This is similar to PPtr::PointsTo, but we want to make it as low-level and general as possible.
// Difference with PPtr::PointsTo:
// 1. Allowing null pointers (addr == 0).
// 2. Relaxed alignment requirement between Dealloc::align and align_of::<T>().
// TODO: consider expose_provenance
pub tracked struct PointsTowithDealloc<T> {
    pub tracked points_to: PointsTo<T>,
    // The Dealloc permission is only valid with non-zero size.
    pub tracked dealloc: Option<Dealloc>,
}

impl<T> Inv for PointsTowithDealloc<T> {
    open spec fn inv(self) -> bool {
        // This alignment is to enable the conversion between PointsTo<T> and PoinstToRaw
        &&& self.points_to.ptr().addr() as int % vstd::layout::align_of::<T>() as int == 0
        &&& match self.dealloc {
            Some(dealloc) => {
                &&& vstd::layout::size_of::<T>() > 0
                &&& self.points_to.ptr().addr() == dealloc.addr()
                &&& self.points_to.ptr()@.provenance == dealloc.provenance()
                &&& dealloc.size() == vstd::layout::size_of::<T>()
                // By definition in raw_ptr, the alignment of Dealloc is determined by alloc and it idoes not need to be equal to the alignment of T.
                // This alignment requirement is to ensure correctness of allocation and deallocation.
                &&& valid_layout(size_of::<T>(), dealloc.align() as usize)
            },
            None => {vstd::layout::size_of::<T>() == 0},
        }

    }
}

impl<T> PointsTowithDealloc<T> {
    pub open spec fn ptr(self) -> *mut T {
        self.points_to.ptr()
    }
    
    pub open spec fn addr(self) -> usize {
        self.ptr().addr()
    }

    pub open spec fn is_uninit(self) -> bool {
        self.points_to.is_uninit()
    }

    pub proof fn new(tracked points_to: PointsTo<T>, tracked dealloc: Option<Dealloc>) -> (tracked ret: Self)
        requires
            match dealloc {
                Some(dealloc) => {
                    &&& vstd::layout::size_of::<T>() > 0
                    &&& valid_layout(size_of::<T>(), dealloc.align() as usize)
                    &&& points_to.ptr().addr() == dealloc.addr()
                    &&& points_to.ptr()@.provenance == dealloc.provenance()
                    &&& dealloc.size() == vstd::layout::size_of::<T>()
                },
                None => {
                    vstd::layout::size_of::<T>() == 0
                },
            },
        ensures
            ret.inv(),
        returns
            (PointsTowithDealloc { points_to, dealloc })
    {
        points_to.is_aligned();
        PointsTowithDealloc { points_to, dealloc }
    }

    pub proof fn new_non_zero_size(tracked points_to: PointsTo<T>, tracked dealloc: Dealloc) -> (tracked ret: Self)
        requires
            0 < vstd::layout::size_of::<T>(),
            valid_layout(size_of::<T>(), dealloc.align() as usize),
            points_to.ptr().addr() == dealloc.addr(),
            points_to.ptr()@.provenance == dealloc.provenance(),
            dealloc.size() == vstd::layout::size_of::<T>() as int,
            dealloc.align() ==  vstd::layout::align_of::<T>(),
        ensures
            ret.inv(),
        returns
            (PointsTowithDealloc { points_to, dealloc: Some(dealloc) })
    {
        points_to.is_aligned();
        PointsTowithDealloc { points_to, dealloc: Some(dealloc) }
    }
    
    pub proof fn new_zero_size(tracked points_to: PointsTo<T>) -> (tracked ret: Self)
        requires
            vstd::layout::size_of::<T>() == 0,
        ensures
            ret.inv(),
        returns
            (PointsTowithDealloc { points_to, dealloc: None })
    {
        points_to.is_aligned();
        PointsTowithDealloc { points_to, dealloc: None }
    }
    
    pub proof fn into_raw(tracked self) -> (tracked ret: (PointsToRaw, Option<Dealloc>))
        requires
            self.inv(),
            self.is_uninit(),
        ensures
            match ret.1 {
                Some(dealloc) => { 
                    &&& vstd::layout::size_of::<T>() > 0
                    &&& dealloc.addr() == self.addr()
                    &&& dealloc.addr() as int % vstd::layout::align_of::<T>() as int == 0
                    &&& dealloc.size() == vstd::layout::size_of::<T>() as int
                    &&& dealloc.provenance() == ret.0.provenance()
                    &&& ret.0.is_range(dealloc.addr() as int, vstd::layout::size_of::<T>() as int)
                },
                None => {
                    &&& vstd::layout::size_of::<T>() == 0
                },
            },
            
    {
        let tracked points_to_raw = self.points_to.into_raw();
        (points_to_raw, self.dealloc)
    }
}

} // verus!
