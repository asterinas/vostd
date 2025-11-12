// SPDX-License-Identifier: MPL-2.0
//! A contiguous range of frames.
use vstd::prelude::*;

use core::{fmt::Debug, mem::ManuallyDrop, ops::Range};

use crate::mm::frame::inc_frame_ref_count;
use crate::mm::frame::untyped::AnyUFrameMeta;

use vstd_extra::ownership::*;

use aster_common::prelude::frame::*;
use aster_common::prelude::*;

verus! {

// impl<M: AnyFrameMeta + ?Sized> Debug for Segment<M> {
//     fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
//         write!(f, "Segment({:#x}..{:#x})", self.range.start, self.range.end)
//     }
// }
/// A contiguous range of homogeneous untyped physical memory frames that have any metadata.
///
/// In other words, the metadata of the frames are of the same type, and they
/// are untyped, but the type of metadata is not known at compile time. An
/// [`USegment`] as a parameter accepts any untyped segments.
///
/// The usage of this frame will not be changed while this object is alive.
pub type USegment = Segment<dyn AnyUFrameMeta>;

// impl<M: AnyFrameMeta + ?Sized> Drop for Segment<M> {
//     fn drop(&mut self) {
//         for paddr in self.range.clone().step_by(PAGE_SIZE()()) {
//             // SAFETY: for each frame there would be a forgotten handle
//             // when creating the `Segment` object.
//             drop(unsafe { Frame::<M>::from_raw(paddr) });
//         }
//     }
// }
// impl<M: AnyFrameMeta + ?Sized> Clone for Segment<M> {
//     fn clone(&self) -> (res: Self)
//         ensures
//             res == *self,
//     {
//         let mut i = 0;
//         let addr_len = (self.range.end - self.range.start) / PAGE_SIZE();
//         while i < addr_len
//             decreases addr_len - i,
//         {
//             let paddr = self.range.start + i * PAGE_SIZE();
//             // SAFETY: for each frame there would be a forgotten handle
//             // when creating the `Segment` object, so we already have
//             // reference counts for the frames.
//             unsafe {
//                 inc_frame_ref_count(paddr);
//             }
//         }
//         Self { range: self.range.clone(), _marker: core::marker::PhantomData }
//     }
// }
impl<M: AnyFrameMeta> Segment<M> {
    #[rustc_allow_incoherent_impl]
    #[verifier::inline]
    pub open spec fn start_paddr_spec(&self) -> Paddr
        recommends
            self.inv(),
    {
        self.range.start
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::inline]
    pub open spec fn end_paddr_spec(&self) -> Paddr
        recommends
            self.inv(),
    {
        self.range.end
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::inline]
    pub open spec fn size_spec(&self) -> usize
        recommends
            self.inv(),
    {
        (self.range.end - self.range.start) as usize
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn split_spec(self, offset: usize) -> (Self, Self)
        recommends
            self.inv(),
            offset % PAGE_SIZE() == 0,
            0 < offset < self.size_spec(),
    {
        let at = (self.range.start + offset) as usize;
        (
            Self { range: self.range.start..at, _marker: core::marker::PhantomData },
            Self { range: at..self.range.end, _marker: core::marker::PhantomData },
        )
    }

    /// Gets the start physical address of the contiguous frames.
    #[rustc_allow_incoherent_impl]
    #[inline(always)]
    #[verifier::when_used_as_spec(start_paddr_spec)]
    pub fn start_paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        ensures
            res == self.start_paddr_spec(),
    {
        self.range.start
    }

    /// Gets the end physical address of the contiguous frames.
    #[rustc_allow_incoherent_impl]
    #[inline(always)]
    #[verifier::when_used_as_spec(end_paddr_spec)]
    pub fn end_paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        ensures
            res == self.end_paddr_spec(),
    {
        self.range.end
    }

    /// Gets the length in bytes of the contiguous frames.
    #[rustc_allow_incoherent_impl]
    #[inline(always)]
    #[verifier::when_used_as_spec(size_spec)]
    pub fn size(&self) -> (res: usize)
        requires
            self.inv(),
        ensures
            res == self.size_spec(),
    {
        self.range.end - self.range.start
    }

    /// Creates a new [`Segment`] from unused frames.
    ///
    /// The caller must provide a closure to initialize metadata for all the frames.
    /// The closure receives the physical address of the frame and returns the
    /// metadata, which is similar to [`core::array::from_fn`].
    ///
    /// It returns an error if:
    ///  - any of the frames cannot be created with a specific reason.
    ///
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn from_unused<F>(range: Range<Paddr>, metadata_fn: impl Fn(Paddr) -> (Paddr, M)) -> (res:
        Result<Self, GetFrameError>)
        requires
            old(regions).inv(),
            range.start % PAGE_SIZE() == 0,
            range.end % PAGE_SIZE() == 0,
            range.start < range.end < MAX_PADDR(),
            forall|paddr_in: Paddr|
                (range.start <= paddr_in < range.end && paddr_in % PAGE_SIZE() == 0) ==> {
                    &&& metadata_fn.requires((paddr_in,))
                },
            forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
                metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> {
                    &&& paddr_out < MAX_PADDR()
                    &&& paddr_out % PAGE_SIZE() == 0
                    &&& old(regions).slots.contains_key(frame_to_index(paddr_out))
                },
        ensures
            regions.inv(),
    {
        // Construct a segment early to recycle previously forgotten frames if
        // the subsequent operations fails in the middle.
        let mut segment = Self {
            range: range.start..range.start,
            _marker: core::marker::PhantomData,
        };

        let mut i = 0;
        let addr_len = (range.end - range.start) / PAGE_SIZE();
        while i < addr_len
            invariant
                range.start % PAGE_SIZE() == 0,
                range.end % PAGE_SIZE() == 0,
                range.start <= range.start + i * PAGE_SIZE() <= range.end,
                addr_len == (range.end - range.start) / PAGE_SIZE() as int,
                i <= addr_len,
                forall|paddr_in: Paddr|
                    (range.start <= paddr_in < range.end && paddr_in % PAGE_SIZE() == 0) ==> {
                        &&& metadata_fn.requires((paddr_in,))
                    },
                forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
                    metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> {
                        &&& paddr_out < MAX_PADDR()
                        &&& paddr_out % PAGE_SIZE() == 0
                        &&& regions.slots.contains_key(frame_to_index(paddr_out))
                    },
                regions.inv(),
            decreases addr_len - i,
        {
            let paddr = range.start + i * PAGE_SIZE();
            let (paddr, meta) = metadata_fn(paddr);

            assert(regions.slot_owners[paddr / PAGE_SIZE()].usage is Unused) by { admit() };
            assert(regions.slot_owners[paddr / PAGE_SIZE()].in_list@.points_to(0)) by { admit() };

            #[verus_spec(with Tracked(regions))]
            let frame = Frame::<M>::from_unused(paddr, meta)?;

            // TODO: `ManuallyDrop` causes runtime crashes; comment it out for now, but later we'll use the `vstd_extra` implementation
            // let _ = ManuallyDrop::new(frame);
            segment.range.end = paddr + PAGE_SIZE();

            i += 1;
        }

        Ok(segment)
    }

    /// Splits the frames into two at the given byte offset from the start.
    ///
    /// The resulting frames cannot be empty. So the offset cannot be neither
    /// zero nor the length of the frames.
    ///
    /// # Panics
    ///
    /// The function panics if the offset is out of bounds, at either ends, or
    /// not base-page-aligned.
    // #[verifier::when_used_as_spec(split_spec)] // <- verus complains about mismatched param numbers
    #[rustc_allow_incoherent_impl]
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn split(self, offset: usize) -> (res: (Self, Self))
        requires
            old(regions).inv(),
            old(regions).paddr_range_in_region(self.range),
            self.inv(),
            offset % PAGE_SIZE() == 0,
            0 < offset < self.size(),
        ensures
            regions.inv(),
            regions.paddr_range_in_region(res.0.range),
            regions.paddr_range_in_region(res.1.range),
            res == self.split_spec(offset),
    {
        // NOTE: in general we prefer to fold runtime assertions into preconditions rather than try to model panics
        let at = self.range.start + offset;
        let res = (
            Self { range: self.range.start..at, _marker: core::marker::PhantomData },
            Self { range: at..self.range.end, _marker: core::marker::PhantomData },
        );

        // TODO: `ManuallyDrop` causes runtime crashes; comment it out for now, but later we'll use the `vstd_extra` implementation
        // let _ = ManuallyDrop::new(self);

        res
    }

    /// Forgets the [`Segment`] and gets a raw range of physical addresses.
    // NOTE: forgotten objects have their `PointsTo` perms removed from the `slots` field of MetaRegionOwners
    // and added to the `dropped_slots` so that they can be restored later.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub(crate) fn into_raw(self) -> (res: Range<Paddr>)
        requires
            old(regions).inv(),
            old(regions).paddr_range_in_region(self.range),
            self.inv(),
    {
        let range = self.range.clone();
        // TODO: `ManuallyDrop` causes runtime crashes; comment it out for now, but later we'll use the `vstd_extra` implementation
        // let _ = ManuallyDrop::new(self);
        range
    }

    /// Restores the [`Segment`] from the raw physical address range.
    ///
    /// # Safety
    ///
    /// The range must be a forgotten [`Segment`] that matches the type `M`.
    /// It could be manually forgotten by [`core::mem::forget`],
    /// [`ManuallyDrop`], or [`Self::into_raw`].
    #[rustc_allow_incoherent_impl]
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub(crate) unsafe fn from_raw(range: Range<Paddr>) -> (res: Self)
        requires
            old(regions).inv(),
            old(regions).paddr_range_in_dropped_region(range),
            range.start % PAGE_SIZE() == 0,
            range.end % PAGE_SIZE() == 0,
            range.start < range.end < MAX_PADDR(),
        ensures
            regions.inv(),
            res.inv(),
            res.range == range,
            regions.paddr_range_in_dropped_region(res.range),
    {
        Self { range, _marker: core::marker::PhantomData }
    }

    /// Gets an extra handle to the frames in the byte offset range.
    ///
    /// The sliced byte offset range in indexed by the offset from the start of
    /// the contiguous frames. The resulting frames holds extra reference counts.
    ///
    /// # Panics
    ///
    /// The function panics if the byte offset range is out of bounds, or if
    /// any of the ends of the byte offset range is not base-page aligned.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn slice(&self, range: &Range<Paddr>) -> (res: Self)
        requires
            old(regions).inv(),
            old(regions).paddr_range_in_region(self.range),
            self.inv(),
            range.start % PAGE_SIZE() == 0,
            range.end % PAGE_SIZE() == 0,
            self.range.start + range.start <= self.range.start + range.end <= self.range.end,
    {
        let start = self.range.start + range.start;
        let end = self.range.start + range.end;

        let mut i = 0;
        let addr_len = (end - start) / PAGE_SIZE();
        while i < addr_len
            invariant
                start % PAGE_SIZE() == 0,
                end % PAGE_SIZE() == 0,
                start + i * PAGE_SIZE() <= end,
                i <= addr_len,
                addr_len == (end - start) / PAGE_SIZE() as int,
            decreases addr_len - i,
        {
            let paddr = start + i * PAGE_SIZE();
            // SAFETY: We already have reference counts for the frames since
            // for each frame there would be a forgotten handle when creating
            // the `Segment` object.
            // unsafe { inc_frame_ref_count(paddr); }
            i += 1;
        }

        Self { range: start..end, _marker: core::marker::PhantomData }
    }

    #[rustc_allow_incoherent_impl]
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn next(&mut self) -> (res: Option<Frame<M>>)
        requires
            old(regions).inv(),
            old(self).inv(),
            old(regions).dropped_slots.contains_key(frame_to_index(old(self).range.start)),
            !old(regions).slots.contains_key(frame_to_index(old(self).range.start)),
    {
        if self.range.start < self.range.end {
            // SAFETY: each frame in the range would be a handle forgotten
            // when creating the `Segment` object.
            let frame = unsafe {
                #[verus_spec(with Tracked(regions))]
                Frame::<M>::from_raw(self.range.start)
            };
            self.range.start = self.range.start + PAGE_SIZE();
            Some(frame)
        } else {
            None
        }
    }
}

// impl<M: AnyFrameMeta + ?Sized> From<Frame<M>> for Segment<M> {
//     fn from(frame: Frame<M>) -> Self {
//         let pa = frame.start_paddr();
//         let _ = ManuallyDrop::new(frame);
//         Self { range: pa..pa + PAGE_SIZE(), _marker: core::marker::PhantomData }
//     }
// }
/*
Don't worry about `dyn` stuff for now
impl<M: AnyFrameMeta> From<Segment<M>> for Segment<dyn AnyFrameMeta> {
    fn from(seg: Segment<M>) -> Self {
        let seg = ManuallyDrop::new(seg);
        Self {
            range: seg.range.clone(),
            _marker: core::marker::PhantomData,
        }
    }
}


impl<M: AnyFrameMeta> TryFrom<Segment<dyn AnyFrameMeta>> for Segment<M> {
    type Error = Segment<dyn AnyFrameMeta>;

    fn try_from(seg: Segment<dyn AnyFrameMeta>) -> core::result::Result<Self, Self::Error> {
        // SAFETY: for each page there would be a forgotten handle
        // when creating the `Segment` object.
        let first_frame = unsafe { Frame::<dyn AnyFrameMeta>::from_raw(seg.range.start) };
        let first_frame = ManuallyDrop::new(first_frame);
        if !(first_frame.dyn_meta() as &dyn core::any::Any).is::<M>() {
            return Err(seg);
        }
        // Since segments are homogeneous, we can safely assume that the rest
        // of the frames are of the same type. We just debug-check here.
        #[cfg(debug_assertions)]
        {
            for paddr in seg.range.clone().step_by(PAGE_SIZE()) {
                let frame = unsafe { Frame::<dyn AnyFrameMeta>::from_raw(paddr) };
                let frame = ManuallyDrop::new(frame);
                debug_assert!((frame.dyn_meta() as &dyn core::any::Any).is::<M>());
            }
        }
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        Ok(unsafe { core::mem::transmute::<Segment<dyn AnyFrameMeta>, Segment<M>>(seg) })
    }
}

impl<M: AnyUFrameMeta> From<Segment<M>> for USegment {
    fn from(seg: Segment<M>) -> Self {
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        unsafe { core::mem::transmute(seg) }
    }
}

impl TryFrom<Segment<dyn AnyFrameMeta>> for USegment {
    type Error = Segment<dyn AnyFrameMeta>;

    /// Try converting a [`Segment<dyn AnyFrameMeta>`] into [`USegment`].
    ///
    /// If the usage of the page is not the same as the expected usage, it will
    /// return the dynamic page itself as is.
    fn try_from(seg: Segment<dyn AnyFrameMeta>) -> core::result::Result<Self, Self::Error> {
        // SAFETY: for each page there would be a forgotten handle
        // when creating the `Segment` object.
        let first_frame = unsafe { Frame::<dyn AnyFrameMeta>::from_raw(seg.range.start) };
        let first_frame = ManuallyDrop::new(first_frame);
        if !first_frame.dyn_meta().is_untyped() {
            return Err(seg);
        }
        // Since segments are homogeneous, we can safely assume that the rest
        // of the frames are of the same type. We just debug-check here.
        #[cfg(debug_assertions)]
        {
            for paddr in seg.range.clone().step_by(PAGE_SIZE()) {
                let frame = unsafe { Frame::<dyn AnyFrameMeta>::from_raw(paddr) };
                let frame = ManuallyDrop::new(frame);
                debug_assert!(frame.dyn_meta().is_untyped());
            }
        }
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        Ok(unsafe { core::mem::transmute::<Segment<dyn AnyFrameMeta>, USegment>(seg) })
    }
}
*/
} // verus!
