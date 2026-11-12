// SPDX-License-Identifier: MPL-2.0
//! Heap slots for allocations.
use vstd::{prelude::*, raw_ptr::PointsToRaw};
use vstd_extra::ownership::Inv;

use crate::mm::kspace::VMALLOC_BASE_VADDR;

use core::ptr::NonNull;

use crate::{
    /*impl_frame_meta_for,*/
    mm::{
        /*FrameAllocOptions, PAGE_SIZE, Segment,*/ Paddr, Vaddr,
        kspace::{LINEAR_MAPPING_BASE_VADDR, paddr_to_vaddr},
    },
};

verus! {

/// A slot that will become or has been turned from a heap allocation.
///
/// Heap slots can come from [`Slab`] or directly from a typed [`Segment`].
///
/// Heap slots can be used to fulfill heap allocations requested by the allocator.
/// Upon deallocation, the deallocated memory also becomes a heap slot.
///
/// The size of the heap slot must match the slot size of the [`Slab`] or the
/// size of the [`Segment`].
///
/// [`Slab`]: super::Slab
pub struct HeapSlot {
    /// The address of the slot.
    pub(super) addr: NonNull<u8>,
    /// The type and size of the slot.
    pub(super) info: SlotInfo,
    #[cfg(verus_keep_ghost_body)]
    pub(super) tracked_mem: Tracked<PointsToRaw>,
}

/// The type and size of the heap slot that should be used for the allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SlotInfo {
    /// The slot is from a [`super::Slab`].
    ///
    /// The size of the slot and the corresponding slab are provided.
    /// Both values are identical.
    SlabSlot(usize),
    /// The slot is from a [`Segment`].
    ///
    /// The size of the slot and the corresponding segment are provided.
    /// Both values are identical.
    LargeSlot(usize),
}

impl SlotInfo {
    pub open spec fn size_spec(self) -> usize {
        match self {
            Self::SlabSlot(size) => size,
            Self::LargeSlot(size) => size,
        }
    }

    /// Gets the size of the slot.
    pub fn size(&self) -> usize
        returns
            self.size_spec(),
    {
        match self {
            Self::SlabSlot(size) => *size,
            Self::LargeSlot(size) => *size,
        }
    }
}

impl Inv for HeapSlot {
    /// Exclusive access to precisely the slot's bytes in the linear mapping.
    open spec fn inv(self) -> bool {
        &&& LINEAR_MAPPING_BASE_VADDR <= self.ptr().addr()
        &&& self.ptr().addr() + self.slot_info().size_spec() <= VMALLOC_BASE_VADDR
        &&& self.memory().is_range(self.ptr().addr() as int, self.slot_info().size_spec() as int)
        &&& self.memory().provenance() == self.ptr()@.provenance
    }
}

impl HeapSlot {
    pub closed spec fn ptr(self) -> *mut u8 {
        self.addr.as_ptr()
    }

    pub closed spec fn slot_info(self) -> SlotInfo {
        self.info
    }

    pub closed spec fn memory(self) -> PointsToRaw {
        self.tracked_mem@
    }

    pub(super) proof fn lemma_fields(&self)
        ensures
            self.ptr() == self.addr.as_ptr(),
            self.slot_info() == self.info,
            self.memory() == self.tracked_mem@,
    {
    }

    /// Creates a new pointer to a heap slot.
    ///
    /// # Safety
    ///
    /// The pointer to the slot must either:
    ///  - be a free slot in a [`super::Slab`], or
    ///  - be a free slot in a [`Segment`].
    ///
    /// If the pointer is from a [`super::Slab`] or [`Segment`], the slot must
    /// have a size that matches the slot size of the slab or segment respectively.
    pub(super) unsafe fn new(
        addr: NonNull<u8>,
        info: SlotInfo,
        Tracked(mem): Tracked<PointsToRaw>,
    ) -> (res: Self)
        requires
            LINEAR_MAPPING_BASE_VADDR <= addr.as_ptr().addr(),
            addr.as_ptr().addr() + info.size_spec() <= VMALLOC_BASE_VADDR,
            mem.is_range(addr.as_ptr().addr() as int, info.size_spec() as int),
            mem.provenance() == addr.as_ptr()@.provenance,
        ensures
            res.inv(),
            res.ptr() == addr.as_ptr(),
            res.slot_info() == info,
            res.memory() == mem,
    {
        Self {
            addr,
            info,
            #[cfg(verus_keep_ghost_body)]
            tracked_mem: Tracked(mem),
        }
    }

    /*/// Allocates a large slot.
    ///
    /// This function allocates in units of [`PAGE_SIZE`] bytes.
    ///
    /// This function returns an error if the frame allocation fails.
    ///
    /// # Panics
    ///
    /// This function panics if the size is not a multiple of [`PAGE_SIZE`].
    pub fn alloc_large(size: usize) -> Result<Self, AllocError> {
        #[cfg(feature = "allow_panic")]
        assert_eq!(size % PAGE_SIZE, 0);
        let nframes = size / PAGE_SIZE;
        let segment = FrameAllocOptions::new()
            .zeroed(false)
            .alloc_segment_with(nframes, |_| LargeAllocFrameMeta)
            .map_err(|_| {
                log::error!("Failed to allocate a large slot");
                AllocError
            })?;

        let paddr_range = segment.into_raw();
        let vaddr = paddr_to_vaddr(paddr_range.start);

        Ok(Self {
            addr: NonNull::new(vaddr as *mut u8).unwrap(),
            info: SlotInfo::LargeSlot(size),
        })
    }

    /// Deallocates a large slot.
    ///
    /// # Panics
    ///
    /// This function aborts if the slot was not allocated with
    /// [`HeapSlot::alloc_large`], as it requires specific memory management
    /// operations that only apply to large slots.
    pub fn dealloc_large(self) {
        let SlotInfo::LargeSlot(size) = self.info else {
            log::error!(
                "Deallocating a large slot that was not allocated with `HeapSlot::alloc_large`"
            );
            #[cfg(feature = "allow_panic")]
            crate::panic::abort();
            #[cfg(not(feature = "allow_panic"))]
            return;
        };

        debug_assert_eq!(size % PAGE_SIZE, 0);
        debug_assert_eq!(self.paddr() % PAGE_SIZE, 0);
        let range = self.paddr()..self.paddr() + size;

        // SAFETY: The segment was once forgotten when allocated.
        drop(unsafe { Segment::<LargeAllocFrameMeta>::from_raw(range) });
    }*/
    /// Gets the physical address of the slot.
    pub fn paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        ensures
            paddr_to_vaddr(res) == self.ptr().addr(),
        returns
            (self.ptr().addr() - LINEAR_MAPPING_BASE_VADDR) as Paddr,
    {
        self.addr.as_ptr() as Vaddr - LINEAR_MAPPING_BASE_VADDR
    }

    /// Gets the size of the slot.
    pub fn size(&self) -> usize
        returns
            self.slot_info().size_spec(),
    {
        match self.info {
            SlotInfo::SlabSlot(size) => size,
            SlotInfo::LargeSlot(size) => size,
        }
    }

    /// Gets the type and size of the slot.
    pub fn info(&self) -> SlotInfo
        returns
            self.slot_info(),
    {
        self.info
    }

    /// Gets the pointer to the slot.
    pub fn as_ptr(&self) -> *mut u8
        returns
            self.ptr(),
    {
        self.addr.as_ptr()
    }
}

} // verus!
/*/// The frames allocated for a large allocation.
#[derive(Debug)]
pub struct LargeAllocFrameMeta;

impl_frame_meta_for!(LargeAllocFrameMeta);*/
