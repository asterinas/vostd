// SPDX-License-Identifier: MPL-2.0
//! Kernel virtual memory allocation
use vstd::prelude::*;
use core::ops::Range;

use super::{KERNEL_PAGE_TABLE, VMALLOC_VADDR_RANGE};
use crate::{
    mm::{
        frame::{untyped::AnyUFrameMeta, Frame, Segment},
        kspace::{KernelPtConfig, MappedItem},
        largest_pages,
        page_prop::PageProperty,
        Paddr, Vaddr, PAGE_SIZE,
        page_table::CursorMut,
    },
};

use crate::specs::task::InAtomicMode;
use crate::specs::mm::page_table::CursorOwner;

//static KVIRT_AREA_ALLOCATOR: RangeAllocator = RangeAllocator::new(VMALLOC_VADDR_RANGE);

verus! {

#[derive(Debug)]
pub struct RangeAllocError;

pub struct RangeAllocator;

impl RangeAllocator {
    #[verifier::external_body]
    pub const fn new(_r: core::ops::Range<Vaddr>) -> Self {
        Self
    }

    #[verifier::external_body]
    pub fn alloc(&self, _size: usize) -> Result<core::ops::Range<Vaddr>, RangeAllocError> {
        unimplemented!("Uses runtime RangeAllocator")
    }
}

#[verifier::external_body]
pub fn disable_preempt<G: InAtomicMode>() -> G {
    unimplemented!()
}

exec static KVIRT_AREA_ALLOCATOR: RangeAllocator = RangeAllocator::new(VMALLOC_VADDR_RANGE);

// Axiomatized spec for alloc - cannot read exec static in proof mode.
pub uninterp spec fn kvirt_alloc_spec(size: usize) -> Result<core::ops::Range<Vaddr>, RangeAllocError>;

pub axiom fn kvirt_alloc_succeeds(area_size: usize)
    requires
        0 < area_size <= usize::MAX / 2,
    ensures
        kvirt_alloc_spec(area_size).is_ok();

pub axiom fn kvirt_alloc_range_bounds(area_size: usize, map_offset: usize, r: core::ops::Range<Vaddr>)
    ensures
        kvirt_alloc_spec(area_size) == Ok::<core::ops::Range<Vaddr>, RangeAllocError>(r)
        ==> r.start <= r.end
            && (r.end - r.start) >= area_size
            && map_offset <= r.end - r.start
            && r.start + map_offset <= usize::MAX
;

/// Kernel virtual area.
///
/// A kernel virtual area manages a range of memory in [`VMALLOC_VADDR_RANGE`].
/// It can map a portion or the entirety of its virtual memory pages to
/// physical memory, whether tracked with metadata or not.
///
/// It is the caller's responsibility to ensure TLB coherence before using the
/// mapped virtual address on a certain CPU.
//
// FIXME: This caller-ensured design is very error-prone. A good option is to
// use a guard the pins the CPU and ensures TLB coherence while accessing the
// `KVirtArea`. However, `IoMem` need some non trivial refactoring to support
// being implemented on a `!Send` and `!Sync` guard.
#[derive(Debug)]
pub struct KVirtArea {
    range: Range<Vaddr>,
}

#[verus_verify]
impl KVirtArea {
    pub fn start(&self) -> Vaddr {
        self.range.start
    }

    pub fn end(&self) -> Vaddr {
        self.range.end
    }

    pub fn range(&self) -> Range<Vaddr> {
        self.range.start..self.range.end
    }

    #[cfg(ktest)]
    pub fn len(&self) -> usize {
        self.range.len()
    }

    #[cfg(ktest)]
    pub fn query(&self, addr: Vaddr) -> Option<super::MappedItem> {
        use align_ext::AlignExt;

        assert!(self.start() <= addr && self.end() >= addr);
        let start = addr.align_down(PAGE_SIZE);
        let vaddr = start..start + PAGE_SIZE;
        let page_table = KERNEL_PAGE_TABLE.get().unwrap();
        //let preempt_guard = disable_preempt();
        let mut cursor = page_table.cursor(&vaddr).unwrap();
        cursor.query().unwrap().1
    }

    /// Create a kernel virtual area and map tracked pages into it.
    ///
    /// The created virtual area will have a size of `area_size`, and the pages
    /// will be mapped starting from `map_offset` in the area.
    ///
    /// # Panics
    ///
    /// This function panics if
    ///  - the area size is not a multiple of [`PAGE_SIZE`];
    ///  - the map offset is not aligned to [`PAGE_SIZE`];
    ///  - the map offset plus the size of the pages exceeds the area size.
    // TODO: T should be any AnyFrameMeta + Repr<MetaSlotStorage>
    #[verifier::external_body]
    pub fn map_frames<T: AnyUFrameMeta, A: InAtomicMode>(
        area_size: usize,
        map_offset: usize,
        frames: alloc::vec::Vec<Frame<T>>,
        prop: PageProperty,
    ) -> Self
        requires
            map_offset <= area_size,
            area_size <= usize::MAX / 2,
    {
        proof {
            kvirt_alloc_succeeds(area_size);
        }
        let range = KVIRT_AREA_ALLOCATOR.alloc(area_size).unwrap();
        let cursor_range = range.start + map_offset..range.end;

        let page_table = KERNEL_PAGE_TABLE.get().unwrap();
        let preempt_guard = disable_preempt::<A>();

        proof_decl! {
            let tracked mut cursor_owner: Tracked<Option<CursorOwner<KernelPtConfig>>>;
        }

        let mut cursor = (#[verus_spec(with => cursor_owner)] page_table.cursor_mut(&preempt_guard, &cursor_range)).unwrap();

        for frame in frames.into_iter() {
            // SAFETY: The constructor of the `KVirtArea` has already ensured
            // that this mapping does not affect kernel's memory safety.
            cursor.map(MappedItem::Tracked(frame.into(), prop));
        }

        Self { range }
    }

    /// Creates a kernel virtual area and maps untracked frames into it.
    ///
    /// The created virtual area will have a size of `area_size`, and the
    /// physical addresses will be mapped starting from `map_offset` in
    /// the area.
    ///
    /// You can provide a `0..0` physical range to create a virtual area without
    /// mapping any physical memory.
    ///
    /// # Panics
    ///
    /// This function panics if
    ///  - the area size is not a multiple of [`PAGE_SIZE`];
    ///  - the map offset is not aligned to [`PAGE_SIZE`];
    ///  - the provided physical range is not aligned to [`PAGE_SIZE`];
    ///  - the map offset plus the length of the physical range exceeds the
    ///    area size;
    ///  - the provided physical range contains tracked physical addresses.
    #[verifier::external_body]
    pub unsafe fn map_untracked_frames<A: InAtomicMode, 'rcu>(
        area_size: usize,
        map_offset: usize,
        pa_range: Range<Paddr>,
        prop: PageProperty,
    ) -> Self {
        /*assert!(pa_range.start % PAGE_SIZE == 0);
        assert!(pa_range.end % PAGE_SIZE == 0);
        assert!(area_size % PAGE_SIZE == 0);
        assert!(map_offset % PAGE_SIZE == 0);
        assert!(map_offset + pa_range.len() <= area_size);*/

        let range = KVIRT_AREA_ALLOCATOR.alloc(area_size).unwrap();

        if !pa_range.is_empty() {
            let len = pa_range.len();
            let va_range = range.start + map_offset..range.start + map_offset + len;

            let page_table = KERNEL_PAGE_TABLE.get().unwrap();
            let preempt_guard = disable_preempt::<A>();

            proof_decl! {
                let tracked mut cursor_owner: Tracked<CursorOwner<KernelPtConfig>>;
            }

            let mut cursor = (#[verus_spec(with => cursor_owner)] page_table.cursor_mut(&preempt_guard, &va_range)).unwrap();

            let pages = largest_pages::<KernelPtConfig>(va_range.start, pa_range.start, len);
            for (pa, level) in pages.into_iter() {
                // SAFETY: The caller of `map_untracked_frames` has ensured the safety of this mapping.
                let _ = cursor.map(MappedItem::Untracked(pa, level, prop));
            }
        }

        Self { range }
    }
}

/*impl Drop for KVirtArea {
    fn drop(&mut self) {
        // 1. unmap all mapped pages.
        let page_table = KERNEL_PAGE_TABLE.unwrap();
        let range = self.start()..self.end();
        //let preempt_guard = disable_preempt();
        let mut cursor = page_table.cursor_mut(&range).unwrap();
        loop {
            // SAFETY: The range is under `KVirtArea` so it is safe to unmap.
            let Some(frag) = (unsafe { cursor.take_next(self.end() - cursor.virt_addr()) }) else {
                break;
            };
            drop(frag);
        }
        // 2. free the virtual block
        //KVIRT_AREA_ALLOCATOR.free(range);
    }
}*/
} // verus!