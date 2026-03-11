// SPDX-License-Identifier: MPL-2.0
//! Kernel virtual memory allocation
use vstd::prelude::*;

use vstd_extra::arithmetic::nat_align_down;
use vstd_extra::ownership::OwnerOf;
use vstd_extra::prelude::Inv;

use core::marker::PhantomData;
use core::ops::Range;

use super::{KERNEL_PAGE_TABLE, VMALLOC_VADDR_RANGE, KERNEL_BASE_VADDR, KERNEL_END_VADDR};
use crate::{
    mm::{
        frame::{untyped::AnyUFrameMeta, Frame, Segment},
        kspace::{KernelPtConfig, MappedItem},
        largest_pages,
        page_prop::PageProperty,
        Paddr, Vaddr, PAGE_SIZE,
        page_table::{CursorMut, PageTable, PageTableConfig},
    },
};

use crate::specs::arch::mm::PAGE_SIZE as SPEC_PAGE_SIZE;
use crate::specs::task::InAtomicMode;
use crate::specs::mm::page_table::cursor::{CursorOwner, CursorView};
use crate::specs::mm::page_table::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::mm::page_table::{lemma_va_align_page_size_level_1, PageTableGuard};

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
    pub fn alloc(&self, size: usize) -> (r: Result<core::ops::Range<Vaddr>, RangeAllocError>)
        ensures
            r == kvirt_alloc_spec(size),
    {
        unimplemented!()
    }
}

#[verifier::external_body]
pub fn disable_preempt<'a, G: InAtomicMode + 'a>() -> &'a G {
    unimplemented!()
}

exec static KVIRT_AREA_ALLOCATOR: RangeAllocator = RangeAllocator::new(VMALLOC_VADDR_RANGE);

#[verifier::external_body]
pub(crate) fn get_kernel_page_table() -> (r: &'static PageTable<KernelPtConfig>)
    ensures
        true,
{
    KERNEL_PAGE_TABLE.get().unwrap()
}

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
            && r.start % PAGE_SIZE == 0
            && r.end % PAGE_SIZE == 0
            && KERNEL_BASE_VADDR <= r.start
            && r.end <= KERNEL_END_VADDR
;

/// Kernel ranges within [KERNEL_BASE_VADDR, KERNEL_END_VADDR] with alignment are valid for
/// KernelPtConfig (which uses sign-extended high-half addresses).
pub axiom fn axiom_kernel_range_valid(r: core::ops::Range<Vaddr>)
    ensures
        (KERNEL_BASE_VADDR <= r.start
            && r.end <= KERNEL_END_VADDR
            && r.start < r.end
            && r.start % PAGE_SIZE == 0
            && r.end % PAGE_SIZE == 0)
        ==> crate::mm::page_table::is_valid_range_spec::<KernelPtConfig>(&r);

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
    pub range: Range<Vaddr>,
}

pub tracked struct KVirtAreaOwner {
    pt_owner: PageTableOwner<KernelPtConfig>,
}

impl KVirtAreaOwner {
    /// The [`CursorView`] at the page containing the given address, representing the kernel page
    /// table's abstract state for query purposes.
    pub closed spec fn cursor_view_at(self, addr: Vaddr) -> CursorView<KernelPtConfig> {
        CursorView {
            cur_va: nat_align_down(addr as nat, SPEC_PAGE_SIZE as nat) as Vaddr,
            mappings: self.pt_owner.view_rec(self.pt_owner.0.value.path),
            phantom: PhantomData,
        }
    }
}

impl Inv for KVirtArea {
    open spec fn inv(self) -> bool {
        &&& KERNEL_BASE_VADDR <= self.range.start
        &&& self.range.end <= KERNEL_END_VADDR
    }
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

    /// Whether there is a mapped item at the page containing the address.
    pub open spec fn query_some_condition(self, owner: KVirtAreaOwner, addr: Vaddr) -> bool {
        owner.cursor_view_at(addr).present()
    }

    /// Postcondition when a mapping exists at the page.
    ///
    /// The returned item corresponds to the abstract mapping given by
    /// [`query_item_spec`](CursorView::query_item_spec).
    pub open spec fn query_some_ensures(
        self,
        owner: KVirtAreaOwner,
        addr: Vaddr,
        r: Option<super::MappedItem>,
    ) -> bool {
        r is Some && owner.cursor_view_at(addr).query_item_spec(r.unwrap()) is Some
    }

    /// Postcondition when no mapping exists at the page.
    pub open spec fn query_none_ensures(r: Option<super::MappedItem>) -> bool {
        r is None
    }

    /// Queries the mapping at the given virtual address.
    ///
    /// Returns the mapped item at the page containing `addr`, or `None` if there is no mapping.
    ///
    /// ## Preconditions
    /// - The kernel virtual area invariant holds ([`inv`](Inv::inv)).
    /// - The address is within the virtual area's range.
    /// ## Postconditions
    /// - If there is a mapped item at the page containing the address ([`query_some_condition`]),
    /// it is returned ([`query_some_ensures`]).
    /// - If there is no mapping at that page, `None` is returned ([`query_none_ensures`]).
    #[verifier::external_body]
    #[verus_spec(r =>
        with Tracked(owner): Tracked<KVirtAreaOwner>,
        requires
            self.inv(),
            self.range.start <= addr && addr < self.range.end,
        ensures
            self.query_some_condition(owner, addr) ==> self.query_some_ensures(owner, addr, r),
            !self.query_some_condition(owner, addr) ==> Self::query_none_ensures(r),
    )]
    pub fn query<A: InAtomicMode>(&self, addr: Vaddr) -> Option<super::MappedItem>
    {
        use align_ext::AlignExt;

        let start = addr.align_down(PAGE_SIZE);
        let vaddr = start..start + PAGE_SIZE;
        let page_table = get_kernel_page_table();

        let preempt_guard = disable_preempt::<A>();
        let (mut cursor, _cursor_owner) = page_table.cursor(preempt_guard, &vaddr).unwrap();
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
    #[verus_spec(
        with Tracked(owner): Tracked<KVirtAreaOwner>,
            Tracked(entry_owners): Tracked<&mut Seq<EntryOwner<KernelPtConfig>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, KernelPtConfig>>,
            Tracked(guard_perm): Tracked<GuardPerm<'a, KernelPtConfig>>
    )]
    pub fn map_frames<'a, T: AnyUFrameMeta, A: InAtomicMode + 'a>(
        area_size: usize,
        map_offset: usize,
        frames: alloc::vec::Vec<Frame<T>>,
        prop: PageProperty,
    ) -> Self
        requires
            0 < area_size,
            map_offset < area_size,
            map_offset % PAGE_SIZE == 0,
            area_size <= usize::MAX / 2,
            old(entry_owners).len() >= frames.len(),
            forall |i: int| 0 <= i < old(entry_owners).len() ==> old(entry_owners)[i].inv(),
    {
        proof { kvirt_alloc_succeeds(area_size); }
        let range = KVIRT_AREA_ALLOCATOR.alloc(area_size).unwrap();
        proof { kvirt_alloc_range_bounds(area_size, map_offset, range); }
        let cursor_range = range.start + map_offset..range.end;

        proof {
                axiom_kernel_range_valid(cursor_range);
        }

        let page_table = get_kernel_page_table();
        let preempt_guard = disable_preempt::<A>();

        let (mut cursor, Tracked(cursor_owner)) = 
        (#[verus_spec(with Tracked(owner.pt_owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
            page_table.cursor_mut(preempt_guard, &cursor_range)).unwrap();

        proof {
            assert(range.start % PAGE_SIZE == 0);
            assert(map_offset % PAGE_SIZE == 0);
            assert(cursor_range.start == range.start + map_offset);
            assert(cursor_range.start % PAGE_SIZE == 0) by {
                admit();
            }
            assert(cursor.inner.va == cursor_range.start);
            assert(cursor.inner.va % PAGE_SIZE == 0);
        }

        for frame in frames.into_iter()
            invariant
                cursor.inner.invariants(cursor_owner, *regions, *guards),
                forall |entry: EntryOwner<KernelPtConfig>| entry_owners.contains(entry) ==>
                    cursor.map_cursor_requires(cursor_owner, *guards),
                forall |i: int| 0 <= i < entry_owners.len() ==> entry_owners[i].inv(),
                cursor.inner.va % PAGE_SIZE == 0,
        {
            assert(entry_owners.len() > 0) by { admit() };
            assert(entry_owners[0].inv());

            let tracked mut entry_owner = entry_owners.tracked_remove(0);

            let item = MappedItem::Tracked(frame.into(), prop);
            assert(cursor.inner.invariants(cursor_owner, *regions, *guards));

            proof {
                let (pa, level, prop_from_item) = KernelPtConfig::item_into_raw_spec(item);
                KernelPtConfig::item_into_raw_spec_level_bounds(item);
                KernelPtConfig::item_into_raw_spec_tracked_level(item);
                assert(1 <= level <= crate::specs::arch::mm::NR_LEVELS + 1);
                assert(level == 1);
                assert(cursor.inner.va % PAGE_SIZE == 0);
                lemma_va_align_page_size_level_1(cursor.inner.va);
                assert(cursor.inner.va % crate::mm::page_table::page_size(level) == 0);
                assert(cursor.inner.va + crate::mm::page_table::page_size(level)
                    <= cursor.inner.barrier_va.end) by { admit() };
                assert(level < cursor.inner.guard_level) by { admit() };
                assert(crate::mm::page_table::Child::Frame(pa, level, prop_from_item).wf(entry_owner))
                    by { admit() };
            }
            assert(cursor.map_item_requires(item, entry_owner));

            assert(cursor.map_cursor_requires(cursor_owner, *guards)) by {
                assert(cursor_owner.in_locked_range()) by { admit() };
                assert(cursor.map_item_requires(item, entry_owner));
                let (_, level, _) = KernelPtConfig::item_into_raw(item);
                assert(cursor.inner.va + crate::mm::page_table::page_size(level)
                    <= cursor.inner.barrier_va.end);
                assert(cursor.inner.va < cursor.inner.barrier_va.end) by { admit() };
                assert(cursor.inner.level < cursor.inner.guard_level);
            };
            assert(cursor.map_panic_conditions(item)) by { admit() };
            assert(CursorMut::<'a, KernelPtConfig, A>::item_not_mapped(item, *regions)) by {
                admit()
            };

            // SAFETY: The constructor of the `KVirtArea` has already ensured
            // that this mapping does not affect kernel's memory safety.
            #[verus_spec(with Tracked(&mut cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))]
            let res = cursor.map(item);

            assert(res.is_ok()) by { admit() };

            proof {
                assert(cursor.inner.va < cursor.inner.barrier_va.end) by { admit() };
                assert(cursor.map_cursor_requires(cursor_owner, *guards));
                assert(forall |entry: EntryOwner<KernelPtConfig>| entry_owners.contains(entry)
                    ==> cursor.map_cursor_requires(cursor_owner, *guards));
                assert(cursor.inner.va % PAGE_SIZE == 0) by {
                    admit();
                }
            }
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

            let (mut cursor, cursor_owner) = page_table.cursor_mut(preempt_guard, &va_range).unwrap();

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