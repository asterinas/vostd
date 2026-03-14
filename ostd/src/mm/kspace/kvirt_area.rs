// SPDX-License-Identifier: MPL-2.0
//! Kernel virtual memory allocation
use vstd::prelude::*;

use vstd_extra::arithmetic::nat_align_down;
use vstd_extra::ownership::{ModelOf, OwnerOf};
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

use crate::specs::arch::mm::{MAX_PADDR, PAGE_SIZE as SPEC_PAGE_SIZE, NR_LEVELS};
use crate::mm::PagingConstsTrait;
use crate::specs::arch::PagingConsts;
use crate::mm::nr_subpage_per_huge;
use crate::specs::task::InAtomicMode;
use crate::specs::mm::page_table::cursor::{CursorOwner, CursorView};
use crate::specs::mm::page_table::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::mm::page_table::{lemma_va_align_page_size_level_1, PageTableGuard};
use crate::mm::frame::DynFrame;
use crate::mm::kspace::AnyFrameMeta;
use crate::specs::mm::frame::mapping::frame_to_index_spec;

//static KVIRT_AREA_ALLOCATOR: RangeAllocator = RangeAllocator::new(VMALLOC_VADDR_RANGE);

verus! {

/// Spec representation of Frame<T> as DynFrame (used when the actual conversion is opaque).
pub open spec fn frame_as_dynframe<T: AnyFrameMeta>(frame: Frame<T>) -> DynFrame {
    DynFrame { ptr: frame.ptr, _marker: PhantomData }
}

/// Converts `Frame<T>` to `DynFrame`, with a spec postcondition connecting the result
/// to the spec function `frame_as_dynframe`. The `Into` impl uses `transmute`, which is
/// `external_body`, so the equality is admitted.
/// TODO: use the conversions in `frame/mod.rs`
fn frame_into_dynframe<T: AnyUFrameMeta>(frame: Frame<T>) -> (res: DynFrame)
    ensures
        res == frame_as_dynframe(frame),
{
    proof { admit(); }
    frame.into()
}

/// Spec function: the entry owner correctly matches the frame and property for mapping.
pub open spec fn frame_entry_wf<T: AnyFrameMeta>(
    frame: Frame<T>,
    prop: PageProperty,
    entry_owner: EntryOwner<KernelPtConfig>,
) -> bool {
    let frame_mss = DynFrame { ptr: frame.ptr, _marker: PhantomData };
    let item = MappedItem::Tracked(frame_mss, prop);
    let (pa, level, prop_from_item) = KernelPtConfig::item_into_raw_spec(item);
    crate::mm::page_table::Child::Frame(pa, level, prop_from_item).wf(entry_owner)
}

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

/// Total size (in bytes) of the pages `elems[from..to]`.
pub open spec fn sum_page_sizes_spec(elems: Seq<(Paddr, u8)>, from: int, to: int) -> nat
    decreases (to - from) when from <= to
{
    if from >= to {
        0nat
    } else {
        crate::mm::page_table::page_size(elems[from].1) as nat
            + sum_page_sizes_spec(elems, from + 1, to)
    }
}

/// `sum(from, to+1) == sum(from, to) + page_size(elems[to])`.
proof fn sum_page_sizes_extend_right(elems: Seq<(Paddr, u8)>, from: int, to: int)
    requires
        0 <= from <= to,
        to < elems.len() as int,
    ensures
        sum_page_sizes_spec(elems, from, to + 1)
            == sum_page_sizes_spec(elems, from, to)
                + crate::mm::page_table::page_size(elems[to].1) as nat,
    decreases to - from,
{
    if from < to {
        sum_page_sizes_extend_right(elems, from + 1, to);
        // Help Verus: unfold sum_page_sizes_spec(elems, from, to) and (from, to+1)
        assert(sum_page_sizes_spec(elems, from, to) ==
            crate::mm::page_table::page_size(elems[from].1) as nat
                + sum_page_sizes_spec(elems, from + 1, to));
        assert(sum_page_sizes_spec(elems, from, to + 1) ==
            crate::mm::page_table::page_size(elems[from].1) as nat
                + sum_page_sizes_spec(elems, from + 1, to + 1));
    } else {
        // from == to; explicitly unfold both sides
        assert(sum_page_sizes_spec(elems, from, to) == 0nat);
        assert(sum_page_sizes_spec(elems, from, to + 1) ==
            crate::mm::page_table::page_size(elems[from].1) as nat
                + sum_page_sizes_spec(elems, from + 1, to + 1));
        assert(sum_page_sizes_spec(elems, from + 1, to + 1) == 0nat);
    }
}

/// `sum(from, to1) <= sum(from, to2)` when `to1 <= to2`.
proof fn sum_page_sizes_mono(elems: Seq<(Paddr, u8)>, from: int, to1: int, to2: int)
    requires
        0 <= from <= to1 <= to2,
        to2 <= elems.len() as int,
    ensures
        sum_page_sizes_spec(elems, from, to1) <= sum_page_sizes_spec(elems, from, to2),
    decreases to2 - to1,
{
    if to1 < to2 {
        sum_page_sizes_extend_right(elems, from, to2 - 1);
        sum_page_sizes_mono(elems, from, to1, to2 - 1);
    }
}

/// Collects the output of `largest_pages` into a `Vec` so that Verus can iterate
/// over it with loop invariants (`impl Iterator` does not implement `ForLoopGhostIteratorNew`).
///
/// The postconditions reflect provable properties of every `(pa, level)` pair emitted by
/// `largest_pages`:
/// - PA alignment and level-validity follow from the loop guard in `largest_pages`.
/// - The sum of page sizes equals `len` (the iterator covers exactly [pa, pa+len)).
/// - At each step, the running VA is aligned to the current page size.
#[verifier::external_body]
fn collect_largest_pages(
    va: Vaddr,
    pa: Paddr,
    len: usize,
) -> (res: alloc::vec::Vec<(Paddr, u8)>)
    ensures
        forall |i: int| 0 <= i < res@.len() ==> res@[i].0 % PAGE_SIZE == 0,
        forall |i: int| 0 <= i < res@.len() ==> 1 <= res@[i].1 && res@[i].1 <= NR_LEVELS,
        forall |i: int| 0 <= i < res@.len() ==>
            res@[i].1 <= KernelPtConfig::HIGHEST_TRANSLATION_LEVEL(),
        sum_page_sizes_spec(res@, 0, res@.len() as int) == len as nat,
        forall |i: int| 0 <= i < res@.len() ==>
            (va as nat + sum_page_sizes_spec(res@, 0, i))
                % crate::mm::page_table::page_size(res@[i].1) as nat == 0,
        // PA tracking: each element's physical address equals pa + sum of preceding page sizes.
        forall |i: int| 0 <= i < res@.len() ==>
            res@[i].0 as nat == pa as nat + sum_page_sizes_spec(res@, 0, i),
{
    largest_pages::<KernelPtConfig>(va, pa, len).collect()
}

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
            old(entry_owners).len() == frames.len(),
            frames.len() as int * PAGE_SIZE as int + map_offset as int <= area_size as int,
            forall |i: int| 0 <= i < old(entry_owners).len() ==> old(entry_owners)[i].inv(),
            forall |i: int| 0 <= i < frames.len() ==>
                frame_entry_wf(frames[i], prop, old(entry_owners)[i]),
            forall |i: int| 0 <= i < frames.len() ==>
                CursorMut::<'a, KernelPtConfig, A>::item_not_mapped(
                    MappedItem::Tracked(frame_as_dynframe(frames[i]), prop),
                    *old(regions),
                ),
            // Frames have distinct physical addresses (follows from linearity of slot_perm ownership).
            forall |i: int, j: int| 0 <= i < j < frames.len() ==>
                old(entry_owners)[i].frame.unwrap().mapped_pa != old(entry_owners)[j].frame.unwrap().mapped_pa,
    {
        proof {
            kvirt_alloc_succeeds(area_size);            
        }
        
        let range = KVIRT_AREA_ALLOCATOR.alloc(area_size).unwrap();

        proof {
            kvirt_alloc_range_bounds(area_size, map_offset, range);
        }

        let cursor_range = range.start + map_offset..range.end;

        proof {
            axiom_kernel_range_valid(cursor_range);
        }

        let page_table = get_kernel_page_table();
        let preempt_guard = disable_preempt::<A>();

        let (mut cursor, Tracked(cursor_owner)) = 
        (#[verus_spec(with Tracked(owner.pt_owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
            page_table.cursor_mut(preempt_guard, &cursor_range)).unwrap();

        let ghost init_frames_len = frames.len();
        // Establish the initial values of the two new loop invariants BEFORE the for loop.
        // At loop start: it.pos=0, it.elements=frames@, entry_owners=old(entry_owners), *regions=*old(regions).
        proof {
            // Initial item_not_mapped invariant.
            // Precondition gives item_not_mapped for each frame in *old(regions).
            // CursorMut::new postcondition: item_not_mapped is preserved by cursor creation.
            assert forall |j: int| #![trigger entry_owners[j]]
                0 <= j < frames@.len()
                implies regions.slot_owners[frame_to_index_spec(entry_owners[j].frame.unwrap().mapped_pa)].path_if_in_pt is None
            by {
                let item = MappedItem::Tracked(frame_as_dynframe(frames@[j]), prop);
                KernelPtConfig::item_into_raw_spec_tracked_level(item);
                let (pa, level, _) = KernelPtConfig::item_into_raw_spec(item);
                assert(level == 1u8);
                vstd::arithmetic::mul::lemma_mul_by_zero_is_zero(
                    nr_subpage_per_huge::<PagingConsts>().ilog2() as int);
                vstd::arithmetic::power::lemma_pow0(2int);
            };

/*            assert forall |entry: EntryOwner<KernelPtConfig>|
                entry_owners.contains(entry)
                implies cursor.map_cursor_requires(cursor_owner, *guards)
            by {};*/
        }
        for frame in it: frames.into_iter()
            invariant
                cursor.inner.invariants(cursor_owner, *regions, *guards),
                forall |entry: EntryOwner<KernelPtConfig>| entry_owners.contains(entry) ==>
                    cursor.map_cursor_requires(cursor_owner, *guards),
                forall |i: int| 0 <= i < entry_owners.len() ==> entry_owners[i].inv(),
                cursor.inner.va % PAGE_SIZE == 0,
                cursor.inner.va as int + entry_owners.len() as int * PAGE_SIZE as int
                    <= cursor.inner.barrier_va.end as int,
                cursor.inner.barrier_va.end % PAGE_SIZE == 0,
                it.elements.len() == init_frames_len,
                init_frames_len <= old(entry_owners).len(),
                entry_owners.len() == old(entry_owners).len() - it.pos,
                forall |j: int|
                    0 <= j < entry_owners.len() && it.pos + j < it.elements.len() ==>
                    frame_entry_wf(it.elements[it.pos + j], prop, entry_owners[j]),
                // item_not_mapped holds in current regions for all remaining frames
                forall |j: int| #![trigger entry_owners[j]]
                    0 <= j < it.elements.len() - it.pos ==>
                    regions.slot_owners[frame_to_index_spec(entry_owners[j].frame.unwrap().mapped_pa)].path_if_in_pt is None,
                // Remaining frames have distinct physical addresses
                forall |i: int, j: int| 0 <= i < j < it.elements.len() - it.pos ==>
                    entry_owners[i].frame.unwrap().mapped_pa != entry_owners[j].frame.unwrap().mapped_pa,
        {
            proof {
                assert(entry_owners.contains(entry_owners[0]));
                assert(cursor.map_cursor_requires(cursor_owner, *guards));
                assert(frame_entry_wf(frame, prop, entry_owners[0]));
            }

            let ghost cur_mapped_pa: usize = entry_owners[0].frame.unwrap().mapped_pa;
            let ghost cur_pa_from_wf: usize = KernelPtConfig::item_into_raw_spec(
                MappedItem::Tracked(frame_as_dynframe(it.elements.index(it.pos as int)), prop)).0;
            let ghost pre_remove_owners: Seq<EntryOwner<KernelPtConfig>> = *entry_owners;

            let tracked mut entry_owner = entry_owners.tracked_remove(0);

            let dynframe = frame_into_dynframe(frame);
            // Now Verus knows: dynframe == frame_as_dynframe(it.elements[it.pos])
            let item = MappedItem::Tracked(dynframe, prop);
            assert(cursor.inner.invariants(cursor_owner, *regions, *guards));

            let ghost regions_before_map = *regions;
            let ghost old_cursor_model: CursorView<KernelPtConfig> = cursor.inner.model(cursor_owner);
            let ghost old_cursor_owner_va = cursor_owner.va;
            proof {
                cursor_owner.va.reflect_prop(cursor.inner.va);
                let (pa, level, prop_from_item) = KernelPtConfig::item_into_raw_spec(item);
                KernelPtConfig::item_into_raw_spec_level_bounds(item);
                KernelPtConfig::item_into_raw_spec_tracked_level(item);
                lemma_va_align_page_size_level_1(cursor.inner.va);
                cursor_owner.locked_range_page_aligned();
                let ghost diff: int = cursor.inner.barrier_va.end as int - cursor.inner.va as int;
                vstd::arithmetic::mul::lemma_mul_by_zero_is_zero(
                    nr_subpage_per_huge::<PagingConsts>().ilog2() as int,
                );
                vstd::arithmetic::power::lemma_pow0(2int);
            }
            assert(CursorMut::<'a, KernelPtConfig, A>::item_not_mapped(item, *regions)) by {
                let pa = KernelPtConfig::item_into_raw_spec(item).0;

                KernelPtConfig::item_into_raw_spec_tracked_level(item);
                let (pa2, level2, _) = KernelPtConfig::item_into_raw_spec(item);
                assert(level2 == 1 && pa2 == pa);
                assert(regions.paddr_range_not_mapped(pa2..(pa2 + crate::mm::page_table::page_size(level2)) as usize)) by {
                    
                };
            };

            // SAFETY: The constructor of the `KVirtArea` has already ensured
            // that this mapping does not affect kernel's memory safety.
            #[verus_spec(with Tracked(&mut cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))]
            let res = cursor.map(item);

            proof {
                // After tracked_remove(0): entry_owners[j] == pre_remove_owners[j+1].
                pre_remove_owners.remove_ensures(0);
                assert(*entry_owners == pre_remove_owners.remove(0));
                let cur_idx = frame_to_index_spec(cur_mapped_pa);

                // (1) Maintain item_not_mapped: map preserved slot_owners for all indices
                //     other than cur_idx; remaining entries have paddrs distinct from cur_mapped_pa.
                assert forall|j: int| #![trigger entry_owners[j]]
                    0 <= j < it.elements.len() - (it.pos + 1)
                    implies regions.slot_owners[frame_to_index_spec(entry_owners[j].frame.unwrap().mapped_pa)].path_if_in_pt is None
                by {
                    // entry_owners[j] == pre_remove_owners[j+1]  (from remove_ensures)
                    assert((*entry_owners)[j] == pre_remove_owners[j + 1]);
                    let pa_j = entry_owners[j].frame.unwrap().mapped_pa;
                    // pa_j != cur_mapped_pa (pre-remove distinctness, i=0 j=j+1)
                    assert(pa_j != cur_mapped_pa) by {
                        assert(0 <= 0 < j + 1 < it.elements.len() - it.pos as int);
                    };
                    // frame_to_index_spec is inline: paddr / PAGE_SIZE
                    // Injectivity: distinct page-aligned paddrs map to distinct indices
                    let idx_j = frame_to_index_spec(pa_j);
                    assert(idx_j != cur_idx) by {
                        assert(entry_owners[j].inv());
                        assert(entry_owners[j].is_frame());
                        assert(pa_j % PAGE_SIZE == 0);
                        assert(cur_mapped_pa % PAGE_SIZE == 0);
                        // Z3's integer arithmetic: a%m==0 && b%m==0 && a!=b && m>0 => a/m != b/m
                    };
                    // slot_owners[idx_j] preserved by map (postcondition: only cur_idx changes)
                    assert(regions.slot_owners[idx_j].path_if_in_pt ==
                        regions_before_map.slot_owners[idx_j].path_if_in_pt);
                    // Before map, slot_owners[idx_j] was None (from pre-remove invariant snapshot)
                    assert(regions_before_map.slot_owners[idx_j].path_if_in_pt is None) by {
                        assert(1 <= j + 1 < it.elements.len() - it.pos as int);
                    };
                };

                // (2) Distinctness: remaining entries are a subsequence of pre_remove_owners[1..].
                assert forall|i: int, j: int| 0 <= i < j < it.elements.len() - (it.pos + 1)
                    implies entry_owners[i].frame.unwrap().mapped_pa != entry_owners[j].frame.unwrap().mapped_pa
                by {
                    // entry_owners[i] == pre_remove_owners[i+1], entry_owners[j] == pre_remove_owners[j+1]
                    assert((*entry_owners)[i] == pre_remove_owners[i + 1]);
                    assert((*entry_owners)[j] == pre_remove_owners[j + 1]);
                    // Pre-remove distinctness: i+1 < j+1 < it.elements.len()-it.pos
                    assert(0 <= i + 1 < j + 1 < it.elements.len() - it.pos as int);
                };

                // Shared computation: aligned_nat = new cursor.inner.va = old_va + PAGE_SIZE.
                // Used for both the geometric invariant maintenance (→ line 529 forall)
                // and the cursor.inner.va % PAGE_SIZE == 0 assertion.
                let (pa, level, prop_) = KernelPtConfig::item_into_raw_spec(item);
                KernelPtConfig::item_into_raw_spec_tracked_level(item);
                assert(level == 1u8);
                assert(crate::mm::page_table::page_size(level) == PAGE_SIZE) by {
                    vstd::arithmetic::mul::lemma_mul_by_zero_is_zero(
                        nr_subpage_per_huge::<PagingConsts>().ilog2() as int,
                    );
                    vstd::arithmetic::power::lemma_pow0(2int);
                };
                // map_item_ensures: cursor_owner@ == old_cursor_model.map_spec(pa, PAGE_SIZE, prop_)
                assert(cursor_owner@ == old_cursor_model.map_spec(pa, PAGE_SIZE, prop_));
                // map_spec.cur_va == split_self.align_up_spec(PAGE_SIZE)
                let split_self = old_cursor_model.split_while_huge(PAGE_SIZE);
                assert(cursor_owner@.cur_va == split_self.align_up_spec(PAGE_SIZE));
                // Unfold align_up_spec to nat_align_up
                let aligned_nat: nat = vstd_extra::arithmetic::nat_align_up(
                    split_self.cur_va as nat, PAGE_SIZE as nat);
                assert(split_self.align_up_spec(PAGE_SIZE) == aligned_nat as Vaddr);
                assert(cursor_owner@.cur_va == aligned_nat as Vaddr);
                // aligned_nat % PAGE_SIZE == 0 and bound < usize::MAX
                vstd_extra::arithmetic::lemma_nat_align_up_sound(
                    split_self.cur_va as nat, PAGE_SIZE as nat);
                assert(aligned_nat % PAGE_SIZE as nat == 0);
                CursorView::<KernelPtConfig>::lemma_split_while_huge_preserves_cur_va(
                    old_cursor_model, PAGE_SIZE);
                assert(split_self.cur_va == old_cursor_model.cur_va);
                assert(old_cursor_model.cur_va == old_cursor_owner_va.to_vaddr());
                assert(aligned_nat == vstd_extra::arithmetic::nat_align_up(
                    old_cursor_owner_va.to_vaddr() as nat, PAGE_SIZE as nat));
                old_cursor_owner_va.align_diff(1);
                assert(aligned_nat < usize::MAX);
                // old_cursor_owner_va.to_vaddr() % PAGE_SIZE == 0 (established in pre-map proof block)
                // align_diff: nat_align_up(old_va, PAGE_SIZE) = nat_align_down(old_va, PAGE_SIZE) + PAGE_SIZE
                //   nat_align_down(old_va, PAGE_SIZE) = old_va  (since old_va % PAGE_SIZE == 0)
                // => aligned_nat = old_cursor_owner_va.to_vaddr() + PAGE_SIZE
                assert(vstd_extra::arithmetic::nat_align_down(
                    old_cursor_owner_va.to_vaddr() as nat, PAGE_SIZE as nat)
                    == old_cursor_owner_va.to_vaddr() as nat);
                assert(aligned_nat == old_cursor_owner_va.to_vaddr() as nat + PAGE_SIZE as nat);
                // cursor.inner.va (post-map) == aligned_nat as usize
                assert(cursor.inner.wf(cursor_owner));
                assert(cursor_owner.va.reflect(cursor.inner.va));
                cursor_owner.va.reflect_prop(cursor.inner.va);
                assert(cursor.inner.va as int == old_cursor_owner_va.to_vaddr() as int
                    + PAGE_SIZE as int);

                // Geometric invariant maintenance:
                // Pre-map loop invariant (with pre_remove_owners.len() == entry_owners.len_BEFORE_REMOVE):
                //   old_cursor_owner_va.to_vaddr() + pre_remove_owners.len() * PAGE_SIZE <= barrier_va.end
                // After remove: entry_owners.len() = pre_remove_owners.len() - 1
                // After map: cursor.inner.va = old_va + PAGE_SIZE
                // New: (old_va + PAGE_SIZE) + (pre_len - 1) * PAGE_SIZE
                //      = old_va + pre_len * PAGE_SIZE <= barrier_va.end
                assert(entry_owners.len() as int == pre_remove_owners.len() as int - 1);
                assert(old_cursor_owner_va.to_vaddr() as int
                    + pre_remove_owners.len() as int * PAGE_SIZE as int
                    <= cursor.inner.barrier_va.end as int);
                assert(cursor.inner.va as int + entry_owners.len() as int * PAGE_SIZE as int
                    <= cursor.inner.barrier_va.end as int);

                // (3) Line 529: forall entry in entry_owners ==> map_cursor_requires.
                // When entry_owners is non-empty, geometric invariant gives cursor.inner.va < barrier_va.end.
                // map postcondition: cursor.inner.va < barrier_va.end ==> map_cursor_requires.
                assert(forall |entry: EntryOwner<KernelPtConfig>| entry_owners.contains(entry) ==>
                    cursor.map_cursor_requires(cursor_owner, *guards)) by {
                    assert forall |entry: EntryOwner<KernelPtConfig>|
                        entry_owners.contains(entry)
                        implies cursor.map_cursor_requires(cursor_owner, *guards) by {
                        assert(entry_owners.len() > 0);
                        assert(entry_owners.len() as int * PAGE_SIZE as int >= PAGE_SIZE as int);
                        assert(cursor.inner.va < cursor.inner.barrier_va.end);
                        // map postcondition: cursor.inner.va < barrier_va.end ==> map_cursor_requires
                    };
                };

                // cursor.inner.va % PAGE_SIZE == 0 (from aligned_nat % PAGE_SIZE == 0, cast is identity)
                assert(cursor_owner@.cur_va % PAGE_SIZE == 0);
                // cursor.inner.va == cursor_owner@.cur_va (from reflect_prop above)
                assert(cursor.inner.va % PAGE_SIZE == 0);
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
    #[verus_spec(
        with Tracked(owner): Tracked<KVirtAreaOwner>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, KernelPtConfig>>,
            Tracked(guard_perm): Tracked<GuardPerm<'a, KernelPtConfig>>
    )]
    pub unsafe fn map_untracked_frames<A: InAtomicMode + 'a, 'a>(
        area_size: usize,
        map_offset: usize,
        pa_range: Range<Paddr>,
        prop: PageProperty,
    ) -> Self
        requires
            0 < area_size,
            area_size <= usize::MAX / 2,
            map_offset % PAGE_SIZE == 0,
            map_offset < area_size,
            // The PA range must fit within [map_offset, area_size) of the virtual area.
            pa_range.end as nat - pa_range.start as nat <= area_size as nat - map_offset as nat,
            // Physical addresses must be within physical memory bounds.
            pa_range.end <= MAX_PADDR,
            // Physical range endpoints must be PAGE_SIZE-aligned (function panics otherwise).
            pa_range.start % PAGE_SIZE == 0,
            pa_range.end % PAGE_SIZE == 0,
            // The physical range must not already be mapped in any page table.
            old(regions).paddr_range_not_mapped(pa_range),
    {
        proof {
            kvirt_alloc_succeeds(area_size);
        }

        let range = KVIRT_AREA_ALLOCATOR.alloc(area_size).unwrap();

        proof {
            kvirt_alloc_range_bounds(area_size, map_offset, range);
        }

        if pa_range.start < pa_range.end {
            let len = pa_range.end - pa_range.start;
            proof {
                // len == pa_range.end - pa_range.start in mathematical integers.
                assert(len as int == pa_range.end as int - pa_range.start as int);
                // New precondition: PA range length <= area_size - map_offset.
                assert(len as int <= area_size as int - map_offset as int);
                // From kvirt_alloc_range_bounds: range.end - range.start >= area_size.
                assert(range.end as int - range.start as int >= area_size as int) by {
                    assert(range.start <= range.end);
                };
                // Combine: range.start + map_offset + len <= range.end.
                assert(range.start as int + map_offset as int + len as int <= range.end as int);
                // range.end <= KERNEL_END_VADDR <= usize::MAX.
                assert(KERNEL_END_VADDR as nat <= usize::MAX as nat) by (compute);
                assert(range.start + map_offset + len <= usize::MAX);
            }
            let va_range = range.start + map_offset..range.start + map_offset + len;

            proof {
                // Conjunct 1: va_range.start < va_range.end (len > 0).
                assert(va_range.start < va_range.end);
                // len % PAGE_SIZE == 0: pa_range.end - pa_range.start, both PAGE_SIZE-aligned.
                // Z3 derives (a-b)%n==0 from a%n==0, b%n==0 for concrete n with the int hint.
                assert(len % PAGE_SIZE == 0) by {
                    assert(len as int == pa_range.end as int - pa_range.start as int);
                };
                // Conjuncts 2 & 3: va_range.start and va_range.end are PAGE_SIZE-aligned.
                // range.start%PAGE_SIZE==0, map_offset%PAGE_SIZE==0, len%PAGE_SIZE==0
                // => Z3 derives alignment of sums.
                assert(va_range.start % PAGE_SIZE == 0);
                assert(va_range.end % PAGE_SIZE == 0);
                // Bounds within the kernel virtual address range.
                assert(KERNEL_BASE_VADDR <= va_range.start);
                assert(va_range.end <= KERNEL_END_VADDR);
                // Conjunct 4: is_valid_range_spec via the kernel-range axiom.
                axiom_kernel_range_valid(va_range);
                // Full condition follows from conjuncts 1-4.
                assert(crate::mm::page_table::Cursor::<KernelPtConfig, A>::cursor_new_success_conditions(&va_range));
            }

            let page_table = get_kernel_page_table();
            let preempt_guard = disable_preempt::<A>();

            // Save regions state before cursor_mut so postcondition trigger can fire.
            let ghost pre_cursor_regions: MetaRegionOwners = *regions;

            let (mut cursor, Tracked(cursor_owner)) =
            (#[verus_spec(with Tracked(owner.pt_owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
                page_table.cursor_mut(preempt_guard, &va_range)).unwrap();

            let pages = collect_largest_pages(va_range.start, pa_range.start, len);
            proof {
                // Initial invariants before the for loop:
                // (a) cursor.inner.va == va_range.start  (cursor_mut postcondition: inner.va == va.start)
                // (b) cursor.inner.barrier_va == va_range  (cursor_mut postcondition)
                //     => barrier_va.end == va_range.start + len
                // (c) sum_page_sizes_spec(pages@, 0, 0) == 0
                //     => cursor.inner.va == va_range.start + sum(0, 0) ✓
                // (d) map_cursor_requires holds from cursor_mut postcondition
                assert(cursor.inner.va == va_range.start);
                assert(cursor.inner.barrier_va == va_range);
                assert(cursor.inner.barrier_va.end == va_range.start + len);
                assert(sum_page_sizes_spec(pages@, 0, 0) == 0nat);
                // PA tracking initial: from collect_largest_pages postcondition.
                // Remaining range initial: sum(0, 0) == 0, so pa_remaining == pa_range.start.
                // cursor_mut preserves item_not_mapped (postcondition at cursor_mut call site),
                // so paddr_range_not_mapped(pa_range) holds after cursor_mut since it held before.
                // cursor_mut preserves slot_owners[idx].path_if_in_pt (postcondition).
                // pre_cursor_regions is the exact pre-cursor_mut state (same as cursor_mut's old(regions)).
                // The precondition gives old(regions).paddr_range_not_mapped(pa_range).
                assert(pre_cursor_regions == *old(regions));
                assert(pre_cursor_regions.paddr_range_not_mapped(pa_range.start..pa_range.end));
                // cursor_mut postcondition: regions.slot_owners[idx].path_if_in_pt ==
                // old(regions).slot_owners[idx].path_if_in_pt (preserved).
                // Function precondition: old(regions).paddr_range_not_mapped(pa_range).
                // Together: regions.paddr_range_not_mapped(pa_range).
                assert forall |paddr: Paddr| #![trigger frame_to_index_spec(paddr)]
                    (pa_range.start <= paddr && paddr < pa_range.end && paddr % PAGE_SIZE == 0)
                    implies regions.slot_owners[frame_to_index_spec(paddr)].path_if_in_pt is None
                by {
                    let idx = frame_to_index_spec(paddr);
                    // Trigger the cursor_mut postcondition for this index.
                    assert(regions.slot_owners[idx].path_if_in_pt
                        == old(regions).slot_owners[idx].path_if_in_pt);
                    // old(regions).paddr_range_not_mapped(pa_range) gives old slot is None.
                    assert(old(regions).slot_owners[idx].path_if_in_pt is None);
                };
                assert(regions.paddr_range_not_mapped(
                    (pa_range.start as nat + sum_page_sizes_spec(pages@, 0, 0)) as usize
                    ..pa_range.end
                ));
                // cursor_mut postcondition: guard_level == NR_LEVELS.
                assert(cursor.inner.guard_level == NR_LEVELS as u8);
            }
            for (pa, level) in it: pages.into_iter()
                invariant
                    cursor.inner.invariants(cursor_owner, *regions, *guards),
                    forall |i: int| 0 <= i < it.elements.len() ==> it.elements[i].0 % PAGE_SIZE == 0,
                    forall |i: int| 0 <= i < it.elements.len() ==>
                        1 <= it.elements[i].1 && it.elements[i].1 <= NR_LEVELS,
                    forall |i: int| 0 <= i < it.elements.len() ==>
                        it.elements[i].1 <= KernelPtConfig::HIGHEST_TRANSLATION_LEVEL(),
                    sum_page_sizes_spec(it.elements, 0, it.elements.len() as int) == len as nat,
                    forall |i: int| 0 <= i < it.elements.len() ==>
                        (va_range.start as nat + sum_page_sizes_spec(it.elements, 0, i))
                            % crate::mm::page_table::page_size(it.elements[i].1) as nat == 0,
                    // VA tracking invariant: cursor has advanced past sum of processed pages.
                    cursor.inner.va as nat
                        == va_range.start as nat
                            + sum_page_sizes_spec(it.elements, 0, it.pos as int),
                    cursor.inner.barrier_va.end == va_range.start + len,
                    it.pos <= it.elements.len(),
                    // map_cursor_requires holds while there are remaining elements.
                    it.pos < it.elements.len() ==>
                        cursor.map_cursor_requires(cursor_owner, *guards),
                    // PA tracking: element[i].0 == pa_range.start + sum of preceding sizes.
                    forall |i: int| 0 <= i < it.elements.len() ==>
                        it.elements[i].0 as nat
                            == pa_range.start as nat + sum_page_sizes_spec(it.elements, 0, i),
                    // Remaining PA range is not mapped.
                    regions.paddr_range_not_mapped(
                        (pa_range.start as nat
                            + sum_page_sizes_spec(it.elements, 0, it.pos as int)) as usize
                        ..pa_range.end
                    ),
                    // pa_range.end == pa_range.start + len in nat (constant throughout loop).
                    pa_range.end as nat == pa_range.start as nat + len as nat,
                    // guard_level == NR_LEVELS (from cursor_mut postcondition, preserved by map).
                    cursor.inner.guard_level == NR_LEVELS as u8,
                    // Physical address bound (function precondition; constant throughout loop).
                    pa_range.end <= MAX_PADDR,
            {
                let pos: Ghost<int> = Ghost(it.pos as int);
                proof {
                    assert(pa % PAGE_SIZE == 0);
                    assert(1 <= level && level <= NR_LEVELS);
                    assert(level <= KernelPtConfig::HIGHEST_TRANSLATION_LEVEL());
                    // cursor.inner.va as nat % page_size(level) as nat == 0
                    assert(
                        (va_range.start as nat
                            + sum_page_sizes_spec(it.elements, 0, pos@))
                            % crate::mm::page_table::page_size(level) as nat == 0
                    );
                    assert(cursor.inner.va as nat % crate::mm::page_table::page_size(level) as nat == 0);

                    // cursor.inner.va + page_size(level) <= barrier_va.end
                    sum_page_sizes_extend_right(it.elements, 0, pos@);
                    sum_page_sizes_mono(it.elements, 0, pos@ + 1, it.elements.len() as int);
                    assert(
                        cursor.inner.va as nat + crate::mm::page_table::page_size(level) as nat
                            == va_range.start as nat
                                + sum_page_sizes_spec(it.elements, 0, pos@ + 1)
                    );
                    assert(
                        cursor.inner.va as nat + crate::mm::page_table::page_size(level) as nat
                            <= cursor.inner.barrier_va.end as nat
                    );
                    // map_cursor_requires from the loop invariant
                    assert(cursor.map_cursor_requires(cursor_owner, *guards));
                    // pa < pa_range.end <= MAX_PADDR (both from loop invariants).
                    assert((pa as nat) < (pa_range.end as nat));
                    // pa_range.end <= MAX_PADDR is a loop invariant; chain to usize.
                    assert(pa < MAX_PADDR);
                }

                let item = MappedItem::Untracked(pa, level, prop);
                proof_decl! {
                    let tracked entry_owner =
                        EntryOwner::<KernelPtConfig>::new_untracked_frame(pa, level, prop);
                }

                let ghost old_cursor_model: CursorView<KernelPtConfig> =
                    cursor.inner.model(cursor_owner);
                let ghost old_cursor_owner_va = cursor_owner.va;
                let ghost old_va: nat = cursor.inner.va as nat;

                proof {
                    assert(cursor.inner.wf(cursor_owner));
                    assert(cursor_owner.va.reflect(cursor.inner.va));
                    cursor_owner.va.reflect_prop(cursor.inner.va);
                    assert(old_cursor_owner_va.to_vaddr() as nat == old_va);

                    KernelPtConfig::item_into_raw_spec_untracked(pa, level, prop);
                    // item_into_raw_spec(item) == (pa, level, prop)

                    assert(cursor.map_item_requires(item, entry_owner)) by {
                        KernelPtConfig::item_into_raw_spec_untracked(pa, level, prop);
                        // 1. entry_owner.inv(): from new_untracked_frame ensures res.inv()
                        //    (pa < MAX_PADDR was proved before the proof_decl! call).
                        assert(entry_owner.inv());
                        // 2. va % page_size(level) == 0 (proved in outer proof block).
                        assert(cursor.inner.va % crate::mm::page_table::page_size(level) == 0) by {
                            assert(cursor.inner.va as nat
                                % crate::mm::page_table::page_size(level) as nat == 0);
                        };
                        // 3. va + page_size(level) <= barrier_va.end (proved in outer proof block).
                        assert(
                            cursor.inner.va + crate::mm::page_table::page_size(level)
                                <= cursor.inner.barrier_va.end
                        ) by {
                            assert(cursor.inner.va as nat
                                + crate::mm::page_table::page_size(level) as nat
                                <= cursor.inner.barrier_va.end as nat);
                        };
                        // 4. level < guard_level: level <= HIGHEST_TRANSLATION_LEVEL < NR_LEVELS == guard_level.
                        assert(level < cursor.inner.guard_level) by {
                            KernelPtConfig::axiom_kernel_htl_lt_nr_levels();
                            assert(cursor.inner.guard_level == NR_LEVELS as u8);
                            assert(level <= KernelPtConfig::HIGHEST_TRANSLATION_LEVEL());
                        };
                        // 5. Child::Frame(pa, level, prop).wf(entry_owner): from new_untracked_frame ensures.
                        assert(crate::mm::page_table::Child::<KernelPtConfig>::Frame(
                            pa, level, prop).wf(entry_owner));
                    };

                    assert(cursor.map_panic_conditions(item)) by {
                        // item_into_raw(item).1 == level (from untracked axiom)
                        // va < barrier_va.end: from map_cursor_requires (loop invariant)
                        // map_cursor_requires (loop invariant) directly gives va < barrier_va.end
                        assert(cursor.inner.va < cursor.inner.barrier_va.end);
                        // level <= HIGHEST_TRANSLATION_LEVEL: loop invariant
                        // !TOP_LEVEL_CAN_UNMAP ==> level < NR_LEVELS:
                        //   TOP_LEVEL_CAN_UNMAP_spec() == false for KernelPtConfig
                        //   level <= HIGHEST_TRANSLATION_LEVEL < NR_LEVELS (axiom)
                        assert(!KernelPtConfig::TOP_LEVEL_CAN_UNMAP_spec());
                        KernelPtConfig::axiom_kernel_htl_lt_nr_levels();
                        // va % page_size(level) == 0 and va + page_size(level) <= barrier_va.end
                        // (established in nat above; admit usize conversion)
                        assert(cursor.inner.va % crate::mm::page_table::page_size(level) == 0)
                            by {
                            assert(cursor.inner.va as nat
                                % crate::mm::page_table::page_size(level) as nat == 0);
                        };
                        assert(
                            cursor.inner.va + crate::mm::page_table::page_size(level)
                                <= cursor.inner.barrier_va.end
                        ) by {
                            assert(cursor.inner.va as nat
                                + crate::mm::page_table::page_size(level) as nat
                                <= cursor.inner.barrier_va.end as nat);
                        };
                    };

                    // pa_range.end == pa_range.start + len (in nat) — from loop invariant.
                    assert(CursorMut::<'a, KernelPtConfig, A>::item_not_mapped(item, *regions))
                        by {
                        // item_not_mapped ↔ paddr_range_not_mapped(pa..(pa + page_size(level)))
                        // where item = Untracked(pa, level, prop).
                        // PA tracking invariant: pa == pa_range.start + sum(0, pos)
                        assert(pa as nat
                            == pa_range.start as nat
                                + sum_page_sizes_spec(it.elements, 0, pos@));
                        // pa + page_size(level) == pa_range.start + sum(0, pos+1)
                        sum_page_sizes_extend_right(it.elements, 0, pos@);
                        assert(pa as nat + crate::mm::page_table::page_size(level) as nat
                            == pa_range.start as nat
                                + sum_page_sizes_spec(it.elements, 0, pos@ + 1));
                        // sum(0, pos+1) <= len == pa_range.end - pa_range.start
                        sum_page_sizes_mono(
                            it.elements, 0, pos@ + 1, it.elements.len() as int);
                        // pa_range.end == pa_range.start + len (proved above)
                        assert(pa_range.end as nat == pa_range.start as nat + len as nat);
                        assert(pa as nat + crate::mm::page_table::page_size(level) as nat
                            <= pa_range.end as nat);
                        // Remaining range invariant: paddr_range_not_mapped(pa..pa_range.end).
                        // (since pa == (pa_range.start + sum(0,pos)) as usize = pa_remaining)
                        assert(pa == (pa_range.start as nat
                            + sum_page_sizes_spec(it.elements, 0, pos@)) as usize);
                        // [pa, pa+page_size(level)) ⊆ [pa, pa_range.end) → subrange proof.
                        assert forall|paddr: Paddr|
                            #![trigger frame_to_index_spec(paddr)]
                            (pa <= paddr
                                && paddr < (pa + crate::mm::page_table::page_size(level)) as usize
                                && paddr % PAGE_SIZE == 0)
                            implies
                            regions.slot_owners[frame_to_index_spec(paddr)].path_if_in_pt is None
                        by {
                            // paddr is in [pa, pa_range.end) since pa+page_size(level) <= pa_range.end
                            // loop invariant paddr_range_not_mapped(pa..pa_range.end) fires here
                        };
                    };
                }

                // Save ghost copy of regions before map for post-map invariant maintenance.
                let ghost pre_map_regions: MetaRegionOwners = *regions;

                // SAFETY: The caller of `map_untracked_frames` has ensured the safety of this mapping.
                #[verus_spec(with Tracked(&mut cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))]
                let _ = cursor.map(item);

                // Post-map: maintain the VA tracking invariant.
                proof {
                    KernelPtConfig::item_into_raw_spec_untracked(pa, level, prop);
                    let level_raw = KernelPtConfig::item_into_raw_spec(item).1;
                    assert(level_raw == level);

                    // From map_item_ensures:
                    // cursor_owner@ == old_cursor_model.map_spec(pa, page_size(level), prop)
                    assert(
                        cursor_owner@
                            == old_cursor_model.map_spec(
                                pa,
                                crate::mm::page_table::page_size(level_raw),
                                prop,
                            )
                    );
                    let split_self = old_cursor_model.split_while_huge(
                        crate::mm::page_table::page_size(level_raw));
                    assert(
                        cursor_owner@.cur_va
                            == split_self.align_up_spec(
                                crate::mm::page_table::page_size(level_raw))
                    );

                    CursorView::<KernelPtConfig>::lemma_split_while_huge_preserves_cur_va(
                        old_cursor_model, crate::mm::page_table::page_size(level_raw));
                    assert(split_self.cur_va == old_cursor_model.cur_va);
                    assert(old_cursor_model.cur_va == old_cursor_owner_va.to_vaddr());

                    let aligned_nat = vstd_extra::arithmetic::nat_align_up(
                        old_cursor_owner_va.to_vaddr() as nat,
                        crate::mm::page_table::page_size(level_raw) as nat,
                    );
                    assert(
                        split_self.align_up_spec(crate::mm::page_table::page_size(level_raw))
                            == aligned_nat as Vaddr
                    );
                    assert(cursor_owner@.cur_va == aligned_nat as Vaddr);

                    // page_size(level) >= PAGE_SIZE > 0, so the precondition align > 0 holds
                    // level_raw == level == it.elements[pos].1, and 1 <= level <= NR_LEVELS
                    assert(1 <= level_raw <= NR_LEVELS) by {
                        assert(level_raw == level);
                        // from loop invariant: 1 <= it.elements[pos@].1 <= NR_LEVELS
                        // level = it.elements[pos@].1 (set earlier in the loop body)
                    };
                    crate::mm::page_table::axiom_page_size_ge_page_size(level_raw);
                    assert(crate::mm::page_table::page_size(level_raw) as nat > 0nat);
                    vstd_extra::arithmetic::lemma_nat_align_up_sound(
                        old_cursor_owner_va.to_vaddr() as nat,
                        crate::mm::page_table::page_size(level_raw) as nat,
                    );

                    old_cursor_owner_va.align_diff(level_raw as int);
                    // => nat_align_up(old_va, ps) = nat_align_down(old_va, ps) + ps
                    // old_va % ps == 0 (nat), so nat_align_down(old_va, ps) = old_va
                    assert(
                        old_cursor_owner_va.to_vaddr() as nat
                            % crate::mm::page_table::page_size(level_raw) as nat == 0
                    );
                    assert(
                        vstd_extra::arithmetic::nat_align_down(
                            old_cursor_owner_va.to_vaddr() as nat,
                            crate::mm::page_table::page_size(level_raw) as nat,
                        ) == old_cursor_owner_va.to_vaddr() as nat
                    );
                    assert(
                        aligned_nat
                            == old_va + crate::mm::page_table::page_size(level_raw) as nat
                    );

                    // cursor.inner.va (post-map) == aligned_nat as usize
                    assert(cursor.inner.wf(cursor_owner));
                    assert(cursor_owner.va.reflect(cursor.inner.va));
                    cursor_owner.va.reflect_prop(cursor.inner.va);
                    assert(
                        cursor.inner.va as nat
                            == old_va + crate::mm::page_table::page_size(level) as nat
                    );

                    // Maintain sum invariant:
                    // cursor.inner.va = old_va + page_size(level)
                    //   = (va_range.start + sum(0, pos)) + page_size(elements[pos])
                    //   = va_range.start + sum(0, pos+1)
                    sum_page_sizes_extend_right(it.elements, 0, pos@);
                    assert(
                        cursor.inner.va as nat
                            == va_range.start as nat
                                + sum_page_sizes_spec(it.elements, 0, pos@ + 1)
                    );

                    // Maintain paddr_range_not_mapped for the remaining elements.
                    // After mapping pa at level, cursor.map postcondition:
                    //   idx != frame_to_index(pa) ==> slot_owners[idx].path_if_in_pt unchanged.
                    // For any paddr in [pa_next, pa_range.end):
                    //   pa_next = pa + page_size(level), both page-aligned
                    //   paddr >= pa + PAGE_SIZE > pa => paddr / PAGE_SIZE > pa / PAGE_SIZE
                    //   => frame_to_index(paddr) != frame_to_index(pa)
                    //   => path_if_in_pt unchanged (= None from pre-map invariant)
                    let pa_next_nat =
                        pa_range.start as nat + sum_page_sizes_spec(it.elements, 0, pos@ + 1);
                    assert(regions.paddr_range_not_mapped(
                        pa_next_nat as usize..pa_range.end
                    )) by {
                        // sum_page_sizes_extend_right already called above
                        assert(pa_next_nat
                            == pa as nat + crate::mm::page_table::page_size(level) as nat);
                        assert forall|paddr: Paddr|
                            #![trigger frame_to_index_spec(paddr)]
                            (paddr >= pa_next_nat as usize
                                && paddr < pa_range.end
                                && paddr % PAGE_SIZE == 0)
                            implies
                            regions.slot_owners[frame_to_index_spec(paddr)].path_if_in_pt is None
                        by {
                            // frame_to_index(paddr) != frame_to_index(pa):
                            //   paddr >= pa + page_size(level) >= pa + PAGE_SIZE > pa
                            //   => paddr / PAGE_SIZE > pa / PAGE_SIZE
                            assert(frame_to_index_spec(paddr) != frame_to_index_spec(pa)) by {
                                // paddr >= pa + page_size(level) >= pa + PAGE_SIZE
                                crate::mm::page_table::axiom_page_size_ge_page_size(level);
                                assert(paddr as nat >= pa as nat + PAGE_SIZE as nat);
                                // (pa + PAGE_SIZE) / PAGE_SIZE == pa / PAGE_SIZE + 1
                                vstd::arithmetic::div_mod::lemma_div_plus_one(
                                    pa as int, PAGE_SIZE as int);
                                // paddr / PAGE_SIZE >= (pa + PAGE_SIZE) / PAGE_SIZE
                                vstd::arithmetic::div_mod::lemma_div_is_ordered(
                                    pa as int + PAGE_SIZE as int,
                                    paddr as int,
                                    PAGE_SIZE as int);
                                // => paddr / PAGE_SIZE >= pa / PAGE_SIZE + 1 > pa / PAGE_SIZE
                            };
                            // cursor.map postcondition: idx != frame_to_index(pa) =>
                            //   regions.slot_owners[idx].path_if_in_pt ==
                            //   old(regions).slot_owners[idx].path_if_in_pt
                            // where old(regions) at the cursor.map call site = pre_map_regions.
                            assert(regions.slot_owners[frame_to_index_spec(paddr)].path_if_in_pt
                                == pre_map_regions.slot_owners[frame_to_index_spec(paddr)].path_if_in_pt);
                            // pre_map_regions.paddr_range_not_mapped(pa..pa_range.end) was the
                            // loop invariant before the map call; paddr >= pa_next > pa so it fires.
                            assert(pre_map_regions.slot_owners[frame_to_index_spec(paddr)].path_if_in_pt
                                is None);
                        };
                    };

                    // Maintain map_cursor_requires for the next iteration.
                    // If pos+1 < len: cursor.inner.va < barrier_va.end
                    //   sum(0, pos+1) + page_size(elements[pos+1]) = sum(0, pos+2) <= sum(0, n) = len
                    //   page_size(elements[pos+1]) >= PAGE_SIZE > 0, so sum(0, pos+1) < len
                    if pos@ + 1 < it.elements.len() as int {
                        let next_level = it.elements[pos@ + 1].1;
                        sum_page_sizes_extend_right(it.elements, 0, pos@ + 1);
                        sum_page_sizes_mono(it.elements, 0, pos@ + 2, it.elements.len() as int);
                        crate::mm::page_table::axiom_page_size_ge_page_size(next_level);
                        // sum(0, pos+2) <= len, page_size(next) >= PAGE_SIZE
                        // => sum(0, pos+1) + PAGE_SIZE <= len => sum(0, pos+1) < len
                        assert(
                            sum_page_sizes_spec(it.elements, 0, pos@ + 1)
                                + PAGE_SIZE as nat <= len as nat
                        );
                        assert(cursor.inner.va < cursor.inner.barrier_va.end);
                        // From map postcondition
                        assert(cursor.map_cursor_requires(cursor_owner, *guards));
                    }
                }
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