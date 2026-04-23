// SPDX-License-Identifier: MPL-2.0
//! Kernel virtual memory allocation
use vstd::prelude::*;

use vstd_extra::arithmetic::nat_align_down;
use vstd_extra::ownership::{InvView, ModelOf, OwnerOf};
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
        page_table::{
            is_valid_range_spec, page_size,
            Child, CursorMut, PageTable, PageTableConfig,
        },
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
use crate::mm::page_table::PageTableGuard;
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
/// to the spec function `frame_as_dynframe`. The `Into` impl uses `transmute`, so the
/// function is marked `external_body` — same trust boundary as the underlying conversion.
#[verifier::external_body]
fn frame_into_dynframe<T: AnyUFrameMeta>(frame: Frame<T>) -> (res: DynFrame)
    ensures
        res == frame_as_dynframe(frame),
{
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
    Child::Frame(pa, level, prop_from_item).wf(entry_owner)
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
        page_size(elems[from].1) as nat
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
                + page_size(elems[to].1) as nat,
    decreases to - from,
{
    if from < to {
        sum_page_sizes_extend_right(elems, from + 1, to);
        // Help Verus: unfold sum_page_sizes_spec(elems, from, to) and (from, to+1)
        assert(sum_page_sizes_spec(elems, from, to) ==
            page_size(elems[from].1) as nat
                + sum_page_sizes_spec(elems, from + 1, to));
        assert(sum_page_sizes_spec(elems, from, to + 1) ==
            page_size(elems[from].1) as nat
                + sum_page_sizes_spec(elems, from + 1, to + 1));
    } else {
        // from == to; explicitly unfold both sides
        assert(sum_page_sizes_spec(elems, from, to) == 0nat);
        assert(sum_page_sizes_spec(elems, from, to + 1) ==
            page_size(elems[from].1) as nat
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
        forall |i: int| 0 <= i < res@.len() ==> (#[trigger] res@[i]).0 % PAGE_SIZE == 0,
        forall |i: int| 0 <= i < res@.len() ==> 1 <= (#[trigger] res@[i]).1 <= NR_LEVELS,
        forall |i: int| 0 <= i < res@.len() ==>
            (#[trigger] res@[i]).1 <= KernelPtConfig::HIGHEST_TRANSLATION_LEVEL(),
        sum_page_sizes_spec(res@, 0, res@.len() as int) == len as nat,
        forall |i: int| 0 <= i < res@.len() ==>
            (va as nat + #[trigger] sum_page_sizes_spec(res@, 0, i))
                % page_size(res@[i].1) as nat == 0,
        // PA tracking: each element's physical address equals pa + sum of preceding page sizes.
        forall |i: int| 0 <= i < res@.len() ==>
            (#[trigger] res@[i]).0 as nat == pa as nat + sum_page_sizes_spec(res@, 0, i),
{
    largest_pages::<KernelPtConfig>(va, pa, len).collect()
}

#[verifier::external_body]
pub(crate) fn get_kernel_page_table<'rcu>(
    Tracked(kernel_owner): Tracked<&mut Option<&PageTableOwner<KernelPtConfig>>>,
    Tracked(regions): Tracked<&MetaRegionOwners>,
    Tracked(guards_k): Tracked<&Guards<'rcu, KernelPtConfig>>,
) -> (r: &'static PageTable<KernelPtConfig>)
    requires
        regions.inv(),
    ensures
        final(kernel_owner)@ is Some,
        final(kernel_owner)@.unwrap().inv(),
        final(kernel_owner)@.unwrap().0.value.node is Some,
        r.root.ptr.addr() == final(kernel_owner)@.unwrap().0.value.node.unwrap().meta_perm.addr(),
        !PageTable::<KernelPtConfig>::create_user_pt_panic_condition(
            final(kernel_owner)@.unwrap().0.value.node.unwrap(),
        ),
        final(kernel_owner)@.unwrap().0.value.metaregion_sound(*regions),
        final(kernel_owner)@.unwrap().metaregion_sound(*regions),
        guards_k.unlocked(
            final(kernel_owner)@.unwrap().0.value.node.unwrap().meta_perm.addr()),
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
        ==> is_valid_range_spec::<KernelPtConfig>(&r);

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
    pub pt_owner: PageTableOwner<KernelPtConfig>,
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
    #[verus_spec(r =>
        with Tracked(owner): Tracked<KVirtAreaOwner>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'static, KernelPtConfig>>,
            Tracked(guard_perm): Tracked<GuardPerm<'static, KernelPtConfig>>
        requires
            self.inv(),
            self.range.start <= addr && addr < self.range.end,
            self.range.start % PAGE_SIZE == 0,
            self.range.end % PAGE_SIZE == 0,
            old(regions).inv(),
            owner.pt_owner.inv(),
            forall |i: usize|
                #![trigger old(regions).slot_owners[i]]
                old(regions).slot_owners.contains_key(i)
                && old(regions).slot_owners[i].inner_perms.ref_count.value()
                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                ==> old(regions).slot_owners[i].inner_perms.ref_count.value() + 1
                    < crate::specs::mm::frame::meta_owners::REF_COUNT_MAX,
        ensures
            self.query_some_condition(owner, addr) ==> self.query_some_ensures(owner, addr, r),
            !self.query_some_condition(owner, addr) ==> Self::query_none_ensures(r),
    )]
    pub fn query<A: InAtomicMode + 'static>(&self, addr: Vaddr) -> Option<super::MappedItem>
    {
        use align_ext::AlignExt;

        proof {
            vstd_extra::prelude::lemma_pow2_is_pow2_to64();
            broadcast use vstd::arithmetic::power2::is_pow2_equiv, vstd::arithmetic::power2::lemma_pow2;
            let witness: nat = choose |i: nat| vstd::arithmetic::power::pow(2, i) == PAGE_SIZE as int;
            assert(vstd::arithmetic::power2::pow2(witness) == PAGE_SIZE);
        }
        let start = addr.align_down(PAGE_SIZE);
        proof {
            assert(start <= addr);
            assert(addr < self.range.end);
            assert(self.range.end <= KERNEL_END_VADDR);
            assert(KERNEL_END_VADDR + PAGE_SIZE <= usize::MAX) by (compute_only);
            // start >= self.range.start: align_down's forall postcondition instantiated at self.range.start.
            assert(start >= self.range.start);
            // start + PAGE_SIZE <= self.range.end: self.range.end is page-aligned and addr < self.range.end.
            assert(start + PAGE_SIZE <= self.range.end);
        }
        let vaddr = start..start + PAGE_SIZE;
        proof {
            axiom_kernel_range_valid(vaddr);
        }
        let page_table = {
            proof_decl! { let tracked mut _kpt_owner: Option<&PageTableOwner<KernelPtConfig>> = None; }
            get_kernel_page_table(Tracked(&mut _kpt_owner), Tracked(regions), Tracked(guards))
        };
        let preempt_guard = disable_preempt::<A>();
        let (mut cursor, Tracked(mut cursor_owner)) =
            (#[verus_spec(with Tracked(owner.pt_owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
                page_table.cursor(preempt_guard, &vaddr)).unwrap();
        proof {
            // Bridge `cursor_owner@.mappings` to `owner.cursor_view_at(addr).mappings`.
            // PageTable::cursor ensures `cursor_owner.as_page_table_owner() == owner.pt_owner`
            // and `cursor_owner.continuations[3].path() == owner.pt_owner.0.value.path`, and
            // `as_page_table_owner_preserves_view_mappings` turns the cursor's view into a
            // `view_rec` call on the owner at the root path.
            cursor_owner.as_page_table_owner_preserves_view_mappings();
            assert(cursor_owner.view_mappings()
                == owner.pt_owner.view_rec(owner.pt_owner.0.value.path));
            // cur_va agreement: `cursor.wf(cursor_owner)` gives `cursor_owner.va.reflect(cursor.va)`,
            // which `reflect_prop` converts into `cursor_owner.va.to_vaddr() == cursor.va`.
            cursor_owner.va.reflect_prop(cursor.va);
            assert(cursor_owner.cur_va() == start);
        }
        let ghost pre_query_view = cursor_owner@;
        let ghost pre_query_cursor_va = cursor.va;
        let state = (#[verus_spec(with Tracked(&mut cursor_owner), Tracked(regions), Tracked(guards))]
            cursor.query()).unwrap();
        proof {
            // `Cursor::query` preserves `self.va` (loop invariant + new ensures) and
            // `cursor_owner@.mappings`. With `cursor.wf(cursor_owner)` reestablished
            // by post-query invariants, we can recover `cursor_owner@.cur_va == start`.
            assert(cursor.va == pre_query_cursor_va);
            assert(cursor_owner@.mappings == pre_query_view.mappings);
            cursor_owner.va.reflect_prop(cursor.va);
            assert(cursor_owner@.cur_va == start);
            assert(cursor_owner@.mappings == owner.cursor_view_at(addr).mappings);
            assert(cursor_owner@.cur_va == owner.cursor_view_at(addr).cur_va);
        }
        state.1
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
    #[verus_spec(
        with Tracked(owner): Tracked<KVirtAreaOwner>,
            Tracked(entry_owners): Tracked<&mut Seq<EntryOwner<KernelPtConfig>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, KernelPtConfig>>,
            Tracked(guard_perm): Tracked<GuardPerm<'a, KernelPtConfig>>
    )]
    pub fn map_frames<'a, A: InAtomicMode + 'a>(
        area_size: usize,
        map_offset: usize,
        frames: alloc::vec::Vec<DynFrame>,
        prop: PageProperty,
    ) -> Self
        requires
            old(regions).inv(),
            0 < area_size,
            map_offset < area_size,
            map_offset % PAGE_SIZE == 0,
            area_size <= usize::MAX / 2,
            old(entry_owners).len() == frames.len(),
            frames.len() as int * PAGE_SIZE as int + map_offset as int <= area_size as int,
            forall |i: int| 0 <= i < old(entry_owners).len() ==> (#[trigger] old(entry_owners)[i]).inv(),
            forall |i: int| 0 <= i < frames.len() ==>
                frame_entry_wf(frames[i], prop, #[trigger] old(entry_owners)[i]),
            // Frames have distinct physical addresses (follows from linearity of slot_perm ownership).
            forall |i: int, j: int| 0 <= i < j < frames.len() ==>
                (#[trigger] old(entry_owners)[i]).frame.unwrap().mapped_pa != (#[trigger] old(entry_owners)[j]).frame.unwrap().mapped_pa,
    {
        #[cfg(feature = "allow_panic")]
        assert!(area_size % PAGE_SIZE == 0);
        #[cfg(feature = "allow_panic")]
        assert!(map_offset % PAGE_SIZE == 0);

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

        let page_table = {
                proof_decl! {
                    let tracked mut _kpt_owner: Option<&PageTableOwner<KernelPtConfig>> = None;
                }
                get_kernel_page_table(Tracked(&mut _kpt_owner), Tracked(regions), Tracked(guards))
            };
        let preempt_guard = disable_preempt::<A>();

        let (mut cursor, Tracked(cursor_owner)) =
        (#[verus_spec(with Tracked(owner.pt_owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
            page_table.cursor_mut(preempt_guard, &cursor_range)).unwrap();

        let ghost init_frames_len = frames.len();

        for frame in it: frames.into_iter()
            invariant
                cursor.inner.invariants(cursor_owner, *regions, *guards),
                forall |i: int| 0 <= i < entry_owners.len() ==> (#[trigger]entry_owners[i]).inv(),
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
                // Remaining frames have distinct physical addresses
                forall |i: int, j: int| 0 <= i < j < it.elements.len() - it.pos ==>
                    (#[trigger]entry_owners[i]).frame.unwrap().mapped_pa != (#[trigger] entry_owners[j]).frame.unwrap().mapped_pa,
        {
            proof {
                assert(entry_owners.contains(entry_owners[0]));
                assert(frame_entry_wf(frame, prop, entry_owners[0]));
            }

            let ghost cur_mapped_pa: usize = entry_owners[0].frame.unwrap().mapped_pa;
            let ghost cur_pa_from_wf: usize = KernelPtConfig::item_into_raw_spec(
                MappedItem::Tracked(frame_as_dynframe(it.elements.index(it.pos as int)), prop)).0;
            let ghost pre_remove_owners: Seq<EntryOwner<KernelPtConfig>> = *entry_owners;

            let tracked mut entry_owner = entry_owners.tracked_remove(0);

            // Now Verus knows: dynframe == frame_as_dynframe(it.elements[it.pos])
            let item = MappedItem::Tracked(frame, prop);
            assert(cursor.inner.invariants(cursor_owner, *regions, *guards));

            let ghost regions_before_map = *regions;
            let ghost old_cursor_model: CursorView<KernelPtConfig> = cursor.inner.model(cursor_owner);
            let ghost old_cursor_owner_va = cursor_owner.va;
            proof {
                cursor_owner.view_preserves_inv(); // old_cursor_model.inv()
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

                KernelPtConfig::item_into_raw_spec_tracked_level(item);
            }

            // SAFETY: The constructor of the `KVirtArea` has already ensured
            // that this mapping does not affect kernel's memory safety.
            assert(CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(
                item, *regions,
            )) by { admit() };
            #[verus_spec(with Tracked(&mut cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))]
            let res = cursor.map(item);

            proof {
                pre_remove_owners.remove_ensures(0);
                let cur_idx = frame_to_index_spec(cur_mapped_pa);

                let (pa, level, prop_) = KernelPtConfig::item_into_raw_spec(item);
                KernelPtConfig::item_into_raw_spec_tracked_level(item);

                let split_self = old_cursor_model.split_while_huge(PAGE_SIZE);

                let aligned_nat: nat = vstd_extra::arithmetic::nat_align_up(
                    split_self.cur_va as nat, PAGE_SIZE as nat);

                vstd_extra::arithmetic::lemma_nat_align_up_sound(
                    split_self.cur_va as nat, PAGE_SIZE as nat);

                CursorView::<KernelPtConfig>::lemma_split_while_huge_preserves_cur_va(
                    old_cursor_model, PAGE_SIZE);

                assert(aligned_nat == vstd_extra::arithmetic::nat_align_up(
                    old_cursor_owner_va.to_vaddr() as nat, PAGE_SIZE as nat));
                old_cursor_owner_va.align_diff(1);

                assert(vstd_extra::arithmetic::nat_align_down(
                    old_cursor_owner_va.to_vaddr() as nat, PAGE_SIZE as nat)
                    == old_cursor_owner_va.to_vaddr() as nat);
                
                cursor_owner.va.reflect_prop(cursor.inner.va);
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
            old(regions).inv(),
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
        #[cfg(feature = "allow_panic")]
        assert!(pa_range.start % PAGE_SIZE == 0);
        #[cfg(feature = "allow_panic")]
        assert!(pa_range.end % PAGE_SIZE == 0);
        #[cfg(feature = "allow_panic")]
        assert!(area_size % PAGE_SIZE == 0);
        #[cfg(feature = "allow_panic")]
        assert!(map_offset % PAGE_SIZE == 0);
        #[cfg(feature = "allow_panic")]
        assert!(map_offset + (pa_range.end - pa_range.start) <= area_size);

        proof {
            kvirt_alloc_succeeds(area_size);
        }

        let range = KVIRT_AREA_ALLOCATOR.alloc(area_size).unwrap();

        proof {
            kvirt_alloc_range_bounds(area_size, map_offset, range);
        }

        if pa_range.start < pa_range.end {
            let len = pa_range.end - pa_range.start;
            let va_range = range.start + map_offset..range.start + map_offset + len;

            proof {
                axiom_kernel_range_valid(va_range);
//                assert(crate::mm::page_table::Cursor::<KernelPtConfig, A>::cursor_new_success_conditions(&va_range));
            }

            let page_table = {
                proof_decl! {
                    let tracked mut _kpt_owner: Option<&PageTableOwner<KernelPtConfig>> = None;
                }
                get_kernel_page_table(Tracked(&mut _kpt_owner), Tracked(regions), Tracked(guards))
            };
            let preempt_guard = disable_preempt::<A>();

            // Save regions state before cursor_mut so postcondition trigger can fire.
            let ghost pre_cursor_regions: MetaRegionOwners = *regions;

            let (mut cursor, Tracked(cursor_owner)) =
            (#[verus_spec(with Tracked(owner.pt_owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
                page_table.cursor_mut(preempt_guard, &va_range)).unwrap();

            let pages = collect_largest_pages(va_range.start, pa_range.start, len);

            for (pa, level) in it: pages.into_iter()
                invariant
                    cursor.inner.invariants(cursor_owner, *regions, *guards),
                    forall |i: int| 0 <= i < it.elements.len() ==> (#[trigger] it.elements[i]).0 % PAGE_SIZE == 0,
                    forall |i: int| 0 <= i < it.elements.len() ==>
                        1 <= (#[trigger] it.elements[i]).1<= NR_LEVELS,
                    forall |i: int| 0 <= i < it.elements.len() ==>
                        (#[trigger] it.elements[i]).1 <= KernelPtConfig::HIGHEST_TRANSLATION_LEVEL(),
                    sum_page_sizes_spec(it.elements, 0, it.elements.len() as int) == len as nat,
                    forall |i: int| 0 <= i < it.elements.len() ==>
                        (va_range.start as nat + #[trigger] sum_page_sizes_spec(it.elements, 0, i))
                            % page_size(it.elements[i].1) as nat == 0,
                    // VA tracking invariant: cursor has advanced past sum of processed pages.
                    cursor.inner.va as nat
                        == va_range.start as nat
                            + sum_page_sizes_spec(it.elements, 0, it.pos as int),
                    cursor.inner.barrier_va.end == va_range.start + len,
                    it.pos <= it.elements.len(),
                    // PA tracking: element[i].0 == pa_range.start + sum of preceding sizes.
                    forall |i: int| #![auto] 0 <= i < it.elements.len() ==>
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
                    sum_page_sizes_extend_right(it.elements, 0, pos@);
                    sum_page_sizes_mono(it.elements, 0, pos@ + 1, it.elements.len() as int);
                }

                let item = MappedItem::Untracked(pa, level, prop);
                proof {
                    lemma_page_size_ge_page_size(level);
                    assert(pa as nat + page_size(level) as nat <= pa_range.end as nat);
                    assert(pa < MAX_PADDR);
                }
                proof_decl! {
                    let tracked mut entry_owner =
                        EntryOwner::<KernelPtConfig>::new_untracked_frame(pa, level, prop);
                    entry_owner.in_scope = false;
                }

                let ghost old_cursor_model: CursorView<KernelPtConfig> =
                    cursor.inner.model(cursor_owner);
                let ghost old_cursor_owner_va = cursor_owner.va;
                let ghost old_va: nat = cursor.inner.va as nat;

                proof {
                    cursor_owner.view_preserves_inv(); // old_cursor_model.inv()
                    cursor_owner.va.reflect_prop(cursor.inner.va);

                    KernelPtConfig::item_into_raw_spec_untracked(pa, level, prop);

                    // pa_range.end == pa_range.start + len (in nat) — from loop invariant.
                    sum_page_sizes_extend_right(it.elements, 0, pos@);
                    sum_page_sizes_mono(
                        it.elements, 0, pos@ + 1, it.elements.len() as int);
                }

                // Save ghost copy of regions before map for post-map invariant maintenance.
                let ghost pre_map_regions: MetaRegionOwners = *regions;

                proof {
                    KernelPtConfig::axiom_kernel_htl_lt_nr_levels();
                    assert(!cursor.map_panic_conditions(item));
                    assert(cursor.item_wf(item, entry_owner));
                }
                // SAFETY: The caller of `map_untracked_frames` has ensured the safety of this mapping.
                assume(CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(item, *regions));
                #[verus_spec(with Tracked(&mut cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))]
                let _ = cursor.map(item);

                // Post-map: maintain the VA tracking invariant.
                proof {
                    KernelPtConfig::item_into_raw_spec_untracked(pa, level, prop);
                    let level_raw = KernelPtConfig::item_into_raw_spec(item).1;
                    
                    let split_self = old_cursor_model.split_while_huge(
                        page_size(level_raw));

                    CursorView::<KernelPtConfig>::lemma_split_while_huge_preserves_cur_va(
                        old_cursor_model, page_size(level_raw));

                    let aligned_nat = vstd_extra::arithmetic::nat_align_up(
                        old_cursor_owner_va.to_vaddr() as nat,
                        page_size(level_raw) as nat,
                    );
                    
                    lemma_page_size_ge_page_size(level_raw);

                    vstd_extra::arithmetic::lemma_nat_align_up_sound(
                        old_cursor_owner_va.to_vaddr() as nat,
                        page_size(level_raw) as nat,
                    );

                    old_cursor_owner_va.align_diff(level_raw as int);
                    
                    sum_page_sizes_extend_right(it.elements, 0, pos@);
                    
                    let pa_next_nat = pa_range.start as nat + sum_page_sizes_spec(it.elements, 0, pos@ + 1);
                    assert(pa_next_nat == pa as nat + page_size(level) as nat);

                    if pos@ + 1 < it.elements.len() as int {
                        let next_level = it.elements[pos@ + 1].1;
                        sum_page_sizes_extend_right(it.elements, 0, pos@ + 1);
                        sum_page_sizes_mono(it.elements, 0, pos@ + 2, it.elements.len() as int);
                        lemma_page_size_ge_page_size(next_level);
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
