// SPDX-License-Identifier: MPL-2.0
//! Kernel virtual memory allocation
use vstd::prelude::*;

use vstd_extra::arithmetic::nat_align_down;
use vstd_extra::ownership::{InvView, ModelOf, OwnerOf};
use vstd_extra::prelude::Inv;

use core::marker::PhantomData;
use core::ops::Range;

use super::{KERNEL_PAGE_TABLE, VMALLOC_VADDR_RANGE, KERNEL_BASE_VADDR, KERNEL_END_VADDR,
    FRAME_METADATA_BASE_VADDR};
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
#[allow(private_interfaces)]
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
            // The allocator draws from `VMALLOC_VADDR_RANGE = [VMALLOC_BASE_VADDR,
            // FRAME_METADATA_BASE_VADDR)`, so `r.end` is bounded by
            // `FRAME_METADATA_BASE_VADDR` — not the much looser
            // `KERNEL_END_VADDR`. This leaves a large safety margin
            // (~64 GB) below `KERNEL_END_VADDR`, so any one-page cursor
            // open at `[end, end + PAGE_SIZE)` stays within the
            // kernel-managed range.
            && r.end <= FRAME_METADATA_BASE_VADDR
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

#[allow(private_interfaces)]
pub tracked struct KVirtAreaOwner {
    pub pt_owner: PageTableOwner<KernelPtConfig>,
}

impl KVirtAreaOwner {
    /// The [`CursorView`] at the page containing the given address, representing the kernel page
    /// table's abstract state for query purposes.
    #[allow(private_interfaces)]
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
        // See `kvirt_alloc_range_bounds`: the real allocator draws from
        // VMALLOC, whose upper bound is FRAME_METADATA_BASE_VADDR. This
        // leaves `end + PAGE_SIZE <= KERNEL_END_VADDR` with plenty of
        // margin, so a one-past-end cursor open stays sound.
        &&& self.range.end <= FRAME_METADATA_BASE_VADDR
        // Page alignment: guaranteed by `kvirt_alloc_range_bounds` at
        // construction, preserved by every operation (no op touches range).
        &&& self.range.start % PAGE_SIZE == 0
        &&& self.range.end % PAGE_SIZE == 0
        &&& self.range.start <= self.range.end
    }
}

impl Inv for KVirtAreaOwner {
    open spec fn inv(self) -> bool {
        self.pt_owner.inv()
    }
}

#[verus_verify]
impl KVirtArea {

    pub fn start(&self) -> Vaddr
        returns self.range.start
    {
        self.range.start
    }

    pub fn end(&self) -> Vaddr
        returns self.range.end
    {
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
            Ghost(root_guard): Ghost<PageTableGuard<'static, KernelPtConfig>>
        requires
            self.inv(),
            old(regions).inv(),
            owner.inv(),
        ensures
            self.query_some_condition(owner, addr) ==> self.query_some_ensures(owner, addr, r),
            !self.query_some_condition(owner, addr) ==> Self::query_none_ensures(r),
            // non-panic conditions
            self.range.start <= addr < self.range.end
    )]
    #[allow(private_interfaces)]
    pub fn query<A: InAtomicMode + 'static>(&self, addr: Vaddr) -> Option<super::MappedItem>
    {
        use align_ext::AlignExt;
        vstd_extra::assert!(self.start() <= addr && self.end() > addr);

        proof {
            vstd_extra::prelude::lemma_pow2_is_pow2_to64();
            broadcast use vstd::arithmetic::power2::is_pow2_equiv, vstd::arithmetic::power2::lemma_pow2;
            let witness: nat = choose |i: nat| vstd::arithmetic::power::pow(2, i) == PAGE_SIZE as int;
            assert(vstd::arithmetic::power2::pow2(witness) == PAGE_SIZE);
        }
        let start = addr.align_down(PAGE_SIZE);
        proof {
            assert(start <= addr);
            assert(addr <= self.range.end);
            // Tightened invariant: end <= FRAME_METADATA_BASE_VADDR, which is
            // ~64 GB below KERNEL_END_VADDR. So start + PAGE_SIZE <= KERNEL_END_VADDR
            // always holds, even when addr == end (start == end in that case).
            assert(self.range.end <= FRAME_METADATA_BASE_VADDR);
            assert(FRAME_METADATA_BASE_VADDR + PAGE_SIZE <= KERNEL_END_VADDR) by (compute_only);
            assert(start >= self.range.start);
            assert(start + PAGE_SIZE <= KERNEL_END_VADDR);
        }
        let vaddr = start..start + PAGE_SIZE;
        proof {
            axiom_kernel_range_valid(vaddr);
            // Discharge cursor's `LOCKED_END_BOUND_spec` precondition: with the
            // +PAGE_SIZE margin built into `KernelPtConfig::LOCKED_END_BOUND_spec`,
            // `start <= addr <= self.range.end <= FRAME_METADATA_BASE_VADDR`
            // gives `start + PAGE_SIZE <= FRAME_METADATA_BASE_VADDR + PAGE_SIZE`.
            assert(vaddr.end as int
                <= <KernelPtConfig as PageTableConfig>::LOCKED_END_BOUND_spec());
        }
        let page_table = {
            proof_decl! { let tracked mut _kpt_owner: Option<&PageTableOwner<KernelPtConfig>> = None; }
            get_kernel_page_table(Tracked(&mut _kpt_owner), Tracked(regions), Tracked(guards))
        };
        let preempt_guard = disable_preempt::<A>();
        let (mut cursor, Tracked(mut cursor_owner)) =
            (#[verus_spec(with Tracked(owner.pt_owner), Ghost(root_guard), Tracked(regions), Tracked(guards))]
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
            Tracked(root_guard): Tracked<PageTableGuard<'a, KernelPtConfig>>,
            Tracked(entry_owners): Tracked<&mut Map<Paddr, EntryOwner<KernelPtConfig>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, KernelPtConfig>>
    )]
    #[allow(private_interfaces)]
    pub fn map_frames<'a, A: InAtomicMode + 'a>(
        area_size: usize,
        map_offset: usize,
        frames: alloc::vec::Vec<DynFrame>,
        prop: PageProperty,
    ) -> Self
        requires
            old(regions).inv(),
            owner.inv(),
            // For each frame, the map contains an appropriate owner keyed by
            // that frame's paddr. Duplicates in `frames` share the same owner.
            forall |i: int| 0 <= i < frames.len() ==> {
                let pa = #[trigger] crate::mm::frame::meta::mapping::meta_to_frame(
                    frames[i].ptr.addr());
                &&& old(entry_owners).contains_key(pa)
                &&& old(entry_owners)[pa].inv()
                &&& frame_entry_wf(frames[i], prop, old(entry_owners)[pa])
            },
            // `Frame ↔ MetaRegionOwners` ownership obligation, hoisted as a precondition
            // (rather than an axiom). Each owned `DynFrame` must have its slot allocated
            // with `rc > 0` in the current regions. The runtime invariant of `Frame<M>`
            // implies this; the caller is responsible for projecting it into spec form.
            forall |i: int| 0 <= i < frames.len() ==>
                CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(
                    MappedItem::Tracked(#[trigger] frames[i], prop), *old(regions)),
    {
        vstd_extra::assert!(area_size % PAGE_SIZE == 0);
        vstd_extra::assert!(map_offset % PAGE_SIZE == 0);

        let range_res = KVIRT_AREA_ALLOCATOR.alloc(area_size);
        vstd_extra::assert!(range_res.is_ok());
        let range = range_res.unwrap();

        proof {
            kvirt_alloc_range_bounds(area_size, map_offset, range);
        }

        let cursor_range = range.start + map_offset..range.end;

        proof {
            // Bridge: FRAME_METADATA_BASE_VADDR < KERNEL_END_VADDR, so the allocator's
            // tightened bound still satisfies axiom_kernel_range_valid's precondition.
            assert(FRAME_METADATA_BASE_VADDR <= KERNEL_END_VADDR) by (compute_only);
            axiom_kernel_range_valid(cursor_range);
            // Discharge cursor_mut's `LOCKED_END_BOUND_spec` precondition: kvirt_alloc
            // bounded `range.end <= FRAME_METADATA_BASE_VADDR == LOCKED_END_BOUND` for
            // KernelPtConfig.
            assert(cursor_range.end as int
                <= <KernelPtConfig as PageTableConfig>::LOCKED_END_BOUND_spec());
        }

        let page_table = {
                proof_decl! {
                    let tracked mut _kpt_owner: Option<&PageTableOwner<KernelPtConfig>> = None;
                }
                get_kernel_page_table(Tracked(&mut _kpt_owner), Tracked(regions), Tracked(guards))
            };
        let preempt_guard = disable_preempt::<A>();

        #[verus_spec(with Tracked(owner.pt_owner), Ghost(root_guard), Tracked(regions), Tracked(guards))]
        let cursor_res = page_table.cursor_mut(preempt_guard, &cursor_range);

        vstd_extra::assert!(cursor_res.is_ok());
        let (mut cursor, Tracked(cursor_owner)) = cursor_res.unwrap();

        for frame in it: frames.into_iter()
            invariant
                cursor.0.invariants(cursor_owner, *regions, *guards),
                // For each remaining frame, the map contains a wf owner at its paddr.
                // Duplicates among remaining frames are fine — one key, one owner.
                forall |i: int| it.pos <= i < it.elements.len() ==> {
                    let pa = #[trigger] crate::mm::frame::meta::mapping::meta_to_frame(
                        it.elements[i].ptr.addr());
                    &&& entry_owners.contains_key(pa)
                    &&& entry_owners[pa].inv()
                    &&& frame_entry_wf(it.elements[i], prop, entry_owners[pa])
                },
                // Slot facts for each remaining frame are preserved across iterations.
                // (Initially established by the function precondition; preserved by
                // `cursor.map`'s effect on unrelated slots — see the focused assume in
                // the loop body.)
                forall |i: int| it.pos <= i < it.elements.len() ==>
                    CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(
                        MappedItem::Tracked(#[trigger] it.elements[i], prop), *regions),
        {
            // Capacity fit check: if the cursor has advanced past its barrier
            // (i.e., too many frames for the allocated area), panic. This
            // lets Verus derive `in_locked_range` for the cursor.map call below.
            vstd_extra::assert!(cursor.0.va < cursor.0.barrier_va.end);

            let ghost cur_mapped_pa: usize =
                crate::mm::frame::meta::mapping::meta_to_frame(frame.ptr.addr());
            proof {
                assert(entry_owners.contains_key(cur_mapped_pa));
                assert(frame_entry_wf(frame, prop, entry_owners[cur_mapped_pa]));
            }

            let ghost cur_pa_from_wf: usize = KernelPtConfig::item_into_raw_spec(
                MappedItem::Tracked(frame_as_dynframe(it.elements.index(it.pos as int)), prop)).0;
            let ghost pre_remove_owners: Map<Paddr, EntryOwner<KernelPtConfig>> = *entry_owners;
            // Save path/parent_level so we can rebuild a fresh owner after `cursor.map`
            // consumes this one, and reinsert into the map for potential reuse by
            // later iterations at the same paddr.
            let ghost cur_path = entry_owners[cur_mapped_pa].path;
            let ghost cur_parent_level = entry_owners[cur_mapped_pa].parent_level;
            // Capture the original-owner facts now (Verus can lose them across the
            // cursor.map call, which churns enormous proof context).
            let ghost orig_mapped_pa = pre_remove_owners[cur_mapped_pa].frame.unwrap().mapped_pa;
            let ghost orig_size = pre_remove_owners[cur_mapped_pa].frame.unwrap().size;
            let ghost orig_prop = pre_remove_owners[cur_mapped_pa].frame.unwrap().prop;
            proof {
                KernelPtConfig::item_into_raw_spec_tracked_level(MappedItem::Tracked(frame, prop));
                KernelPtConfig::item_into_raw_spec_tracked_pa(
                    DynFrame { ptr: frame.ptr, _marker: PhantomData }, prop);
                KernelPtConfig::item_into_raw_spec_tracked_prop(
                    DynFrame { ptr: frame.ptr, _marker: PhantomData }, prop);
                assert(orig_mapped_pa == cur_mapped_pa);
                assert(orig_prop == prop);
                assert(cur_parent_level == 1);
                assert(orig_size == page_size(cur_parent_level));
                assert(pre_remove_owners[cur_mapped_pa].inv_base());
            }

            let tracked mut entry_owner = entry_owners.tracked_remove(cur_mapped_pa);

            // Now Verus knows: dynframe == frame_as_dynframe(it.elements[it.pos])
            let item = MappedItem::Tracked(frame, prop);
            // For a tracked frame, item_into_raw gives level 1 (4KB page), and
            // frame_entry_wf requires `entry_owner.parent_level == level`, so:
            proof {
                KernelPtConfig::item_into_raw_spec_tracked_level(item);
                assert(cur_parent_level == 1);
            }
            assert(cursor.0.invariants(cursor_owner, *regions, *guards));

            let ghost regions_before_map = *regions;
            let ghost old_cursor_model: CursorView<KernelPtConfig> = cursor.0.model(cursor_owner);
            let ghost old_cursor_owner_va = cursor_owner.va;
            proof {
                cursor_owner.view_preserves_inv(); // old_cursor_model.inv()
                cursor_owner.va.reflect_prop(cursor.0.va);
                let (pa, level, prop_from_item) = KernelPtConfig::item_into_raw_spec(item);
                KernelPtConfig::item_into_raw_spec_level_bounds(item);
                KernelPtConfig::item_into_raw_spec_tracked_level(item);
                lemma_va_align_page_size_level_1(cursor.0.va);
                cursor_owner.locked_range_page_aligned();
                let ghost diff: int = cursor.0.barrier_va.end as int - cursor.0.va as int;
                vstd::arithmetic::mul::lemma_mul_by_zero_is_zero(
                    nr_subpage_per_huge::<PagingConsts>().ilog2() as int,
                );
                vstd::arithmetic::power::lemma_pow0(2int);

                KernelPtConfig::item_into_raw_spec_tracked_level(item);
            }

            // SAFETY: The constructor of the `KVirtArea` has already ensured
            // that this mapping does not affect kernel's memory safety.
            // `item_slot_in_regions` for the current item is delivered by the
            // loop invariant (instantiated at i = it.pos), itself established by
            // the function precondition.
            assert(CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(item, *regions));
            #[verus_spec(with Tracked(&mut cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))]
            let res = cursor.map(item);

            // `item_slot_in_regions` preservation for the remaining frames
            // follows from cursor.map's strengthened ensures: ref_count is
            // preserved at non-mapped non-UNUSED indices, and at the mapped
            // index ref_count > 0 is preserved (covers duplicates). slots
            // keys are monotonic across map.
            proof {
                let cur_pa = KernelPtConfig::item_into_raw_spec(item).0;
                let cur_pa_idx = frame_to_index_spec(cur_pa);
                assert forall |i: int| (it.pos as int + 1) <= i < it.elements.len() implies
                    CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(
                        MappedItem::Tracked(#[trigger] it.elements[i], prop), *regions)
                by {
                    let item_i = MappedItem::Tracked(it.elements[i], prop);
                    let pa_i = KernelPtConfig::item_into_raw_spec(item_i).0;
                    let idx_i = frame_to_index_spec(pa_i);
                    KernelPtConfig::item_into_raw_spec_tracked_level(item_i);
                    // Loop invariant gives item_slot_in_regions for item_i
                    // against `regions_before_map`. cursor.map preserves
                    // slots-monotonicity and the relevant ref_count fact at
                    // either branch (idx_i != cur_pa_idx via direct equality,
                    // idx_i == cur_pa_idx via mapped-idx > 0 preservation).
                    assert(CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(
                        item_i, regions_before_map));
                    if idx_i != cur_pa_idx {
                        assert(regions.slot_owners[idx_i].inner_perms.ref_count.value()
                            == regions_before_map.slot_owners[idx_i].inner_perms.ref_count.value());
                    }
                };
            }

            proof {
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

                // va is PAGE_SIZE-aligned (loop invariant via cursor.0.invariants),
                // so nat_align_down returns va unchanged.
                vstd_extra::arithmetic::lemma_nat_align_down_sound(
                    old_cursor_owner_va.to_vaddr() as nat, PAGE_SIZE as nat);
                assert(vstd_extra::arithmetic::nat_align_down(
                    old_cursor_owner_va.to_vaddr() as nat, PAGE_SIZE as nat)
                    == old_cursor_owner_va.to_vaddr() as nat);

                cursor_owner.va.reflect_prop(cursor.0.va);

                // Reinsert a fresh owner for this paddr so later iterations on the
                // same frame reuse it. `new_frame` fabricates an `EntryOwner` with
                // the correct `new_frame_spec` shape for the paddr/level/prop;
                // `frame_entry_wf` holds for any future frame at the same paddr.
                // Note: `new_frame` returns with `in_scope = true`; clear it for
                // `inv()` to hold (which requires `!in_scope`).
                let tracked mut fresh = EntryOwner::<KernelPtConfig>::new_frame(
                    cur_mapped_pa, cur_path, cur_parent_level, prop, /* is_tracked */ true);
                fresh.in_scope = false;
                entry_owners.tracked_insert(cur_mapped_pa, fresh);
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
            Tracked(root_guard): Tracked<PageTableGuard<'a, KernelPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'a, KernelPtConfig>>
    )]
    #[allow(private_interfaces)]
    pub unsafe fn map_untracked_frames<A: InAtomicMode + 'a, 'a>(
        area_size: usize,
        map_offset: usize,
        pa_range: Range<Paddr>,
        prop: PageProperty,
    ) -> (res: Self)
        requires
            old(regions).inv(),
            owner.inv(),
            map_offset + vstd_extra::external::range::range_usize_len(&pa_range) <= usize::MAX,
        ensures
            final(regions).inv(),
            res.inv(),
    {
        vstd_extra::assert!(pa_range.start % PAGE_SIZE == 0);
        vstd_extra::assert!(pa_range.end % PAGE_SIZE == 0);
        vstd_extra::assert!(area_size % PAGE_SIZE == 0);
        vstd_extra::assert!(map_offset % PAGE_SIZE == 0);

        vstd_extra::assert!(map_offset + vstd_extra::external::range::range_usize_len(&pa_range) <= area_size);

        let range_res = KVIRT_AREA_ALLOCATOR.alloc(area_size);
        // Rust's `unwrap()` panics if not ok. TODO: make our own wrapper.
        vstd_extra::assert!(range_res.is_ok());
        let range = range_res.unwrap();

        proof {
            kvirt_alloc_range_bounds(area_size, map_offset, range);
        }

        if pa_range.start < pa_range.end {
            let len = pa_range.end - pa_range.start;
            let va_range = range.start + map_offset..range.start + map_offset + len;

            proof {
                assert(FRAME_METADATA_BASE_VADDR <= KERNEL_END_VADDR) by (compute_only);
                axiom_kernel_range_valid(va_range);
                assert(va_range.end as int
                    <= <KernelPtConfig as PageTableConfig>::LOCKED_END_BOUND_spec());
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

            #[verus_spec(with Tracked(owner.pt_owner), Ghost(root_guard), Tracked(regions), Tracked(guards))]
            let cursor_res = page_table.cursor_mut(preempt_guard, &va_range);

            vstd_extra::assert!(cursor_res.is_ok());

            let (mut cursor, Tracked(cursor_owner)) = cursor_res.unwrap();

            let pages = collect_largest_pages(va_range.start, pa_range.start, len);

            for (pa, level) in it: pages.into_iter()
                invariant
                    cursor.0.invariants(cursor_owner, *regions, *guards),
                    // Level bounds / alignment from `collect_largest_pages` postconditions.
                    forall |i: int| 0 <= i < it.elements.len() ==>
                        (#[trigger] it.elements[i]).0 % PAGE_SIZE == 0,
                    forall |i: int| 0 <= i < it.elements.len() ==>
                        1 <= (#[trigger] it.elements[i]).1 <= NR_LEVELS,
                    forall |i: int| 0 <= i < it.elements.len() ==>
                        (#[trigger] it.elements[i]).1 <= KernelPtConfig::HIGHEST_TRANSLATION_LEVEL(),
                    forall |i: int| 0 <= i < it.elements.len() ==>
                        (va_range.start as nat + #[trigger] sum_page_sizes_spec(it.elements, 0, i))
                            % page_size(it.elements[i].1) as nat == 0,
                    forall |i: int| #![auto] 0 <= i < it.elements.len() ==>
                        it.elements[i].0 as nat
                            == pa_range.start as nat + sum_page_sizes_spec(it.elements, 0, i),
                    sum_page_sizes_spec(it.elements, 0, it.elements.len() as int) == len as nat,
                    // VA tracking: cursor has advanced past sum of processed pages.
                    cursor.0.va as nat
                        == va_range.start as nat
                            + sum_page_sizes_spec(it.elements, 0, it.pos as int),
                    cursor.0.barrier_va.end == va_range.start + len,
                    // `pa_range.end == pa_range.start + len` so pa + page_size(level) stays bounded.
                    pa_range.end as nat == pa_range.start as nat + len as nat,
                    cursor.0.guard_level == NR_LEVELS as u8,
                    pa_range.end <= MAX_PADDR,
                    // Slot facts for the remaining PAs are preserved across iterations.
                    // Initially established by the function precondition; each iteration's
                    // `cursor.map` only touches the slot at its own mapped PA — see the
                    // focused assume in the loop body.
                    forall |pa: Paddr| #![trigger crate::mm::frame::meta::mapping::frame_to_index(pa)]
                        pa_range.start <= pa < pa_range.end && pa % PAGE_SIZE == 0 ==> {
                            let idx = crate::mm::frame::meta::mapping::frame_to_index(pa);
                            &&& regions.slots.contains_key(idx)
                            &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                                != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                        },
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
                    cursor.0.model(cursor_owner);
                let ghost old_cursor_owner_va = cursor_owner.va;
                let ghost old_va: nat = cursor.0.va as nat;

                proof {
                    cursor_owner.view_preserves_inv(); // old_cursor_model.inv()
                    cursor_owner.va.reflect_prop(cursor.0.va);

                    KernelPtConfig::item_into_raw_spec_untracked(pa, level, prop);

                    // pa_range.end == pa_range.start + len (in nat) — from loop invariant.
                    sum_page_sizes_extend_right(it.elements, 0, pos@);
                    sum_page_sizes_mono(
                        it.elements, 0, pos@ + 1, it.elements.len() as int);
                }

                // Pre-map: capture the overflow bound `cursor_owner.va + page_size(level) <= usize::MAX`.
                // Valid because the cursor is `in_locked_range` here (required by `cursor.map`).
                proof {
                    KernelPtConfig::item_into_raw_spec_untracked(pa, level, prop);
                    cursor_owner.va_plus_page_size_no_overflow(level);
                }

                // Save ghost copy of regions before map for post-map invariant maintenance.
                let ghost pre_map_regions: MetaRegionOwners = *regions;

                proof {
                    KernelPtConfig::axiom_kernel_htl_lt_nr_levels();
                    assert(!cursor.map_panic_conditions(item));
                    assert(cursor.item_wf(item, entry_owner));
                }
                
                // SAFETY: The caller of `map_untracked_frames` has ensured the safety of this mapping.
                // `item_slot_in_regions` for the current `(pa, level)` follows from the
                // loop invariant's per-PA slot facts, instantiated at the current `pa`.
                proof {
                    KernelPtConfig::item_into_raw_spec_untracked(pa, level, prop);
                    let idx = crate::mm::frame::meta::mapping::frame_to_index(pa);
                    assert(pa % PAGE_SIZE == 0);
                    assert(pa_range.start <= pa < pa_range.end);
                    assert(regions.slots.contains_key(idx));
                    assert(regions.slot_owners[idx].inner_perms.ref_count.value()
                        != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED);
                    assert(CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(item, *regions));
                }
                #[verus_spec(with Tracked(&mut cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))]
                let _ = cursor.map(item);

                proof {
                    cursor_owner.va.reflect_prop(cursor.0.va);
                }

                proof {
                    KernelPtConfig::item_into_raw_spec_untracked(pa, level, prop);
                    let level_raw = KernelPtConfig::item_into_raw_spec(item).1;
                    
                    crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(level_raw);
                    KernelPtConfig::item_into_raw_spec_level_bounds(item);
                    let split_self = old_cursor_model.split_while_huge(
                        page_size(level_raw));

                    CursorView::<KernelPtConfig>::lemma_split_while_huge_preserves_cur_va(
                        old_cursor_model, page_size(level_raw));

                    lemma_page_size_ge_page_size(level_raw);

                    vstd_extra::arithmetic::lemma_nat_align_down_sound(
                        old_cursor_owner_va.to_vaddr() as nat,
                        page_size(level_raw) as nat,
                    );
                    vstd_extra::arithmetic::lemma_nat_align_down_sound(
                        old_cursor_owner_va.to_vaddr() as nat,
                        page_size(level_raw) as nat,
                    );
                    assert(
                        vstd_extra::arithmetic::nat_align_down(
                            old_cursor_owner_va.to_vaddr() as nat,
                            page_size(level_raw) as nat)
                        + page_size(level_raw) as nat <= usize::MAX as nat
                    );
                    old_cursor_owner_va.align_up_advances_general(level_raw as int);
                    
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
