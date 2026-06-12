// SPDX-License-Identifier: MPL-2.0
//! Kernel virtual memory allocation
use vstd::prelude::*;

use vstd_extra::arithmetic::nat_align_down;
use vstd_extra::assert;
use vstd_extra::ownership::{InvView, ModelOf, OwnerOf};
use vstd_extra::panic::may_panic;
use vstd_extra::prelude::Inv;

use core::marker::PhantomData;
use core::ops::Range;

use super::{
    FRAME_METADATA_BASE_VADDR, KERNEL_BASE_VADDR, KERNEL_END_VADDR, KERNEL_PAGE_TABLE,
    VMALLOC_VADDR_RANGE,
};
use crate::mm::{
    PAGE_SIZE, Paddr, Vaddr,
    frame::{Frame, Segment, untyped::AnyUFrameMeta},
    kspace::{KernelPtConfig, MappedItem},
    largest_pages,
    page_prop::PageProperty,
    page_table::{Child, CursorMut, PageTable, PageTableConfig, is_valid_range_spec, page_size},
};

use crate::arch::mm::PagingConsts;
use crate::mm::PagingConstsTrait;
use crate::mm::frame::DynFrame;
use crate::mm::kspace::AnyFrameMeta;
use crate::mm::nr_subpage_per_huge;
use crate::mm::page_table::PageTableGuard;
use crate::specs::arch::mm::{MAX_PADDR, NR_LEVELS, PAGE_SIZE as SPEC_PAGE_SIZE};
use crate::specs::mm::frame::mapping::frame_to_index;
use crate::specs::mm::frame::meta_owners::{
    MetaSlotStorage, PageUsage, REF_COUNT_MAX, is_mmio_paddr,
};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::{CursorOwner, CursorView};
use crate::specs::mm::page_table::*;
use crate::specs::task::InAtomicMode;
use vstd_extra::cast_ptr::Repr;

//static KVIRT_AREA_ALLOCATOR: RangeAllocator = RangeAllocator::new(VMALLOC_VADDR_RANGE);

verus! {

/// Spec representation of Frame<T> as DynFrame (used when the actual conversion is opaque).
pub open spec fn frame_as_dynframe<T: AnyFrameMeta + Repr<MetaSlotStorage>>(
    frame: Frame<T>,
) -> DynFrame {
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
pub open spec fn frame_entry_wf<T: AnyFrameMeta + Repr<MetaSlotStorage>>(
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

/// Phase A: caller-precludable model of allocator OOM. An uninterpreted
/// spec predicate over the request size: `kvirt_alloc_spec(size) is Err
/// <==> kvirt_alloc_oom_condition(size)`. The real allocator's state is
/// not modeled in detail; the caller-side contract is "if you can prove
/// no OOM, the alloc succeeds." Used to bridge `assert!(range_res.is_ok())`
/// into a precise `map_frames_panic_condition` / `map_untracked_frames_panic_condition`
/// disjunct.
pub uninterp spec fn kvirt_alloc_oom_condition(size: usize) -> bool;

impl RangeAllocator {
    #[verifier::external_body]
    pub const fn new(_r: core::ops::Range<Vaddr>) -> Self {
        Self
    }

    #[verifier::external_body]
    pub fn alloc(&self, size: usize) -> (r: Result<core::ops::Range<Vaddr>, RangeAllocError>)
        ensures
            r == kvirt_alloc_spec(size),
            r is Err <==> kvirt_alloc_oom_condition(size),
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
    decreases (to - from),
    when from <= to
{
    if from >= to {
        0nat
    } else {
        page_size(elems[from].1) as nat + sum_page_sizes_spec(elems, from + 1, to)
    }
}

/// `sum(from, to+1) == sum(from, to) + page_size(elems[to])`.
proof fn sum_page_sizes_extend_right(elems: Seq<(Paddr, u8)>, from: int, to: int)
    requires
        0 <= from <= to,
        to < elems.len() as int,
    ensures
        sum_page_sizes_spec(elems, from, to + 1) == sum_page_sizes_spec(elems, from, to)
            + page_size(elems[to].1) as nat,
    decreases to - from,
{
    if from < to {
        sum_page_sizes_extend_right(elems, from + 1, to);
        // Help Verus: unfold sum_page_sizes_spec(elems, from, to) and (from, to+1)
        assert(sum_page_sizes_spec(elems, from, to) == page_size(elems[from].1) as nat
            + sum_page_sizes_spec(elems, from + 1, to));
        assert(sum_page_sizes_spec(elems, from, to + 1) == page_size(elems[from].1) as nat
            + sum_page_sizes_spec(elems, from + 1, to + 1));
    } else {
        // from == to; explicitly unfold both sides
        assert(sum_page_sizes_spec(elems, from, to) == 0nat);
        assert(sum_page_sizes_spec(elems, from, to + 1) == page_size(elems[from].1) as nat
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
fn collect_largest_pages(va: Vaddr, pa: Paddr, len: usize) -> (res: alloc::vec::Vec<(Paddr, u8)>)
    ensures
        forall|i: int| 0 <= i < res@.len() ==> (#[trigger] res@[i]).0 % PAGE_SIZE == 0,
        forall|i: int| 0 <= i < res@.len() ==> 1 <= (#[trigger] res@[i]).1 <= NR_LEVELS,
        forall|i: int|
            0 <= i < res@.len() ==> (#[trigger] res@[i]).1
                <= KernelPtConfig::HIGHEST_TRANSLATION_LEVEL(),
        sum_page_sizes_spec(res@, 0, res@.len() as int) == len as nat,
        forall|i: int|
            0 <= i < res@.len() ==> (va as nat + #[trigger] sum_page_sizes_spec(res@, 0, i))
                % page_size(res@[i].1) as nat == 0,
        // PA tracking: each element's physical address equals pa + sum of preceding page sizes.
        forall|i: int|
            0 <= i < res@.len() ==> (#[trigger] res@[i]).0 as nat == pa as nat
                + sum_page_sizes_spec(res@, 0, i),
{
    largest_pages::<KernelPtConfig>(va, pa, len).collect()
}

#[verifier::external_body]
pub(crate) fn get_kernel_page_table<'rcu>(
    Tracked(kernel_owner): Tracked<&mut Option<&PageTableOwner<KernelPtConfig>>>,
    Tracked(regions): Tracked<&MetaRegionOwners>,
    Tracked(guards): Tracked<&Guards<'rcu>>,
) -> (r: &'static PageTable<KernelPtConfig>)
    requires
        regions.inv(),
    ensures
        final(kernel_owner)@ is Some,
        final(kernel_owner)@.unwrap().inv(),
        final(kernel_owner)@.unwrap().0.value.is_node(),
        r.root.ptr.addr() == final(kernel_owner)@.unwrap().0.value.node().meta_addr_self(),
        !PageTable::<KernelPtConfig>::create_user_pt_panic_condition(
            final(kernel_owner)@.unwrap().0.value.node(),
        ),
        final(kernel_owner)@.unwrap().0.value.metaregion_sound(*regions),
        final(kernel_owner)@.unwrap().metaregion_sound(*regions),
        guards.unlocked(final(kernel_owner)@.unwrap().0.value.node().meta_addr_self()),
{
    KERNEL_PAGE_TABLE.get().unwrap()
}

// Axiomatized spec for alloc - cannot read exec static in proof mode.
pub uninterp spec fn kvirt_alloc_spec(size: usize) -> Result<
    core::ops::Range<Vaddr>,
    RangeAllocError,
>;

pub axiom fn kvirt_alloc_range_bounds(
    area_size: usize,
    map_offset: usize,
    r: core::ops::Range<Vaddr>,
)
    ensures
        kvirt_alloc_spec(area_size) == Ok::<core::ops::Range<Vaddr>, RangeAllocError>(r) ==> r.start
            <= r.end
        // **Phase C: tightened to equality.** Page-aligned `area_size`
        // requests get back exactly `area_size` bytes — the kvirt
        // allocator does not over-allocate. This pins
        // `cursor.barrier_va.end - cursor.barrier_va.start = area_size`
        // so the per-iteration capacity check
        // `cursor.0.va < cursor.0.barrier_va.end` in `map_frames` is
        // soundly bridged to a caller-side
        // `map_offset + frames·PAGE_SIZE <= area_size` precondition.
         && (r.end - r.start) == area_size && map_offset <= r.end - r.start && r.start + map_offset
            <= usize::MAX && r.start % PAGE_SIZE == 0 && r.end % PAGE_SIZE == 0 && KERNEL_BASE_VADDR
            <= r.start
        // The allocator draws from `VMALLOC_VADDR_RANGE = [VMALLOC_BASE_VADDR,
        // FRAME_METADATA_BASE_VADDR)`, so `r.end` is bounded by
        // `FRAME_METADATA_BASE_VADDR` — not the much looser
        // `KERNEL_END_VADDR`. This leaves a large safety margin
        // (~64 GB) below `KERNEL_END_VADDR`, so any one-page cursor
        // open at `[end, end + PAGE_SIZE)` stays within the
        // kernel-managed range.
         && r.end <= FRAME_METADATA_BASE_VADDR,
;

/// Kernel ranges within [KERNEL_BASE_VADDR, KERNEL_END_VADDR] with alignment are valid for
/// KernelPtConfig (which uses sign-extended high-half addresses).
pub axiom fn axiom_kernel_range_valid(r: core::ops::Range<Vaddr>)
    ensures
        (KERNEL_BASE_VADDR <= r.start && r.end <= KERNEL_END_VADDR && r.start < r.end && r.start
            % PAGE_SIZE == 0 && r.end % PAGE_SIZE == 0) ==> is_valid_range_spec::<KernelPtConfig>(
            &r,
        ),
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
        &&& KERNEL_BASE_VADDR
            <= self.range.start
        // See `kvirt_alloc_range_bounds`: the real allocator draws from
        // VMALLOC, whose upper bound is FRAME_METADATA_BASE_VADDR. This
        // leaves `end + PAGE_SIZE <= KERNEL_END_VADDR` with plenty of
        // margin, so a one-past-end cursor open stays sound.
        &&& self.range.end
            <= FRAME_METADATA_BASE_VADDR
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
    /// Precise panic condition for [`Self::query`]. `query` diverges iff:
    ///  - `addr` is outside the area's range (the diverging `assert!` at
    ///    the top), or
    ///  - the kernel-page-table leaf at `addr.align_down(PAGE_SIZE)` is a
    ///    **tracked** frame (non-MMIO) and *that specific slot* is at
    ///    `REF_COUNT_MAX`, so the inner `Cursor::query`'s clone would
    ///    overflow. The leaf is resolved via `owner.cursor_view_at(addr)`,
    ///    which exactly matches the inner cursor's `query_panic_condition`
    ///    slot — bridged through `lock_range`'s new Frame-slot
    ///    preservation ensures (`slot.usage matches PageUsage::Frame ==>
    ///    refcount preserved exactly`).
    pub open spec fn query_panic_condition(
        self,
        owner: KVirtAreaOwner,
        addr: Vaddr,
        regions: MetaRegionOwners,
    ) -> bool {
        let v = owner.cursor_view_at(addr);
        let pa = v.query_mapping().pa_range.start;
        let idx = frame_to_index(pa);
        ||| !(self.range.start <= addr < self.range.end)
        ||| (v.present() && !is_mmio_paddr(pa)
            && regions.slot_owners[idx].inner_perms.ref_count.value() >= REF_COUNT_MAX)
    }

    pub fn start(&self) -> Vaddr
        returns
            self.range.start,
    {
        self.range.start
    }

    pub fn end(&self) -> Vaddr
        returns
            self.range.end,
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
            Tracked(guards): Tracked<&mut Guards<'rcu>>,
            Ghost(root_guard): Ghost<PageTableGuard<'rcu, KernelPtConfig>>
        requires
            self.inv(),
            old(regions).inv(),
            owner.inv(),
            // Precise: out-of-range diverges at the top `assert!`, and the
            // inner `Cursor::query` clones the resolved leaf frame — that
            // clone aborts only when *that specific slot* is saturated.
            // `query_panic_condition` captures both classes precisely.
            self.query_panic_condition(owner, addr, *old(regions)) ==> may_panic(),
        ensures
            self.query_some_condition(owner, addr) ==> self.query_some_ensures(owner, addr, r),
            !self.query_some_condition(owner, addr) ==> Self::query_none_ensures(r),
            !self.query_panic_condition(owner, addr, *old(regions)),
            // non-panic conditions
            self.range.start <= addr < self.range.end
    )]
    #[allow(private_interfaces)]
    pub fn query<'rcu, A: InAtomicMode + 'static>(&self, addr: Vaddr) -> Option<super::MappedItem> {
        use align_ext::AlignExt;
        assert!(self.start() <= addr && self.end() > addr);

        proof {
            vstd_extra::prelude::lemma_pow2_is_pow2_to64();
            broadcast use
                vstd::arithmetic::power2::is_pow2_equiv,
                vstd::arithmetic::power2::lemma_pow2,
            ;

            let witness: nat = choose|i: nat|
                vstd::arithmetic::power::pow(2, i) == PAGE_SIZE as int;
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
        let preempt_guard: &'rcu A = disable_preempt::<A>();
        let (mut cursor, Tracked(mut cursor_owner)) = (
        #[verus_spec(with Tracked(owner.pt_owner), Ghost(root_guard), Tracked(regions), Tracked(guards))]
        page_table.cursor(preempt_guard, &vaddr)).unwrap();
        proof {
            // Bridge `cursor_owner@.mappings` to `owner.cursor_view_at(addr).mappings`.
            // PageTable::cursor ensures `cursor_owner.as_page_table_owner() == owner.pt_owner`
            // and `cursor_owner.continuations[3].path() == owner.pt_owner.0.value.path`, and
            // `as_page_table_owner_preserves_view_mappings` turns the cursor's view into a
            // `view_rec` call on the owner at the root path.
            cursor_owner.as_page_table_owner_preserves_view_mappings();
            assert(cursor_owner.view_mappings() == owner.pt_owner.view_rec(
                owner.pt_owner.0.value.path,
            ));
            // cur_va agreement: `cursor.wf(cursor_owner)` gives `cursor_owner.va.reflect(cursor.va)`,
            // which `reflect_prop` converts into `cursor_owner.va.to_vaddr() == cursor.va`.
            cursor_owner.va.reflect_prop(cursor.va);
            assert(cursor_owner.cur_va() == start);
        }
        let ghost pre_query_view = cursor_owner@;
        let ghost pre_query_cursor_va = cursor.va;
        let ghost pre_query_regions = *regions;
        let ghost pre_query_cursor_barrier = cursor.barrier_va;
        let ghost pre_query_cursor_va_run = cursor.va;
        proof {
            // Discharge `Cursor::query`'s saturation precondition. Bridges:
            //  (a) `cursor_owner@ == owner.cursor_view_at(addr)` (mappings + cur_va).
            //  (b) `Cursor::new`'s saturated-slot bridge: a slot at `>= REF_COUNT_MAX`
            //      post-`Cursor::new` had the same value pre-`Cursor::new`. So if
            //      cursor would saturate at idx, the kvirt-entry snapshot was also
            //      saturated there ⟹ kvirt's P fires ⟹ `may_panic()`.
            let pa = cursor_owner@.query_mapping().pa_range.start;
            let idx = frame_to_index(pa);
            if cursor_owner@.present() && !is_mmio_paddr(pa) && (
            *regions).slot_owners[idx].inner_perms.ref_count.value() >= REF_COUNT_MAX {
                // Trigger Cursor::new's forward saturated-slot bridge.
                assert((*old(regions)).slot_owners[idx].inner_perms.ref_count.value() == (
                *regions).slot_owners[idx].inner_perms.ref_count.value());
                assert(cursor_owner@.mappings == owner.cursor_view_at(addr).mappings);
                assert(cursor_owner@.cur_va == owner.cursor_view_at(addr).cur_va);
                assert(cursor_owner@ == owner.cursor_view_at(addr));
                assert(self.query_panic_condition(owner, addr, *old(regions)));
                assert(may_panic());
            }
        }
        let state = (
        #[verus_spec(with Tracked(&mut cursor_owner), Tracked(regions), Tracked(guards))]
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
            // Discharge `ensures !self.query_panic_condition(...)`:
            //  - Bound conjunct: top `assert!(self.start() <= addr && self.end() > addr)`
            //    held on this return path.
            //  - Saturation conjunct: contradiction case — if old(regions)[idx] >= MAX,
            //    `Cursor::new`'s reverse saturated-slot bridge gives
            //    pre_query_regions[idx].value >= MAX. But `cursor.query` returned, so
            //    its `ensures !query_panic_condition` (with present && !is_mmio &&
            //    in-range) gives pre_query_regions[idx].value < MAX. Contradiction.
            let pa = owner.cursor_view_at(addr).query_mapping().pa_range.start;
            let idx = frame_to_index(pa);
            assert(self.range.start <= addr < self.range.end);
            assert(pre_query_view == owner.cursor_view_at(addr));
            if owner.cursor_view_at(addr).present() && !is_mmio_paddr(pa) && (*old(
                regions,
            )).slot_owners[idx].inner_perms.ref_count.value() >= REF_COUNT_MAX {
                // Reverse saturated-slot bridge (Cursor::new).
                assert(pre_query_regions.slot_owners[idx].inner_perms.ref_count.value() == (*old(
                    regions,
                )).slot_owners[idx].inner_perms.ref_count.value());
                // cursor.query's `ensures !P_cursor`: with in-range (always) +
                // pre_query_view.present() (== owner.cursor_view_at(addr).present()
                // via ==) + !is_mmio_paddr(pa') where pa' = pre_query_view's
                // query_mapping().pa_range.start (== pa via ==), the saturation
                // conjunct must be false: pre_query_regions[idx].value < MAX.
                assert(false);
            }
            assert(!self.query_panic_condition(owner, addr, *old(regions)));
        }
        state.1
    }

    /// Caller-precludable *bounds* panic condition for [`Self::map_frames`]:
    /// alignment + capacity. These are the documented `# Panics` bullets
    /// that callers can always satisfy (and are required to). The
    /// allocator-OOM disjunct is split out into
    /// [`Self::map_frames_panic_condition`] (the full predicate) since OOM
    /// is uninterpreted and typically not precludable by callers.
    pub open spec fn map_frames_bounds_panic_condition(
        area_size: usize,
        map_offset: usize,
        n_frames: usize,
    ) -> bool {
        ||| area_size % PAGE_SIZE != 0
        ||| map_offset % PAGE_SIZE != 0
        ||| map_offset >= area_size
        ||| map_offset as int + n_frames as int * PAGE_SIZE as int > area_size as int
    }

    /// Full panic condition for [`Self::map_frames`] = bounds OR OOM.
    /// Used in `ensures` to give callers a single negation guarantee on
    /// the success path.
    pub open spec fn map_frames_panic_condition(
        area_size: usize,
        map_offset: usize,
        n_frames: usize,
    ) -> bool {
        ||| Self::map_frames_bounds_panic_condition(area_size, map_offset, n_frames)
        ||| kvirt_alloc_oom_condition(area_size)
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
            Tracked(guards): Tracked<&mut Guards<'a>>
    )]
    #[allow(private_interfaces)]
    pub fn map_frames<'a, A: InAtomicMode + 'a>(
        area_size: usize,
        map_offset: usize,
        frames: alloc::vec::Vec<DynFrame>,
        prop: PageProperty,
    ) -> (res: Self)
        requires
            Self::map_frames_bounds_panic_condition(area_size, map_offset, frames.len())
                ==> may_panic(),
            kvirt_alloc_oom_condition(area_size) ==> may_panic(),
            old(regions).inv(),
            owner.inv(),
            // For each frame, the map contains an appropriate owner keyed by
            // that frame's paddr. Duplicates in `frames` share the same owner.
            forall|i: int|
                0 <= i < frames.len() ==> {
                    let pa = #[trigger] crate::mm::frame::meta::mapping::meta_to_frame(
                        frames[i].ptr.addr(),
                    );
                    &&& old(entry_owners).contains_key(pa)
                    &&& old(entry_owners)[pa].inv()
                    &&& frame_entry_wf(frames[i], prop, old(entry_owners)[pa])
                },
            // `Frame ↔ MetaRegionOwners` ownership obligation, hoisted as a precondition
            // (rather than an axiom). Each owned `DynFrame` must have its slot allocated
            // with `rc > 0` in the current regions. The runtime invariant of `Frame<M>`
            // implies this; the caller is responsible for projecting it into spec form.
            forall|i: int|
                0 <= i < frames.len() ==> CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(
                    MappedItem::Tracked(#[trigger] frames[i], prop),
                    *old(regions),
                ),
        ensures
            !Self::map_frames_panic_condition(area_size, map_offset, frames.len()),
    {
        assert!(area_size % PAGE_SIZE == 0);
        assert!(map_offset % PAGE_SIZE == 0);

        let range_res = KVIRT_AREA_ALLOCATOR.alloc(area_size);
        assert!(range_res.is_ok());
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
            assert(cursor_range.start % <KernelPtConfig as PagingConstsTrait>::BASE_PAGE_SIZE_spec()
                == 0);
            assert(cursor_range.end % <KernelPtConfig as PagingConstsTrait>::BASE_PAGE_SIZE_spec()
                == 0);
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

        proof {
            // Discharge `assert!(cursor_res.is_ok())` via the may_panic chain:
            // if `cursor_res` is `Err`, `cursor_mut`'s contrapositive ensures
            // `!cursor_new_success_conditions(cursor_range)`. Alignment +
            // range validity hold (top asserts + axiom_kernel_range_valid),
            // so the failure must be `cursor_range.start >= cursor_range.end`
            // ⟺ `map_offset >= range.end - range.start == area_size`
            // ⟺ `map_offset >= area_size` ⟹ `bounds_panic_condition`
            // ⟹ `may_panic()` via the requires implication.
            if !cursor_res.is_ok() {
                assert(!crate::mm::page_table::Cursor::<
                    KernelPtConfig,
                    A,
                >::cursor_new_success_conditions(&cursor_range));
                assert(map_offset >= area_size);
                assert(Self::map_frames_bounds_panic_condition(
                    area_size,
                    map_offset,
                    frames.len(),
                ));
                assert(may_panic());
            }
        }
        assert!(cursor_res.is_ok());
        let (mut cursor, Tracked(cursor_owner)) = cursor_res.unwrap();

        for frame in it: frames.into_iter()
            invariant
                cursor.0.invariants(cursor_owner, *regions, *guards),
                // Carry the requires implication into the loop body so
                // that may_panic is derivable per-iteration when a guard
                // implies the bounds-panic condition (mirrors jump's
                // per-iteration `jump_panic_condition ==> may_panic()`).
                Self::map_frames_bounds_panic_condition(area_size, map_offset, frames.len())
                    ==> may_panic(),
                // Cursor VA tracking (purely structural — no bounds).
                // Lets the per-iter capacity assert below chain a
                // `cursor.va >= barrier ⟹ map_offset + frames.len()*PAGE
                // > area_size` derivation that fires `map_frames_bounds_panic_condition`'s
                // capacity disjunct ⟹ `may_panic()` via the invariant.
                it.seq().len() == frames.len(),
                cursor.0.barrier_va.start == range.start + map_offset,
                cursor.0.barrier_va.end == range.end,
                cursor.0.guard_level == NR_LEVELS as u8,
                range.end - range.start == area_size,
                cursor.0.va == range.start + map_offset + it.index() * PAGE_SIZE,
                // For each remaining frame, the map contains a wf owner at its paddr.
                // Duplicates among remaining frames are fine — one key, one owner.
                forall|i: int|
                    it.index() <= i < it.seq().len() ==> {
                        let pa = #[trigger] crate::mm::frame::meta::mapping::meta_to_frame(
                            it.seq()[i].ptr.addr(),
                        );
                        &&& entry_owners.contains_key(pa)
                        &&& entry_owners[pa].inv()
                        &&& frame_entry_wf(it.seq()[i], prop, entry_owners[pa])
                    },
                // Slot facts for each remaining frame are preserved across iterations.
                // (Initially established by the function precondition; preserved by
                // `cursor.map`'s effect on unrelated slots — see the focused assume in
                // the loop body.)
                forall|i: int|
                    it.index() <= i < it.seq().len() ==> CursorMut::<
                        'a,
                        KernelPtConfig,
                        A,
                    >::item_slot_in_regions(
                        MappedItem::Tracked(#[trigger] it.seq()[i], prop),
                        *regions,
                    ),
        {
            proof {
                // Discharge the per-iter capacity assert via the may_panic
                // chain: if `cursor.0.va >= cursor.0.barrier_va.end`, the
                // loop-invariant cursor-VA tracking + range relationship
                // gives `map_offset + it.index()*PAGE_SIZE >= area_size`;
                // with `it.index() < frames.len()`, this implies
                // `map_offset + frames.len()*PAGE_SIZE > area_size` (the
                // capacity disjunct of `map_frames_bounds_panic_condition`)
                // ⟹ `may_panic()`.
                if !(cursor.0.va < cursor.0.barrier_va.end) {
                    assert(it.index() < frames.len());
                    assert(map_offset as int + (frames.len() as int) * (PAGE_SIZE as int)
                        > area_size as int) by (nonlinear_arith)
                        requires
                            cursor.0.va == range.start + map_offset + it.index() * PAGE_SIZE,
                            cursor.0.barrier_va.end == range.end,
                            range.end - range.start == area_size,
                            cursor.0.va >= cursor.0.barrier_va.end,
                            it.index() < frames.len(),
                            PAGE_SIZE > 0,
                    ;
                    assert(Self::map_frames_bounds_panic_condition(
                        area_size,
                        map_offset,
                        frames.len(),
                    ));
                    assert(may_panic());
                }
            }
            assert!(cursor.0.va < cursor.0.barrier_va.end);

            let ghost cur_mapped_pa: usize = crate::mm::frame::meta::mapping::meta_to_frame(
                frame.ptr.addr(),
            );
            proof {
                assert(entry_owners.contains_key(cur_mapped_pa));
                assert(frame_entry_wf(frame, prop, entry_owners[cur_mapped_pa]));
            }

            let ghost cur_pa_from_wf: usize = KernelPtConfig::item_into_raw_spec(
                MappedItem::Tracked(frame_as_dynframe(it.seq().index(it.index() as int)), prop),
            ).0;
            let ghost pre_remove_owners: Map<Paddr, EntryOwner<KernelPtConfig>> = *entry_owners;
            // Save path/parent_level so we can rebuild a fresh owner after `cursor.map`
            // consumes this one, and reinsert into the map for potential reuse by
            // later iterations at the same paddr.
            let ghost cur_path = entry_owners[cur_mapped_pa].path;
            let ghost cur_parent_level = entry_owners[cur_mapped_pa].parent_level;
            // Capture the original-owner facts now (Verus can lose them across the
            // cursor.map call, which churns enormous proof context).
            let ghost orig_mapped_pa = pre_remove_owners[cur_mapped_pa].frame().mapped_pa;
            let ghost orig_size = pre_remove_owners[cur_mapped_pa].frame().size;
            let ghost orig_prop = pre_remove_owners[cur_mapped_pa].frame().prop;
            proof {
                KernelPtConfig::item_into_raw_spec_tracked_level(MappedItem::Tracked(frame, prop));
                KernelPtConfig::item_into_raw_spec_tracked_pa(
                    DynFrame { ptr: frame.ptr, _marker: PhantomData },
                    prop,
                );
                KernelPtConfig::item_into_raw_spec_tracked_prop(
                    DynFrame { ptr: frame.ptr, _marker: PhantomData },
                    prop,
                );
                assert(orig_mapped_pa == cur_mapped_pa);
                assert(orig_prop == prop);
                assert(cur_parent_level == 1);
                assert(orig_size == page_size(cur_parent_level));
                assert(pre_remove_owners[cur_mapped_pa].inv_base());
            }

            let tracked mut entry_owner = entry_owners.tracked_remove(cur_mapped_pa);

            // Now Verus knows: dynframe == frame_as_dynframe(it.seq()[it.index()])
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
                cursor_owner.view_preserves_inv();  // old_cursor_model.inv()
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
            // loop invariant (instantiated at i = it.index()), itself established by
            // the function precondition.
            assert(CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(item, *regions));
            proof {
                // Discharge `cursor.map`'s `map_panic_conditions ==>
                // may_panic()` via the chain. Most disjuncts of
                // `map_panic_conditions` are ruled out by loop invariants
                // (cursor.va < barrier from the just-passed assert,
                // level==1 ⟹ ≤ HIGHEST_TRANSLATION_LEVEL/< guard_level/<
                // NR_LEVELS, va aligned). The only one that can fire is
                // `cursor.va + page_size(1) > barrier.end`, which via
                // cursor-VA tracking + range relationship gives
                // `map_offset + (it.index()+1)*PAGE > area_size`, ⟹
                // `map_offset + frames.len()*PAGE > area_size` (capacity
                // disjunct) ⟹ `may_panic()`.
                KernelPtConfig::axiom_kernel_htl_lt_nr_levels();
                if cursor.map_panic_conditions(item) {
                    assert(it.index() < frames.len());
                    assert(map_offset as int + (frames.len() as int) * (PAGE_SIZE as int)
                        > area_size as int) by (nonlinear_arith)
                        requires
                            cursor.0.va == range.start + map_offset + it.index() * PAGE_SIZE,
                            cursor.0.barrier_va.end == range.end,
                            range.end - range.start == area_size,
                            cursor.0.va + PAGE_SIZE > cursor.0.barrier_va.end,
                            it.index() < frames.len(),
                            PAGE_SIZE > 0,
                    ;
                    assert(Self::map_frames_bounds_panic_condition(
                        area_size,
                        map_offset,
                        frames.len(),
                    ));
                    assert(may_panic());
                }
            }
            let res = unsafe {
                #[verus_spec(with Tracked(&mut cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))]
                cursor.map(item)
            };

            // `item_slot_in_regions` preservation for the remaining frames
            // follows from cursor.map's strengthened ensures: ref_count is
            // preserved at non-mapped non-UNUSED indices, and at the mapped
            // index ref_count > 0 is preserved (covers duplicates). slots
            // keys are monotonic across map.
            proof {
                let cur_pa = KernelPtConfig::item_into_raw_spec(item).0;
                let cur_pa_idx = frame_to_index(cur_pa);
                assert forall|i: int|
                    (it.index() as int + 1) <= i < it.seq().len() implies CursorMut::<
                    'a,
                    KernelPtConfig,
                    A,
                >::item_slot_in_regions(
                    MappedItem::Tracked(#[trigger] it.seq()[i], prop),
                    *regions,
                ) by {
                    let item_i = MappedItem::Tracked(it.seq()[i], prop);
                    let pa_i = KernelPtConfig::item_into_raw_spec(item_i).0;
                    let idx_i = frame_to_index(pa_i);
                    KernelPtConfig::item_into_raw_spec_tracked_level(item_i);
                    // Loop invariant gives item_slot_in_regions for item_i
                    // against `regions_before_map`. cursor.map preserves
                    // slots-monotonicity and the relevant ref_count fact at
                    // either branch (idx_i != cur_pa_idx via direct equality,
                    // idx_i == cur_pa_idx via mapped-idx > 0 preservation).
                    assert(CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(
                        item_i,
                        regions_before_map,
                    ));
                    if idx_i != cur_pa_idx {
                        assert(regions.slot_owners[idx_i].inner_perms.ref_count.value()
                            == regions_before_map.slot_owners[idx_i].inner_perms.ref_count.value());
                    }
                };
            }

            proof {
                let cur_idx = frame_to_index(cur_mapped_pa);

                let (pa, level, prop_) = KernelPtConfig::item_into_raw_spec(item);
                KernelPtConfig::item_into_raw_spec_tracked_level(item);

                let split_self = old_cursor_model.split_while_huge(PAGE_SIZE);

                let aligned_nat: nat = vstd_extra::arithmetic::nat_align_up(
                    split_self.cur_va as nat,
                    PAGE_SIZE as nat,
                );

                vstd_extra::arithmetic::lemma_nat_align_up_sound(
                    split_self.cur_va as nat,
                    PAGE_SIZE as nat,
                );

                CursorView::<KernelPtConfig>::lemma_split_while_huge_preserves_cur_va(
                    old_cursor_model,
                    PAGE_SIZE,
                );

                assert(aligned_nat == vstd_extra::arithmetic::nat_align_up(
                    old_cursor_owner_va.to_vaddr() as nat,
                    PAGE_SIZE as nat,
                ));

                // va is PAGE_SIZE-aligned (loop invariant via cursor.0.invariants),
                // so nat_align_down returns va unchanged.
                vstd_extra::arithmetic::lemma_nat_align_down_sound(
                    old_cursor_owner_va.to_vaddr() as nat,
                    PAGE_SIZE as nat,
                );
                assert(vstd_extra::arithmetic::nat_align_down(
                    old_cursor_owner_va.to_vaddr() as nat,
                    PAGE_SIZE as nat,
                ) == old_cursor_owner_va.to_vaddr() as nat);

                cursor_owner.va.reflect_prop(cursor.0.va);

                // Reinsert a fresh owner for this paddr so later iterations on the
                // same frame reuse it. `new_frame` fabricates an `EntryOwner` with
                // the correct `new_frame` shape for the paddr/level/prop;
                // `frame_entry_wf` holds for any future frame at the same paddr.
                // Note: `new_frame` returns with `in_scope = true`; clear it for
                // `inv()` to hold (which requires `!in_scope`).
                let tracked mut fresh = EntryOwner::<KernelPtConfig>::tracked_new_frame(
                    cur_mapped_pa,
                    cur_path,
                    cur_parent_level,
                    prop,  /* is_tracked */
                    true,
                );
                fresh.in_scope = false;
                entry_owners.tracked_insert(cur_mapped_pa, fresh);
            }
        }

        proof {
            // The diverging `assert!`s at the top (`area_size % PAGE_SIZE`
            // and `map_offset % PAGE_SIZE`) did not fire, so the
            // caller-precludable panic condition is false on this path.
            assert(!Self::map_frames_panic_condition(area_size, map_offset, frames.len()));
        }
        Self { range }
    }

    /// Caller-precludable *bounds* panic condition for
    /// [`Self::map_untracked_frames`]: physical range / area size / map
    /// offset misalignment, plus the top-level capacity assert.
    pub open spec fn map_untracked_frames_bounds_panic_condition(
        area_size: usize,
        map_offset: usize,
        pa_range: &Range<Paddr>,
    ) -> bool {
        ||| pa_range.start % PAGE_SIZE != 0
        ||| pa_range.end % PAGE_SIZE != 0
        ||| area_size % PAGE_SIZE != 0
        ||| map_offset % PAGE_SIZE != 0
        ||| map_offset as int + vstd_extra::external::range::range_usize_len(pa_range) as int
            > area_size as int
    }

    /// Full panic condition for [`Self::map_untracked_frames`] = bounds OR OOM.
    pub open spec fn map_untracked_frames_panic_condition(
        area_size: usize,
        map_offset: usize,
        pa_range: &Range<Paddr>,
    ) -> bool {
        ||| Self::map_untracked_frames_bounds_panic_condition(area_size, map_offset, pa_range)
        ||| kvirt_alloc_oom_condition(area_size)
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
            Tracked(guards): Tracked<&mut Guards<'a>>
    )]
    #[allow(private_interfaces)]
    pub unsafe fn map_untracked_frames<A: InAtomicMode + 'a, 'a>(
        area_size: usize,
        map_offset: usize,
        pa_range: Range<Paddr>,
        prop: PageProperty,
    ) -> (res: Self)
        requires
    // **Precise form** (post Phases A/B/C). Bounds are caller-
    // provable; OOM uses the implication form.

            !Self::map_untracked_frames_bounds_panic_condition(area_size, map_offset, &pa_range),
            kvirt_alloc_oom_condition(area_size) ==> may_panic(),
            old(regions).inv(),
            owner.inv(),
            map_offset + vstd_extra::external::range::range_usize_len(&pa_range) <= usize::MAX,
        ensures
            final(regions).inv(),
            res.inv(),
            !Self::map_untracked_frames_panic_condition(area_size, map_offset, &pa_range),
    {
        assert!(pa_range.start % PAGE_SIZE == 0);
        assert!(pa_range.end % PAGE_SIZE == 0);
        assert!(area_size % PAGE_SIZE == 0);
        assert!(map_offset % PAGE_SIZE == 0);

        assert!(map_offset + vstd_extra::external::range::range_usize_len(&pa_range) <= area_size);

        let range_res = KVIRT_AREA_ALLOCATOR.alloc(area_size);
        // Rust's `unwrap()` panics if not ok. TODO: make our own wrapper.
        assert!(range_res.is_ok());
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
                // Discharge `cursor_new_success_conditions(&va_range)` so
                // `cursor_mut`'s `ensures cursor_new_success_conditions ==> r
                // is Ok` fires — making `assert!(cursor_res.is_ok())` below
                // dischargeable *without* `may_panic`. Under `!map_untracked_frames_panic_condition`
                // we have pa_range / area_size / map_offset alignment and
                // `map_offset + len <= area_size`. `len > 0` by the
                // surrounding `if pa_range.start < pa_range.end`, so
                // `va_range.start < va_range.end`.
                assert(va_range.start < va_range.end);
                assert(va_range.start % <KernelPtConfig as PagingConstsTrait>::BASE_PAGE_SIZE_spec()
                    == 0);
                assert(va_range.end % <KernelPtConfig as PagingConstsTrait>::BASE_PAGE_SIZE_spec()
                    == 0);
                assert(crate::mm::page_table::Cursor::<
                    KernelPtConfig,
                    A,
                >::cursor_new_success_conditions(&va_range));
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

            assert!(cursor_res.is_ok());

            let (mut cursor, Tracked(cursor_owner)) = cursor_res.unwrap();

            let pages = collect_largest_pages(va_range.start, pa_range.start, len);

            for (pa, level) in it: pages.into_iter()
                invariant
                    cursor.0.invariants(cursor_owner, *regions, *guards),
                    // Level bounds / alignment from `collect_largest_pages` postconditions.
                    forall|i: int|
                        0 <= i < it.seq().len() ==> (#[trigger] it.seq()[i]).0 % PAGE_SIZE == 0,
                    forall|i: int|
                        0 <= i < it.seq().len() ==> 1 <= (#[trigger] it.seq()[i]).1 <= NR_LEVELS,
                    forall|i: int|
                        0 <= i < it.seq().len() ==> (#[trigger] it.seq()[i]).1
                            <= KernelPtConfig::HIGHEST_TRANSLATION_LEVEL(),
                    forall|i: int|
                        0 <= i < it.seq().len() ==> (va_range.start as nat
                            + #[trigger] sum_page_sizes_spec(it.seq(), 0, i)) % page_size(
                            it.seq()[i].1,
                        ) as nat == 0,
                    forall|i: int|
                        #![auto]
                        0 <= i < it.seq().len() ==> it.seq()[i].0 as nat == pa_range.start as nat
                            + sum_page_sizes_spec(it.seq(), 0, i),
                    sum_page_sizes_spec(it.seq(), 0, it.seq().len() as int) == len as nat,
                    // VA tracking: cursor has advanced past sum of processed pages.
                    cursor.0.va as nat == va_range.start as nat + sum_page_sizes_spec(
                        it.seq(),
                        0,
                        it.index() as int,
                    ),
                    cursor.0.barrier_va.end == va_range.start + len,
                    // `pa_range.end == pa_range.start + len` so pa + page_size(level) stays bounded.
                    pa_range.end as nat == pa_range.start as nat + len as nat,
                    cursor.0.guard_level == NR_LEVELS as u8,
                    pa_range.end <= MAX_PADDR,
                    // Slot facts for the remaining PAs are preserved across iterations.
                    // Initially established by the function precondition; each iteration's
                    // `cursor.map` only touches the slot at its own mapped PA — see the
                    // focused assume in the loop body.
                    forall|pa: Paddr|
                        #![trigger crate::mm::frame::meta::mapping::frame_to_index(pa)]
                        pa_range.start <= pa < pa_range.end && pa % PAGE_SIZE == 0 ==> {
                            let idx = crate::mm::frame::meta::mapping::frame_to_index(pa);
                            &&& regions.slots.contains_key(idx)
                            &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                                != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                        },
            {
                let pos: Ghost<int> = Ghost(it.index() as int);

                proof {
                    sum_page_sizes_extend_right(it.seq(), 0, pos@);
                    sum_page_sizes_mono(it.seq(), 0, pos@ + 1, it.seq().len() as int);
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

                let ghost old_cursor_model: CursorView<KernelPtConfig> = cursor.0.model(
                    cursor_owner,
                );
                let ghost old_cursor_owner_va = cursor_owner.va;
                let ghost old_va: nat = cursor.0.va as nat;

                proof {
                    cursor_owner.view_preserves_inv();  // old_cursor_model.inv()
                    cursor_owner.va.reflect_prop(cursor.0.va);

                    KernelPtConfig::item_into_raw_spec_untracked(pa, level, prop);

                    // pa_range.end == pa_range.start + len (in nat) — from loop invariant.
                    sum_page_sizes_extend_right(it.seq(), 0, pos@);
                    sum_page_sizes_mono(it.seq(), 0, pos@ + 1, it.seq().len() as int);
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
                    assert(CursorMut::<'a, KernelPtConfig, A>::item_slot_in_regions(
                        item,
                        *regions,
                    ));
                }
                let _ = unsafe {
                    #[verus_spec(with Tracked(&mut cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))]
                    cursor.map(item)
                };

                proof {
                    cursor_owner.va.reflect_prop(cursor.0.va);
                }

                proof {
                    KernelPtConfig::item_into_raw_spec_untracked(pa, level, prop);
                    let level_raw = KernelPtConfig::item_into_raw_spec(item).1;

                    crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(
                    level_raw);
                    KernelPtConfig::item_into_raw_spec_level_bounds(item);
                    let split_self = old_cursor_model.split_while_huge(page_size(level_raw));

                    CursorView::<KernelPtConfig>::lemma_split_while_huge_preserves_cur_va(
                        old_cursor_model,
                        page_size(level_raw),
                    );

                    lemma_page_size_ge_page_size(level_raw);

                    vstd_extra::arithmetic::lemma_nat_align_down_sound(
                        old_cursor_owner_va.to_vaddr() as nat,
                        page_size(level_raw) as nat,
                    );
                    vstd_extra::arithmetic::lemma_nat_align_down_sound(
                        old_cursor_owner_va.to_vaddr() as nat,
                        page_size(level_raw) as nat,
                    );
                    assert(vstd_extra::arithmetic::nat_align_down(
                        old_cursor_owner_va.to_vaddr() as nat,
                        page_size(level_raw) as nat,
                    ) + page_size(level_raw) as nat <= usize::MAX as nat);
                    old_cursor_owner_va.align_up_advances_general(level_raw as int);

                    sum_page_sizes_extend_right(it.seq(), 0, pos@);

                    let pa_next_nat = pa_range.start as nat + sum_page_sizes_spec(
                        it.seq(),
                        0,
                        pos@ + 1,
                    );
                    assert(pa_next_nat == pa as nat + page_size(level) as nat);
                }
            }
        }
        proof {
            // The diverging `assert!`s at the top (range/size/offset
            // alignment and the `map_offset + len <= area_size` capacity
            // check) did not fire, so the caller-precludable panic
            // condition is false on this path.
            assert(!Self::map_untracked_frames_panic_condition(area_size, map_offset, &pa_range));
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
