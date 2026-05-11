// SPDX-License-Identifier: MPL-2.0
use vstd::arithmetic::power2::*;
use vstd::atomic::PermissionU64;
use vstd::prelude::*;
use vstd::simple_pptr;
use vstd::std_specs::clone::*;

use vstd_extra::prelude::{lemma_usize_ilog2_ordered, lemma_usize_pow2_ilog2};

use core::{
    fmt::Debug,
    intrinsics::transmute_unchecked,
    ops::{Range, RangeInclusive},
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::mm::frame::meta::MetaSlot;

use super::{
    kspace::KernelPtConfig, lemma_nr_subpage_per_huge_bounded, nr_subpage_per_huge,
    page_prop::PageProperty, vm_space::UserPtConfig, Paddr, PagingConstsTrait, PagingLevel, Vaddr,
};

use crate::specs::mm::page_table::*;

use crate::specs::arch::mm::*;
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::page_table::cursor::*;
use crate::specs::task::InAtomicMode;

use crate::mm::frame::meta::mapping::frame_to_index;
use crate::mm::kspace::kvirt_area::disable_preempt;
use crate::specs::arch::PageTableEntry;
use crate::specs::mm::frame::meta_owners::MetaPerm;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use vstd_extra::ownership::Inv;

mod node;
pub use node::*;
mod cursor;

pub(crate) use cursor::*;

#[cfg(ktest)]
mod test;

//pub(crate) mod boot_pt;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PageTableError {
    /// The provided virtual address range is invalid.
    InvalidVaddrRange(Vaddr, Vaddr),
    /// The provided virtual address is invalid.
    InvalidVaddr(Vaddr),
    /// Using virtual address not aligned.
    UnalignedVaddr,
}

pub trait RCClone: Sized {
    spec fn clone_requires(self, perm: MetaRegionOwners) -> bool;

    spec fn clone_ensures(
        self,
        old_perm: MetaRegionOwners,
        new_perm: MetaRegionOwners,
        res: Self,
    ) -> bool;

    fn clone(&self, Tracked(perm): Tracked<&mut MetaRegionOwners>) -> (res: Self)
        requires
            self.clone_requires(*old(perm)),
        ensures
            res == *self,
            self.clone_ensures(*old(perm), *final(perm), res),
            final(perm).inv(),
            final(perm).slots =~= old(perm).slots,
            final(perm).slot_owners.dom() =~= old(perm).slot_owners.dom(),
    ;
}

/// The configurations of a page table.
///
/// It abstracts away both the usage and the architecture specifics from the
/// general page table implementation. For examples:
///  - the managed virtual address range;
///  - the trackedness of physical mappings;
///  - the PTE layout;
///  - the number of page table levels, etc.
///
/// # Safety
///
/// The implementor must ensure that the `item_into_raw` and `item_from_raw`
/// are implemented correctly so that:
///  - `item_into_raw` consumes the ownership of the item;
///  - if the provided raw form matches the item that was consumed by
///    `item_into_raw`, `item_from_raw` restores the exact item that was
///    consumed by `item_into_raw`.
pub unsafe trait PageTableConfig: Clone + Debug + Send + Sync + 'static {
    /// The index range at the top level (`C::NR_LEVELS()`) page table.
    ///
    /// When configured with this value, the [`PageTable`] instance will only
    /// be allowed to manage the virtual address range that is covered by
    /// this range. The range can be smaller than the actual allowed range
    /// specified by the hardware MMU (limited by `C::ADDRESS_WIDTH`).
    spec fn TOP_LEVEL_INDEX_RANGE_spec() -> Range<usize>;

    /// The leading bits `[48, 64)` of every virtual address managed by this
    /// config.
    ///
    /// Concretely, a mapping `m` in this page table has
    /// `m.va_range.start / 2^48 == LEADING_BITS_spec()`. For non-sign-extended
    /// configurations (e.g. `UserPtConfig`) this is `0`. For x86-64 kernel
    /// PT it is `0xffff` (sign-extended high half). The type is wide enough
    /// to carry arbitrary bit patterns, so the model can accommodate future
    /// configurations that place their managed range at a non-canonical
    /// fixed offset.
    ///
    /// Combined with `TOP_LEVEL_INDEX_RANGE_spec`, this fully determines
    /// the managed VA range, computed as
    /// [`vaddr_range_bounds_spec::<Self>`]. Callers that previously used
    /// `VADDR_RANGE_spec()` should use `vaddr_range_bounds_spec::<C>()`
    /// directly — the inclusive `(start, end_inclusive)` form avoids the
    /// `end == usize::MAX + 1` overflow that plagues `Range<Vaddr>` for
    /// sign-extended kernel configurations.
    open spec fn LEADING_BITS_spec() -> usize {
        0
    }

    fn TOP_LEVEL_INDEX_RANGE() -> (r: Range<usize>)
        ensures
            r == Self::TOP_LEVEL_INDEX_RANGE_spec(),
    ;

    /// If we can remove the top-level page table entries.
    ///
    /// This is for the kernel page table, whose second-top-level page
    /// tables need `'static` lifetime to be shared with user page tables.
    /// Other page tables do not need to set this to `false`.
    open spec fn TOP_LEVEL_CAN_UNMAP_spec() -> bool {
        true
    }

    fn TOP_LEVEL_CAN_UNMAP() -> (b: bool)
        ensures
            b == Self::TOP_LEVEL_CAN_UNMAP_spec(),
    ;

    /// Upper bound on `locked_range().end as int` for cursors of this config.
    ///
    /// May be tighter than the structural `vaddr_range_bounds_spec().1 + 1`
    /// when the actual sources of cursor ranges (e.g. the kvirt allocator
    /// for `KernelPtConfig`) draw from a sub-window of the configured VA
    /// range. `KernelPtConfig` overrides this to `FRAME_METADATA_BASE_VADDR`,
    /// which the `kvirt_alloc_range_bounds` axiom enforces. This bound is
    /// what allows the cursor's `move_forward` proof to discharge
    /// `prefix.idx[NR_LEVELS - 1] + 1 < NR_ENTRIES` at the top-level
    /// boundary — the structural bound only gives `<= NR_ENTRIES` for
    /// configurations whose `TOP_LEVEL_INDEX_RANGE.end == NR_ENTRIES`.
    ///
    /// Default: `usize::MAX + 1` (no tightening over the structural bound).
    open spec fn LOCKED_END_BOUND_spec() -> int {
        0x1_0000_0000_0000_0000int
    }

    /// The type of the page table entry.
    type E: PageTableEntryTrait;

    /// The paging constants.
    type C: PagingConstsTrait;

    proof fn axiom_nr_subpage_per_huge_eq_nr_entries()
        ensures
            Self::C::BASE_PAGE_SIZE() / Self::C::PTE_SIZE() == NR_ENTRIES,
    ;

    /// The item that can be mapped into the virtual memory space using the
    /// page table.
    ///
    /// Usually, this item is a [`crate::mm::Frame`], which we call a "tracked"
    /// frame. The page table can also do "untracked" mappings that only maps
    /// to certain physical addresses without tracking the ownership of the
    /// mapped physical frame. The user of the page table APIs can choose by
    /// defining this type and the corresponding methods [`item_into_raw`] and
    /// [`item_from_raw`].
    ///
    /// [`item_from_raw`]: PageTableConfig::item_from_raw
    /// [`item_into_raw`]: PageTableConfig::item_into_raw
    type Item: RCClone;

    /// Consumes the item and returns the physical address, the paging level,
    /// and the page property.
    ///
    /// The ownership of the item will be consumed, i.e., the item will be
    /// forgotten after this function is called.
    spec fn item_into_raw_spec(item: Self::Item) -> (Paddr, PagingLevel, PageProperty);

    #[verifier::when_used_as_spec(item_into_raw_spec)]
    fn item_into_raw(item: Self::Item) -> (res: (Paddr, PagingLevel, PageProperty))
        ensures
            1 <= res.1 <= NR_LEVELS,
            res == Self::item_into_raw_spec(item),
            res.0 % crate::specs::arch::mm::PAGE_SIZE == 0,
            res.0 < crate::specs::arch::mm::MAX_PADDR,
            res.0 % crate::mm::page_table::cursor::page_size(res.1) == 0,
            res.0 + crate::mm::page_table::cursor::page_size(res.1)
                <= crate::specs::arch::mm::MAX_PADDR,
    ;

    /// Restores the item from the physical address and the paging level.
    ///
    /// There could be transformations after [`PageTableConfig::item_into_raw`]
    /// and before [`PageTableConfig::item_from_raw`], which include:
    ///  - splitting and coalescing the items, for example, splitting one item
    ///    into 512 `level - 1` items with and contiguous physical addresses;
    ///  - protecting the items, for example, changing the page property.
    ///
    /// Splitting and coalescing maintains ownership rules, i.e., if one
    /// physical address is within the range of one item, after splitting/
    /// coalescing, there should be exactly one item that contains the address.
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    ///  - the physical address and the paging level represent a page table
    ///    item or part of it (as described above);
    ///  - either the ownership of the item is properly transferred to the
    ///    return value, or the return value is wrapped in a
    ///    [`core::mem::ManuallyDrop`] that won't outlive the original item.
    ///
    /// A concrete trait implementation may require the caller to ensure that
    ///  - the [`super::PageFlags::AVAIL1`] flag is the same as that returned
    ///    from [`PageTableConfig::item_into_raw`].
    spec fn item_from_raw_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item;

    #[verifier::when_used_as_spec(item_from_raw_spec)]
    fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item
        returns
            Self::item_from_raw_spec(paddr, level, prop),
    ;

    /// Whether cloning this item bumps a slot's refcount. For ref-counted items
    /// (e.g. `MappedItem::Tracked`), `true`; for items where clone is a no-op
    /// (e.g. `MappedItem::Untracked` for kernel MMIO frames), `false`.
    spec fn tracked(item: Self::Item) -> bool;

    /// Per-config predicate that captures the structural well-formedness an item
    /// reconstructed via `item_from_raw_spec` must satisfy. Typically: the
    /// `Frame::inv()` of the tracked-frame component (if any).
    ///
    /// `KernelPtConfig` defines this as `match item { Tracked(f, _) => f.inv(),
    /// Untracked => true }`. `UserPtConfig` defines it as `item.frame.inv()`.
    spec fn item_well_formed(item: Self::Item) -> bool;

    /// The item produced by `item_from_raw_spec` is structurally
    /// well-formed (see `item_well_formed`).
    proof fn item_from_raw_well_formed(pa: Paddr, level: PagingLevel, prop: PageProperty)
        requires
            crate::mm::frame::meta::has_safe_slot(pa),
        ensures
            Self::item_well_formed(Self::item_from_raw_spec(pa, level, prop)),
    ;

    /// Proves that `clone_ensures` for `Self::Item` implies concrete per-field
    /// properties on `MetaRegionOwners`. Each `PageTableConfig` implementor proves
    /// this by unfolding its `MappedItem::clone_ensures` → `Frame::clone_ensures`.
    /// Proves that after `clone`, the slot at `frame_to_index(pa)` has the expected
    /// per-field properties. Implementors unfold their `MappedItem::clone_ensures` to
    /// `Frame::clone_ensures` and connect `pa` to the frame's internal pointer address.
    proof fn clone_ensures_concrete(
        item: Self::Item,
        pa: Paddr,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        res: Self::Item,
    )
        requires
            item.clone_ensures(old_regions, new_regions, res),
            Self::item_into_raw_spec(item).0 == pa,
            res == item,
            new_regions.inv(),
            new_regions.slots =~= old_regions.slots,
            new_regions.slot_owners.dom() =~= old_regions.slot_owners.dom(),
        ensures
    // Other slots always unchanged.

            forall|i: usize|
                i != frame_to_index(pa) ==> (#[trigger] new_regions.slot_owners[i]
                    == old_regions.slot_owners[i]),
            // The frame's slot: bumped if the item is ref-counted, otherwise unchanged.
            Self::tracked(item) ==> {
                &&& new_regions.slot_owners[frame_to_index(pa)].inner_perms.ref_count.value()
                    == old_regions.slot_owners[frame_to_index(pa)].inner_perms.ref_count.value() + 1
                &&& new_regions.slot_owners[frame_to_index(pa)].inner_perms.ref_count.id()
                    == old_regions.slot_owners[frame_to_index(pa)].inner_perms.ref_count.id()
                &&& new_regions.slot_owners[frame_to_index(pa)].inner_perms.storage
                    == old_regions.slot_owners[frame_to_index(pa)].inner_perms.storage
                &&& new_regions.slot_owners[frame_to_index(pa)].inner_perms.vtable_ptr
                    == old_regions.slot_owners[frame_to_index(pa)].inner_perms.vtable_ptr
                &&& new_regions.slot_owners[frame_to_index(pa)].inner_perms.in_list
                    == old_regions.slot_owners[frame_to_index(pa)].inner_perms.in_list
                &&& new_regions.slot_owners[frame_to_index(pa)].paths_in_pt
                    == old_regions.slot_owners[frame_to_index(pa)].paths_in_pt
                &&& new_regions.slot_owners[frame_to_index(pa)].self_addr
                    == old_regions.slot_owners[frame_to_index(pa)].self_addr
                &&& new_regions.slot_owners[frame_to_index(pa)].raw_count
                    == old_regions.slot_owners[frame_to_index(pa)].raw_count
                &&& new_regions.slot_owners[frame_to_index(pa)].usage
                    == old_regions.slot_owners[frame_to_index(pa)].usage
            },
            !Self::tracked(item) ==> new_regions.slot_owners[frame_to_index(pa)]
                == old_regions.slot_owners[frame_to_index(pa)],
    ;

    proof fn item_roundtrip(item: Self::Item, paddr: Paddr, level: PagingLevel, prop: PageProperty)
        ensures
            Self::item_into_raw_spec(item) == (paddr, level, prop) <==> Self::item_from_raw_spec(
                paddr,
                level,
                prop,
            ) == item,
    ;

    /// Proves `item.clone_requires(regions)` from the concrete frame-slot facts
    /// delivered by `metaregion_sound` plus the non-saturation bound propagated
    /// from `Cursor::query`. Implementors unfold their `MappedItem::clone_requires`
    /// to `Frame::clone_requires` and connect `pa` to the frame's internal pointer
    /// address.
    proof fn clone_requires_concrete(
        item: Self::Item,
        pa: Paddr,
        level: PagingLevel,
        prop: PageProperty,
        regions: MetaRegionOwners,
    )
        requires
            regions.inv(),
            Self::item_from_raw_spec(pa, level, prop) == item,
            crate::mm::frame::meta::has_safe_slot(pa),
            regions.slots.contains_key(frame_to_index(pa)),
            regions.slot_owners.contains_key(frame_to_index(pa)),
            Self::tracked(item) ==> regions.slot_owners[frame_to_index(
                pa,
            )].inner_perms.ref_count.value() > 0,
            // `rc != UNUSED` is needed only for tracked frames (untracked clone is a no-op).
            Self::tracked(item) ==> regions.slot_owners[frame_to_index(
                pa,
            )].inner_perms.ref_count.value()
                != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED,
        ensures
            item.clone_requires(regions),
    ;
}

// Implement it so that we can comfortably use low level functions
// like `page_size::<C>` without typing `C::C` everywhere.
impl<C: PageTableConfig> PagingConstsTrait for C {
    open spec fn BASE_PAGE_SIZE_spec() -> usize {
        C::C::BASE_PAGE_SIZE_spec()
    }

    fn BASE_PAGE_SIZE() -> usize {
        C::C::BASE_PAGE_SIZE()
    }

    open spec fn NR_LEVELS_spec() -> PagingLevel {
        C::C::NR_LEVELS_spec()
    }

    fn NR_LEVELS() -> PagingLevel {
        C::C::NR_LEVELS()
    }

    open spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel {
        C::C::HIGHEST_TRANSLATION_LEVEL_spec()
    }

    fn HIGHEST_TRANSLATION_LEVEL() -> PagingLevel {
        C::C::HIGHEST_TRANSLATION_LEVEL()
    }

    open spec fn PTE_SIZE_spec() -> usize {
        C::C::PTE_SIZE_spec()
    }

    fn PTE_SIZE() -> usize {
        C::C::PTE_SIZE()
    }

    open spec fn ADDRESS_WIDTH_spec() -> usize {
        C::C::ADDRESS_WIDTH_spec()
    }

    fn ADDRESS_WIDTH() -> usize {
        C::C::ADDRESS_WIDTH()
    }

    open spec fn VA_SIGN_EXT_spec() -> bool {
        C::C::VA_SIGN_EXT_spec()
    }

    fn VA_SIGN_EXT() -> bool {
        C::C::VA_SIGN_EXT()
    }

    proof fn lemma_BASE_PAGE_SIZE_properties()
        ensures
            0 < Self::BASE_PAGE_SIZE_spec(),
            is_pow2(Self::BASE_PAGE_SIZE_spec() as int),
    {
        C::C::lemma_BASE_PAGE_SIZE_properties();
    }

    proof fn lemma_PTE_SIZE_properties()
        ensures
            0 < Self::PTE_SIZE_spec() <= Self::BASE_PAGE_SIZE(),
            is_pow2(Self::PTE_SIZE_spec() as int),
    {
        C::C::lemma_PTE_SIZE_properties();
    }
}

/// The interface for defining architecture-specific page table entries.
///
/// Note that a default PTE should be a PTE that points to nothing.
pub trait PageTableEntryTrait: Clone + Copy + Debug + Sized + Send + Sync + 'static {
    spec fn default_spec() -> Self;

    /// For implement `Default` trait.
    #[verifier::when_used_as_spec(default_spec)]
    fn default() -> (res: Self)
        ensures
            res == Self::default_spec(),
    ;

    /// Create a set of new invalid page table flags that indicates an absent page.
    ///
    /// Note that currently the implementation requires an all zero PTE to be an absent PTE.
    spec fn new_absent_spec() -> Self;

    #[verifier(when_used_as_spec(new_absent_spec))]
    fn new_absent() -> (res: Self)
        ensures
            res == Self::new_absent_spec(),
            res.paddr() % PAGE_SIZE == 0,
            res.paddr() < MAX_PADDR,
    ;

    /// If the flags are present with valid mappings.
    spec fn is_present_spec(&self) -> bool;

    #[verifier::when_used_as_spec(is_present_spec)]
    fn is_present(&self) -> (res: bool)
        ensures
            res == self.is_present_spec(),
    ;

    /// Create a new PTE with the given physical address and flags that map to a page.
    spec fn new_page_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self;

    #[verifier::when_used_as_spec(new_page_spec)]
    fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> (res: Self)
        requires
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
        ensures
            res == Self::new_page_spec(paddr, level, prop),
            res.paddr() == paddr,
            res.paddr() % PAGE_SIZE == 0,
            res.paddr() < MAX_PADDR,
    ;

    /// Create a new PTE that map to a child page table.
    spec fn new_pt_spec(paddr: Paddr) -> Self;

    #[verifier::when_used_as_spec(new_pt_spec)]
    fn new_pt(paddr: Paddr) -> (res: Self)
        requires
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
        ensures
            res == Self::new_pt_spec(paddr),
            res.paddr() == paddr,
            res.paddr() % PAGE_SIZE == 0,
            res.paddr() < MAX_PADDR,
    ;

    proof fn new_properties()
        ensures
            !Self::new_absent_spec().is_present(),
            forall|level: PagingLevel|
                #![trigger Self::new_absent_spec().is_last(level)]
                1 < level ==> !Self::new_absent_spec().is_last(level),
            forall|paddr: Paddr, level: PagingLevel, prop: PageProperty|
                #![trigger Self::new_page_spec(paddr, level, prop)]
                {
                    &&& Self::new_page_spec(paddr, level, prop).is_present()
                    &&& Self::new_page_spec(paddr, level, prop).paddr() == paddr
                    &&& Self::new_page_spec(paddr, level, prop).prop() == prop
                    &&& Self::new_page_spec(paddr, level, prop).is_last(level)
                },
            forall|paddr: Paddr|
                #![trigger Self::new_pt_spec(paddr)]
                {
                    &&& Self::new_pt_spec(paddr).is_present()
                    &&& Self::new_pt_spec(paddr).paddr() == paddr
                    &&& forall|level: PagingLevel| !Self::new_pt_spec(paddr).is_last(level)
                },
    ;

    /// Get the physical address from the PTE.
    /// The physical address recorded in the PTE is either:
    /// - the physical address of the next level page table;
    /// - or the physical address of the page it maps to.
    spec fn paddr_spec(&self) -> Paddr;

    #[verifier::when_used_as_spec(paddr_spec)]
    fn paddr(&self) -> (res: Paddr)
        ensures
            res == self.paddr_spec(),
    ;

    spec fn prop_spec(&self) -> PageProperty;

    #[verifier::when_used_as_spec(prop_spec)]
    fn prop(&self) -> (res: PageProperty)
        ensures
            res == self.prop_spec(),
    ;

    /// Set the page property of the PTE.
    ///
    /// This will be only done if the PTE is present. If not, this method will
    /// do nothing.
    spec fn set_prop_spec(&self, prop: PageProperty) -> Self;

    fn set_prop(&mut self, prop: PageProperty)
        ensures
            old(self).set_prop_spec(prop) == *final(self),
    ;

    proof fn set_prop_properties(self, prop: PageProperty)
        ensures
            self.set_prop_spec(prop).prop() == prop,
            self.set_prop_spec(prop).paddr() == self.paddr(),
            self.is_present() ==> self.set_prop_spec(prop).is_present(),
            forall|level: PagingLevel|
                #![trigger self.is_last(level)]
                self.is_last(level) ==> self.set_prop_spec(prop).is_last(level),
    ;

    /// If the PTE maps a page rather than a child page table.
    ///
    /// The level of the page table the entry resides is given since architectures
    /// like amd64 only uses a huge bit in intermediate levels.
    spec fn is_last_spec(&self, level: PagingLevel) -> bool;

    #[verifier::when_used_as_spec(is_last_spec)]
    fn is_last(&self, level: PagingLevel) -> (b: bool)
        ensures
            b == self.is_last_spec(level),
    ;

    /// Converts the PTE into its corresponding `usize` value.
    spec fn as_usize_spec(self) -> usize;

    #[verifier::external_body]
    #[verifier::when_used_as_spec(as_usize_spec)]
    fn as_usize(self) -> (res: usize)
        ensures
            res == self.as_usize_spec(),
    {
        unimplemented!()
        // SAFETY: `Self` is `Pod` and has the same memory representation as `usize`.
        //        unsafe { transmute_unchecked(self) }

    }

    /// Converts a usize `pte_raw` into a PTE.
    #[verifier::external_body]
    fn from_usize(pte_raw: usize) -> Self {
        unimplemented!()
        // SAFETY: `Self` is `Pod` and has the same memory representation as `usize`.
        //        unsafe { transmute_unchecked(pte_raw) }

    }
}

/// A handle to a page table.
/// A page table can track the lifetime of the mapped physical pages.
pub struct PageTable<C: PageTableConfig> {
    pub root: PageTableNode<C>,
}

#[verifier::inline]
pub open spec fn nr_pte_index_bits_spec<C: PagingConstsTrait>() -> usize {
    nr_subpage_per_huge::<C>().ilog2() as usize
}

/// The number of virtual address bits used to index a PTE in a page.
#[inline(always)]
#[verifier::when_used_as_spec(nr_pte_index_bits_spec)]
pub fn nr_pte_index_bits<C: PagingConstsTrait>() -> (res: usize)
    ensures
        res == nr_pte_index_bits_spec::<C>(),
{
    proof {
        lemma_nr_subpage_per_huge_bounded::<C>();
    }
    nr_subpage_per_huge::<C>().ilog2() as usize
}

pub proof fn lemma_nr_pte_index_bits_bounded<C: PagingConstsTrait>()
    ensures
        0 <= nr_pte_index_bits::<C>() <= C::BASE_PAGE_SIZE().ilog2(),
{
    lemma_nr_subpage_per_huge_bounded::<C>();
    let nr = nr_subpage_per_huge::<C>();
    assert(1 <= nr <= C::BASE_PAGE_SIZE());
    let bits = nr.ilog2();
    assert(0 <= bits) by {
        lemma_usize_ilog2_ordered(1, nr);
    }
    assert(bits <= C::BASE_PAGE_SIZE().ilog2()) by {
        lemma_usize_ilog2_ordered(nr, C::BASE_PAGE_SIZE());
    }
}

/// Splits the address range into largest page table items.
///
/// Each of the returned items is a tuple of the physical address and the
/// paging level. It is helpful when you want to map a physical address range
/// into the provided virtual address.
///
/// For example, on x86-64, `C: PageTableConfig` may specify level 1 page as
/// 4KiB, level 2 page as 2MiB, and level 3 page as 1GiB. Suppose that the
/// supplied physical address range is from `0x3fdff000` to `0x80002000`,
/// and the virtual address is also `0x3fdff000`, the following 5 items will
/// be returned:
///
/// ```text
/// 0x3fdff000                                                 0x80002000
/// start                                                             end
///   |----|----------------|--------------------------------|----|----|
///    4KiB      2MiB                       1GiB              4KiB 4KiB
/// ```
///
/// # Panics
///
/// Panics if:
///  - any of `va`, `pa`, or `len` is not aligned to the base page size;
///  - the range `va..(va + len)` is not valid for the page table.
#[verifier::external_body]
pub fn largest_pages<C: PageTableConfig>(
    mut va: Vaddr,
    mut pa: Paddr,
    mut len: usize,
) -> impl Iterator<Item = (Paddr, PagingLevel)> {
    assert_eq!(va % C::BASE_PAGE_SIZE(), 0);
    assert_eq!(pa % C::BASE_PAGE_SIZE(), 0);
    assert_eq!(len % C::BASE_PAGE_SIZE(), 0);
    assert!(is_valid_range::<C>(&(va..(va + len))));

    core::iter::from_fn(
        move ||
            {
                if len == 0 {
                    return None;
                }
                let mut level = C::HIGHEST_TRANSLATION_LEVEL();
                while page_size(level) > len || va % page_size(level) != 0 || pa % page_size(level)
                    != 0 {
                    level -= 1;
                }

                let item_start = pa;
                va += page_size(level);
                pa += page_size(level);
                len -= page_size(level);

                Some((item_start, level))
            },
    )
}

/// Gets the managed virtual addresses range for the page table.
///
/// It returns a [`RangeInclusive`] because the end address, if being
/// [`Vaddr::MAX`], overflows [`Range<Vaddr>`].
#[verifier::external_body]
fn top_level_index_width<C: PageTableConfig>() -> usize {
    C::ADDRESS_WIDTH() - pte_index_bit_offset::<C>(C::NR_LEVELS())
}

/// Concrete positional start of the VA range: `idx_range.start * 2^offset`.
#[verifier::external_body]
fn pt_va_range_start<C: PageTableConfig>() -> (ret: Vaddr)
    ensures
        ret as int == C::TOP_LEVEL_INDEX_RANGE_spec().start as int * pow2(
            pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat,
        ) as int,
{
    C::TOP_LEVEL_INDEX_RANGE().start << pte_index_bit_offset::<C>(C::NR_LEVELS())
}

/// Concrete positional end of the VA range (inclusive):
/// `(idx_range.end * 2^offset) - 1`, with wrap semantics when
/// `idx_range.end * 2^offset == 2^64` (e.g. kernel top-level with all
/// entries mapped — `2^64 - 1 = usize::MAX`).
#[verifier::external_body]
fn pt_va_range_end<C: PageTableConfig>() -> (ret: Vaddr)
    ensures
        ret as int == (C::TOP_LEVEL_INDEX_RANGE_spec().end as int * pow2(
            pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat,
        ) as int - 1) % 0x1_0000_0000_0000_0000int,
{
    C::TOP_LEVEL_INDEX_RANGE().end.unbounded_shl(
        pte_index_bit_offset::<C>(C::NR_LEVELS()) as u32,
    ).wrapping_sub(1)  // Inclusive end.

}

/// Test whether bit `ADDRESS_WIDTH - 1` of `va` is set.
#[verifier::external_body]
fn sign_bit_of_va<C: PageTableConfig>(va: Vaddr) -> (ret: bool)
    ensures
        ret == ((va as int / pow2((C::ADDRESS_WIDTH() - 1) as nat) as int) % 2 == 1),
{
    (va >> (C::ADDRESS_WIDTH() - 1)) & 1 != 0
}

/// Trait-level invariant the upstream enforces via `const` assertions in
/// `vaddr_range`'s prologue. Captured here as an axiom so we can use it in
/// proofs (Verus has no `const { ... }` form for trait constants).
///
/// `idx.start < 2^(ADDRESS_WIDTH - offset)` and `idx.end <= 2^(...)`
/// together bound the positional VA at `pt_va_range_start` /
/// `pt_va_range_end` by `2^ADDRESS_WIDTH`.
pub axiom fn axiom_top_level_index_range_bounds<C: PageTableConfig>()
    ensures
        (C::TOP_LEVEL_INDEX_RANGE_spec().start as int) < (pow2(
            (C::ADDRESS_WIDTH() as int - pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS())) as nat,
        ) as int),
        C::TOP_LEVEL_INDEX_RANGE_spec().end as int <= pow2(
            (C::ADDRESS_WIDTH() as int - pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS())) as nat,
        ) as int,
        pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) <= C::ADDRESS_WIDTH() as int,
        pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) >= 0,
        // Non-empty index range: idx.start < idx.end (matches the upstream
        // `const` assertion).
        (C::TOP_LEVEL_INDEX_RANGE_spec().start as int) < (
        C::TOP_LEVEL_INDEX_RANGE_spec().end as int),
        // 64-bit hardware bound (Rust `usize` is 64 bits on supported targets).
        C::ADDRESS_WIDTH() as int <= 64,
;

/// Per-config relationship between `LEADING_BITS_spec` and the sign-ext
/// branch of `vaddr_range`: a non-zero `LEADING_BITS` requires both
/// `VA_SIGN_EXT` and that bit `ADDRESS_WIDTH - 1` of `pt_va_range_start`
/// is set. Equivalently (contrapositive), if either of those fails, then
/// `LEADING_BITS == 0`.
///
/// For `UserPtConfig` (`LB=0`) the conclusion is vacuous; for
/// `KernelPtConfig` (`LB=0xffff`, `idx.start=256`, `off=39`,
/// `ADDRESS_WIDTH=48`), `2^47 / 2^47 % 2 == 1` and `VA_SIGN_EXT == true`
/// — so the implication holds.
pub axiom fn axiom_leading_bits_only_when_high_half<C: PageTableConfig>()
    ensures
        C::LEADING_BITS_spec() != 0usize ==> (C::VA_SIGN_EXT() && (((
        C::TOP_LEVEL_INDEX_RANGE_spec().start as int) * (pow2(
            pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat,
        ) as int)) / (pow2((C::ADDRESS_WIDTH() - 1) as nat) as int)) % 2 == 1),
;

#[verifier::inline]
pub open spec fn pte_index_bit_offset_spec<C: PagingConstsTrait>(level: PagingLevel) -> int {
    (C::BASE_PAGE_SIZE().ilog2() as int) + (nr_pte_index_bits::<C>() as int) * (level as int - 1)
}

/// Spec for the managed virtual address range (exclusive end).
/// For configs without VA_SIGN_EXT (e.g. UserPtConfig) or when the base range has sign bit 0.
/// Configs with sign extension (e.g. KernelPtConfig) use a wrapped range in exec;
/// we use an axiom to connect that case.
#[verifier::inline]
pub open spec fn vaddr_range_spec<C: PageTableConfig>() -> Range<Vaddr> {
    let idx_range = C::TOP_LEVEL_INDEX_RANGE_spec();
    let offset = pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat;
    let start = (idx_range.start as int) * pow2(offset);
    let end_inclusive = (idx_range.end as int) * pow2(offset) - 1;
    (start as Vaddr)..((end_inclusive + 1) as Vaddr)
}

/// Spec for whether a range is within the page table's managed address space.
#[verifier::inline]
pub open spec fn is_valid_range_spec<C: PageTableConfig>(r: &Range<Vaddr>) -> bool {
    let va_range = vaddr_range_spec::<C>();
    (r.start == 0 && r.end == 0) || (va_range.start <= r.start && r.end > 0 && r.end - 1
        <= va_range.end - 1)
}

/// Gets the managed virtual addresses range for the page table.
///
/// Returns a [`RangeInclusive`] because the end address, when the range
/// reaches the top of the 64-bit address space (e.g. the canonical
/// high-half kernel range ending at `usize::MAX`), would overflow the
/// exclusive end of a [`Range<Vaddr>`].
fn vaddr_range<C: PageTableConfig>() -> (ret: RangeInclusive<Vaddr>)
    ensures
        ret@.start == vaddr_range_bounds_spec::<C>().0,
        ret@.end == vaddr_range_bounds_spec::<C>().1,
        ret@.exhausted == false,
{
    let mut start = pt_va_range_start::<C>();
    let mut end = pt_va_range_end::<C>();

    proof {
        lemma_vaddr_range_bounds_spec_unfold::<C>();
        axiom_top_level_index_range_bounds::<C>();
        crate::specs::mm::page_table::vaddr_range_proofs::lemma_idx_times_pow2_bound::<C>(
            start,
            end,
        );
    }
    let pt_start = pt_va_range_start::<C>();
    let va_sign_ext = C::VA_SIGN_EXT();
    let sign_bit_set = sign_bit_of_va::<C>(pt_start);
    if va_sign_ext && sign_bit_set {
        start = apply_sign_ext::<C>(start);
        end = apply_sign_ext::<C>(end);
    } else {
        proof {
            // The if-condition was false, so either va_sign_ext is false
            // or sign_bit_set is false. The contrapositive of
            // `axiom_leading_bits_only_when_high_half` gives LEADING_BITS == 0.
            axiom_leading_bits_only_when_high_half::<C>();
            assert(!va_sign_ext || !sign_bit_set);
            // Bridge exec bool to spec form. `va_sign_ext == C::VA_SIGN_EXT()`
            // by `when_used_as_spec`; `sign_bit_set == ((pt_start as int /
            // 2^(aw-1)) % 2 == 1)` by `sign_bit_of_va`'s ensures.
            assert(va_sign_ext == C::VA_SIGN_EXT());
            let off = pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat;
            let aw_m1 = (C::ADDRESS_WIDTH() - 1) as nat;
            let i_start = C::TOP_LEVEL_INDEX_RANGE_spec().start as int;
            let p_off = pow2(off) as int;
            let p_aw_m1 = pow2(aw_m1) as int;
            assert(pt_start as int == i_start * p_off);
            assert(sign_bit_set == ((pt_start as int / p_aw_m1) % 2 == 1));
            assert(sign_bit_set == ((i_start * p_off / p_aw_m1) % 2 == 1));
            // Now invoke the axiom's contrapositive form explicitly.
            if C::LEADING_BITS_spec() != 0usize {
                assert(C::VA_SIGN_EXT() && ((i_start * p_off / p_aw_m1) % 2 == 1));
                assert(va_sign_ext);
                assert(sign_bit_set);
                assert(false);
            }
            assert(C::LEADING_BITS_spec() == 0usize);
        }
    }
    proof {
        // Both branches now establish the equation
        //   start as int == lb * 2^48 + idx.start * 2^off
        //   end as int   == lb * 2^48 + idx.end * 2^off - 1
        // matching the unfolded `vaddr_range_bounds_spec`.
        assert(start as int == (C::LEADING_BITS_spec() as int) * 0x1_0000_0000_0000int + (
        C::TOP_LEVEL_INDEX_RANGE_spec().start as int) * (pow2(
            pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat,
        ) as int));
        assert(end as int == (C::LEADING_BITS_spec() as int) * 0x1_0000_0000_0000int + (
        C::TOP_LEVEL_INDEX_RANGE_spec().end as int) * (pow2(
            pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat,
        ) as int) - 1);
    }
    RangeInclusive::new(start, end)
}

/// Apply the sign-extension OR to a positional value.
///
/// For any value `va` in `[0, 2^ADDRESS_WIDTH)` with bit `ADDRESS_WIDTH - 1`
/// set, the OR with `!0 ^ ((1 << ADDRESS_WIDTH) - 1)` is equivalent to
/// adding `LEADING_BITS_spec() * 2^48`, because the mask's bits and `va`'s
/// bits are disjoint.
///
/// The helper is `external_body` only so Verus doesn't need to verify the
/// bit-level OR; the ensures states the arithmetic equivalent.
#[verifier::external_body]
fn apply_sign_ext<C: PageTableConfig>(va: Vaddr) -> (ret: Vaddr)
    requires
        (va as int) < pow2(C::ADDRESS_WIDTH() as nat) as int,
    ensures
        ret as int == va as int + C::LEADING_BITS_spec() as int * 0x1_0000_0000_0000int,
{
    let sign_ext_mask = !0 ^ ((1usize << C::ADDRESS_WIDTH()) - 1);
    va | sign_ext_mask
}

/// Checks if the given range is covered by the valid range of the page table.
#[verifier::external_body]
fn is_valid_range<C: PageTableConfig>(r: &Range<Vaddr>) -> (ret: bool)
    ensures
        ret == is_valid_range_spec::<C>(r),
{
    let va_range = vaddr_range::<C>();
    (r.start == 0 && r.end == 0) || (*va_range.start() <= r.start && r.end - 1 <= *va_range.end())
}

/// Sanity-check: for x86_64 kernel PT, `vaddr_range_spec` evaluates to the
/// low-half `[2^47, 2^48)` window. The exec path (`vaddr_range`) applies
/// sign extension on top of this and wraps at `usize::MAX + 1`, which is
/// the "KNOWN BUG" referenced in `vm_space::unmap`. See
/// `vaddr_range_bounds_spec` below for the overflow-free formulation.
pub(crate) proof fn lemma_vaddr_range_spec_kernel()
    ensures
        vaddr_range_spec::<KernelPtConfig>() == (
        0x0000_8000_0000_0000_usize..0x0001_0000_0000_0000_usize),
{
    use vstd::arithmetic::power2::{lemma2_to64, lemma2_to64_rest, lemma_pow2_adds};
    lemma2_to64();
    lemma2_to64_rest();
    lemma_usize_pow2_ilog2(12);
    assert(PagingConsts::BASE_PAGE_SIZE().ilog2() == 12u32);
    assert(nr_subpage_per_huge::<PagingConsts>() == 512_usize);
    lemma_usize_pow2_ilog2(9);
    assert(nr_pte_index_bits::<PagingConsts>() == 9_usize);
    assert(pte_index_bit_offset_spec::<PagingConsts>(4) == 39);
    lemma_pow2_adds(8, 39);
    lemma_pow2_adds(9, 39);
    assert((256 as int) * pow2(39) == pow2(47));
    assert((512 as int) * pow2(39) == pow2(48));
}

/// Canonical bounds of the VA range managed by a page-table config,
/// returned as inclusive `(start, end_inclusive)`. `end_inclusive` may
/// equal `usize::MAX` for sign-extended kernel configs, which is why the
/// inclusive form is used — `Range<Vaddr>` cannot represent that.
///
/// Derived from `LEADING_BITS_spec` and `TOP_LEVEL_INDEX_RANGE_spec`. For
/// `UserPtConfig` `(LEADING_BITS=0, idx=0..256)` this is `(0, 2^47 - 1)`;
/// for `KernelPtConfig` `(LEADING_BITS=0xffff, idx=256..512)` this is
/// `(0xffff_8000_0000_0000, 0xffff_ffff_ffff_ffff)`.
pub closed spec fn vaddr_range_bounds_spec<C: PageTableConfig>() -> (Vaddr, Vaddr) {
    let idx = C::TOP_LEVEL_INDEX_RANGE_spec();
    let off = pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat;
    let lb = C::LEADING_BITS_spec() as int;
    let base = lb * 0x1_0000_0000_0000int;
    let start = (base + (idx.start as int) * pow2(off)) as usize;
    let end_inclusive = (base + (idx.end as int) * pow2(off) - 1) as usize;
    (start, end_inclusive)
}

/// Reveal the body of `vaddr_range_bounds_spec` at a call site without
/// making the function itself open (which causes z3-context pollution in
/// cursor invariants).
pub proof fn lemma_vaddr_range_bounds_spec_unfold<C: PageTableConfig>()
    ensures
        vaddr_range_bounds_spec::<C>() == {
            let idx = C::TOP_LEVEL_INDEX_RANGE_spec();
            let off = pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat;
            let lb = C::LEADING_BITS_spec() as int;
            let base = lb * 0x1_0000_0000_0000int;
            let start = (base + (idx.start as int) * pow2(off)) as usize;
            let end_inclusive = (base + (idx.end as int) * pow2(off) - 1) as usize;
            (start, end_inclusive)
        },
{
}

/// Sanity-check: for x86_64 user PT, the bounds are
/// `(0, 0x0000_7FFF_FFFF_FFFF)`, i.e. the low-half 47-bit user VA space.
pub(crate) proof fn lemma_vaddr_range_bounds_spec_user()
    ensures
        vaddr_range_bounds_spec::<crate::mm::vm_space::UserPtConfig>() == (
            0_usize,
            0x0000_7FFF_FFFF_FFFF_usize,
        ),
{
    use vstd::arithmetic::power2::{lemma2_to64, lemma2_to64_rest, lemma_pow2_adds};
    lemma2_to64();
    lemma2_to64_rest();
    lemma_usize_pow2_ilog2(12);
    lemma_usize_pow2_ilog2(9);
    lemma_pow2_adds(8, 39);
    assert(nr_subpage_per_huge::<PagingConsts>() == 512_usize);
    assert(nr_pte_index_bits::<PagingConsts>() == 9_usize);
    assert(pte_index_bit_offset_spec::<PagingConsts>(4) == 39);
    assert((0 as int) * pow2(39) == 0);
    assert((256 as int) * pow2(39) == pow2(47));
    assert(pow2(47) as int - 1 == 0x0000_7FFF_FFFF_FFFF_int);
    // UserPtConfig: LEADING_BITS = 0 via trait default.
    assert(<crate::mm::vm_space::UserPtConfig as PageTableConfig>::LEADING_BITS_spec() == 0_usize);
}

/// Sanity-check: for x86_64 kernel PT, the bounds are the canonical
/// upper half `(0xFFFF_8000_0000_0000, 0xFFFF_FFFF_FFFF_FFFF)`.
pub(crate) proof fn lemma_vaddr_range_bounds_spec_kernel()
    ensures
        vaddr_range_bounds_spec::<KernelPtConfig>() == (
            0xFFFF_8000_0000_0000_usize,
            0xFFFF_FFFF_FFFF_FFFF_usize,
        ),
{
    use vstd::arithmetic::power2::{lemma2_to64, lemma2_to64_rest, lemma_pow2_adds};
    lemma2_to64();
    lemma2_to64_rest();
    lemma_usize_pow2_ilog2(12);
    lemma_usize_pow2_ilog2(9);
    lemma_pow2_adds(8, 39);
    lemma_pow2_adds(9, 39);
    assert(nr_subpage_per_huge::<PagingConsts>() == 512_usize);
    assert(nr_pte_index_bits::<PagingConsts>() == 9_usize);
    assert(PagingConsts::BASE_PAGE_SIZE().ilog2() == 12u32);
    assert(pte_index_bit_offset_spec::<PagingConsts>(4) == 39);
    assert((256 as int) * pow2(39) == pow2(47));
    assert((512 as int) * pow2(39) == pow2(48));
    assert(0xffff_int * 0x1_0000_0000_0000int + pow2(47) as int == 0xffff_8000_0000_0000int);
    assert(0xffff_int * 0x1_0000_0000_0000int + pow2(48) as int - 1 == 0xffff_ffff_ffff_ffffint);
}

// Here are some const values that are determined by the paging constants.
/// The index of a VA's PTE in a page table node at the given level.
#[verifier::external_body]
fn pte_index<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel) -> (res: usize)
    ensures
        res == AbstractVaddr::from_vaddr(va).index[level - 1],
{
    (va >> pte_index_bit_offset::<C>(level)) & (nr_subpage_per_huge::<C>() - 1)
}

/// The bit offset of the entry offset part in a virtual address.
///
/// This function returns the bit offset of the least significant bit. Take
/// x86-64 as an example, the `pte_index_bit_offset(2)` should return 21, which
/// is 12 (the 4KiB in-page offset) plus 9 (index width in the level-1 table).
#[verifier::external_body]
fn pte_index_bit_offset<C: PagingConstsTrait>(level: PagingLevel) -> usize {
    C::BASE_PAGE_SIZE().ilog2() as usize + nr_pte_index_bits::<C>() * (level as usize - 1)
}

/*
impl PageTable<UserPtConfig> {
    pub fn activate(&self) {
        // SAFETY: The user mode page table is safe to activate since the kernel
        // mappings are shared.
        unsafe {
            self.root.activate();
        }
    }
}*/

impl PageTable<KernelPtConfig> {
    /// Panic condition for [`Self::create_user_page_table`]:
    /// Some kernel root entry at index `i` in `TOP_LEVEL_INDEX_RANGE` is
    /// not a page table node (i.e., is absent or maps a huge frame).
    pub open spec fn create_user_pt_panic_condition(root_owner: NodeOwner<KernelPtConfig>) -> bool {
        exists|i: usize|
            #![trigger root_owner.children_perm.value()[i as int]]
            KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().start <= i
                < KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end && {
                let pte = root_owner.children_perm.value()[i as int];
                ||| !pte.is_present()
                ||| pte.is_last(root_owner.level)
            }
    }

    /// Create a new kernel page table.
    #[verifier::external_body]
    pub(crate) fn new_kernel_page_table() -> Self {
        unimplemented!()/*        let kpt = Self::empty();

        // Make shared the page tables mapped by the root table in the kernel space.
        {
            let preempt_guard = disable_preempt();
            let mut root_node = kpt.root.borrow().lock(&preempt_guard);

            for i in KernelPtConfig::TOP_LEVEL_INDEX_RANGE {
                let mut root_entry = root_node.entry(i);
                let _ = root_entry.alloc_if_none(&preempt_guard).unwrap();
            }
        }

        kpt*/

    }

    /// Create a new user page table.
    ///
    /// This should be the only way to create the user page table, that is to
    /// duplicate the kernel page table with all the kernel mappings shared.
    #[verus_spec(r =>
        with Tracked(kernel_owner): Tracked<&PageTableOwner<KernelPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards_k): Tracked<&mut Guards<'static, KernelPtConfig>>,
            Tracked(guards_u): Tracked<&mut Guards<'static, UserPtConfig>>,
        requires
            kernel_owner.inv(),
            old(regions).inv(),
            kernel_owner.0.value.node is Some,
            !Self::create_user_pt_panic_condition(kernel_owner.0.value.node.unwrap()),
            // The kernel page table's root frame matches the tracked owner.
            self.root.ptr.addr() == kernel_owner.0.value.node.unwrap().meta_perm.addr(),
            // The kernel root entry is sound with respect to the meta regions.
            kernel_owner.0.value.metaregion_sound(*old(regions)),
            // The whole kernel page-table tree is sound: every entry's metaregion
            // bookkeeping matches `old(regions)`. Needed to derive each child's
            // soundness inside the loop body.
            kernel_owner.metaregion_sound(*old(regions)),
            // The kernel root is not currently locked.
            old(guards_k).unlocked(kernel_owner.0.value.node.unwrap().meta_perm.addr()),
    )]
    pub(in crate::mm) fn create_user_page_table<G: InAtomicMode + 'static>(
        &'static self,
    ) -> PageTable<UserPtConfig> {
        let preempt_guard: &G = disable_preempt::<G>();

        proof_decl! {
            let tracked mut new_pt_owner: Option<PageTableOwner<UserPtConfig>> = None;
        }
        let ghost regions_before_alloc = *regions;
        let new_pt: PageTable<UserPtConfig> = (
        #[verus_spec(with Tracked(&mut new_pt_owner), Tracked(regions), Tracked(guards_u))]
        PageTable::empty_with_owner());
        let new_root = new_pt.root;
        // Capture new_idx as a ghost BEFORE the tracked_take below empties new_pt_owner.
        let ghost new_idx_g: usize = crate::specs::mm::frame::mapping::frame_to_index(
            new_pt_owner@.unwrap().0.value.meta_slot_paddr().unwrap(),
        );
        let ghost new_pt_owner_snap = new_pt_owner@.unwrap();
        proof {
            // Transfer metaregion_sound for the kernel root entry from regions_before_alloc
            // to the post-alloc regions. The kernel root is a node, so metaregion_sound
            // only depends on slot_owners (not slots). empty_with_owner only changes one
            // slot_owner (the new PT's), and the kernel root's slot_owner is at a different
            // index, so it is preserved.
            let kern_idx = crate::specs::mm::frame::mapping::frame_to_index(
                kernel_owner.0.value.meta_slot_paddr().unwrap(),
            );
            let new_idx = new_idx_g;
            // The new PT's slot was previously in the free pool, so its index differed
            // from any active node's slot index — including the kernel root's.
            crate::specs::mm::page_table::node::entry_owners::EntryOwner::<
                KernelPtConfig,
            >::active_entry_not_in_free_pool(kernel_owner.0.value, regions_before_alloc, new_idx);
            assert(kern_idx != new_idx);
            assert(regions.slot_owners[kern_idx] == regions_before_alloc.slot_owners[kern_idx]);
            // Tree-wide kernel_owner.metaregion_sound transfer comes from the
            // freshness postcondition of empty_with_owner.
            assert(kernel_owner.metaregion_sound(*regions));
            // Capture freshness of new_idx in slots: empty_with_owner's
            // postcondition says new_idx is no longer in regions.slots.
            assert(!regions.slots.contains_key(new_idx));
        }

        proof_decl! {
            let tracked root_owner: &NodeOwner<KernelPtConfig>
                = kernel_owner.0.borrow_value().node.tracked_borrow();
            let tracked root_perm: &MetaPerm<PageTablePageMeta<KernelPtConfig>>
                = &root_owner.meta_perm;
            let tracked mut new_pt_owner_val: PageTableOwner<UserPtConfig>
                = new_pt_owner.tracked_take();
            let tracked mut new_node_owner: NodeOwner<UserPtConfig>
                = new_pt_owner_val.0.value.node.tracked_take();
            let tracked mut entry_owner: &EntryOwner<KernelPtConfig>;
        }

        // Discharge borrow/lock preconditions for the kernel root from
        // kernel_owner.inv() + metaregion_sound + guards unlocked.
        proof {
            assert(kernel_owner.0.value.is_node());
            assert(kernel_owner.0.value.metaregion_sound(*regions));
        }
        let ghost regions_before_self_borrow: MetaRegionOwners = *regions;
        let mut root_node = {
            #[verus_spec(with Tracked(regions), Tracked(root_perm))]
            let root_ref = self.root.borrow();
            #[verus_spec(with Tracked(root_owner), Tracked(guards_k))]
            root_ref.lock(preempt_guard)
        };
        let ghost regions_after_kroot_borrow: MetaRegionOwners = *regions;
        let mut new_node: PageTableGuard<'static, UserPtConfig> = {
            #[verus_spec(with Tracked(regions), Tracked(&new_node_owner.meta_perm))]
            let new_ref = new_root.borrow();
            #[verus_spec(with Tracked(&new_node_owner), Tracked(guards_u))]
            new_ref.lock(preempt_guard)
        };
        proof {
            // Each `borrow` adjusts raw_count to 1 at one slot index. For the kernel
            // root, raw_count was already 1 (its expected_raw_count, given !in_scope),
            // so slot_owners is in fact fully preserved. For the new PT, the slot
            // index is `new_idx`, which is disjoint from any kernel-tree entry's
            // index.
            //
            // Step 1: kernel root borrow. Show slot_owners is fully equal.
            // From metaregion_sound, raw_count == expected_raw_count == 1 (kernel
            // root has !in_scope, so expected is 1). The borrow's postcondition
            // says raw_count == 1 after, plus all other fields preserved at kern_idx,
            // plus all other indices unchanged. So slot_owners is fully equal as a Map.
            let kern_idx = crate::specs::mm::frame::mapping::frame_to_index(
                kernel_owner.0.value.meta_slot_paddr().unwrap(),
            );
            assert(regions_before_self_borrow.slot_owners
                =~= regions_after_kroot_borrow.slot_owners) by {
                assert(regions_before_self_borrow.slot_owners[kern_idx].raw_count == 1);
                assert(regions_after_kroot_borrow.slot_owners[kern_idx].raw_count == 1);
            }
            // Slots: kern_idx was NOT in regions_before_self_borrow.slots (it was
            // owned by the NodeOwner; active_entry_not_in_free_pool gives no active
            // node has its idx in the free pool). So at k == kern_idx the precondition
            // is vacuously true. At k != kern_idx, borrow preserves the value.
            assert forall|k: usize|
                regions_before_self_borrow.slots.contains_key(
                    k,
                ) implies regions_before_self_borrow.slots[k]
                == #[trigger] regions_after_kroot_borrow.slots[k] by {
                if k == kern_idx {
                    crate::specs::mm::page_table::node::entry_owners::EntryOwner::<
                        KernelPtConfig,
                    >::active_entry_not_in_free_pool(
                        kernel_owner.0.value,
                        regions_before_self_borrow,
                        k,
                    );
                }
            };
            kernel_owner.metaregion_sound_preserved_slot_owners_eq(
                regions_before_self_borrow,
                regions_after_kroot_borrow,
            );
            // Step 2: transfer across the new pt borrow.
            let new_idx = new_idx_g;
            // From empty_with_owner postcondition: new_idx was in
            // regions_before_alloc.slots. Use this to derive kern_idx != new_idx
            // via active_entry_not_in_free_pool.
            assert(regions_before_alloc.slots.contains_key(new_idx));
            assert(kern_idx != new_idx) by {
                crate::specs::mm::page_table::node::entry_owners::EntryOwner::<
                    KernelPtConfig,
                >::active_entry_not_in_free_pool(
                    kernel_owner.0.value,
                    regions_before_alloc,
                    new_idx,
                );
            };
            // After empty_with_owner, new_idx is removed from regions.slots; that
            // state is captured as regions_before_self_borrow (no slots changes
            // happened in the intervening proof_decl block).
            assert(!regions_before_self_borrow.slots.contains_key(new_idx));
            // The kernel root borrow doesn't change contains_key at indices !=
            // kern_idx (Frame::borrow's strengthened postcondition), so new_idx
            // is still absent.
            assert(!regions_after_kroot_borrow.slots.contains_key(new_idx));
            // Now slots-preservation for the lemma is vacuous at k == new_idx.
            assert forall|k: usize|
                regions_after_kroot_borrow.slots.contains_key(
                    k,
                ) implies regions_after_kroot_borrow.slots[k] == #[trigger] regions.slots[k] by {
                if k != new_idx {
                    // borrow preserves slots[k] at k != self.index() == new_idx
                }
            };
            // Instantiate the freshness postconditions of empty_with_owner with
            // kt = *kernel_owner. The forall in empty_with_owner's postcondition
            // ranges over `kt: PageTableOwner<KernelPtConfig>`; trigger it via
            // `kt.metaregion_sound(*old(regions))`.
            assert(kernel_owner.metaregion_sound(regions_before_alloc));
            // The freshness predicate we have (`sub_idx != new_idx`) needs to be
            // weakened to the lemma's predicate (`sub_idx != new_idx || (slot
            // still in r1.slots ...)`). Use map_implies to transfer.
            kernel_owner.0.map_implies(
                kernel_owner.0.value.path,
                |
                    e: crate::specs::mm::page_table::node::entry_owners::EntryOwner<KernelPtConfig>,
                    p: vstd_extra::ghost_tree::TreePath<NR_ENTRIES>,
                |
                    e.is_frame() && e.parent_level > 1 ==> {
                        let pa = e.frame.unwrap().mapped_pa;
                        let nr_pages = crate::mm::page_table::cursor::page_size_spec(e.parent_level)
                            / crate::specs::arch::mm::PAGE_SIZE;
                        forall|j: usize|
                            0 < j < nr_pages ==> {
                                let sub_idx =
                                    #[trigger] crate::specs::mm::frame::mapping::frame_to_index(
                                    (pa + j * crate::specs::arch::mm::PAGE_SIZE) as usize,
                                );
                                sub_idx != new_idx
                            }
                    },
                |
                    e: crate::specs::mm::page_table::node::entry_owners::EntryOwner<KernelPtConfig>,
                    p: vstd_extra::ghost_tree::TreePath<NR_ENTRIES>,
                |
                    e.is_frame() && e.parent_level > 1 ==> {
                        let pa = e.frame.unwrap().mapped_pa;
                        let nr_pages = crate::mm::page_table::cursor::page_size_spec(e.parent_level)
                            / crate::specs::arch::mm::PAGE_SIZE;
                        forall|j: usize|
                            0 < j < nr_pages ==> {
                                let sub_idx =
                                    #[trigger] crate::specs::mm::frame::mapping::frame_to_index(
                                    (pa + j * crate::specs::arch::mm::PAGE_SIZE) as usize,
                                );
                                sub_idx != new_idx || (regions.slots.contains_key(sub_idx)
                                    && regions.slot_owners[sub_idx].inner_perms.ref_count.value()
                                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                                    && regions.slot_owners[sub_idx].inner_perms.ref_count.value()
                                    > 0)
                            }
                    },
            );
            kernel_owner.metaregion_sound_preserved_one_slot_changed(
                regions_after_kroot_borrow,
                *regions,
                new_idx,
            );
        }
        let mut i: usize = KernelPtConfig::TOP_LEVEL_INDEX_RANGE().start;
        while i < KernelPtConfig::TOP_LEVEL_INDEX_RANGE().end
            invariant
                kernel_owner.inv(),
                kernel_owner.0.value.node is Some,
                regions.inv(),
                !Self::create_user_pt_panic_condition(kernel_owner.0.value.node.unwrap()),
                i <= KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end,
                KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().start <= i,
                // Lock postcondition for the kernel root.
                *root_owner == kernel_owner.0.value.node.unwrap(),
                root_owner.relate_guard(root_node),
                // Tree-wide soundness of the kernel page table.
                kernel_owner.metaregion_sound(*regions),
                // The new node owner's invariants and guard relation.
                new_node_owner.inv(),
                new_node_owner.relate_guard(new_node),
            decreases KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end - i,
        {
            proof {
                let kern_node = kernel_owner.0.value.node.unwrap();
                assert forall|j: usize|
                    #![trigger kern_node.children_perm.value()[j as int]]
                    KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().start <= j
                        < KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end implies {
                    let pte = kern_node.children_perm.value()[j as int];
                    pte.is_present() && !pte.is_last(kern_node.level)
                } by {
                    let pte = kern_node.children_perm.value()[j as int];
                    if !pte.is_present() || pte.is_last(kern_node.level) {
                        assert(Self::create_user_pt_panic_condition(kern_node));
                    }
                }

                kernel_owner.pt_inv_unroll(i as int);
                let tracked child_opt: &Option<OwnerSubtree<KernelPtConfig>> =
                    kernel_owner.0.children.tracked_borrow(i as int);
                let tracked child_subtree: &OwnerSubtree<KernelPtConfig> =
                    child_opt.tracked_borrow();
                entry_owner = child_subtree.borrow_value();
                let kern_node = kernel_owner.0.value.node.unwrap();
                assert(entry_owner.match_pte(
                    kern_node.children_perm.value()[i as int],
                    entry_owner.parent_level,
                ));
                assert(entry_owner.parent_level == kern_node.level);
                assert(child_subtree.inv());
                assert(entry_owner.inv());
                assert(!entry_owner.in_scope);
                assert(root_owner.relate_guard(root_node));

                kernel_owner.0.map_unroll_once(
                    kernel_owner.0.value.path,
                    PageTableOwner::<KernelPtConfig>::metaregion_sound_pred(*regions),
                    i as int,
                );
                assert(child_subtree.tree_predicate_map(
                    kernel_owner.0.value.path.push_tail(i as usize),
                    PageTableOwner::<KernelPtConfig>::metaregion_sound_pred(*regions),
                ));
                assert(entry_owner.metaregion_sound(*regions));
            }

            #[verus_spec(with Tracked(root_owner), Tracked(entry_owner))]
            let root_entry = root_node.entry(i);
            let ghost pre_to_ref_regions: MetaRegionOwners = *regions;
            #[verus_spec(with Tracked(entry_owner), Tracked(root_owner), Tracked(regions))]
            let child = root_entry.to_ref();

            // Derive `child is PageTable` from entry_owner.is_node() (forced by the
            // panic condition) and ChildRef::wf's case discrimination.
            proof {
                let kern_node = kernel_owner.0.value.node.unwrap();
                let pte = kern_node.children_perm.value()[i as int];
                // From the negation of the panic condition: every in-range slot is
                // present and not is_last. Provide `i` as the existential witness.
                assert(pte.is_present() && !pte.is_last(kern_node.level)) by {
                    if !pte.is_present() || pte.is_last(kern_node.level) {
                        assert(KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().start <= i
                            < KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end);
                        assert(exists|j: usize|
                            KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().start <= j
                                < KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end && {
                                let p = #[trigger] kern_node.children_perm.value()[j as int];
                                ||| !p.is_present()
                                ||| p.is_last(kern_node.level)
                            });
                        assert(Self::create_user_pt_panic_condition(kern_node));
                    }
                }
                // entry_owner.match_pte(pte, parent_level) + (present && !is_last)
                // ⟹ entry_owner.is_node().
                assert(entry_owner.is_node());
                // ChildRef::invariants(entry_owner, regions) gives child.wf(entry_owner).
                // For the Frame and None variants, wf requires is_frame() or is_absent(),
                // contradicting is_node(). Hence child must be PageTable.
                assert(child is PageTable);
                // to_ref's borrow_paddr preserves slot_owners exactly and only
                // grows `slots` (existing keys preserved). Use the tree-wide
                // preservation lemma.
                kernel_owner.metaregion_sound_preserved_slot_owners_eq(
                    pre_to_ref_regions,
                    *regions,
                );
            }
            let pt = match child {
                ChildRef::PageTable(pt) => pt,
                _ => vstd::pervasive::unreached(),
            };

            #[verus_spec(with Tracked(&entry_owner.node.tracked_borrow().meta_perm.points_to))]
            let pt_addr = pt.start_paddr();
            let pte = PageTableEntry::new_pt(pt_addr);

            #[verus_spec(with Tracked(&mut new_node_owner))]
            new_node.write_pte(i, pte);

            i = i + 1;
        }

        PageTable::<UserPtConfig> { root: new_root }
    }/*
    /// Protect the given virtual address range in the kernel page table.
    ///
    /// This method flushes the TLB entries when doing protection.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the protection operation does not affect
    /// the memory safety of the kernel.
    pub unsafe fn protect_flush_tlb(
        &self,
        vaddr: &Range<Vaddr>,
        mut op: impl FnMut(&mut PageProperty),
    ) -> Result<(), PageTableError> {
        let preempt_guard = disable_preempt();
        let mut cursor = CursorMut::new(self, &preempt_guard, vaddr)?;
        // SAFETY: The safety is upheld by the caller.
        while let Some(range) =
            unsafe { cursor.protect_next(vaddr.end - cursor.virt_addr(), &mut op) }
        {
            crate::arch::mm::tlb_flush_addr(range.start);
        }
        Ok(())
    }*/

}

#[verus_verify]
impl<C: PageTableConfig> PageTable<C> {
    pub uninterp spec fn root_paddr_spec(&self) -> Paddr;

    /// Create a new empty page table.
    ///
    /// Useful for the IOMMU page tables only.
    #[verifier::external_body]
    pub fn empty() -> Self {
        unimplemented!()
    }

    /// Create a new empty page table together with its tracked ownership.
    #[verifier::external_body]
    #[verus_spec(r =>
        with Tracked(owner): Tracked<&mut Option<PageTableOwner<C>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'static, C>>,
        requires
            old(regions).inv(),
        ensures
            final(owner)@ is Some,
            final(owner)@.unwrap().inv(),
            final(owner)@.unwrap().0.value.is_node(),
            final(owner)@.unwrap().0.value.node is Some,
            r.root.ptr.addr() == final(owner)@.unwrap().0.value.node.unwrap().meta_perm.addr(),
            final(owner)@.unwrap().0.value.metaregion_sound(*final(regions)),
            final(regions).inv(),
            final(guards).unlocked(final(owner)@.unwrap().0.value.node.unwrap().meta_perm.addr()),
            // The newly allocated slot was in the free pool before the call.
            old(regions).slots.contains_key(
                crate::specs::mm::frame::mapping::frame_to_index(
                    final(owner)@.unwrap().0.value.meta_slot_paddr().unwrap())),
            // After the alloc, the slot is removed from the free pool (now owned
            // by the new pt's NodeOwner).
            !final(regions).slots.contains_key(
                crate::specs::mm::frame::mapping::frame_to_index(
                    final(owner)@.unwrap().0.value.meta_slot_paddr().unwrap())),
            // Other slots and lock state are preserved.
            forall |i: usize| #![trigger final(regions).slot_owners[i]]
                i != crate::specs::mm::frame::mapping::frame_to_index(
                    final(owner)@.unwrap().0.value.meta_slot_paddr().unwrap())
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
            forall |a: usize| old(guards).lock_held(a) ==> final(guards).lock_held(a),
            forall |idx: usize| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                final(regions).slot_owners[idx].paths_in_pt
                    == old(regions).slot_owners[idx].paths_in_pt,
            // Allocation preserves the soundness of the kernel page-table tree:
            // a fresh allocation cannot collide with any active node or frame entry
            // (the allocator returns a slot that wasn't in use). Stated as a
            // postcondition because deriving it requires a freshness axiom on the
            // underlying frame allocator.
            forall |kt: PageTableOwner<KernelPtConfig>|
                #![trigger kt.metaregion_sound(*final(regions))]
                kt.inv() && kt.metaregion_sound(*old(regions))
                ==> kt.metaregion_sound(*final(regions)),
            // Freshness: the new PT's slot index is not used (as a primary slot
            // or huge-frame sub-page slot) by any entry in any KernelPtConfig PT
            // tree that was sound before the alloc. Used to discharge the borrow
            // step that mutates `slot_owners[new_idx]`.
            forall |kt: PageTableOwner<KernelPtConfig>|
                #![trigger kt.metaregion_sound(*old(regions))]
                kt.inv() && kt.metaregion_sound(*old(regions)) ==>
                kt.0.tree_predicate_map(
                    kt.0.value.path,
                    |e: crate::specs::mm::page_table::node::entry_owners::EntryOwner<KernelPtConfig>,
                     p: vstd_extra::ghost_tree::TreePath<NR_ENTRIES>|
                        e.meta_slot_paddr() is Some
                            ==> crate::specs::mm::frame::mapping::frame_to_index(
                                e.meta_slot_paddr().unwrap()) !=
                                crate::specs::mm::frame::mapping::frame_to_index(
                                    final(owner)@.unwrap().0.value.meta_slot_paddr().unwrap()),
                ),
            // Sub-page freshness: for any huge frame entry in any pre-existing
            // sound KernelPtConfig tree, the new PT's slot index isn't a sub-page
            // slot of the huge frame either. Same allocator-freshness rationale.
            forall |kt: PageTableOwner<KernelPtConfig>|
                #![trigger kt.metaregion_sound(*old(regions))]
                kt.inv() && kt.metaregion_sound(*old(regions)) ==>
                kt.0.tree_predicate_map(
                    kt.0.value.path,
                    |e: crate::specs::mm::page_table::node::entry_owners::EntryOwner<KernelPtConfig>,
                     p: vstd_extra::ghost_tree::TreePath<NR_ENTRIES>|
                        e.is_frame() && e.parent_level > 1 ==> {
                            let pa = e.frame.unwrap().mapped_pa;
                            let nr_pages = crate::mm::page_table::cursor::page_size_spec(
                                e.parent_level) / crate::specs::arch::mm::PAGE_SIZE;
                            forall |j: usize| 0 < j < nr_pages ==> {
                                let sub_idx =
                                    #[trigger] crate::specs::mm::frame::mapping::frame_to_index(
                                        (pa + j * crate::specs::arch::mm::PAGE_SIZE) as usize);
                                sub_idx != crate::specs::mm::frame::mapping::frame_to_index(
                                    final(owner)@.unwrap().0.value.meta_slot_paddr().unwrap())
                            }
                        },
                ),
    )]
    pub fn empty_with_owner() -> Self {
        unimplemented!()
    }

    #[verifier::external_body]
    pub(in crate::mm) unsafe fn first_activate_unchecked(&self) {
        unimplemented!()
        // SAFETY: The safety is upheld by the caller.
        //        unsafe { self.root.first_activate() };

    }

    /// The physical address of the root page table.
    ///
    /// Obtaining the physical address of the root page table is safe, however, using it or
    /// providing it to the hardware will be unsafe since the page table node may be dropped,
    /// resulting in UAF.
    #[verifier::external_body]
    #[verifier::when_used_as_spec(root_paddr_spec)]
    pub fn root_paddr(&self) -> (r: Paddr)
        returns
            self.root_paddr_spec(),
    {
        unimplemented!()
        //        self.root.start_paddr()

    }

    /// Query about the mapping of a single byte at the given virtual address.
    ///
    /// Note that this function may fail reflect an accurate result if there are
    /// cursors concurrently accessing the same virtual address range, just like what
    /// happens for the hardware MMU walk.
    #[cfg(ktest)]
    pub fn page_walk(&self, vaddr: Vaddr) -> Option<(Paddr, PageProperty)> {
        // SAFETY: The root node is a valid page table node so the address is valid.
        unsafe { page_walk::<C>(self.root_paddr(), vaddr) }
    }

    /// Create a new cursor exclusively accessing the virtual address range for mapping.
    ///
    /// If another cursor is already accessing the range, the new cursor may wait until the
    /// previous cursor is dropped.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<PageTableOwner<C>>,
            Ghost(root_guard): Ghost<PageTableGuard<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            // Per-config tightening; see `Cursor::new`.
            va.end as int <= C::LOCKED_END_BOUND_spec(),
        ensures
            Cursor::<C, G>::cursor_new_success_conditions(va) ==> {
                &&& r is Ok
                &&& r.unwrap().0.0.invariants(*r.unwrap().1, *final(regions), *final(guards))
                &&& r.unwrap().1.in_locked_range()
                &&& r.unwrap().0.0.level < r.unwrap().0.0.guard_level
                &&& r.unwrap().0.0.guard_level == NR_LEVELS as PagingLevel
                &&& r.unwrap().0.0.va < r.unwrap().0.0.barrier_va.end
                &&& r.unwrap().0.0.va == va.start
                &&& r.unwrap().0.0.barrier_va == *va
            },
            !Cursor::<C, G>::cursor_new_success_conditions(va) ==> r is Err,
            forall |item: C::Item| #![trigger CursorMut::<'rcu, C, G>::item_not_mapped(item, *old(regions))]
                CursorMut::<'rcu, C, G>::item_not_mapped(item, *old(regions)) ==>
                CursorMut::<'rcu, C, G>::item_not_mapped(item, *final(regions)),
            // cursor_mut only locks page-table node slots; paths_in_pt is unchanged for all slots.
            forall |idx: usize| #![auto]
                (*final(regions)).slot_owners[idx].paths_in_pt == (*old(regions)).slot_owners[idx].paths_in_pt,
    )]
    #[verifier::external_body]
    pub fn cursor_mut<'rcu, G: InAtomicMode>(
        &'rcu self,
        guard: &'rcu G,
        va: &Range<Vaddr>,
    ) -> Result<(CursorMut<'rcu, C, G>, Tracked<CursorOwner<'rcu, C>>), PageTableError> {
        #[verus_spec(with Tracked(owner), Ghost(root_guard), Tracked(regions), Tracked(guards))]
        CursorMut::new(self, guard, va)
    }

    /// Create a new cursor exclusively accessing the virtual address range for querying.
    ///
    /// If another cursor is already accessing the range, the new cursor may wait until the
    /// previous cursor is dropped. The modification to the mapping by the cursor may also
    /// block or be overridden by the mapping of another cursor.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<PageTableOwner<C>>,
            Ghost(root_guard): Ghost<PageTableGuard<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            owner.inv(),
            // Per-config tightening; see `Cursor::new`.
            va.end as int <= C::LOCKED_END_BOUND_spec(),
        ensures
            Cursor::<C, G>::cursor_new_success_conditions(va) ==> {
                &&& r is Ok
                &&& r.unwrap().0.invariants(*r.unwrap().1, *final(regions), *final(guards))
                &&& r.unwrap().1.in_locked_range()
                &&& r.unwrap().0.level == r.unwrap().0.guard_level
                &&& r.unwrap().0.va < r.unwrap().0.barrier_va.end
                &&& r.unwrap().0.va == va.start
                &&& r.unwrap().0.barrier_va == *va
                &&& r.unwrap().1@.as_page_table_owner() == owner
                &&& r.unwrap().1@.continuations[3].path() == owner.0.value.path
            },
            !Cursor::<C, G>::cursor_new_success_conditions(va) ==> r is Err,
            forall|idx: usize| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                old(regions).slot_owners[idx].inner_perms.ref_count.value()
                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                ==> final(regions).slot_owners[idx].paths_in_pt
                        == old(regions).slot_owners[idx].paths_in_pt,
            // Non-saturation preservation.
            (forall |i: usize| #![trigger old(regions).slot_owners[i]]
                old(regions).slot_owners.contains_key(i)
                && old(regions).slot_owners[i].inner_perms.ref_count.value()
                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                ==> old(regions).slot_owners[i].inner_perms.ref_count.value() + 1
                    < crate::specs::mm::frame::meta_owners::REF_COUNT_MAX)
            ==>
            (forall |i: usize| #![trigger final(regions).slot_owners[i]]
                final(regions).slot_owners.contains_key(i)
                && final(regions).slot_owners[i].inner_perms.ref_count.value()
                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                ==> final(regions).slot_owners[i].inner_perms.ref_count.value() + 1
                    < crate::specs::mm::frame::meta_owners::REF_COUNT_MAX),
    )]
    pub fn cursor<'rcu, G: InAtomicMode>(&'rcu self, guard: &'rcu G, va: &Range<Vaddr>) -> Result<
        (Cursor<'rcu, C, G>, Tracked<CursorOwner<'rcu, C>>),
        PageTableError,
    > {
        #[verus_spec(with Tracked(owner), Ghost(root_guard), Tracked(regions), Tracked(guards))]
        Cursor::new(self, guard, va)
    }/*
    /// Create a new reference to the same page table.
    /// The caller must ensure that the kernel page table is not copied.
    /// This is only useful for IOMMU page tables. Think twice before using it in other cases.
    pub unsafe fn shallow_copy(&self) -> Self {
        PageTable {
            root: self.root.clone(),
        }
    }
    */

}

/// A software emulation of the MMU address translation process.
///
/// This method returns the physical address of the given virtual address and
/// the page property if a valid mapping exists for the given virtual address.
///
/// # Safety
///
/// The caller must ensure that the `root_paddr` is a pointer to a valid root
/// page table node.
///
/// # Notes on the page table use-after-free problem
///
/// Neither the hardware MMU nor the software page walk method acquires the page
/// table locks while reading. They can enter a to-be-recycled page table node
/// and read the page table entries after the node is recycled and reused.
///
/// For the hardware MMU page walk, we mitigate this problem by dropping the page
/// table nodes only after the TLBs have been flushed on all the CPUs that
/// activate the page table.
///
/// For the software page walk, we only need to disable preemption at the beginning
/// since the page table nodes won't be recycled in the RCU critical section.
#[cfg(ktest)]
pub(super) unsafe fn page_walk<C: PageTableConfig>(root_paddr: Paddr, vaddr: Vaddr) -> Option<
    (Paddr, PageProperty),
> {
    use super::paddr_to_vaddr;

    let _rcu_guard = disable_preempt();

    let mut pt_addr = paddr_to_vaddr(root_paddr);
    #[verusfmt::skip]
    for cur_level in (1..= C::NR_LEVELS()).rev() {
        let offset = pte_index::<C>(vaddr, cur_level);
        // SAFETY:
        //  - The page table node is alive because (1) the root node is alive and
        //    (2) all child nodes cannot be recycled because we're in the RCU critical section.
        //  - The index is inside the bound, so the page table entry is valid.
        //  - All page table entries are aligned and accessed with atomic operations only.
        let cur_pte = unsafe { load_pte((pt_addr as *mut C::E).add(offset), Ordering::Acquire) };

        if !cur_pte.is_present() {
            return None;
        }
        if cur_pte.is_last(cur_level) {
            debug_assert!(cur_level <= C::HIGHEST_TRANSLATION_LEVEL);
            return Some(
                (cur_pte.paddr() + (vaddr & (page_size::<C>(cur_level) - 1)), cur_pte.prop()),
            );
        }
        pt_addr = paddr_to_vaddr(cur_pte.paddr());
    }

    unreachable!("All present PTEs at the level 1 must be last-level PTEs");
}

/// Loads a page table entry with an atomic instruction.
///
/// # Verification Design
/// ## Preconditions
/// - The pointer must be a valid pointer to the array that represents the page table node.
/// - The array must be initialized at the target index.
/// ## Postconditions
/// - The value is loaded from the array at the given index.
/// ## Safety
/// - We require the caller to provide a permission token to ensure that this function is only called on a valid array
/// and the pointer is in bounds.
/// - Like an `AtomicUsize::load` in normal Rust, this function assumes that the value being loaded is an integer
/// (and therefore can be safely cloned). We model the PTE as an abstract type, but in all actual implementations it is an
/// integer. Importantly, it does not include any data that is unsafe to duplicate.
#[verifier::external_body]
#[verus_spec(
    with Tracked(perm): Tracked<&vstd_extra::array_ptr::PointsTo<E, NR_ENTRIES>>
    requires
        perm.is_init(ptr.index as int),
        perm.addr() == ptr.addr(),
        0 <= ptr.index < NR_ENTRIES,
    returns
        perm.value()[ptr.index as int],
)]
pub fn load_pte<E: PageTableEntryTrait>(
    ptr: vstd_extra::array_ptr::ArrayPtr<E, NR_ENTRIES>,
    ordering: Ordering,
) -> (pte: E) {
    unimplemented!()
}

/// Stores a page table entry with an atomic instruction.
///
/// # Verification Design
/// We axiomatize this function as a store operation in the array that represents the page table node.
/// ## Preconditions
/// - The pointer must be a valid pointer to the array that represents the page table node.
/// - The array must be initialized so that the verifier knows that it remains initialized after the store.
/// ## Postconditions
/// - The new value is stored in the array at the given index.
/// ## Safety
/// - We require the caller to provide a permission token to ensure that this function is only called on a valid array
/// and the pointer is in bounds.
#[verifier::external_body]
#[verus_spec(
    with Tracked(perm): Tracked<&mut vstd_extra::array_ptr::PointsTo<E, NR_ENTRIES>>
    requires
        old(perm).addr() == ptr.addr(),
        0 <= ptr.index < NR_ENTRIES,
        old(perm).is_init_all(),
    ensures
        final(perm).value()[ptr.index as int] == new_val,
        final(perm).value() == old(perm).value().update(ptr.index as int, new_val),
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init_all(),
)]
pub fn store_pte<E: PageTableEntryTrait>(
    ptr: vstd_extra::array_ptr::ArrayPtr<E, NR_ENTRIES>,
    new_val: E,
    ordering: Ordering,
);

} // verus!
