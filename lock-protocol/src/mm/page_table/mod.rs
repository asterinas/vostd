pub mod cursor;
pub mod node;

use cursor::spec_helpers;
use vstd::prelude::*;
pub use node::*;
use core::fmt::Debug;
use std::{marker::PhantomData, ops::Range};

use crate::helpers::{math::lemma_u64_and_less_than};
use vstd_extra::extra_num::lemma_usize_ilog2_to32;

use super::{
    meta::AnyFrameMeta, nr_subpage_per_huge, page_prop::PageProperty, vm_space::Token, Paddr,
    PagingLevel, Vaddr,
};

use crate::exec;

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
pub(crate) unsafe trait PageTableConfig {
    /// The index range at the top level (`C::NR_LEVELS`) page table.
    ///
    /// When configured with this value, the [`PageTable`] instance will only
    /// be allowed to manage the virtual address range that is covered by
    /// this range. The range can be smaller than the actual allowed range
    /// specified by the hardware MMU (limited by `C::ADDRESS_WIDTH`).
    #[verifier::when_used_as_spec(TOP_LEVEL_INDEX_RANGE_spec)]
    fn TOP_LEVEL_INDEX_RANGE() -> Range<usize>;

    spec fn TOP_LEVEL_INDEX_RANGE_spec() -> Range<usize>;

    /// If we can remove the top-level page table entries.
    ///
    /// This is for the kernel page table, whose second-top-level page
    /// tables need `'static` lifetime to be shared with user page tables.
    /// Other page tables do not need to set this to `false`.
    #[verifier::when_used_as_spec(TOP_LEVEL_CAN_UNMAP_spec)]
    fn TOP_LEVEL_CAN_UNMAP() -> bool;

    spec fn TOP_LEVEL_CAN_UNMAP_spec() -> bool;

    /// The type of the page table entry.
    type E: PageTableEntryTrait;

    /// The paging constants.
    type C: PagingConstsTrait;

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
    type Item: Clone;

    /// Consumes the item and returns the physical address, the paging level,
    /// and the page property.
    ///
    /// The ownership of the item will be consumed, i.e., the item will be
    /// forgotten after this function is called.
    fn item_into_raw(item: Self::Item) -> (Paddr, PagingLevel, PageProperty);

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
    unsafe fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item;
}

impl<C: PageTableConfig> PagingConstsTrait for C {
    open spec fn BASE_PAGE_SIZE_SPEC() -> usize {
        C::C::BASE_PAGE_SIZE_SPEC()
    }

    fn BASE_PAGE_SIZE() -> (res: usize) {
        C::C::BASE_PAGE_SIZE()
    }

    open spec fn NR_LEVELS_SPEC() -> PagingLevel {
        C::C::NR_LEVELS_SPEC()
    }

    fn NR_LEVELS() -> (res: PagingLevel) {
        C::C::NR_LEVELS()
    }
}

pub trait PageTableEntryTrait:
// Clone + Copy +
// Default +
// Sized + Send + Sync + 'static
// Debug // TODO: Implement Debug for PageTableEntryTrait
// + Pod + PodOnce // TODO: Implement Pod and PodOnce for PageTableEntryTrait
Sized {
    /// Create a set of new invalid page table flags that indicates an absent page.
    ///
    /// Note that currently the implementation requires an all zero PTE to be an absent PTE.
    // TODO: Implement
    fn new_absent() -> Self;

    /// If the flags are present with valid mappings.
    ///
    /// For PTEs created by [`Self::new_absent`], [`Self::new_token`], this
    /// method should return false. And for PTEs created by [`Self::new_page`]
    /// or [`Self::new_pt`], whatever modified with [`Self::set_prop`] or not,
    /// this method should return true.
    fn is_present(&self, spt: &exec::SubPageTable) -> (res: bool)
        requires
            spt.wf(),
            self.pte_paddr() == exec::get_pte_from_addr(self.pte_paddr(), spt).pte_addr,
            self.frame_paddr() == exec::get_pte_from_addr(self.pte_paddr(), spt).frame_pa,
        ensures
    // spt.ptes@.value().contains_key(self.pte_paddr() as int) == res,

            res ==> spt.ptes@.value().contains_key(self.pte_paddr() as int)
                && spt.frames@.value().contains_key(self.frame_paddr() as int),
            !res ==> !spt.ptes@.value().contains_key(self.pte_paddr() as int),
            spt.wf(),
    ;

    /// Create a new PTE with the given physical address and flags that map to a page.
    fn new_page(
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
        spt: &mut exec::SubPageTable,
        ghost_index: usize,
    ) -> (res: Self)
        requires
            old(spt).wf(),
            spec_helpers::mpt_not_contains_not_allocated_frames(old(spt), ghost_index),
        ensures
            spt.wf(),
            spt.ptes@.instance_id() == old(spt).ptes@.instance_id(),
            spt.frames@.instance_id() == old(spt).frames@.instance_id(),
            spec_helpers::frame_keys_do_not_change(spt, old(spt)),
            spec_helpers::mpt_not_contains_not_allocated_frames(spt, ghost_index),
    ;

    /// Create a new PTE that map to a child page table.
    fn new_pt(paddr: Paddr) -> (res: Self);

    /// Create a new PTE with the given token value but don't map to anything.
    fn new_token(token: Token) -> Self;

    /// Get the physical address the PTE points to.
    /// The physical address recorded in the PTE is either:
    ///  - the physical address of the next level page table;
    ///  - the physical address of the page it maps to;
    ///  - the value of the token.
    #[verifier::when_used_as_spec(frame_paddr_spec)]
    fn frame_paddr(&self) -> Paddr
        returns
            self.frame_paddr_spec(),
    ;

    spec fn frame_paddr_spec(&self) -> Paddr;

    #[verifier::when_used_as_spec(pte_addr_spec)]
    fn pte_paddr(&self) -> Paddr
        returns
            self.pte_addr_spec(),
    ;

    spec fn pte_addr_spec(&self) -> Paddr;

    fn prop(&self) -> PageProperty;

    /// Set the page property of the PTE.
    ///
    /// This will be only done if the PTE is present. If not, this method will
    /// do nothing.
    fn set_prop(&mut self, prop: PageProperty);

    /// Set the physical address of the PTE.
    ///
    /// This can be done for both present and absent PTEs.
    fn set_paddr(&mut self, paddr: Paddr);

    /// If the PTE maps a page rather than a child page table.
    ///
    /// The level of the page table the entry resides is given since architectures
    /// like amd64 only uses a huge bit in intermediate levels.
    fn is_last(&self, level: PagingLevel) -> bool;

    /// Converts the PTE into its corresponding `usize` value.
    // TODO: Implement as_usize and from_usize
    fn as_usize(self) -> usize;

    /// Converts a usize `pte_raw` into a PTE.
    // TODO: Implement as_usize and from_usize
    fn from_usize(pte_raw: usize, spt: &exec::SubPageTable) -> (res: Self)
        requires
            spt.wf(),
        ensures
            res.pte_paddr() == pte_raw as Paddr,
            res.frame_paddr() == exec::get_pte_from_addr_spec(pte_raw, spt).frame_pa,
            res.frame_paddr() == 0 ==> !spt.ptes@.value().contains_key(pte_raw as int),
            res.frame_paddr() != 0 ==> {
                &&& spt.ptes@.value().contains_key(res.pte_paddr() as int)
                &&& spt.ptes@.value()[res.pte_paddr() as int].frame_pa == res.frame_paddr() as int
                &&& spt.frames@.value().contains_key(res.frame_paddr() as int)
            },
    ;
}

/// A minimal set of constants that determines the paging system.
/// This provides an abstraction over most paging modes in common architectures.
pub trait PagingConstsTrait:
    // Clone + Debug + Default + Send + Sync + 'static
Sized {
    spec fn BASE_PAGE_SIZE_SPEC() -> usize;

    // /// The smallest page size.
    // /// This is also the page size at level 1 page tables.
    #[verifier::when_used_as_spec(BASE_PAGE_SIZE_SPEC)]
    fn BASE_PAGE_SIZE() -> (res: usize)
        ensures
            res != 0,
            res == Self::BASE_PAGE_SIZE_SPEC(),
    ;

    spec fn NR_LEVELS_SPEC() -> PagingLevel;

    // /// The number of levels in the page table.
    // /// The numbering of levels goes from deepest node to the root node. For example,
    // /// the level 1 to 5 on AMD64 corresponds to Page Tables, Page Directory Tables,
    // /// Page Directory Pointer Tables, Page-Map Level-4 Table, and Page-Map Level-5
    // /// Table, respectively.
    #[verifier::when_used_as_spec(NR_LEVELS_SPEC)]
    fn NR_LEVELS() -> PagingLevel
        returns
            Self::NR_LEVELS_SPEC(),
    ;  // /
    // The highest level that a PTE can be directly used to translate a VA.
    // /// This affects the the largest page size supported by the page table.
    // const HIGHEST_TRANSLATION_LEVEL: PagingLevel;
    // /// The size of a PTE.
    // const PTE_SIZE: usize;
    // /// The address width may be BASE_PAGE_SIZE.ilog2() + NR_LEVELS * IN_FRAME_INDEX_BITS.
    // /// If it is shorter than that, the higher bits in the highest level are ignored.
    // const ADDRESS_WIDTH: usize;

}

// TODO: This is for x86, create the arch directory and move this to x86/mod.rs
pub(crate) const NR_ENTRIES_PER_PAGE: usize = 512;

// TODO: This is for x86, create the arch directory and move this to x86/mod.rs
// #[derive(Clone, Debug, Default)]
pub struct PagingConsts {}

// TODO: This is for x86, create the arch directory and move this to x86/mod.rs
impl PagingConstsTrait for PagingConsts {
    open spec fn BASE_PAGE_SIZE_SPEC() -> usize {
        4096
    }

    fn BASE_PAGE_SIZE() -> (res: usize) {
        4096
    }

    open spec fn NR_LEVELS_SPEC() -> PagingLevel {
        4
    }

    fn NR_LEVELS() -> (res: PagingLevel) {
        4
    }
    // const ADDRESS_WIDTH: usize = 48;
    // const HIGHEST_TRANSLATION_LEVEL: PagingLevel = 2;
    // const PTE_SIZE: usize = core::mem::size_of::<PageTableEntry>();

}

// Copied from aster_common
// TODO: Check if these are correct
// Here are some const values that are determined by the paging constants.
pub proof fn bits_of_base_page_size()
    ensures
        PagingConsts::BASE_PAGE_SIZE_SPEC().ilog2() == 12,
{
    lemma_usize_ilog2_to32();
}

pub proof fn value_of_nr_subpage_per_huge()
    ensures
// TODO
// nr_subpage_per_huge::<PagingConsts>() == 512,

        nr_subpage_per_huge() == 512,
{
}

pub proof fn bits_of_nr_pte_index()
    ensures
        nr_pte_index_bits::<PagingConsts>() == 9,
{
    value_of_nr_subpage_per_huge();
    lemma_usize_ilog2_to32();
}

#[verifier::inline]
pub open spec fn nr_pte_index_bits_spec<C: PagingConstsTrait>() -> usize {
    // nr_subpage_per_huge::<C>().ilog2() as usize // TODO
    nr_subpage_per_huge().ilog2() as usize
}

/// The number of virtual address bits used to index a PTE in a page.
#[inline(always)]
#[verifier::when_used_as_spec(nr_pte_index_bits_spec)]
pub const fn nr_pte_index_bits<C: PagingConstsTrait>() -> (res: usize)
    ensures
        res == nr_pte_index_bits_spec::<C>(),
{
    // nr_subpage_per_huge::<C>().ilog2() as usize // TODO
    nr_subpage_per_huge().ilog2() as usize
}

#[verifier::inline]
pub open spec fn pte_index_mask_spec() -> usize {
    0x1ff
}

#[inline(always)]
#[verifier::when_used_as_spec(pte_index_mask_spec)]
pub fn pte_index_mask() -> (res: usize)
    ensures
        res == pte_index_mask_spec(),
{
    // nr_subpage_per_huge::<PagingConsts>() - 1 // TODO
    nr_subpage_per_huge() - 1
}

pub open spec fn pte_index_spec(va: Vaddr, level: PagingLevel) -> usize
    recommends
        0 < level <= PagingConsts::NR_LEVELS_SPEC(),
{
    let base_bits = PagingConsts::BASE_PAGE_SIZE_SPEC().ilog2();
    let index_bits = nr_pte_index_bits::<PagingConsts>();
    let shift = base_bits + (level - 1) as u32 * index_bits as u32;
    (va >> shift) & pte_index_mask()
}

#[verifier::when_used_as_spec(pte_index_spec)]
/// The index of a VA's PTE in a page table node at the given level.
// const fn pte_index<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel) -> usize
pub fn pte_index(va: Vaddr, level: PagingLevel) -> (res: usize)  // TODO: type, const
    requires
        0 < level <= PagingConsts::NR_LEVELS_SPEC(),
    ensures
        res == pte_index_spec(va, level),
        res < nr_subpage_per_huge(),
{
    let base_bits = PagingConsts::BASE_PAGE_SIZE().ilog2();
    assert(base_bits == 12) by {
        bits_of_base_page_size();
    };
    let index_bits = nr_pte_index_bits::<PagingConsts>();
    assert(index_bits == 9) by {
        bits_of_nr_pte_index();
    };
    assert(0 <= (level - 1) * index_bits <= 36);
    let shift = base_bits + (level - 1) as u32 * index_bits as u32;
    let res = (va >> shift) as u64 & pte_index_mask() as u64;
    assert(res <= pte_index_mask()) by {
        lemma_u64_and_less_than((va >> shift) as u64, pte_index_mask() as u64);
    };
    res as usize
}

/// A handle to a page table.
/// A page table can track the lifetime of the mapped physical pages.
// TODO: Debug for PageTable
// #[derive(Debug)]
pub struct PageTable<C: PageTableConfig> {
    root: PageTableNode,
    _phantom: PhantomData<C>,
}

} // verus!
