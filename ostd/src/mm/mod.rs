// SPDX-License-Identifier: MPL-2.0
//! Virtual memory (VM).
use crate::specs::arch::CONST_PAGE_SIZE;
use core::fmt::Debug;
use vstd::arithmetic::div_mod::group_div_basics;
use vstd::arithmetic::div_mod::lemma_div_non_zero;
use vstd::layout::is_power_2;
use vstd::prelude::*;
use vstd_extra::extern_const;

/// Virtual addresses.
pub type Vaddr = usize;

/// Physical addresses.
pub type Paddr = usize;

/// The level of a page table node or a frame.
pub type PagingLevel = u8;

/// The maximum value of `PagingConstsTrait::NR_LEVELS`.
pub const MAX_NR_LEVELS: usize = 4;

//pub(crate) mod dma;
pub mod frame;
//pub mod heap;
pub mod io;
pub mod kspace;
pub(crate) mod page_prop;
pub mod page_table;
pub mod pod;
//pub mod tlb;
// pub mod vm_space;

#[cfg(ktest)]
mod test;

use core::ops::Range;

// Import types and constants from arch
pub use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
pub use crate::specs::arch::paging_consts::PagingConsts;

// Re-export paddr_to_vaddr from kspace
pub use kspace::paddr_to_vaddr;

// Re-export largest_pages from page_table
pub use page_table::largest_pages;

/// The maximum virtual address of user space (non inclusive).
///
/// Typical 64-bit systems have at least 48-bit virtual address space.
/// A typical way to reserve half of the address space for the kernel is
/// to use the highest 48-bit virtual address space.
///
/// Also, the top page is not regarded as usable since it's a workaround
/// for some x86_64 CPUs' bugs. See
/// <https://github.com/torvalds/linux/blob/480e035fc4c714fb5536e64ab9db04fedc89e910/arch/x86/include/asm/page_64.h#L68-L78>
/// for the rationale.
extern_const!(
/// Page size.
pub MAX_USERSPACE_VADDR [MAX_USERSPACE_VADDR_SPEC, CONST_MAX_USERSPACE_VADDR]: usize =
    0x0000_8000_0000_0000 - CONST_PAGE_SIZE);

/// The kernel address space.
///
/// There are the high canonical addresses defined in most 48-bit width
/// architectures.
pub const KERNEL_VADDR_RANGE: Range<Vaddr> = 0xffff_8000_0000_0000..0xffff_ffff_ffff_0000;

/// Gets physical address trait
pub trait HasPaddr {
    /// Returns the physical address.
    fn paddr(&self) -> Paddr;
}

/// Checks if the given address is page-aligned.
pub const fn is_page_aligned(p: usize) -> bool {
    (p & (PAGE_SIZE() - 1)) == 0
}

verus! {

#[allow(non_snake_case)]
pub trait PagingConstsTrait: Debug + Sync {
    spec fn BASE_PAGE_SIZE_spec() -> usize;

    proof fn lemma_BASE_PAGE_SIZE_properties()
        ensures
            0 < Self::BASE_PAGE_SIZE_spec(),
            is_power_2(Self::BASE_PAGE_SIZE_spec() as int),
    ;

    /// The smallest page size.
    /// This is also the page size at level 1 page tables.
    #[inline(always)]
    #[verifier::when_used_as_spec(BASE_PAGE_SIZE_spec)]
    fn BASE_PAGE_SIZE() -> (res: usize)
        ensures
            res == Self::BASE_PAGE_SIZE_spec(),
            0 < res,
            is_power_2(res as int),
    ;

    spec fn NR_LEVELS_spec() -> PagingLevel;

    /// The number of levels in the page table.
    /// The numbering of levels goes from deepest node to the root node. For example,
    /// the level 1 to 5 on AMD64 corresponds to Page Tables, Page Directory Tables,
    /// Page Directory Pointer Tables, Page-Map Level-4 Table, and Page-Map Level-5
    /// Table, respectively.
    #[inline(always)]
    #[verifier::when_used_as_spec(NR_LEVELS_spec)]
    fn NR_LEVELS() -> (res: PagingLevel)
        ensures
            res == Self::NR_LEVELS_spec(),
            res > 0,
    ;

    spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel;

    /// The highest level that a PTE can be directly used to translate a VA.
    /// This affects the the largest page size supported by the page table.
    #[inline(always)]
    #[verifier::when_used_as_spec(HIGHEST_TRANSLATION_LEVEL_spec)]
    fn HIGHEST_TRANSLATION_LEVEL() -> (res: PagingLevel)
        ensures
            res == Self::HIGHEST_TRANSLATION_LEVEL_spec(),
    ;

    spec fn PTE_SIZE_spec() -> usize;

    /// The size of a PTE.
    #[inline(always)]
    #[verifier::when_used_as_spec(PTE_SIZE_spec)]
    fn PTE_SIZE() -> (res: usize)
        ensures
            res == Self::PTE_SIZE_spec(),
            is_power_2(res as int),
            0 < res <= Self::BASE_PAGE_SIZE(),
    ;

    proof fn lemma_PTE_SIZE_properties()
        ensures
            0 < Self::PTE_SIZE_spec() <= Self::BASE_PAGE_SIZE(),
            is_power_2(Self::PTE_SIZE_spec() as int),
    ;

    spec fn ADDRESS_WIDTH_spec() -> usize;

    /// The address width may be BASE_PAGE_SIZE.ilog2() + NR_LEVELS * IN_FRAME_INDEX_BITS.
    /// If it is shorter than that, the higher bits in the highest level are ignored.
    #[inline(always)]
    #[verifier::when_used_as_spec(ADDRESS_WIDTH_spec)]
    fn ADDRESS_WIDTH() -> (res: usize)
        ensures
            res == Self::ADDRESS_WIDTH_spec(),
    ;

    /// Whether virtual addresses are sign-extended.
    ///
    /// The sign bit of a [`Vaddr`] is the bit at index [`PagingConstsTrait::ADDRESS_WIDTH`] - 1.
    /// If this constant is `true`, bits in [`Vaddr`] that are higher than the sign bit must be
    /// equal to the sign bit. If an address violates this rule, both the hardware and OSTD
    /// should reject it.
    ///
    /// Otherwise, if this constant is `false`, higher bits must be zero.
    ///
    /// Regardless of sign extension, [`Vaddr`] is always not signed upon calculation.
    /// That means, `0xffff_ffff_ffff_0000 < 0xffff_ffff_ffff_0001` is `true`.
    spec fn VA_SIGN_EXT_spec() -> bool;

    #[inline(always)]
    #[verifier::when_used_as_spec(VA_SIGN_EXT_spec)]
    fn VA_SIGN_EXT() -> bool;
}

#[verifier::inline]
pub open spec fn nr_subpage_per_huge_spec<C: PagingConstsTrait>() -> usize {
    C::BASE_PAGE_SIZE() / C::PTE_SIZE()
}

/// The number of sub pages in a huge page.
#[inline(always)]
#[verifier::when_used_as_spec(nr_subpage_per_huge_spec)]
pub fn nr_subpage_per_huge<C: PagingConstsTrait>() -> (res: usize)
    ensures
        res == nr_subpage_per_huge_spec::<C>(),
{
    C::BASE_PAGE_SIZE() / C::PTE_SIZE()
}

pub proof fn lemma_nr_subpage_per_huge_bounded<C: PagingConstsTrait>()
    ensures
        0 < nr_subpage_per_huge::<C>() <= C::BASE_PAGE_SIZE(),
{
    C::lemma_PTE_SIZE_properties();
    broadcast use group_div_basics;

    assert(C::PTE_SIZE() <= C::BASE_PAGE_SIZE());
    assert(C::BASE_PAGE_SIZE() / C::PTE_SIZE() <= C::BASE_PAGE_SIZE());
    assert(C::BASE_PAGE_SIZE() / C::PTE_SIZE() > 0) by {
        lemma_div_non_zero(C::BASE_PAGE_SIZE() as int, C::PTE_SIZE() as int);
    };
}

} // verus!
