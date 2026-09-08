// SPDX-License-Identifier: MPL-2.0
//! Virtual memory (VM).
use vstd::arithmetic::div_mod::group_div_basics;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

/// Virtual addresses.
pub type Vaddr = usize;

/// Physical addresses.
pub type Paddr = usize;

pub(crate) mod dma;
pub mod frame;
//pub mod heap;
pub mod io;
pub mod kspace;
pub(crate) mod page_prop;
pub mod page_table;
pub mod tlb;
pub mod vm_space;

#[cfg(ktest)]
mod test;

use core::{fmt::Debug, ops::Range};

pub use self::{
    dma::{Daddr, DmaCoherent, /* DmaDirection, DmaStream, DmaStreamSlice, */ HasDaddr},
    frame::{
        Frame,
        allocator::FrameAllocOptions,
        segment::{Segment, USegment},
        unique::UniqueFrame,
        untyped::{AnyUFrameMeta, UFrame, UntypedMem},
    },
    io::{
        Fallible, FallibleVmRead, FallibleVmWrite, Infallible, PodOnce, VmIo, VmIoOnce, VmReader,
        VmWriter,
    },
    page_prop::{CachePolicy, PageFlags, PageProperty},
    vm_space::VmSpace,
};
pub(crate) use self::{
    kspace::paddr_to_vaddr, page_prop::PrivilegedPageFlags, page_table::PageTable,
};
pub(crate) use crate::arch::mm::PagingConsts;
pub use crate::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};

// Re-export largest_pages from page_table
pub(crate) use page_table::largest_pages;

/// The level of a page table node or a frame.
pub type PagingLevel = u8;

verus! {

/// Current verification upper bound for tracked physical addresses.
///
/// This is a memory-model bound, not the architectural physical-address width.
pub const MAX_PADDR: Paddr = 0x8000_0000;

/// Maximum number of base-page frames represented by the current memory model.
pub const MAX_NR_PAGES: u64 = (MAX_PADDR / PAGE_SIZE) as u64;

/// A minimal set of constants that determines the paging system.
/// This provides an abstraction over most paging modes in common architectures.
pub trait PagingConstsTrait: Clone + Debug + Send + Sync + 'static {
    spec fn BASE_PAGE_SIZE_spec() -> usize;

    /// The smallest page size.
    /// This is also the page size at level 1 page tables.
    #[verifier::when_used_as_spec(BASE_PAGE_SIZE_spec)]
    fn BASE_PAGE_SIZE() -> (res: usize)
        returns
            Self::BASE_PAGE_SIZE(),
    ;

    spec fn NR_LEVELS_spec() -> PagingLevel;

    /// The number of levels in the page table.
    /// The numbering of levels goes from deepest node to the root node. For example,
    /// the level 1 to 5 on AMD64 corresponds to Page Tables, Page Directory Tables,
    /// Page Directory Pointer Tables, Page-Map Level-4 Table, and Page-Map Level-5
    /// Table, respectively.
    #[verifier::when_used_as_spec(NR_LEVELS_spec)]
    fn NR_LEVELS() -> (res: PagingLevel)
        returns
            Self::NR_LEVELS(),
    ;

    spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel;

    /// The highest level that a PTE can be directly used to translate a VA.
    /// This affects the the largest page size supported by the page table.
    #[verifier::when_used_as_spec(HIGHEST_TRANSLATION_LEVEL_spec)]
    fn HIGHEST_TRANSLATION_LEVEL() -> PagingLevel
        returns
            Self::HIGHEST_TRANSLATION_LEVEL(),
    ;

    spec fn PTE_SIZE_spec() -> usize;

    /// The size of a PTE.
    #[verifier::when_used_as_spec(PTE_SIZE_spec)]
    fn PTE_SIZE() -> (res: usize)
        returns
            Self::PTE_SIZE(),
    ;

    spec fn ADDRESS_WIDTH_spec() -> usize;

    /// The address width may be BASE_PAGE_SIZE.ilog2() + NR_LEVELS * IN_FRAME_INDEX_BITS.
    /// If it is shorter than that, the higher bits in the highest level are ignored.
    #[verifier::when_used_as_spec(ADDRESS_WIDTH_spec)]
    fn ADDRESS_WIDTH() -> (res: usize)
        returns
            Self::ADDRESS_WIDTH(),
    ;

    spec fn VA_SIGN_EXT_spec() -> bool;

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
    #[verifier::when_used_as_spec(VA_SIGN_EXT_spec)]
    fn VA_SIGN_EXT() -> bool
        returns
            Self::VA_SIGN_EXT(),
    ;

    /// The requirements of the paging constants so that the memory management system can work correctly.
    ///
    /// NOTE: The postcondition is designed to be minimal, to actually be used in proofs, call `lemma_paging_consts_properties`
    /// instead to get all the properties that are derived from the requirements.
    ///
    proof fn lemma_paging_consts_requirements()
        ensures
            0 < Self::BASE_PAGE_SIZE(),
            is_pow2(Self::BASE_PAGE_SIZE() as int),
            Self::NR_LEVELS() > 0,
            is_pow2(Self::PTE_SIZE() as int),
            0 < Self::PTE_SIZE() <= Self::BASE_PAGE_SIZE(),
            0 < Self::ADDRESS_WIDTH() < usize::BITS,
            Self::BASE_PAGE_SIZE().ilog2() + (Self::BASE_PAGE_SIZE() / Self::PTE_SIZE()).ilog2()
                * Self::NR_LEVELS() <= Self::ADDRESS_WIDTH(),
            Self::PTE_SIZE() == core::mem::size_of::<usize>(),
    ;

    /// The derived properties of the paging constants.
    ///
    /// NOTE: Implementations of `PagingConstsTrait` do not need to implement this lemma, the proof is automatically inherited from the default implementation.
    proof fn lemma_paging_consts_properties()
        ensures
    // Derived properties.

            Self::BASE_PAGE_SIZE().ilog2() + (Self::BASE_PAGE_SIZE() / Self::PTE_SIZE()).ilog2() * (
            Self::NR_LEVELS() - 1) <= Self::ADDRESS_WIDTH(),
            0 < Self::BASE_PAGE_SIZE() / Self::PTE_SIZE() <= Self::BASE_PAGE_SIZE(),
            // Copied from the postcondition of `lemma_paging_consts_requirements`
            // so that we only need to call this lemma in proofs.
            0 < Self::BASE_PAGE_SIZE(),
            is_pow2(Self::BASE_PAGE_SIZE() as int),
            Self::NR_LEVELS() > 0,
            is_pow2(Self::PTE_SIZE() as int),
            0 < Self::PTE_SIZE() <= Self::BASE_PAGE_SIZE(),
            0 < Self::ADDRESS_WIDTH() < usize::BITS,
            Self::BASE_PAGE_SIZE().ilog2() + (Self::BASE_PAGE_SIZE() / Self::PTE_SIZE()).ilog2()
                * Self::NR_LEVELS() <= Self::ADDRESS_WIDTH(),
            Self::PTE_SIZE() == core::mem::size_of::<usize>(),
    {
        Self::lemma_paging_consts_requirements();
        broadcast use group_div_basics;

        let base = Self::BASE_PAGE_SIZE() as int;
        let pte = Self::PTE_SIZE() as int;
        let levels = Self::NR_LEVELS() as int;
        let base_bits = Self::BASE_PAGE_SIZE().ilog2() as int;
        let index_bits = (Self::BASE_PAGE_SIZE() / Self::PTE_SIZE()).ilog2() as int;
        assert(0 < base / pte) by {
            vstd::arithmetic::div_mod::lemma_div_non_zero(base, pte);
        };
        assert(base / pte <= base) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(0, base, pte);
        };
        assert(base_bits + index_bits * (levels - 1) <= base_bits + index_bits * levels)
            by (nonlinear_arith)
            requires
                0 <= index_bits,
                1 <= levels,
        ;
    }
}

/// Bridge between a paging configuration and the build-selected architecture.
///
/// This is intentionally separate from [`PagingConstsTrait`]. Public paging
/// types still use build-selected constants in const-generic positions, while
/// generic paging specifications can range over any [`PagingConstsTrait`].
pub trait CurrentPagingConstsTrait: PagingConstsTrait {
    proof fn lemma_current_paging_consts_requirements()
        ensures
            Self::BASE_PAGE_SIZE() == PAGE_SIZE,
            Self::NR_LEVELS() == NR_LEVELS as PagingLevel,
            Self::BASE_PAGE_SIZE() / Self::PTE_SIZE() == NR_ENTRIES,
    ;
}

/// The page-size formula for an explicit paging configuration.
pub open spec fn page_size_for_spec<C: PagingConstsTrait>(level: PagingLevel) -> usize {
    (C::BASE_PAGE_SIZE_spec() * pow2(
        (nr_subpage_per_huge::<C>().ilog2() * (level - 1)) as nat,
    )) as usize
}

/// The page-size formula for the architecture selected by this build.
pub open spec fn page_size_spec(level: PagingLevel) -> usize {
    page_size_for_spec::<PagingConsts>(level)
}

// /// The page size
// pub const PAGE_SIZE: usize = page_size::<PagingConsts>(1);
/// The page size at a given level.
#[verifier::when_used_as_spec(page_size_spec)]
pub fn page_size(level: PagingLevel) -> (ret: usize)
    requires
        1 <= level <= NR_LEVELS + 1,
    ensures
        ret == page_size_spec(level),
        is_pow2(ret as int),
        ret >= PAGE_SIZE,
{
    proof {
        let index_bits: usize = nr_subpage_per_huge::<PagingConsts>().ilog2() as usize;
        PagingConsts::lemma_paging_consts_properties();
        crate::arch::mm::lemma_nr_subpage_per_huge_eq_nr_entries();
        vstd::layout::unsigned_int_max_values();
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        vstd_extra::external::ilog2::lemma_usize_pow2_ilog2(9);
        let level_index: usize = (level - 1) as usize;
        let shift: usize = (index_bits * level_index) as usize;
        let ghost shift_nat = shift as nat;
        let ghost page_shift = 12nat + shift_nat;

        vstd::arithmetic::power2::lemma_pow2_adds(12, shift_nat);
        if page_shift < 48nat {
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(page_shift, 48nat);
        }
        vstd::bits::lemma_usize_shl_is_mul(PAGE_SIZE, shift);
        vstd_extra::external::ilog2::lemma_usize_pow2_shl_is_pow2(PAGE_SIZE, shift);
    }
    PAGE_SIZE << (nr_subpage_per_huge::<PagingConsts>().ilog2() as usize * (level as usize - 1))
}

#[verifier::inline]
pub open spec fn nr_subpage_per_huge_spec<C: PagingConstsTrait>() -> usize {
    C::BASE_PAGE_SIZE_spec() / C::PTE_SIZE_spec()
}

/// The number of sub pages in a huge page.
#[verifier::when_used_as_spec(nr_subpage_per_huge_spec)]
pub fn nr_subpage_per_huge<C: PagingConstsTrait>() -> (res: usize)
    ensures
        res == nr_subpage_per_huge_spec::<C>(),
{
    proof {
        C::lemma_paging_consts_properties();
    }
    C::BASE_PAGE_SIZE() / C::PTE_SIZE()
}

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
pub const MAX_USERSPACE_VADDR: Vaddr = 0x0000_8000_0000_0000_usize - PAGE_SIZE;

/// The kernel address space.
///
/// There are the high canonical addresses defined in most 48-bit width
/// architectures.
pub const KERNEL_VADDR_RANGE: Range<Vaddr> =
    0xffff_8000_0000_0000_usize..0xffff_ffff_ffff_0000_usize;

/// Gets physical address trait
pub trait HasPaddr {
    /// Returns the physical address.
    fn paddr(&self) -> Paddr;
}

/// Checks if the given address is page-aligned.
pub const fn is_page_aligned(p: usize) -> bool {
    (p & (PAGE_SIZE - 1)) == 0
}

} // verus!
