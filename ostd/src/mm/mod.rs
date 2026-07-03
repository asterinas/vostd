// SPDX-License-Identifier: MPL-2.0
//! Virtual memory (VM).
use crate::specs::arch::*;
use vstd::arithmetic::div_mod::{group_div_basics, lemma_div_non_zero};
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

pub use self::io::{
    Fallible, FallibleVmRead, FallibleVmWrite, Infallible, PodOnce, VmIo, VmIoOnce, VmReader,
    VmWriter,
};
#[doc(hidden)]
pub use crate::arch::mm::PagingConsts;

// Re-export paddr_to_vaddr from kspace
#[doc(hidden)]
pub use self::kspace::paddr_to_vaddr;

// Re-export largest_pages from page_table
#[doc(hidden)]
pub use page_table::largest_pages;

/// The level of a page table node or a frame.
pub type PagingLevel = u8;

verus! {

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
    /// FIXME： General architecture support.
    /// All configs in vostd use the same value for the per-config
    /// `NR_LEVELS()` as the architecture-level constant `NR_LEVELS`
    /// (= 4 for x86_64). This is *implicit* in the cursor framework:
    /// `CursorOwner::inv()` hardcodes `self.level <= NR_LEVELS` (const)
    /// for cursors over any `C: PagingConstsTrait`, so a config whose
    /// `NR_LEVELS_spec()` exceeded `NR_LEVELS` would be unusable. This
    /// lemma exposes that equality as a usable fact so generic proofs
    /// can chain `level != C::NR_LEVELS_spec()` to `level < NR_LEVELS`
    /// (e.g. `Cursor::find_next_impl`'s PageTable-branch gate ⟹
    /// `CursorMut::take_next`'s `replace_cur_entry` discharge).
    proof fn lemma_paging_consts_requirements()
        ensures
            0 < Self::BASE_PAGE_SIZE() / Self::PTE_SIZE() <= Self::BASE_PAGE_SIZE(),
            // Copied from the postcondition of `lemma_paging_consts_requirements`
            // so that we only need to call this lemma in proofs.
            0 < Self::BASE_PAGE_SIZE(),
            is_pow2(Self::BASE_PAGE_SIZE() as int),
            Self::NR_LEVELS() > 0,
            is_pow2(Self::PTE_SIZE() as int),
            0 < Self::PTE_SIZE() <= Self::BASE_PAGE_SIZE(),
            0 < Self::ADDRESS_WIDTH() < usize::BITS,
            Self::BASE_PAGE_SIZE().ilog2() + (Self::BASE_PAGE_SIZE() / Self::PTE_SIZE()).ilog2() * (
            Self::NR_LEVELS() - 1) <= Self::ADDRESS_WIDTH(),
            // The following statement holds for all architectures,
            // but the actual value of the constants may vary.
            Self::BASE_PAGE_SIZE() == PAGE_SIZE,
            Self::NR_LEVELS() == NR_LEVELS,
            Self::BASE_PAGE_SIZE() / Self::PTE_SIZE() == NR_ENTRIES,
            Self::PTE_SIZE() == core::mem::size_of::<usize>(),
    ;

    /// The derived properties of the paging constants.
    ///
    /// NOTE: Implementations of `PagingConstsTrait` do not need to implement this lemma, the proof is automatically inherited from the default implementation.
    proof fn lemma_paging_consts_properties()
        ensures
    // Derived properties.

            0 < Self::BASE_PAGE_SIZE() / Self::PTE_SIZE() <= Self::BASE_PAGE_SIZE(),
            NR_ENTRIES * Self::PTE_SIZE() == PAGE_SIZE,
            // Copied from the postcondition of `lemma_paging_consts_requirements`
            // so that we only need to call this lemma in proofs.
            0 < Self::BASE_PAGE_SIZE(),
            is_pow2(Self::BASE_PAGE_SIZE() as int),
            Self::NR_LEVELS() > 0,
            is_pow2(Self::PTE_SIZE() as int),
            0 < Self::PTE_SIZE() <= Self::BASE_PAGE_SIZE(),
            0 < Self::ADDRESS_WIDTH() < usize::BITS,
            Self::BASE_PAGE_SIZE().ilog2() + (Self::BASE_PAGE_SIZE() / Self::PTE_SIZE()).ilog2() * (
            Self::NR_LEVELS() - 1) <= Self::ADDRESS_WIDTH(),
            // The following statement holds for all architectures,
            // but the actual value of the constants may vary.
            Self::BASE_PAGE_SIZE() == PAGE_SIZE,
            Self::NR_LEVELS() == NR_LEVELS,
            Self::BASE_PAGE_SIZE() / Self::PTE_SIZE() == NR_ENTRIES,
            Self::PTE_SIZE() == core::mem::size_of::<usize>(),
    {
        Self::lemma_paging_consts_requirements();
        broadcast use group_div_basics;

        assert(Self::BASE_PAGE_SIZE() / Self::PTE_SIZE() > 0) by {
            lemma_div_non_zero(Self::BASE_PAGE_SIZE() as int, Self::PTE_SIZE() as int);
        };
    }
}

pub open spec fn page_size_spec(level: PagingLevel) -> usize {
    (PAGE_SIZE * pow2(
        (nr_subpage_per_huge::<PagingConsts>().ilog2() * (level - 1)) as nat,
    )) as usize
}

// /// The page size
// pub const PAGE_SIZE: usize = page_size::<PagingConsts>(1);
/// The page size at a given level.
#[verifier::when_used_as_spec(page_size_spec)]
#[verifier::external_body]
pub fn page_size(level: PagingLevel) -> (ret: usize)
    requires
        1 <= level <= NR_LEVELS + 1,
    ensures
        ret == page_size_spec(level),
        is_pow2(ret as int),
        ret >= PAGE_SIZE,
{
    PAGE_SIZE << (nr_subpage_per_huge::<PagingConsts>().ilog2() as usize * (level as usize - 1))
}

#[verifier::inline]
pub open spec fn nr_subpage_per_huge_spec<C: PagingConstsTrait>() -> usize {
    C::BASE_PAGE_SIZE() / C::PTE_SIZE()
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
