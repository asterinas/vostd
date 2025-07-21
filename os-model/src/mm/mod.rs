use vstd::prelude::*;
use vstd::arithmetic::power2::*;
use vstd_extra::bits_extra::*;

verus! {

global layout usize is size == 8;

// Assuming 64-bit architecture
/// Virtual addresses.
pub type Vaddr = usize;

/// Physical addresses.
pub type Paddr = usize;

/// The level of a page table node or a frame.
pub type PagingLevel = u8;

// A minimal set of constants that determines the paging system.
/// This provides an abstraction over most paging modes in common architectures.
// Clone + Debug + Default + Send + Sync + 'static
#[allow(non_snake_case)]
pub(crate) trait PagingConstsTrait: Sized {
    spec fn base_page_size_width() -> usize;

    spec fn pte_size_width() -> usize;

    open spec fn in_frame_index_width() -> usize {
        (Self::base_page_size_width() - Self::pte_size_width()) as usize
    }

    open spec fn BASE_PAGE_SIZE_spec() -> usize {
        pow2(Self::base_page_size_width() as nat) as usize
    }

    spec fn NR_LEVELS_spec() -> PagingLevel;

    spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel;

    open spec fn PTE_SIZE_spec() -> usize {
        pow2(Self::pte_size_width() as nat) as usize
    }

    spec fn ADDRESS_WIDTH_spec() -> usize;

    spec fn VA_SIGN_EXT_spec() -> bool;

    proof fn lemma_paging_const_properties()
        ensures
            0 < Self::pte_size_width() < Self::base_page_size_width() < Self::ADDRESS_WIDTH_spec()
                <= usize::BITS,
            Self::ADDRESS_WIDTH_spec() == Self::base_page_size_width() + Self::NR_LEVELS()
                * Self::in_frame_index_width(),
            0 < Self::HIGHEST_TRANSLATION_LEVEL() <= Self::NR_LEVELS(),
            Self::BASE_PAGE_SIZE_spec() == pow2(Self::base_page_size_width() as nat) as usize,
            Self::PTE_SIZE_spec() == pow2(Self::pte_size_width() as nat) as usize,
            0 < Self::HIGHEST_TRANSLATION_LEVEL_spec() <= Self::NR_LEVELS_spec(),
    ;

    /// The smallest page size.
    /// This is also the page size at level 1 page tables.
    #[inline(always)]
    #[verifier::when_used_as_spec(BASE_PAGE_SIZE_spec)]
    fn BASE_PAGE_SIZE() -> (res: usize)
        returns
            Self::BASE_PAGE_SIZE_spec(),
    ;

    /// The number of levels in the page table.
    /// The numbering of levels goes from deepest node to the root node. For example,
    /// the level 1 to 5 on AMD64 corresponds to Page Tables, Page Directory Tables,
    /// Page Directory Pointer Tables, Page-Map Level-4 Table, and Page-Map Level-5
    /// Table, respectively.
    #[inline(always)]
    #[verifier::when_used_as_spec(NR_LEVELS_spec)]
    fn NR_LEVELS() -> (res: PagingLevel)
        returns
            Self::NR_LEVELS_spec(),
    ;

    /// The highest level that a PTE can be directly used to translate a VA.
    /// This affects the the largest page size supported by the page table.
    #[inline(always)]
    #[verifier::when_used_as_spec(HIGHEST_TRANSLATION_LEVEL_spec)]
    fn HIGHEST_TRANSLATION_LEVEL() -> (res: PagingLevel)
        returns
            Self::HIGHEST_TRANSLATION_LEVEL_spec(),
    ;

    /// The size of a PTE.
    //#[inline(always)]
    #[verifier::when_used_as_spec(PTE_SIZE_spec)]
    fn PTE_SIZE() -> (res: usize)
        returns
            Self::PTE_SIZE_spec(),
    ;

    /// The address width may be BASE_PAGE_SIZE.ilog2() + NR_LEVELS * IN_FRAME_INDEX_BITS.
    /// If it is shorter than that, the higher bits in the highest level are ignored.
    #[inline(always)]
    #[verifier::when_used_as_spec(ADDRESS_WIDTH_spec)]
    fn ADDRESS_WIDTH() -> (res: usize)
        returns
            Self::ADDRESS_WIDTH_spec(),
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
    #[inline(always)]
    #[verifier::when_used_as_spec(VA_SIGN_EXT_spec)]
    fn VA_SIGN_EXT() -> (res: bool)
        returns
            Self::VA_SIGN_EXT_spec(),
    ;
}

/// The number of sub pages in a huge page.
pub(crate)   /*const*/
fn nr_subpage_per_huge<C: PagingConstsTrait>() -> usize
    returns
        pow2((C::base_page_size_width() - C::pte_size_width()) as nat) as usize,
{
    proof {
        C::lemma_paging_const_properties();
        let page_width = C::base_page_size_width();
        let pte_width = C::pte_size_width();
        lemma_usize_pow2_no_overflow(pte_width as nat);

    }
    C::BASE_PAGE_SIZE() / C::PTE_SIZE()
}

} // verus!
