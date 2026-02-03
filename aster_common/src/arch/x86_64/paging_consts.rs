use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use vstd_extra::prelude::*;

use super::*;

verus! {

#[derive(Debug, Default)]
pub struct PagingConsts {}

impl Clone for PagingConsts {
    fn clone(&self) -> (res: Self)
        returns
            *self,
    {
        PagingConsts {  }
    }
}

impl PagingConstsTrait for PagingConsts {
    // Expansion for BASE_PAGE_SIZE
    #[verifier::inline]
    open spec fn BASE_PAGE_SIZE_spec() -> usize {
        4096
    }

    proof fn lemma_BASE_PAGE_SIZE_properties()
        ensures
            0 < Self::BASE_PAGE_SIZE_spec(),
            is_pow2(Self::BASE_PAGE_SIZE_spec() as int),
    {
        lemma_pow2_is_pow2_to64();
    }

    #[inline(always)]
    fn BASE_PAGE_SIZE() -> (res: usize)
        ensures
            res == Self::BASE_PAGE_SIZE_spec(),
    {
        proof {
            Self::lemma_BASE_PAGE_SIZE_properties();
        }
        4096
    }

    // Expansion for NR_LEVELS
    #[verifier::inline]
    open spec fn NR_LEVELS_spec() -> PagingLevel {
        4
    }

    #[inline(always)]
    fn NR_LEVELS() -> (res: PagingLevel)
        ensures
            res == Self::NR_LEVELS_spec(),
    {
        4
    }

    // Expansion for ADDRESS_WIDTH
    #[verifier::inline]
    open spec fn ADDRESS_WIDTH_spec() -> usize {
        48
    }

    #[inline(always)]
    fn ADDRESS_WIDTH() -> (res: usize)
        ensures
            res == Self::ADDRESS_WIDTH_spec(),
    {
        48
    }

    // Expansion for HIGHEST_TRANSLATION_LEVEL
    #[verifier::inline]
    open spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel {
        2
    }

    #[inline(always)]
    fn HIGHEST_TRANSLATION_LEVEL() -> (res: PagingLevel)
        ensures
            res == Self::HIGHEST_TRANSLATION_LEVEL_spec(),
    {
        2
    }

    #[verifier::inline]
    open spec fn VA_SIGN_EXT_spec() -> bool {
        true
    }

    #[inline(always)]
    fn VA_SIGN_EXT() -> bool {
        true
    }

    // Expansion for PTE_SIZE
    #[verifier::inline]
    open spec fn PTE_SIZE_spec() -> usize {
        8
    }

    proof fn lemma_PTE_SIZE_properties()
        ensures
            0 < Self::PTE_SIZE_spec() <= Self::BASE_PAGE_SIZE(),
            is_pow2(Self::PTE_SIZE_spec() as int),
    {
        lemma_pow2_is_pow2_to64();
    }

    #[inline(always)]
    fn PTE_SIZE() -> (res: usize)
        ensures
            res == Self::PTE_SIZE_spec(),
    {
        proof {
            Self::lemma_PTE_SIZE_properties();
        }
        8
    }
}

} // verus!
