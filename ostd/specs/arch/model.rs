use crate::mm::{Paddr, PagingConstsTrait, Vaddr};
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd_extra::prelude::lemma_pow2_is_pow2_to64;

verus! {

/// The paging-related part of an architecture contract.
///
/// The associated paging constants are still supplied by the existing
/// `PagingConstsTrait`; this trait only adds the architecture-wide physical
/// address bound and the proof that the two contracts are compatible.
pub trait ArchPagingModel {
    type C: PagingConstsTrait;

    /// The exclusive upper bound for physical frame addresses.
    spec fn max_paddr_spec() -> Paddr;

    proof fn lemma_paging_model_requirements()
        ensures
            0 < Self::max_paddr_spec(),
            Self::C::BASE_PAGE_SIZE() <= Self::max_paddr_spec(),
            Self::max_paddr_spec() % Self::C::BASE_PAGE_SIZE() == 0,
    ;
}

/// A physical address that can identify a base-page frame for architecture `A`.
pub open spec fn valid_frame_paddr_for<A: ArchPagingModel>(pa: Paddr) -> bool {
    pa % A::C::BASE_PAGE_SIZE() == 0 && pa < A::max_paddr_spec()
}

/// The address-space part of an architecture contract.
pub trait ArchAddressSpaceModel: ArchPagingModel {
    /// The base of the kernel's physical-to-virtual linear mapping.
    spec fn linear_mapping_base_vaddr_spec() -> Vaddr;

    /// The first virtual address reserved for vmalloc mappings.
    spec fn vmalloc_base_vaddr_spec() -> Vaddr;

    proof fn lemma_address_space_model_requirements()
        ensures
            Self::linear_mapping_base_vaddr_spec() % Self::C::BASE_PAGE_SIZE() == 0,
            Self::linear_mapping_base_vaddr_spec() < Self::vmalloc_base_vaddr_spec(),
            Self::max_paddr_spec() < Self::vmalloc_base_vaddr_spec()
                - Self::linear_mapping_base_vaddr_spec(),
            Self::max_paddr_spec() + Self::linear_mapping_base_vaddr_spec() < usize::MAX,
    ;
}

/// Convert a physical address through architecture `A`'s linear mapping.
pub open spec fn paddr_to_vaddr_for<A: ArchAddressSpaceModel>(pa: Paddr) -> Vaddr {
    (pa + A::linear_mapping_base_vaddr_spec()) as usize
}

/// Convert a linear-mapped virtual address back to a physical address.
pub open spec fn vaddr_to_paddr_for<A: ArchAddressSpaceModel>(va: Vaddr) -> Paddr {
    (va - A::linear_mapping_base_vaddr_spec()) as usize
}

/// The top-level contract used by architecture-independent specifications.
pub trait ArchTrait: ArchAddressSpaceModel {

}

/// A proof-only Sv39 paging configuration.
///
/// This configuration exercises the generic page-table arithmetic with three
/// translation levels. It is deliberately independent from the RISC-V runtime
/// target, which currently activates Sv48.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Debug, Default)]
pub struct Sv39PagingConsts;

impl PagingConstsTrait for Sv39PagingConsts {
    #[verifier::inline]
    open spec fn BASE_PAGE_SIZE_spec() -> usize {
        4096
    }

    fn BASE_PAGE_SIZE() -> usize {
        4096
    }

    #[verifier::inline]
    open spec fn NR_LEVELS_spec() -> crate::mm::PagingLevel {
        3
    }

    fn NR_LEVELS() -> crate::mm::PagingLevel {
        3
    }

    #[verifier::inline]
    open spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> crate::mm::PagingLevel {
        3
    }

    fn HIGHEST_TRANSLATION_LEVEL() -> crate::mm::PagingLevel {
        3
    }

    #[verifier::inline]
    open spec fn PTE_SIZE_spec() -> usize {
        8
    }

    fn PTE_SIZE() -> usize {
        8
    }

    #[verifier::inline]
    open spec fn ADDRESS_WIDTH_spec() -> usize {
        39
    }

    fn ADDRESS_WIDTH() -> usize {
        39
    }

    #[verifier::inline]
    open spec fn VA_SIGN_EXT_spec() -> bool {
        true
    }

    fn VA_SIGN_EXT() -> bool {
        true
    }

    proof fn lemma_paging_consts_requirements() {
        lemma_pow2_is_pow2_to64();
        lemma2_to64();
        lemma2_to64_rest();
        assert(usize::BITS == 64) by (compute);
        vstd::layout::unsigned_int_max_values();
        vstd_extra::external::ilog2::lemma_usize_pow2_ilog2(9);
        vstd_extra::external::ilog2::lemma_usize_pow2_ilog2(12);
        lemma_pow2_adds(9, 30);
    }
}

/// Regression facts for the generic page-size formula.
pub proof fn lemma_sv39_page_size_formula()
    ensures
        crate::mm::page_size_for_spec::<Sv39PagingConsts>(1) == 4096,
        crate::mm::page_size_for_spec::<Sv39PagingConsts>(2) == 2_097_152,
        crate::mm::page_size_for_spec::<Sv39PagingConsts>(3) == 1_073_741_824,
        crate::mm::page_size_for_spec::<Sv39PagingConsts>(4) == 549_755_813_888,
{
    Sv39PagingConsts::lemma_paging_consts_properties();
    vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
    lemma2_to64();
    lemma2_to64_rest();
    assert(Sv39PagingConsts::BASE_PAGE_SIZE_spec() == 4096usize) by (compute_only);
    assert(Sv39PagingConsts::PTE_SIZE_spec() == 8usize) by (compute_only);
    assert(crate::mm::nr_subpage_per_huge_spec::<Sv39PagingConsts>()
        == Sv39PagingConsts::BASE_PAGE_SIZE_spec() / Sv39PagingConsts::PTE_SIZE_spec());
    assert(crate::mm::nr_subpage_per_huge_spec::<Sv39PagingConsts>() == 512usize) by {
        assert(Sv39PagingConsts::BASE_PAGE_SIZE_spec() / Sv39PagingConsts::PTE_SIZE_spec()
            == 512usize);
    }
    assert(crate::mm::nr_subpage_per_huge_spec::<Sv39PagingConsts>().ilog2() == 9u32) by {
        assert(pow2(9nat) as usize == 512usize);
        vstd_extra::external::ilog2::lemma_usize_pow2_ilog2(9);
    }
    vstd::bits::lemma_usize_pow2_no_overflow(18);
    vstd::bits::lemma_usize_pow2_no_overflow(27);
    assert(pow2(18nat) == 262144nat);
    assert(pow2(27nat) == 134217728nat);
    assert((9u32 * (3u8 - 1u8)) as nat == 18nat) by (compute_only);
    assert((9u32 * (4u8 - 1u8)) as nat == 27nat) by (compute_only);
    assert(crate::mm::page_size_for_spec::<Sv39PagingConsts>(1) == 4096usize);
    assert(crate::mm::page_size_for_spec::<Sv39PagingConsts>(2) == 4096usize * 512usize);
    assert(crate::mm::page_size_for_spec::<Sv39PagingConsts>(3) == 4096usize * 512usize * 512usize);
    assert(crate::mm::page_size_for_spec::<Sv39PagingConsts>(4) == 4096usize * 512usize * 512usize
        * 512usize);
    vstd::bits::lemma_usize_pow2_no_overflow(39);
}

} // verus!
