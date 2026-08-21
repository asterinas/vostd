use crate::mm::{Paddr, PagingConstsTrait, Vaddr};
use vstd::prelude::*;

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

} // verus!
