//! Architecture contracts for modeled frames and linear address mappings.
//!
//! # Verified Properties
//!
//! These erased contracts require each architecture instance to prove that its
//! modeled physical-address bound is page-aligned and that its linear mapping
//! has room for those addresses without overflow. The bound limits tracked
//! memory; it does not describe the processor's physical-address width.
//! Physical-to-virtual conversion preserves bounds within the model's linear
//! mapping window. All definitions depend only on the architecture contract.
use vstd::prelude::*;

use crate::mm::{Paddr, PagingConstsTrait, Vaddr};

verus! {

/// The architecture contract for modeled physical frames and their linear mapping.
///
/// The associated paging constants are still supplied by the existing
/// `PagingConstsTrait`; this trait supplies the modeled physical-address bound
/// and the kernel's linear mapping, together with their compatibility proofs.
pub trait ArchAddressSpaceModel {
    type C: PagingConstsTrait;

    /// The exclusive upper bound for modeled physical frame addresses.
    spec fn max_paddr_spec() -> Paddr;

    /// The base of the kernel's physical-to-virtual linear mapping.
    spec fn linear_mapping_base_vaddr_spec() -> Vaddr;

    /// The first virtual address reserved for vmalloc mappings.
    spec fn vmalloc_base_vaddr_spec() -> Vaddr;

    /// Proves that the physical range and linear mapping satisfy the model requirements.
    proof fn lemma_model_requirements()
        ensures
            0 < Self::max_paddr_spec(),
            Self::C::BASE_PAGE_SIZE() <= Self::max_paddr_spec(),
            Self::max_paddr_spec() % Self::C::BASE_PAGE_SIZE() == 0,
            Self::linear_mapping_base_vaddr_spec() % Self::C::BASE_PAGE_SIZE() == 0,
            Self::max_paddr_spec() + Self::linear_mapping_base_vaddr_spec()
                < Self::vmalloc_base_vaddr_spec(),
    ;
}

/// A physical address that can identify a base-page frame for architecture `A`.
pub open spec fn valid_frame_paddr_for<A: ArchAddressSpaceModel>(pa: Paddr) -> bool {
    pa % A::C::BASE_PAGE_SIZE() == 0 && pa < A::max_paddr_spec()
}

/// Convert a physical address through architecture `A`'s linear mapping.
pub open spec fn paddr_to_vaddr_for<A: ArchAddressSpaceModel>(pa: Paddr) -> Vaddr {
    (pa + A::linear_mapping_base_vaddr_spec()) as usize
}

/// Maps a physical offset into the linear mapping window without overflow.
pub proof fn lemma_paddr_to_vaddr_properties_for<A: ArchAddressSpaceModel>(pa: Paddr)
    requires
        pa < A::vmalloc_base_vaddr_spec() - A::linear_mapping_base_vaddr_spec(),
    ensures
        A::linear_mapping_base_vaddr_spec() <= paddr_to_vaddr_for::<A>(pa)
            < A::vmalloc_base_vaddr_spec(),
{
}

} // verus!
