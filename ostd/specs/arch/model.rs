//! Architecture contracts for modeled frames and linear address mappings.
//!
//! # Verified Properties
//!
//! These erased contracts require each architecture instance to prove that its
//! modeled physical-address bound is page-aligned and that its linear mapping
//! has room for those addresses without overflow. The bound limits tracked
//! memory; it does not describe the processor's physical-address width.
//! Within each architecture's linear mapping window, the address conversions
//! preserve bounds and are mutual inverses. Physical-to-virtual conversion also
//! preserves base-page alignment.
//! `CurrentArch` selects the instance for this target. Paging configurations must
//! prove the layout requirements declared by `PagingConstsTrait`.
use vstd::prelude::*;
use vstd_extra::arithmetic::lemma_mod_0_add;

use crate::mm::{Paddr, PagingConstsTrait, Vaddr};

verus! {

/// The architecture contract for modeled physical frames and their linear mapping.
///
/// The associated paging constants are still supplied by the existing
/// `PagingConstsTrait`; this trait supplies the modeled physical-address bound
/// and the kernel's linear mapping, together with their compatibility proofs.
pub trait ArchAddressSpaceModel {
    type C: PagingConstsTrait;

    /// The exclusive upper bound of the physical address space modeled for this architecture.
    const ARCH_MAX_PADDR: Paddr;

    /// The exclusive upper bound for modeled physical frame addresses.
    const MAX_PADDR: Paddr;

    /// The base of the kernel's physical-to-virtual linear mapping.
    const LINEAR_MAPPING_BASE_VADDR: Vaddr;

    /// The first virtual address reserved for vmalloc mappings.
    const VMALLOC_BASE_VADDR: Vaddr;

    /// Proves that the physical range and linear mapping satisfy the model requirements.
    proof fn lemma_model_requirements()
        ensures
            0 < Self::MAX_PADDR,
            Self::C::BASE_PAGE_SIZE <= Self::MAX_PADDR,
            Self::MAX_PADDR % Self::C::BASE_PAGE_SIZE == 0,
            Self::LINEAR_MAPPING_BASE_VADDR % Self::C::BASE_PAGE_SIZE == 0,
            Self::MAX_PADDR + Self::LINEAR_MAPPING_BASE_VADDR < Self::VMALLOC_BASE_VADDR,
    ;
}

/// A physical address that can identify a base-page frame for architecture `A`.
pub open spec fn valid_frame_paddr_for<A: ArchAddressSpaceModel>(pa: Paddr) -> bool {
    pa % A::C::BASE_PAGE_SIZE == 0 && pa < A::MAX_PADDR
}

/// Convert a physical address through architecture `A`'s linear mapping.
pub open spec fn paddr_to_vaddr_for<A: ArchAddressSpaceModel>(pa: Paddr) -> Vaddr {
    (pa + A::LINEAR_MAPPING_BASE_VADDR) as usize
}

/// Convert a linear-mapped virtual address back to a physical address.
pub open spec fn vaddr_to_paddr_for<A: ArchAddressSpaceModel>(va: Vaddr) -> Paddr {
    (va - A::LINEAR_MAPPING_BASE_VADDR) as usize
}

/// Maps a physical offset into the linear mapping window and back without loss.
pub proof fn lemma_paddr_to_vaddr_properties_for<A: ArchAddressSpaceModel>(pa: Paddr)
    requires
        pa < A::VMALLOC_BASE_VADDR - A::LINEAR_MAPPING_BASE_VADDR,
    ensures
        A::LINEAR_MAPPING_BASE_VADDR <= paddr_to_vaddr_for::<A>(pa) < A::VMALLOC_BASE_VADDR,
        vaddr_to_paddr_for::<A>(paddr_to_vaddr_for::<A>(pa)) == pa,
{
}

/// Maps a linear-mapped virtual address to a physical offset and back without loss.
pub proof fn lemma_vaddr_to_paddr_properties_for<A: ArchAddressSpaceModel>(va: Vaddr)
    requires
        A::LINEAR_MAPPING_BASE_VADDR <= va < A::VMALLOC_BASE_VADDR,
    ensures
        vaddr_to_paddr_for::<A>(va) < A::VMALLOC_BASE_VADDR - A::LINEAR_MAPPING_BASE_VADDR,
        paddr_to_vaddr_for::<A>(vaddr_to_paddr_for::<A>(va)) == va,
{
}

/// Preserves base-page alignment when mapping a physical offset into the linear window.
pub proof fn lemma_paddr_to_vaddr_aligned_for<A: ArchAddressSpaceModel>(pa: Paddr)
    requires
        pa < A::VMALLOC_BASE_VADDR - A::LINEAR_MAPPING_BASE_VADDR,
        pa % A::C::BASE_PAGE_SIZE == 0,
    ensures
        paddr_to_vaddr_for::<A>(pa) % A::C::BASE_PAGE_SIZE == 0,
{
    A::C::lemma_paging_consts_requirements();
    A::lemma_model_requirements();
    lemma_mod_0_add(pa as int, A::LINEAR_MAPPING_BASE_VADDR as int, A::C::BASE_PAGE_SIZE as int);
}

} // verus!
