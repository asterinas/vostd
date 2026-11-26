//! External specifications for the [`x86` crate](https://crates.io/crates/x86)
//! constants and MSR accessors. Constant values are trusted to match
//! the crate sources; the original constants are re-exported below. Also models the
//! [`x86_64` crate](https://docs.rs/x86_64/0.15.5/x86_64/) MSR, address, paging frame,
//! TLB, and CR3 APIs.
//!
//! The `x86_64` address, paging frame, TLB, and CR3 specifications below were audited
//! against `x86_64` 0.15.5 (with default `memory_encryption` disabled):
//! - `src/addr.rs` (`VirtAddr::new`, `PhysAddr::new`)
//! - `src/structures/paging/page.rs` (`PageSize`, `Size4KiB`, `AddressNotAligned`)
//! - `src/structures/paging/frame.rs` (`PhysFrame`, `PhysFrame::from_start_address`)
//! - `src/instructions/tlb.rs` (`tlb::flush`, `tlb::flush_all`)
//! - `src/registers/control.rs` (`Cr3`, `Cr3Flags`, `Cr3::write`)
//!
//! Hardware TLB invalidation and CR3 page-table activation side effects are outside
//! Verus's pure memory model and are not tracked by these contracts.
use vstd::prelude::*;

use core::arch::x86_64::CpuidResult;
use x86::cpuid::CpuIdResult;

pub use x86::{
    apic::xapic::{
        XAPIC_EOI, XAPIC_ESR, XAPIC_ICR0, XAPIC_ICR1, XAPIC_ID, XAPIC_LVT_TIMER, XAPIC_SVR,
        XAPIC_TIMER_CURRENT_COUNT, XAPIC_TIMER_DIV_CONF, XAPIC_TIMER_INIT_COUNT, XAPIC_VERSION,
    },
    msr::{
        IA32_APIC_BASE, IA32_X2APIC_APICID, IA32_X2APIC_CUR_COUNT, IA32_X2APIC_DIV_CONF,
        IA32_X2APIC_EOI, IA32_X2APIC_ESR, IA32_X2APIC_ICR, IA32_X2APIC_INIT_COUNT,
        IA32_X2APIC_LVT_TIMER, IA32_X2APIC_SIVR, IA32_X2APIC_VERSION,
    },
};
use x86_64::{
    PhysAddr, VirtAddr,
    instructions::tlb,
    registers::{
        control::{Cr3, Cr3Flags},
        model_specific::Msr,
    },
    structures::paging::{
        PhysFrame,
        page::{AddressNotAligned, PageSize, Size4KiB},
    },
};

verus! {

/// Exposes the four u32 result registers.
#[verifier::external_type_specification]
pub struct ExCpuIdResult(CpuIdResult);

/// Exposes the four u32 result registers of the `core::arch` CPUID intrinsics.
#[verifier::external_type_specification]
pub struct ExCpuidResult(CpuidResult);

pub assume_specification[ x86::apic::xapic::XAPIC_ID ] -> u32
    returns
        0x020u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_VERSION ] -> u32
    returns
        0x030u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_EOI ] -> u32
    returns
        0x0B0u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_SVR ] -> u32
    returns
        0x0F0u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_ESR ] -> u32
    returns
        0x280u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_ICR0 ] -> u32
    returns
        0x300u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_ICR1 ] -> u32
    returns
        0x310u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_LVT_TIMER ] -> u32
    returns
        0x320u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_TIMER_INIT_COUNT ] -> u32
    returns
        0x380u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_TIMER_CURRENT_COUNT ] -> u32
    returns
        0x390u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_TIMER_DIV_CONF ] -> u32
    returns
        0x3E0u32,
;

pub assume_specification[ x86::msr::IA32_APIC_BASE ] -> u32
    returns
        0x1bu32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_APICID ] -> u32
    returns
        0x802u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_VERSION ] -> u32
    returns
        0x803u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_EOI ] -> u32
    returns
        0x80bu32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_SIVR ] -> u32
    returns
        0x80fu32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_ESR ] -> u32
    returns
        0x828u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_ICR ] -> u32
    returns
        0x830u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_LVT_TIMER ] -> u32
    returns
        0x832u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_INIT_COUNT ] -> u32
    returns
        0x838u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_CUR_COUNT ] -> u32
    returns
        0x839u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_DIV_CONF ] -> u32
    returns
        0x83eu32,
;

/// [x86::msr::rdmsr](https://docs.rs/x86/0.52.0/x86/msr/fn.rdmsr.html) returns an unconstrained value.
pub assume_specification[ x86::msr::rdmsr ](msr: u32) -> u64
    opens_invariants none
    no_unwind
;

/// [x86::msr::wrmsr](https://docs.rs/x86/0.52.0/x86/msr/fn.wrmsr.html).
pub assume_specification[ x86::msr::wrmsr ](msr: u32, value: u64)
    opens_invariants none
    no_unwind
;

/// Opaque external wrapper for the x86_64 crate's MSR handle.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExMsr(Msr);

/// [`Msr::new`](https://docs.rs/x86_64/0.15.5/x86_64/registers/model_specific/struct.Msr.html#method.new).
pub assume_specification[ Msr::new ](reg: u32) -> Msr
    opens_invariants none
    no_unwind
;

/// [`Msr::read`](https://docs.rs/x86_64/0.15.5/x86_64/registers/model_specific/struct.Msr.html#method.read)
/// returns an unconstrained value.
pub assume_specification[ Msr::read ](msr: &Msr) -> u64
    opens_invariants none
    no_unwind
;

/// [`Msr::write`](https://docs.rs/x86_64/0.15.5/x86_64/registers/model_specific/struct.Msr.html#method.write).
pub assume_specification[ Msr::write ](msr: &mut Msr, value: u64)
    opens_invariants none
    no_unwind
;

/// First non-canonical address above the lower 48-bit canonical half (`1 << 47`).
pub const X86_CANONICAL_LOWER_END: u64 = 0x0000_8000_0000_0000;

/// First canonical address of the upper 48-bit canonical half (`!((1 << 47) - 1)`).
pub const X86_CANONICAL_UPPER_START: u64 = 0xffff_8000_0000_0000;

/// Exclusive upper bound for 52-bit x86-64 physical addresses (`1 << 52`).
pub const X86_PHYS_ADDR_END: u64 = 0x0010_0000_0000_0000;

/// Whether `addr` is a canonical 48-bit x86-64 virtual address (bits 48..64 sign-extend bit 47).
///
/// Matches `x86_64::VirtAddr::try_new` (`((addr << 16) as i64 >> 16) as u64 == addr`).
pub open spec fn is_canonical_vaddr(addr: u64) -> bool {
    addr < X86_CANONICAL_LOWER_END || addr >= X86_CANONICAL_UPPER_START
}

/// Whether `addr` is a valid 52-bit x86-64 physical address (bits 52..64 are zero).
///
/// Matches `x86_64::PhysAddr::try_new` without the `memory_encryption` feature.
pub open spec fn is_valid_x86_paddr(addr: u64) -> bool {
    addr < X86_PHYS_ADDR_END
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExVirtAddr(VirtAddr);

/// [`VirtAddr::new`](https://docs.rs/x86_64/0.15.5/x86_64/addr/struct.VirtAddr.html#method.new);
/// panics iff `!is_canonical_vaddr(addr)`.
pub assume_specification[ VirtAddr::new ](addr: u64) -> VirtAddr
    requires
        is_canonical_vaddr(addr),
    opens_invariants none
    no_unwind when is_canonical_vaddr(addr)
;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPhysAddr(PhysAddr);

/// Logical `u64` value stored inside a [`PhysAddr`].
pub uninterp spec fn phys_addr_as_u64(addr: PhysAddr) -> u64;

/// [`PhysAddr::new`](https://docs.rs/x86_64/0.15.5/x86_64/addr/struct.PhysAddr.html#method.new);
/// panics iff `!is_valid_x86_paddr(addr)`.
pub assume_specification[ PhysAddr::new ](addr: u64) -> (ret: PhysAddr)
    requires
        is_valid_x86_paddr(addr),
    ensures
        phys_addr_as_u64(ret) == addr,
    opens_invariants none
    no_unwind when is_valid_x86_paddr(addr)
;

/// External specification for the sealed [`PageSize`] trait.
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(PageSizeSpec via PageSizeSpecImpl)]
#[verifier::external_trait_private_bound(x86_64::sealed::Sealed)]
pub trait ExPageSize: Copy + Eq + PartialOrd + Ord {
    type ExternalTraitSpecificationFor: PageSize;

    /// Whether `Self`'s page size is modeled by [`Self::spec_size`].
    spec fn obeys_page_size_spec() -> bool;

    /// Logical page size in bytes matching `Self::SIZE`.
    spec fn spec_size() -> u64;
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExSize4KiB(Size4KiB);

impl PageSizeSpecImpl for Size4KiB {
    open spec fn obeys_page_size_spec() -> bool {
        true
    }

    open spec fn spec_size() -> u64 {
        4096u64
    }
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAddressNotAligned(AddressNotAligned);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(S)]
pub struct ExPhysFrame<S: PageSize = Size4KiB>(PhysFrame<S>);

/// [`PhysFrame::from_start_address`](https://docs.rs/x86_64/0.15.5/x86_64/structures/paging/frame/struct.PhysFrame.html#method.from_start_address);
/// returns `Ok` iff `address` is aligned to `S::SIZE`.
pub assume_specification<S: PageSize>[ PhysFrame::<S>::from_start_address ](
    address: PhysAddr,
) -> (ret: Result<PhysFrame<S>, AddressNotAligned>)
    ensures
        S::obeys_page_size_spec() ==> (ret is Ok <==> phys_addr_as_u64(address) % S::spec_size()
            == 0),
    opens_invariants none
    no_unwind
;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCr3(Cr3);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCr3Flags(Cr3Flags);

/// [`Cr3Flags::empty`](https://docs.rs/x86_64/0.15.5/x86_64/registers/control/struct.Cr3Flags.html#method.empty).
pub assume_specification[ Cr3Flags::empty ]() -> Cr3Flags
    opens_invariants none
    no_unwind
;

/// [`Cr3Flags::PAGE_LEVEL_WRITETHROUGH`](https://docs.rs/x86_64/0.15.5/x86_64/registers/control/struct.Cr3Flags.html#associatedconstant.PAGE_LEVEL_WRITETHROUGH).
pub assume_specification[ Cr3Flags::PAGE_LEVEL_WRITETHROUGH ] -> Cr3Flags
;

/// [`Cr3Flags::PAGE_LEVEL_CACHE_DISABLE`](https://docs.rs/x86_64/0.15.5/x86_64/registers/control/struct.Cr3Flags.html#associatedconstant.PAGE_LEVEL_CACHE_DISABLE).
pub assume_specification[ Cr3Flags::PAGE_LEVEL_CACHE_DISABLE ] -> Cr3Flags
;

/// [`Cr3::write`](https://docs.rs/x86_64/0.15.5/x86_64/registers/control/struct.Cr3.html#method.write).
pub assume_specification[ Cr3::write ](frame: PhysFrame<Size4KiB>, flags: Cr3Flags)
    opens_invariants none
    no_unwind
;

/// [`tlb::flush`](https://docs.rs/x86_64/0.15.5/x86_64/instructions/tlb/fn.flush.html).
pub assume_specification[ tlb::flush ](addr: VirtAddr)
    opens_invariants none
    no_unwind
;

/// [`tlb::flush_all`](https://docs.rs/x86_64/0.15.5/x86_64/instructions/tlb/fn.flush_all.html);
/// reloads CR3 (`Cr3::read` masks bits 52..63 so `PhysAddr::new` cannot panic).
pub assume_specification[ tlb::flush_all ]()
    opens_invariants none
    no_unwind
;

} // verus!
