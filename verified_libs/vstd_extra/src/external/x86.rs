//! External specifications for the [`x86` crate](https://crates.io/crates/x86)
//! CPUID queries, constants and MSR accessors. Constant values are trusted to match
//! the crate sources; the original constants are re-exported below. Also models the
//! [`x86_64` crate](https://crates.io/crates/x86_64) MSR accessors.
use vstd::prelude::*;
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
use x86_64::registers::model_specific::Msr;

verus! {

/// Exposes the four u32 result registers.
#[verifier::external_type_specification]
pub struct ExCpuIdResult(CpuIdResult);

/// CPU capabilities enumerated by CPUID, without OS enablement state.
pub ghost struct CpuModel {
    /// Maximum basic leaf reported by CPUID.(0, 0):EAX.
    pub max_basic_leaf: u32,
    /// CPUID.(1, 0):ECX[28], meaningful only when leaf 1 is supported.
    pub avx_bit: bool,
    /// CPUID.(7, 0):EBX[16], meaningful only when leaf 7 is supported.
    pub avx512f_bit: bool,
}

impl CpuModel {
    pub open spec fn supports_avx(self) -> bool {
        self.max_basic_leaf >= 1 && self.avx_bit
    }

    pub open spec fn supports_avx512f(self) -> bool {
        self.max_basic_leaf >= 7 && self.avx512f_bit
    }
}

/// CPUID capabilities shared by every logical CPU on which OSTD executes.
///
/// The unconditional native CPUID contract below assumes that the maximum basic
/// leaf and the modeled bits of supported leaves agree across those CPUs and
/// remain stable throughout execution. This includes the values presented by
/// firmware and virtualization, including TDX. The model describes enumerated
/// capabilities; it does not establish OS enablement or instruction usability.
pub uninterp spec fn cpu_model() -> CpuModel;

/// Matches the maximum basic leaf and the AVX/AVX512F encodings in the Intel SDM
/// CPUID instruction reference. Other queries and register bits are unconstrained.
pub open spec fn cpuid_consistent(
    model: CpuModel,
    leaf: u32,
    subleaf: u32,
    result: CpuIdResult,
) -> bool {
    &&& (leaf == 0 && subleaf == 0) ==> result.eax == model.max_basic_leaf
    &&& (leaf == 1 && subleaf == 0 && model.max_basic_leaf >= 1) ==> ((result.ecx & (1u32 << 28)
        != 0) == model.avx_bit)
    &&& (leaf == 7 && subleaf == 0 && model.max_basic_leaf >= 7) ==> ((result.ebx & (1u32 << 16)
        != 0) == model.avx512f_bit)
}

/// Trusted native read: x86 0.52/raw-cpuid 10.7 delegates to `__cpuid_count`.
/// Requires x86_64 outside SGX. The result is trusted to match the CPUID encodings
/// and the platform consistency and stability assumptions documented by [`cpu_model`].
pub assume_specification[ x86::cpuid::native_cpuid::cpuid_count ](
    leaf: u32,
    subleaf: u32,
) -> (result: CpuIdResult)
    ensures
        cpuid_consistent(cpu_model(), leaf, subleaf, result),
    opens_invariants none
    no_unwind
;

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

} // verus!
