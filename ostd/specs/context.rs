//! Global context of OSTD verification.
//!
//! On x86_64, CPUID reads expose the platform-wide capabilities in `cpu_feature_model()`.
use vstd::prelude::*;

use core::arch::x86_64::CpuidResult;
use x86::cpuid::CpuIdResult;

verus! {

/// The CPU capabilities and nominal TSC calibration data enumerated by CPUID.
/// Each feature flag is false when its basic leaf is unavailable.
pub ghost struct CpuFeatureModel {
    /// The maximum basic leaf reported by CPUID.(EAX=0):EAX.
    pub max_basic_leaf: u32,
    pub supports_avx: bool,
    /// AVX-512 Foundation.
    pub supports_avx512f: bool,
    pub supports_xapic: bool,
    pub supports_x2apic: bool,
    /// CPUID.(0x15, 0):EAX, the denominator of the TSC/core crystal clock ratio.
    pub tsc_denominator: u32,
    /// CPUID.(0x15, 0):EBX, the numerator of that ratio.
    pub tsc_numerator: u32,
    /// CPUID.(0x15, 0):ECX, the nominal core crystal clock frequency in Hz.
    pub crystal_hz: u32,
    /// Raw CPUID.(0x16, 0):EAX. Bits 15:0 encode the base frequency in MHz. OSTD reads all 32 bits.
    pub base_mhz: u32,
}

impl CpuFeatureModel {
    /// Constructs the shared model from the reference CPU's readings.
    pub open spec fn from_cpuid(reference: spec_fn((u32, u32)) -> CpuidResult) -> Self {
        let max_basic_leaf = reference((0, 0)).eax;
        let features = reference((1, 0));
        let tsc = reference((0x15, 0));
        Self {
            max_basic_leaf,
            supports_avx: max_basic_leaf >= 1 && features.ecx & (1u32 << 28) != 0,
            supports_avx512f: max_basic_leaf >= 7 && reference((7, 0)).ebx & (1u32 << 16) != 0,
            supports_xapic: max_basic_leaf >= 1 && features.edx & (1u32 << 9) != 0,
            supports_x2apic: max_basic_leaf >= 1 && features.ecx & (1u32 << 21) != 0,
            tsc_denominator: tsc.eax,
            tsc_numerator: tsc.ebx,
            crystal_hz: tsc.ecx,
            base_mhz: reference((0x16, 0)).eax,
        }
    }
}

/// A reference CPU's register values indexed by CPUID leaf and subleaf.
pub uninterp spec fn reference_cpuid() -> spec_fn((u32, u32)) -> CpuidResult;

/// The CPUID data shared by every logical CPU on which OSTD executes.
///
/// The CPUID contracts assume that the maximum basic leaf agrees across those CPUs
/// and remains stable throughout execution.
pub open spec fn cpu_feature_model() -> CpuFeatureModel {
    CpuFeatureModel::from_cpuid(reference_cpuid())
}

/// Whether `result`, read at (`leaf`, `subleaf`), agrees with `model`.
///
/// Fixes the maximum basic leaf, the modeled feature bits and the TSC calibration
/// fields for supported queries. Other queries and register bits are unconstrained.
pub open spec fn cpuid_consistent(
    model: CpuFeatureModel,
    leaf: u32,
    subleaf: u32,
    result: CpuidResult,
) -> bool {
    subleaf == 0 && leaf <= model.max_basic_leaf ==> match leaf {
        0 => result.eax == model.max_basic_leaf,
        1 => {
            &&& model.supports_avx == (result.ecx & (1u32 << 28) != 0)
            &&& model.supports_xapic == (result.edx & (1u32 << 9) != 0)
            &&& model.supports_x2apic == (result.ecx & (1u32 << 21) != 0)
        },
        7 => model.supports_avx512f == (result.ebx & (1u32 << 16) != 0),
        0x15 => (result.eax, result.ebx, result.ecx) == (
            model.tsc_denominator,
            model.tsc_numerator,
            model.crystal_hz,
        ),
        0x16 => result.eax == model.base_mhz,
        _ => true,
    }
}

/// OSTD trusts this intrinsic to read subleaf zero under the platform assumptions
/// of [`cpu_feature_model`].
#[cfg(not(target_env = "sgx"))]
pub assume_specification[ core::arch::x86_64::__cpuid ](leaf: u32) -> (result: CpuidResult)
    ensures
        cpuid_consistent(cpu_feature_model(), leaf, 0, result),
    opens_invariants none
    no_unwind
;

/// OSTD trusts this intrinsic to read the requested subleaf under the same
/// platform assumptions.
#[cfg(not(target_env = "sgx"))]
pub assume_specification[ core::arch::x86_64::__cpuid_count ](leaf: u32, subleaf: u32) -> (result:
    CpuidResult)
    ensures
        cpuid_consistent(cpu_feature_model(), leaf, subleaf, result),
    opens_invariants none
    no_unwind
;

/// `raw-cpuid` implements the native read behind `cpuid!` by copying the four
/// registers returned by `__cpuid_count(leaf, subleaf)`.
#[cfg(not(target_env = "sgx"))]
pub assume_specification[ x86::cpuid::native_cpuid::cpuid_count ](
    leaf: u32,
    subleaf: u32,
) -> (result: CpuIdResult)
    ensures
        cpuid_consistent(
            cpu_feature_model(),
            leaf,
            subleaf,
            CpuidResult { eax: result.eax, ebx: result.ebx, ecx: result.ecx, edx: result.edx },
        ),
    opens_invariants none
    no_unwind
;

} // verus!
