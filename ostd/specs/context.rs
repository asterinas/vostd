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
    pub supports_rdrand: bool,
    /// CPUID.(0x15, 0):EAX, the denominator of the TSC/core crystal clock ratio.
    pub tsc_denominator: u32,
    /// CPUID.(0x15, 0):EBX, the numerator of that ratio.
    pub tsc_numerator: u32,
    /// CPUID.(0x15, 0):ECX, the nominal core crystal clock frequency in Hz.
    pub crystal_hz: u32,
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
            supports_rdrand: max_basic_leaf >= 1 && features.ecx & (1u32 << 30) != 0,
            tsc_denominator: tsc.eax,
            tsc_numerator: tsc.ebx,
            crystal_hz: tsc.ecx,
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
/// fields of leaf 0x15. The base frequency in leaf 0x16 is scoped to a logical
/// processor (Intel SDM Vol. 1, Table 21-54).
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
            &&& model.supports_rdrand == (result.ecx & (1u32 << 30) != 0)
        },
        7 => model.supports_avx512f == (result.ebx & (1u32 << 16) != 0),
        0x15 => (result.eax, result.ebx, result.ecx) == (
            model.tsc_denominator,
            model.tsc_numerator,
            model.crystal_hz,
        ),
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

/// OSTD trusts [`core::arch::x86_64::_rdrand64_step`](https://doc.rust-lang.org/core/arch/x86_64/fn._rdrand64_step.html)
/// to execute `RDRAND` without unwinding once CPUID reports `RDRAND` support.
pub assume_specification[ core::arch::x86_64::_rdrand64_step ](val: &mut u64) -> (flag: i32)
    requires
        cpu_feature_model().supports_rdrand,
    ensures
        flag == 0 || flag == 1,
        flag == 0 ==> *final(val) == 0u64,
    opens_invariants none
    no_unwind when cpu_feature_model().supports_rdrand
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
