//! Global context of OSTD verification.
//!
//! On x86_64, CPUID reads expose the platform-wide capabilities in `cpu_feature_model()`.
use vstd::prelude::*;

use core::arch::x86_64::CpuidResult;
use x86::cpuid::CpuIdResult;

verus! {

/// A feature enumerated by a single bit of a basic CPUID leaf.
pub enum CpuFeature {
    Avx,
    /// AVX-512 Foundation.
    Avx512F,
    XApic,
    X2Apic,
}

impl CpuFeature {
    pub open spec fn variants() -> Seq<Self> {
        seq![Self::Avx, Self::Avx512F, Self::XApic, Self::X2Apic]
    }

    pub proof fn lemma_variants_complete(self)
        ensures
            Self::variants().contains(self),
    {
    }

    /// The basic leaf and subleaf that enumerate this feature in the Intel SDM.
    pub open spec fn query(self) -> (u32, u32) {
        match self {
            CpuFeature::Avx | CpuFeature::XApic | CpuFeature::X2Apic => (1, 0),
            CpuFeature::Avx512F => (7, 0),
        }
    }

    /// Decodes the feature bit from a result of [`Self::query`].
    pub open spec fn bit_set_in(self, result: CpuidResult) -> bool {
        match self {
            CpuFeature::Avx => result.ecx & (1u32 << 28) != 0,
            CpuFeature::Avx512F => result.ebx & (1u32 << 16) != 0,
            CpuFeature::XApic => result.edx & (1u32 << 9) != 0,
            CpuFeature::X2Apic => result.ecx & (1u32 << 21) != 0,
        }
    }
}

/// The CPU capabilities and nominal TSC calibration data enumerated by CPUID.
pub ghost struct CpuFeatureModel {
    /// The maximum basic leaf reported by CPUID.(EAX=0):EAX.
    pub max_basic_leaf: u32,
    /// The raw feature bit. Its value is meaningful only for supported leaves.
    pub feature_bits: spec_fn(CpuFeature) -> bool,
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
        let tsc = reference((0x15, 0));
        Self {
            max_basic_leaf: reference((0, 0)).eax,
            feature_bits: |feature: CpuFeature| feature.bit_set_in(reference(feature.query())),
            tsc_denominator: tsc.eax,
            tsc_numerator: tsc.ebx,
            crystal_hz: tsc.ecx,
            base_mhz: reference((0x16, 0)).eax,
        }
    }

    /// All modeled features use subleaf zero, so the maximum basic leaf suffices
    /// to determine whether their query is available.
    pub open spec fn supports(self, feature: CpuFeature) -> bool {
        feature.query().0 <= self.max_basic_leaf && (self.feature_bits)(feature)
    }
}

/// The CPUID data shared by every logical CPU on which OSTD executes.
///
/// The CPUID contracts assume that the maximum basic leaf agrees across those CPUs
/// and remains stable throughout execution. For supported leaves, the same holds
/// for the modeled feature bits and the nominal calibration fields of 0x15 and 0x16.
/// This includes the values presented by firmware and virtualization, including TDX.
/// [`lemma_cpuid_model_admits`] shows that these fields suffice to construct a shared model
/// even when other bits vary between reads. OS enablement and instruction usability depend
/// on additional processor state.
pub uninterp spec fn cpu_feature_model() -> CpuFeatureModel;

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
    &&& (leaf, subleaf) == (0, 0) ==> result.eax == model.max_basic_leaf
    &&& (leaf, subleaf) == (0x15, 0) && leaf <= model.max_basic_leaf ==> {
        (result.eax, result.ebx, result.ecx) == (
            model.tsc_denominator,
            model.tsc_numerator,
            model.crystal_hz,
        )
    }
    &&& (leaf, subleaf) == (0x16, 0) && leaf <= model.max_basic_leaf ==> result.eax
        == model.base_mhz
    &&& CpuFeature::variants().all(
        |feature: CpuFeature|
            feature.query() == (leaf, subleaf) && leaf <= model.max_basic_leaf ==> model.supports(
                feature,
            ) == feature.bit_set_in(result),
    )
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

/// Every query in a batch agrees with the model built from `reference` when the
/// observed CPU reports the same maximum basic leaf and modeled fields of supported leaves.
/// The same reference can be used for observations from any CPU or time.
pub proof fn lemma_cpuid_model_admits(
    reference: spec_fn((u32, u32)) -> CpuidResult,
    observed: spec_fn((u32, u32)) -> CpuidResult,
    queries: Seq<(u32, u32)>,
)
    requires
        observed((0, 0)).eax == reference((0, 0)).eax,
        0x15 <= reference((0, 0)).eax ==> {
            let ref_tsc = reference((0x15, 0));
            let obs_tsc = observed((0x15, 0));
            (obs_tsc.eax, obs_tsc.ebx, obs_tsc.ecx) == (ref_tsc.eax, ref_tsc.ebx, ref_tsc.ecx)
        },
        0x16 <= reference((0, 0)).eax ==> observed((0x16, 0)).eax == reference((0x16, 0)).eax,
        CpuFeature::variants().all(
            |feature: CpuFeature|
                feature.query().0 <= reference((0, 0)).eax ==> feature.bit_set_in(
                    observed(feature.query()),
                ) == feature.bit_set_in(reference(feature.query())),
        ),
    ensures
        queries.all(
            |q: (u32, u32)|
                cpuid_consistent(CpuFeatureModel::from_cpuid(reference), q.0, q.1, observed(q)),
        ),
{
}

} // verus!
