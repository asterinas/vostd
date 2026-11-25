// SPDX-License-Identifier: MPL-2.0
//! Platform-specific code for the x86 platform.
use vstd::prelude::*;
use vstd_extra::{
    external::x86::{
        FpuOnce, XCR0_KNOWN_MASK, feature_info_ecx, feature_info_edx, xcr0_flag_groups_valid,
    },
    resource_invariant::ValueInvariant,
};

use crate::specs::context::cpu_feature_model;

/*pub mod boot;*/
pub(crate) mod cpu;
pub mod device;
pub(crate) mod ex_table;
pub(crate) mod io;
/*pub(crate) mod iommu;*/
pub(crate) mod irq;
pub(crate) mod kernel;
pub(crate) mod mm;
pub(crate) mod pci;
/*pub mod qemu;
pub(crate) mod serial; */
pub(crate) mod task;
pub mod timer;
/* pub mod trap; */

/*use io::construct_io_mem_allocator_builder;*/
/*use spin::Once;*/
use x86::cpuid::{/*CpuId,*/ FeatureInfo};

/*
#[cfg(feature = "cvm_guest")]
pub(crate) mod tdx_guest;

use core::sync::atomic::Ordering;

use log::warn;

#[cfg(feature = "cvm_guest")]
pub(crate) fn init_cvm_guest() {
    match ::tdx_guest::init_tdx() {
        Ok(td_info) => {
            crate::early_println!(
                "[kernel] Intel TDX initialized\n[kernel] td gpaw: {}, td attributes: {:?}",
                td_info.gpaw,
                td_info.attributes
            );
        }
        Err(::tdx_guest::tdcall::InitError::TdxGetVpInfoError(td_call_error)) => {
            panic!(
                "[kernel] Intel TDX not initialized, Failed to get TD info: {:?}",
                td_call_error
            );
        }
        // The machine has no TDX support.
        Err(_) => {}
    }
}*/
verus! {

pub(crate) ghost struct CpuFeaturesInvariant;

impl ValueInvariant<FeatureInfo> for CpuFeaturesInvariant {
    open spec fn inv(info: FeatureInfo) -> bool {
        &&& feature_info_edx(info) & 1u32 != 0
        &&& feature_info_ecx(info) & (1u32 << 26) != 0
    }
}

pub(crate) uninterp spec fn cpu_features_cell_id() -> vstd::resource::Loc;

} // verus!
/* Origin Rust: static CPU_FEATURES: Once<FeatureInfo> = Once::new();
 * Carry the initializer's predicate through the unchanged spin::Once protocol. */
#[verus_verify]
static CPU_FEATURES: FpuOnce<FeatureInfo, CpuFeaturesInvariant> =
    verus_exec_expr! { FpuOnce::new(Ghost(CpuFeaturesInvariant)) };

#[inline]
#[verus_verify(external_body)]
#[verus_spec(r => ensures r.id() == cpu_features_cell_id())]
pub(crate) fn cpu_features_ref() -> &'static FpuOnce<FeatureInfo, CpuFeaturesInvariant> {
    &CPU_FEATURES
}
/*
/// Architecture-specific initialization on the bootstrapping processor.
///
/// It should be called when the heap and frame allocators are available.
///
/// # Safety
///
/// This function must be called only once in the boot context of the
/// bootstrapping processor.
pub(crate) unsafe fn late_init_on_bsp() {
    // SAFETY: This function is only called once on BSP.
    unsafe { trap::init() };

    let io_mem_builder = construct_io_mem_allocator_builder();

    kernel::apic::init(&io_mem_builder).expect("APIC doesn't exist");
    kernel::irq::init(&io_mem_builder);

    kernel::tsc::init_tsc_freq();
    timer::init_bsp();

    // SAFETY: We're on the BSP and we're ready to boot all APs.
    unsafe { crate::boot::smp::boot_all_aps() };

    if_tdx_enabled!({
    } else {
        match iommu::init(&io_mem_builder) {
            Ok(_) => {}
            Err(err) => warn!("IOMMU initialization error:{:?}", err),
        }
    });

    // SAFETY:
    // 1. All the system device memory have been removed from the builder.
    // 2. All the port I/O regions belonging to the system device are defined using the macros.
    // 3. `MAX_IO_PORT` defined in `crate::arch::io` is the maximum value specified by x86-64.
    unsafe { crate::io::init(io_mem_builder) };
}

/// Architecture-specific initialization on the application processor.
///
/// # Safety
///
/// This function must be called only once on each application processor.
/// And it should be called after the BSP's call to [`init_on_bsp`].
///
/// [`init_on_bsp`]: crate::cpu::init_on_bsp
pub(crate) unsafe fn init_on_ap() {
    timer::init_ap();
}

pub(crate) fn interrupts_ack(irq_number: usize) {
    if !cpu::context::CpuException::is_cpu_exception(irq_number) {
        // TODO: We're in the interrupt context, so `disable_preempt()` is not
        // really necessary here.
        kernel::apic::get_or_init(&crate::task::disable_preempt() as _).eoi();
    }
}

/// Returns the frequency of TSC. The unit is Hz.
pub fn tsc_freq() -> u64 {
    kernel::tsc::TSC_FREQ.load(Ordering::Acquire)
}

/// Reads the current value of the processor’s time-stamp counter (TSC).
pub fn read_tsc() -> u64 {
    use core::arch::x86_64::_rdtsc;

    // SAFETY: It is safe to read a time-related counter.
    unsafe { _rdtsc() }
}

/// Reads a hardware generated 64-bit random value.
///
/// Returns None if no random value was generated.
pub fn read_random() -> Option<u64> {
    use core::arch::x86_64::_rdrand64_step;

    // Recommendation from "Intel® Digital Random Number Generator (DRNG) Software
    // Implementation Guide" - Section 5.2.1 and "Intel® 64 and IA-32 Architectures
    // Software Developer’s Manual" - Volume 1 - Section 7.3.17.1.
    const RETRY_LIMIT: usize = 10;

    for _ in 0..RETRY_LIMIT {
        let mut val = 0;
        let generated = unsafe { _rdrand64_step(&mut val) };
        if generated == 1 {
            return Some(val);
        }
    }
    None
}*/

#[verus_spec(returns cpu_feature_model().supports_avx)]
fn has_avx() -> bool {
    use core::arch::x86_64::{__cpuid, __cpuid_count};

    let cpuid_result = unsafe { __cpuid(0) };
    if cpuid_result.eax < 1 {
        // CPUID function 1 is not supported
        return false;
    }

    let cpuid_result = unsafe { __cpuid_count(1, 0) };
    // Check for AVX (bit 28 of ecx)
    cpuid_result.ecx & (1 << 28) != 0
}

#[verus_spec(returns cpu_feature_model().supports_avx512f)]
fn has_avx512() -> bool {
    use core::arch::x86_64::{__cpuid, __cpuid_count};

    let cpuid_result = unsafe { __cpuid(0) };
    if cpuid_result.eax < 7 {
        // CPUID function 7 is not supported
        return false;
    }

    let cpuid_result = unsafe { __cpuid_count(7, 0) };
    // Check for AVX-512 Foundation (bit 16 of ebx)
    cpuid_result.ebx & (1 << 16) != 0
}

verus! {

pub(crate) open spec fn enabled_fpu_xcr0(xcr0: u64) -> u64 {
    ((xcr0 | 2u64) | (if cpu_feature_model().supports_avx {
        4u64
    } else {
        0u64
    })) | (if cpu_feature_model().supports_avx512f {
        0xe0u64
    } else {
        0u64
    })
}

} // verus!
// Hardware support and the enabled XSAVE bound are caller obligations.
#[verus_spec(
    with Tracked(cpu): Tracked<&mut vstd_extra::external::x86::X86CpuRegisterOwner>
        -> initialization: Tracked<cpu::context::FpuInitialization>
    requires
        old(cpu).kernel_cpu(),
        old(cpu)@.fpu, old(cpu)@.xsave,
        old(cpu)@.fsgsbase, old(cpu)@.fxsr, old(cpu)@.sse, old(cpu)@.pge, old(cpu)@.nx,
        old(cpu)@.max_basic_leaf >= 0xd,
        cpu_feature_model().matches_xstates(old(cpu)),
        xcr0_flag_groups_valid(enabled_fpu_xcr0(old(cpu)@.xcr0) & XCR0_KNOWN_MASK),
        enabled_fpu_xcr0(old(cpu)@.xcr0) & !old(cpu)@.user_xstates == 0,
        576 <= (old(cpu)@.xsave_size_for)(enabled_fpu_xcr0(old(cpu)@.xcr0)) <= 4096,
        (old(cpu)@.xsave_size_for)(enabled_fpu_xcr0(old(cpu)@.xcr0)) as usize
            == cpu::context::platform_xsave_area_size(),
    ensures initialization@.enabled_on(final(cpu)),
            final(cpu)@.fxsr,
            initialization@.uses_xsave(),
            576 <= initialization@.len() <= 4096,
            final(cpu)@ == (vstd_extra::external::x86::X86CpuSnapshot {
                cr0: old(cpu)@.cr0 & !12u64,
                cr4: old(cpu)@.cr4 | 0x50680u64,
                efer: old(cpu)@.efer | 0x800u64,
                xcr0: enabled_fpu_xcr0(old(cpu)@.xcr0),
                x87_control: 0x037f, x87_status: 0, x87_tag: 0xffff,
                ..old(cpu)@
            }),
)]
pub(crate) fn enable_cpu_features() {
    use vstd_extra::external::x86::{
        cr4_bits, cr4_fsgsbase, cr4_or, cr4_or_assign, cr4_osfxsr, cr4_osxmmexcpt, cr4_osxsave,
        cr4_page_global, enable_cr4_flags, enable_nxe, read_cr4, read_feature_info, read_xcr0,
        write_xcr0, xcr0_avx, xcr0_bits, xcr0_hi16_zmm, xcr0_opmask, xcr0_or, xcr0_or_assign,
        xcr0_sse, xcr0_zmm_hi256,
    };

    /*use x86_64::registers::{control::Cr4Flags, model_specific::EferFlags, xcontrol::XCr0Flags};*/
    proof_decl! { let tracked initialized; }
    verus_exec_expr! {{
        /* Origin Rust: CPU_FEATURES.call_once(|| {
         *     let cpuid = CpuId::new();
         *     cpuid.get_feature_info().unwrap()
         * });
         * Carry CPU authority into the original lazy initializer. */
        let tracked read_cpu = &*cpu;
        let (_, Tracked(features_initialized)) = cpu_features_ref().call_once(
            || -> (r: FeatureInfo) ensures CpuFeaturesInvariant::inv(r) {
                read_feature_info(Tracked(read_cpu))
            }
        );
        /* Origin Rust: let mut cr4 = x86_64::registers::control::Cr4::read();
         * The same read carries the current-CPU register authority. */
        let mut cr4 = read_cr4(Tracked(&*cpu));
        let ghost old_cr4 = cpu@.cr4;
        let ghost cr4_read_bits = cr4_bits(cr4);
        assert((((0x10000u64 | 0x40000u64) | 0x200u64) | 0x400u64) | 0x80u64 == 0x50680u64) by (bit_vector);
        /* Origin Rust: cr4 |= Cr4Flags::FSGSBASE | Cr4Flags::OSXSAVE
         *     | Cr4Flags::OSFXSR | Cr4Flags::OSXMMEXCPT_ENABLE | Cr4Flags::PAGE_GLOBAL;
         * Thin wrappers retain the native operators; their spec-trait impl is foreign. */
        cr4_or_assign(&mut cr4, cr4_or(cr4_or(cr4_or(cr4_or(
            cr4_fsgsbase(), cr4_osxsave()), cr4_osfxsr()),
            cr4_osxmmexcpt()), cr4_page_global()));
        unsafe {
            /* Origin Rust: x86_64::registers::control::Cr4::write(cr4);
             * Pass the linear state through the unchanged hardware write. */
            let ghost cr4_write_bits = cr4_bits(cr4);
            enable_cr4_flags(cr4, Tracked(&mut *cpu));
            assert((old_cr4 | 0x50680u64) & 0x40000u64 != 0) by (bit_vector);
        }

        /* Origin Rust: let mut xcr0 = x86_64::registers::xcontrol::XCr0::read();
         * Keep the read and its from_bits_truncate behavior. */
        let mut xcr0 = read_xcr0(Tracked(&*cpu));
        let ghost old_xcr0 = cpu@.xcr0;
        let ghost initial_bits = xcr0_bits(xcr0);
        /* Origin Rust: xcr0 |= XCr0Flags::SSE;
         * Keep native BitOrAssign behind its narrow software contract. */
        xcr0_or_assign(&mut xcr0, xcr0_sse());
        let ghost after_sse = xcr0_bits(xcr0);
        let ghost mut avx_bits = 0u64;
        let ghost mut avx512_bits = 0u64;
        if has_avx() {
            /* Origin Rust: xcr0 |= XCr0Flags::AVX;
             * The external BitOrAssign operation requires a contract. */
            xcr0_or_assign(&mut xcr0, xcr0_avx());
            proof { avx_bits = 4u64; }
        }

        let ghost after_avx = xcr0_bits(xcr0);
        assert(after_avx | 0u64 == after_avx) by (bit_vector);
        if has_avx512() {
            assert((0x20u64 | 0x40u64) | 0x80u64 == 0xe0u64) by (bit_vector);
            /* Origin Rust: xcr0 |= XCr0Flags::OPMASK | XCr0Flags::ZMM_HI256 | XCr0Flags::HI16_ZMM;
             * Preserve the three native OR operations and their order. */
            xcr0_or_assign(&mut xcr0, xcr0_or(xcr0_or(xcr0_opmask(),
                xcr0_zmm_hi256()), xcr0_hi16_zmm()));
            proof { avx512_bits = 0xe0u64; }
        }

        unsafe {
            /* Origin Rust: x86_64::registers::xcontrol::XCr0::write(xcr0);
             * Preserve raw bits outside the wrapper's known mask. */
            let ghost current_bits = xcr0_bits(xcr0);
            let ghost target_bits = enabled_fpu_xcr0(old_xcr0);
            assert(current_bits == target_bits & XCR0_KNOWN_MASK) by (bit_vector)
                requires current_bits == ((initial_bits | 2u64) | avx_bits) | avx512_bits,
                    initial_bits == old_xcr0 & XCR0_KNOWN_MASK,
                    target_bits == ((old_xcr0 | 2u64) | avx_bits) | avx512_bits,
                    avx_bits == 0 || avx_bits == 4,
                    avx512_bits == 0 || avx512_bits == 0xe0;

            assert(current_bits & !XCR0_KNOWN_MASK == 0) by (bit_vector)
                requires current_bits == ((initial_bits | 2u64) | avx_bits) | avx512_bits,
                    initial_bits == old_xcr0 & XCR0_KNOWN_MASK,
                    avx_bits == 0 || avx_bits == 4,
                    avx512_bits == 0 || avx512_bits == 0xe0;
            assert(current_bits & !0xe6u64 == (old_xcr0 & XCR0_KNOWN_MASK) & !0xe6u64) by (bit_vector)
                requires current_bits == ((initial_bits | 2u64) | avx_bits) | avx512_bits,
                    initial_bits == old_xcr0 & XCR0_KNOWN_MASK,
                    avx_bits == 0 || avx_bits == 4,
                    avx512_bits == 0 || avx512_bits == 0xe0;

            assert(((old_xcr0 & !XCR0_KNOWN_MASK) | current_bits)
                == ((old_xcr0 | 2u64) | avx_bits) | avx512_bits) by (bit_vector)
                requires current_bits == ((initial_bits | 2u64) | avx_bits) | avx512_bits,
                    initial_bits == old_xcr0 & XCR0_KNOWN_MASK;
            write_xcr0(xcr0, Tracked(&mut *cpu));
        }

        let tracked result;
        #[verus_spec(with Tracked(&mut *cpu), Tracked(&features_initialized) => Tracked(result))]
        cpu::context::enable_essential_features();
        unsafe {
            // enable non-executable page protection
            /* Origin Rust: x86_64::registers::model_specific::Efer::update(|efer| {
             *     *efer |= EferFlags::NO_EXECUTE_ENABLE;
             * });
             * Keep the same update while stating the register frame. */
            enable_nxe(Tracked(&mut *cpu));
        }
        proof { initialized = result; }
    }}
    proof_with!(|= Tracked(initialized));
    ()
}

/// Inserts a TDX-specific code block.
///
/// This macro conditionally executes a TDX-specific code block based on the following conditions:
/// (1) The `cvm_guest` feature is enabled at compile time.
/// (2) The TDX feature is detected at runtime via `::tdx_guest::tdx_is_enabled()`.
///
/// If both conditions are met, the `if_block` is executed. If an `else_block` is provided, it will be executed
/// when either the `cvm_guest` feature is not enabled or the TDX feature is not detected at runtime.
#[macro_export]
macro_rules! if_tdx_enabled {
    // Match when there is an else block
    ($if_block:block else $else_block:block) => {{
        #[cfg(feature = "cvm_guest")]
        {
            if ::tdx_guest::tdx_is_enabled() {
                $if_block
            } else {
                $else_block
            }
        }
        #[cfg(not(feature = "cvm_guest"))]
        {
            $else_block
        }
    }};
    // Match when there is no else block
    ($if_block:block) => {{
        #[cfg(feature = "cvm_guest")]
        {
            if ::tdx_guest::tdx_is_enabled() {
                $if_block
            }
        }
    }};
}

pub use if_tdx_enabled;
