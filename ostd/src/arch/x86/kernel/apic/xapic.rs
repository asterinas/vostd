// SPDX-License-Identifier: MPL-2.0
#![expect(dead_code)]

use vstd::prelude::*;
use vstd_extra::debug_assert;

use x86::apic::xapic;

use super::ApicTimer;
use crate::mm;

verus! {

// `align_of` has no primitive axiom; pin it (compiler-checked, not trusted).
global layout u32 is size == 4, align == 4;

const IA32_APIC_BASE_MSR: u32 = 0x1B;

// Processor is a BSP
const IA32_APIC_BASE_MSR_BSP: u32 = 0x100;

// Enable bit
const IA32_APIC_BASE_MSR_ENABLE: u64 = 0x800;

const APIC_LVT_MASK_BITS: u32 = 1 << 16;

#[derive(Debug)]
pub struct XApic {
    mmio_start: *mut u32,
}

impl XApic {
    // The register file fits in the address space and is u32-aligned.
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.mmio_start@.addr + 1024 <= usize::MAX && self.mmio_start@.addr % 4 == 0
    }

    /// The MMIO register-file base address, closed so `new`'s contract can
    /// name it without exposing the private field.
    pub closed spec fn mmio_addr(self) -> usize {
        self.mmio_start@.addr
    }

    /// Trusted: the register-file vaddr, as `XApic::new` maps it.
    pub uninterp spec fn apic_register_file_vaddr_spec() -> usize;

    /// Trusted: the CPUID.01H:EDX[9] local-APIC flag.
    pub uninterp spec fn has_xapic_spec() -> bool;
}

} // verus!
// The APIC instance can be shared among threads running on the same CPU, but not among those
// running on different CPUs. Therefore, it is not `Send`/`Sync`.
impl !Send for XApic {}
impl !Sync for XApic {}

#[verus_verify]
impl XApic {
    /// Creates an APIC instance for the local CPU's MMIO register file.
    /* Trusted (external_body): the usize-to-`*mut u32` cast is rejected by
     * the verifier; the address is pinned to the spec model and claimed
     * in-bounds and page-aligned (the MSR base field is page-aligned). */
    #[verus_verify(external_body)]
    #[verus_spec(ret =>
        ensures
            ret.is_some() == XApic::has_xapic_spec(),
            ret matches Some(x) ==> {
                &&& x.mmio_addr() == XApic::apic_register_file_vaddr_spec()
                &&& XApic::apic_register_file_vaddr_spec() + 1024 <= usize::MAX
                &&& XApic::apic_register_file_vaddr_spec() % 4 == 0
            },
    )]
    pub fn new() -> Option<Self> {
        if !Self::has_xapic() {
            return None;
        }
        let address = mm::paddr_to_vaddr(get_xapic_base_address());
        Some(Self {
            mmio_start: address as *mut u32,
        })
    }

    /// Reads a register from the MMIO region.
    #[verus_spec(
        requires
            offset % 4 == 0,
            offset < 1024,
    )]
    fn read(&self, offset: u32) -> u32 {
        assert!(offset as usize % 4 == 0);
        let index = offset as usize / 4;
        debug_assert!(index < 256);
        proof! {
            use_type_invariant(self);
        }
        unsafe { core::ptr::read_volatile(self.mmio_start.add(index)) }
    }

    /// Writes a register in the MMIO region.
    #[verus_spec(
        requires
            offset % 4 == 0,
            offset < 1024,
    )]
    fn write(&self, offset: u32, val: u32) {
        assert!(offset as usize % 4 == 0);
        let index = offset as usize / 4;
        debug_assert!(index < 256);
        proof! {
            use_type_invariant(self);
        }
        unsafe { core::ptr::write_volatile(self.mmio_start.add(index), val) }
    }

    pub fn enable(&mut self) {
        proof! {
            use_type_invariant(&*self);
        }
        // Enable xAPIC
        set_apic_base_address(get_xapic_base_address());

        // Set SVR, Enable APIC and set Spurious Vector to 15 (Reserved irq number)
        let svr: u32 = (1 << 8) | 15;
        self.write(xapic::XAPIC_SVR, svr);
    }

    /* `__cpuid` has no verifier model; trusted body under `external_body`. */
    #[verus_verify(external_body)]
    #[verus_spec(ret => returns XApic::has_xapic_spec())]
    pub(super) fn has_xapic() -> bool {
        let value = unsafe { core::arch::x86_64::__cpuid(1) };
        value.edx & 0x100 != 0
    }
}

#[verus_verify]
impl super::Apic for XApic {
    fn id(&self) -> u32 {
        proof! {
            use_type_invariant(self);
        }
        self.read(xapic::XAPIC_ID)
    }

    fn version(&self) -> u32 {
        proof! {
            use_type_invariant(self);
        }
        self.read(xapic::XAPIC_VERSION)
    }

    fn eoi(&self) {
        proof! {
            use_type_invariant(self);
        }
        self.write(xapic::XAPIC_EOI, 0);
    }

    /* The polling loop terminates only on hardware action; whole op unverified. */
    #[verus_verify(external_body)]
    unsafe fn send_ipi(&self, icr: super::Icr) {
        let _guard = crate::trap::irq::disable_local();
        self.write(xapic::XAPIC_ESR, 0);
        // The upper 32 bits of ICR must be written into XAPIC_ICR1 first,
        // because writing into XAPIC_ICR0 will trigger the action of
        // interrupt sending.
        self.write(xapic::XAPIC_ICR1, icr.upper());
        self.write(xapic::XAPIC_ICR0, icr.lower());
        loop {
            let icr = self.read(xapic::XAPIC_ICR0);
            if ((icr >> 12) & 0x1) == 0 {
                break;
            }
            if self.read(xapic::XAPIC_ESR) > 0 {
                break;
            }
        }
    }
}

#[verus_verify]
impl ApicTimer for XApic {
    fn set_timer_init_count(&self, value: u64) {
        proof! {
            use_type_invariant(self);
        }
        self.write(xapic::XAPIC_TIMER_INIT_COUNT, value as u32);
    }

    fn timer_current_count(&self) -> u64 {
        proof! {
            use_type_invariant(self);
        }
        self.read(xapic::XAPIC_TIMER_CURRENT_COUNT) as u64
    }

    fn set_lvt_timer(&self, value: u64) {
        proof! {
            use_type_invariant(self);
        }
        self.write(xapic::XAPIC_LVT_TIMER, value as u32);
    }

    fn set_timer_div_config(&self, div_config: super::DivideConfig) {
        proof! {
            use_type_invariant(self);
        }
        self.write(xapic::XAPIC_TIMER_DIV_CONF, div_config as u32);
    }
}

/// Sets APIC base address and enables it
#[verus_verify]
fn set_apic_base_address(address: usize) {
    unsafe {
        x86_64::registers::model_specific::Msr::new(IA32_APIC_BASE_MSR)
            .write(address as u64 | IA32_APIC_BASE_MSR_ENABLE);
    }
}

/// Gets xAPIC base address
#[verus_verify]
pub(super) fn get_xapic_base_address() -> usize {
    unsafe {
        (x86_64::registers::model_specific::Msr::new(IA32_APIC_BASE_MSR).read() & 0xf_ffff_f000)
            as usize
    }
}
