// SPDX-License-Identifier: MPL-2.0
//! Interrupts.
use vstd::prelude::*;

// Intel(R) 64 and IA-32 rchitectures Software Developer's Manual,
// Volume 3A, Section 6.2 says "Vector numbers in the range 32 to 255
// are designated as user-defined interrupts and are not reserved by
// the Intel 64 and IA-32 architecture."
pub(crate) const IRQ_NUM_MIN: u8 = 32;
pub(crate) const IRQ_NUM_MAX: u8 = 255;

/* The IOMMU module is outside the active verified module graph, so interrupt remapping is
 * unavailable in this build. This preserves the original no-IOMMU branch: initialization is a
 * no-op and the query returns `None`. TODO: restore the IOMMU-backed path when that module enters
 * the verified graph.
 * Origin Rust:
 * pub(crate) struct IrqRemapping { entry: Once<IrtEntryHandle> }
 * impl IrqRemapping {
 *     pub(crate) const fn new() -> Self { Self { entry: Once::new() } }
 *     pub(crate) fn init(&self, irq_num: u8) {
 *         if !has_interrupt_remapping() { return; }
 *         self.entry.call_once(|| {
 *             let handle = alloc_irt_entry().unwrap();
 *             handle.enable(irq_num as u32);
 *             handle
 *         });
 *     }
 *     pub(crate) fn remapping_index(&self) -> Option<u16> {
 *         Some(self.entry.get()?.index())
 *     }
 * }
 */
pub(crate) struct IrqRemapping;

impl IrqRemapping {
    pub(crate) const fn new() -> Self {
        Self
    }

    pub(crate) fn init(&self, _irq_num: u8) {}

    pub(crate) fn remapping_index(&self) -> Option<u16> {
        None
    }
}

/* Local IRQ hardware operations are not required by the PCI dependency slice.
 * Origin Rust:
// FIXME: Mark this as unsafe. See
// <https://github.com/asterinas/asterinas/issues/1120#issuecomment-2748696592>.
pub(crate) fn enable_local() {
    x86_64::instructions::interrupts::enable();
    // When emulated with QEMU, interrupts may not be delivered if a STI instruction is immediately
    // followed by a RET instruction. It is a BUG of QEMU, see the following patch for details.
    // https://lore.kernel.org/qemu-devel/20231210190147.129734-2-lrh2000@pku.edu.cn/
    x86_64::instructions::nop();
}

/// Enables local IRQs and halts the CPU to wait for interrupts.
///
/// This method guarantees that no interrupts can occur in the middle. In other words, IRQs must
/// either have been processed before this method is called, or they must wake the CPU up from the
/// halting state.
//
// FIXME: Mark this as unsafe. See
// <https://github.com/asterinas/asterinas/issues/1120#issuecomment-2748696592>.
pub(crate) fn enable_local_and_halt() {
    // SAFETY:
    // 1. `sti` is safe to use because its safety requirement is upheld by the caller.
    // 2. `hlt` is safe to use because it halts the CPU for interrupts.
    unsafe {
        // Intel(R) 64 and IA-32 Architectures Software Developer's Manual says:
        // "If IF = 0, maskable hardware interrupts remain inhibited on the instruction boundary
        // following an execution of STI."
        //
        // So interrupts will only occur at or after the HLT instruction, which guarantee that
        // interrupts won't occur between enabling the local IRQs and halting the CPU.
        core::arch::asm!("sti", "hlt", options(nomem, nostack, preserves_flags),)
    };
} */

pub(crate) fn disable_local() {
    // x86_64::instructions::interrupts::disable();
    unimplemented!()
}

pub(crate) fn is_local_enabled() -> bool {
    // (rflags::read_raw() & RFlags::INTERRUPT_FLAG.bits()) != 0
    unimplemented!()
}

// ####### Inter-Processor Interrupts (IPIs) #######
/*
/// Hardware-specific, architecture-dependent CPU ID.
///
/// This is the Local APIC ID in the x86_64 architecture.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct HwCpuId(u32);

impl HwCpuId {
    pub(crate) fn read_current(guard: &dyn PinCurrentCpu) -> Self {
        use crate::arch::kernel::apic;

        let apic = apic::get_or_init(guard);
        Self(apic.id())
    }
}

/// Sends a general inter-processor interrupt (IPI) to the specified CPU.
///
/// # Safety
///
/// The caller must ensure that the interrupt number is valid and that
/// the corresponding handler is configured correctly on the remote CPU.
/// Furthermore, invoking the interrupt handler must also be safe.
pub(crate) unsafe fn send_ipi(hw_cpu_id: HwCpuId, irq_num: u8, guard: &dyn PinCurrentCpu) {
    use crate::arch::kernel::apic::{self, Icr};

    let icr = Icr::new(
        apic::ApicId::from(hw_cpu_id.0),
        apic::DestinationShorthand::NoShorthand,
        apic::TriggerMode::Edge,
        apic::Level::Assert,
        apic::DeliveryStatus::Idle,
        apic::DestinationMode::Physical,
        apic::DeliveryMode::Fixed,
        irq_num,
    );

    let apic = apic::get_or_init(guard);
    // SAFETY: The ICR is valid to generate the request IPI. Generating the request IPI is safe
    // as guaranteed by the caller.
    unsafe { apic.send_ipi(icr) };
} */
