// SPDX-License-Identifier: MPL-2.0
pub(super) mod acpi;
pub(super) mod apic;
pub(super) mod irq;
pub(super) mod tsc;

pub use irq::{IrqChip, MappedIrqLine, IRQ_CHIP};
