// SPDX-License-Identifier: MPL-2.0
//! Handles trap across kernel and user space.
// mod handler;
pub mod irq;

#[cfg(target_arch = "riscv64")]
pub(crate) use crate::arch::trap::TrapFrame;

// pub(crate) use handler::call_irq_callback_functions;
// pub use handler::{in_interrupt_context, register_bottom_half_handler};
