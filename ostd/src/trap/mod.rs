// SPDX-License-Identifier: MPL-2.0
//! Handles trap across kernel and user space.
// mod handler;
pub mod irq;

// pub(crate) use handler::call_irq_callback_functions;
// pub use handler::{in_interrupt_context, register_bottom_half_handler};

/* Restore the Asterinas v0.15 re-export for `ostd::user`'s `crate::trap::TrapFrame` import,
 * gated to riscv64 while x86_64/loongarch64 `arch::trap` modules remain commented out.
 * Origin Rust: pub use crate::arch::trap::TrapFrame;
 */
#[cfg(target_arch = "riscv64")]
pub use crate::arch::trap::TrapFrame;
