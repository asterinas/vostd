// SPDX-License-Identifier: MPL-2.0
//! The architecture support of context switch.
//!
//! # Verified Properties
//!
//! The contracts cover the saved register values in Rust. The assembly
//! `context_switch` is outside verification.
use vstd::prelude::*;

use crate::task::TaskContextApi;

core::arch::global_asm!(include_str!("switch.S"));

verus! {

#[verus_verify]
#[derive(Debug, Default, Clone, Copy)]
#[repr(C)]
pub(crate) struct TaskContext {
    pub regs: CalleeRegs,
    pub ra: usize,
    /// Thread-local storage pointer.
    pub tp: usize,
}

/// Callee-saved registers.
#[verus_verify]
#[derive(Debug, Default, Clone, Copy)]
#[repr(C)]
pub struct CalleeRegs {
    /// sp
    pub sp: usize,
    /// fp
    pub fp: usize,
    /// s0
    pub s0: usize,
    /// s1
    pub s1: usize,
    /// s2
    pub s2: usize,
    /// s3
    pub s3: usize,
    /// s4
    pub s4: usize,
    /// s5
    pub s5: usize,
    /// s6
    pub s6: usize,
    /// s7
    pub s7: usize,
    /// s8
    pub s8: usize,
}

#[verus_verify]
impl CalleeRegs {
    /// Creates new `CalleeRegs`
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::new())]
    pub const fn new() -> Self {
        CalleeRegs { sp: 0, fp: 0, s0: 0, s1: 0, s2: 0, s3: 0, s4: 0, s5: 0, s6: 0, s7: 0, s8: 0 }
    }
}

// Closed projections let public method contracts describe this crate-private type.
impl TaskContext {
    /// The saved callee registers, exposed through a closed specification.
    pub closed spec fn regs_spec(&self) -> CalleeRegs {
        self.regs
    }

    /// The saved instruction pointer, exposed through a closed specification.
    pub closed spec fn ra_spec(&self) -> usize {
        self.ra
    }

    /// The saved TLS pointer, exposed through a closed specification.
    pub closed spec fn tp_spec(&self) -> usize {
        self.tp
    }
}

#[verus_verify]
impl TaskContext {
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::new())]
    pub const fn new() -> Self {
        TaskContext { regs: CalleeRegs::new(), ra: 0, tp: 0 }
    }

    /// Sets thread-local storage pointer.
    #[verus_spec(ensures
        final(self).tp_spec() == tls,
        final(self).regs_spec() == old(self).regs_spec(),
        final(self).ra_spec() == old(self).ra_spec(),
    )]
    pub fn set_tls_pointer(&mut self, tls: usize) {
        self.tp = tls;
    }

    /// Gets thread-local storage pointer.
    #[verus_spec(returns self.tp_spec())]
    pub fn tls_pointer(&self) -> usize {
        self.tp
    }
}

#[verus_verify]
impl TaskContextApi for TaskContext {
    #[verus_spec(ensures
        final(self).ra_spec() == ip,
        final(self).regs_spec() == old(self).regs_spec(),
        final(self).tp_spec() == old(self).tp_spec(),
    )]
    fn set_instruction_pointer(&mut self, ip: usize) {
        self.ra = ip;
    }

    #[verus_spec(returns self.ra_spec())]
    fn instruction_pointer(&self) -> usize {
        self.ra
    }

    #[verus_spec(ensures
        final(self).regs_spec() == (CalleeRegs { sp, ..old(self).regs_spec() }),
        final(self).ra_spec() == old(self).ra_spec(),
        final(self).tp_spec() == old(self).tp_spec(),
    )]
    fn set_stack_pointer(&mut self, sp: usize) {
        self.regs.sp = sp;
    }

    #[verus_spec(returns self.regs_spec().sp)]
    fn stack_pointer(&self) -> usize {
        self.regs.sp
    }
}

} // verus!
unsafe extern "C" {
    pub(crate) unsafe fn context_switch(cur: *mut TaskContext, nxt: *const TaskContext);
}
