// SPDX-License-Identifier: MPL-2.0
//! The architecture support of context switch.
//!
//! # Verified Properties
//!
//! The contracts cover the saved register values in Rust. The assembly
//! `context_switch` is outside verification; it does not save or restore TLS.
use vstd::prelude::*;

use crate::task::TaskContextApi;

core::arch::global_asm!(include_str!("switch.S"));

verus! {

#[verus_verify]
#[derive(Debug, Default, Clone, Copy)]
#[repr(C)]
pub(crate) struct TaskContext {
    pub regs: CalleeRegs,
    pub pc: usize,
    pub fsbase: usize,
}

/// Callee-saved registers.
#[verus_verify]
#[derive(Debug, Default, Clone, Copy)]
#[repr(C)]
pub struct CalleeRegs {
    /// sp
    pub sp: u64,
    /// s0
    pub s0: u64,
    /// s1
    pub s1: u64,
    /// s2
    pub s2: u64,
    /// s3
    pub s3: u64,
    /// s4
    pub s4: u64,
    /// s5
    pub s5: u64,
    /// s6
    pub s6: u64,
    /// s7
    pub s7: u64,
    /// s8
    pub s8: u64,
    /// s9
    pub s9: u64,
    /// s10
    pub s10: u64,
    /// s11
    pub s11: u64,
}

#[verus_verify]
impl CalleeRegs {
    /// Creates new `CalleeRegs`
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::new())]
    pub const fn new() -> Self {
        CalleeRegs {
            sp: 0,
            s0: 0,
            s1: 0,
            s2: 0,
            s3: 0,
            s4: 0,
            s5: 0,
            s6: 0,
            s7: 0,
            s8: 0,
            s9: 0,
            s10: 0,
            s11: 0,
        }
    }
}

// Closed projections let public method contracts describe this crate-private type.
impl TaskContext {
    /// The saved callee registers, exposed through a closed specification.
    pub closed spec fn regs_spec(&self) -> CalleeRegs {
        self.regs
    }

    /// The saved instruction pointer, exposed through a closed specification.
    pub closed spec fn pc_spec(&self) -> usize {
        self.pc
    }

    /// The saved TLS pointer, exposed through a closed specification.
    pub closed spec fn fsbase_spec(&self) -> usize {
        self.fsbase
    }
}

#[verus_verify]
impl TaskContext {
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::new())]
    pub const fn new() -> Self {
        TaskContext { regs: CalleeRegs::new(), pc: 0, fsbase: 0 }
    }

    /// Sets thread-local storage pointer.
    #[verus_spec(ensures
        final(self).fsbase_spec() == tls,
        final(self).regs_spec() == old(self).regs_spec(),
        final(self).pc_spec() == old(self).pc_spec(),
    )]
    pub fn set_tls_pointer(&mut self, tls: usize) {
        self.fsbase = tls;
    }

    /// Gets thread-local storage pointer.
    #[verus_spec(returns self.fsbase_spec())]
    pub fn tls_pointer(&self) -> usize {
        self.fsbase
    }
}

#[verus_verify]
impl TaskContextApi for TaskContext {
    #[verus_spec(ensures
        final(self).pc_spec() == ip,
        final(self).regs_spec() == old(self).regs_spec(),
        final(self).fsbase_spec() == old(self).fsbase_spec(),
    )]
    fn set_instruction_pointer(&mut self, ip: usize) {
        self.pc = ip;
    }

    #[verus_spec(returns self.pc_spec())]
    fn instruction_pointer(&self) -> usize {
        self.pc
    }

    #[verus_spec(ensures
        final(self).regs_spec() == (CalleeRegs { sp: sp as u64, ..old(self).regs_spec() }),
        final(self).pc_spec() == old(self).pc_spec(),
        final(self).fsbase_spec() == old(self).fsbase_spec(),
    )]
    fn set_stack_pointer(&mut self, sp: usize) {
        self.regs.sp = sp as u64;
    }

    #[verus_spec(returns self.regs_spec().sp as usize)]
    fn stack_pointer(&self) -> usize {
        self.regs.sp as usize
    }
}

} // verus!
extern "C" {
    pub(crate) fn context_switch(cur: *mut TaskContext, nxt: *const TaskContext);
}
