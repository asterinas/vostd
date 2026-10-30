// SPDX-License-Identifier: MPL-2.0
//! The architecture support of context switch.
//!
//! Verified Properties: the saved-register contracts cover the Rust data
//! operations; the assembly `context_switch` remains outside verification.
use vstd::prelude::*;

use crate::task::TaskContextApi;

core::arch::global_asm!(include_str!("switch.S"));

verus! {

#[verus_verify]
#[derive(Debug, Default, Clone, Copy)]
#[repr(C)]
pub(crate) struct TaskContext {
    pub regs: CalleeRegs,
    pub rip: usize,
    pub fsbase: usize,
}

/// Spec model of the saved context.
pub ghost struct TaskContextView {
    pub regs: CalleeRegs,
    pub rip: usize,
    pub fsbase: usize,
}

impl View for TaskContext {
    type V = TaskContextView;

    closed spec fn view(&self) -> Self::V {
        TaskContextView { regs: self.regs, rip: self.rip, fsbase: self.fsbase }
    }
}

#[verus_verify]
impl TaskContext {
    /// Creates a context with all saved registers cleared.
    #[verus_spec(ret => ensures ret@ == (TaskContextView {
        regs: CalleeRegs::new(), rip: 0, fsbase: 0,
    }))]
    pub const fn new() -> Self {
        Self { regs: CalleeRegs::new(), rip: 0, fsbase: 0 }
    }

    /// Sets thread-local storage pointer.
    #[verus_spec(ensures
        final(self)@ == (TaskContextView { fsbase: tls, ..old(self)@ }),
    )]
    pub fn set_tls_pointer(&mut self, tls: usize) {
        self.fsbase = tls;
    }

    /// Gets thread-local storage pointer.
    #[verus_spec(returns self@.fsbase)]
    pub fn tls_pointer(&self) -> usize {
        self.fsbase
    }
}

/// Callee-saved registers.
#[verus_verify]
#[derive(Debug, Default, Clone, Copy)]
#[repr(C)]
pub struct CalleeRegs {
    /// RSP
    pub rsp: u64,
    /// RBX
    pub rbx: u64,
    /// RBP
    pub rbp: u64,
    /// R12
    pub r12: u64,
    /// R13
    pub r13: u64,
    /// R14
    pub r14: u64,
    /// R15
    pub r15: u64,
}

#[verus_verify]
impl CalleeRegs {
    /// Creates new `CalleeRegs`
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::new())]
    pub const fn new() -> Self {
        CalleeRegs { rsp: 0, rbx: 0, rbp: 0, r12: 0, r13: 0, r14: 0, r15: 0 }
    }
}

#[verus_verify]
impl TaskContextApi for TaskContext {
    /// Sets the saved instruction pointer.
    #[verus_spec(ensures
        final(self)@ == (TaskContextView { rip: ip, ..old(self)@ }),
    )]
    fn set_instruction_pointer(&mut self, ip: usize) {
        self.rip = ip;
    }

    /// Gets the saved instruction pointer.
    #[verus_spec(returns self@.rip)]
    fn instruction_pointer(&self) -> usize {
        self.rip
    }

    /// Sets the saved stack pointer.
    #[verus_spec(ensures
        final(self)@ == (TaskContextView {
            regs: CalleeRegs { rsp: sp as u64, ..old(self)@.regs },
            ..old(self)@
        }),
    )]
    fn set_stack_pointer(&mut self, sp: usize) {
        self.regs.rsp = sp as u64;
    }

    /// Gets the saved stack pointer without truncation on x86-64.
    #[verus_spec(returns self@.regs.rsp as usize)]
    fn stack_pointer(&self) -> usize {
        self.regs.rsp as usize
    }
}

} // verus!
extern "C" {
    pub(crate) fn context_switch(cur: *mut TaskContext, nxt: *const TaskContext);
}
