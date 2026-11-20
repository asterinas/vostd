// SPDX-License-Identifier: MPL-2.0
//! The architecture support of context switch.
//!
//! # Verified Properties
//!
//! Verus verifies the Rust register accessors and trusts `switch.S`.
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

// Closed projections let public method contracts describe this crate-private type.
impl TaskContext {
    /// The saved callee registers, exposed through a closed specification.
    pub closed spec fn regs_spec(&self) -> CalleeRegs {
        self.regs
    }

    /// The saved instruction pointer, exposed through a closed specification.
    pub closed spec fn rip_spec(&self) -> usize {
        self.rip
    }

    /// The saved TLS pointer, exposed through a closed specification.
    pub closed spec fn fsbase_spec(&self) -> usize {
        self.fsbase
    }
}

#[verus_verify]
impl TaskContext {
    /// Creates a context with all saved registers cleared.
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::new())]
    pub const fn new() -> Self {
        Self { regs: CalleeRegs::new(), rip: 0, fsbase: 0 }
    }

    /// Sets thread-local storage pointer.
    #[verus_spec(ensures
        final(self).fsbase_spec() == tls,
        final(self).regs_spec() == old(self).regs_spec(),
        final(self).rip_spec() == old(self).rip_spec(),
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
        final(self).rip_spec() == ip,
        final(self).regs_spec() == old(self).regs_spec(),
        final(self).fsbase_spec() == old(self).fsbase_spec(),
    )]
    fn set_instruction_pointer(&mut self, ip: usize) {
        self.rip = ip;
    }

    /// Gets the saved instruction pointer.
    #[verus_spec(returns self.rip_spec())]
    fn instruction_pointer(&self) -> usize {
        self.rip
    }

    /// Sets the saved stack pointer.
    #[verus_spec(ensures
        final(self).regs_spec() == (CalleeRegs { rsp: sp as u64, ..old(self).regs_spec() }),
        final(self).rip_spec() == old(self).rip_spec(),
        final(self).fsbase_spec() == old(self).fsbase_spec(),
    )]
    fn set_stack_pointer(&mut self, sp: usize) {
        self.regs.rsp = sp as u64;
    }

    /// Gets the saved stack pointer without truncation on x86-64.
    #[verus_spec(returns self.regs_spec().rsp as usize)]
    fn stack_pointer(&self) -> usize {
        self.regs.rsp as usize
    }
}

} // verus!
extern "C" {
    /// Switches from `cur` to `nxt` and returns when `cur` resumes.
    ///
    /// # Safety
    ///
    /// Disable local IRQs and hold both records exclusively. The records and return
    /// slots must be disjoint. Preserve the suspended stack and continuation until resumption.
    /// `nxt` needs a valid continuation, a writable slot at its saved RSP, and ABI alignment
    /// after `ret`. Enable FSGSBASE and use a canonical target FSBASE. Any active shadow
    /// stack must permit the target RIP.
    #[cfg_attr(verus_keep_ghost, allow(improper_ctypes))]
    pub(crate) fn context_switch(
        cur: *mut TaskContext,
        nxt: *const TaskContext,
        #[cfg(verus_keep_ghost)] current: Tracked<&mut PointsTo<TaskContext>>,
        #[cfg(verus_keep_ghost)] next: Tracked<PointsTo<TaskContext>>,
    );
}

#[cfg(verus_keep_ghost)]
verus! {

use vstd::raw_ptr::PointsTo;

pub(crate) assume_specification[ context_switch ](
    cur: *mut TaskContext,
    nxt: *const TaskContext,
    Tracked(current): Tracked<&mut PointsTo<TaskContext>>,
    Tracked(next): Tracked<PointsTo<TaskContext>>,
)
    requires
        old(current).ptr() == cur,
        next.ptr() == nxt,
        cur.addr() != nxt.addr(),
        next.is_init(),
    ensures
        final(current).ptr() == cur,
        final(current).is_init(),
        final(current).value().regs.rsp % 16 == 8,
;

} // verus!
