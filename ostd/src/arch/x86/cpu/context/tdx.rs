// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;

use tdx_guest::{
    /*TdgVeInfo,*/
    TdxTrapFrame, /*handle_virtual_exception as do_handle_virtual_exception, tdcall,*/
};

use super::{GeneralRegs /*, UserContext*/};

/*pub(crate) struct VirtualizationExceptionHandler {
    ve_info: TdgVeInfo,
}

impl VirtualizationExceptionHandler {
    /// Creates a VE handler.
    ///
    /// It is important that such a handler is created immediately after a VE happens,
    /// before the local IRQs are re-enabled. This is because the handler needs to retrieve more information
    /// about the last VE from the trusted Intel TDX module. If another VE happens, the information about
    /// the last one held by Intel TDX module would be overridden and lost!
    ///
    /// This constructor method retrieves the VE information from
    /// Intel TDX module and saved into the newly-created instance.
    /// So after instantiating a `VirtualizationExceptionHandler`,
    /// we won't need to worry about triggering a new VE.
    pub fn new() -> Self {
        let ve_info = tdcall::get_veinfo().expect("#VE handler: fail to get VE info\n");
        Self { ve_info }
    }

    pub fn handle(&self, ctx: &mut UserContext) {
        let mut generalrags_wrapper = GeneralRegsWrapper(&mut *ctx.general_regs_mut());
        do_handle_virtual_exception(&mut generalrags_wrapper, &self.ve_info);
        *ctx.general_regs_mut() = *generalrags_wrapper.0;
    }
}*/

#[verus_verify]
struct GeneralRegsWrapper<'a>(&'a mut GeneralRegs);

verus! {

impl View for GeneralRegsWrapper<'_> {
    type V = GeneralRegs;

    closed spec fn view(&self) -> GeneralRegs {
        *self.0
    }
}

} // verus!
#[verus_verify]
impl TdxTrapFrame for GeneralRegsWrapper<'_> {
    #[verus_spec(returns self@.rax)]
    fn rax(&self) -> usize {
        self.0.rax
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { rax, ..old(self)@ }))]
    fn set_rax(&mut self, rax: usize) {
        self.0.rax = rax;
    }
    #[verus_spec(returns self@.rbx)]
    fn rbx(&self) -> usize {
        self.0.rbx
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { rbx, ..old(self)@ }))]
    fn set_rbx(&mut self, rbx: usize) {
        self.0.rbx = rbx;
    }
    #[verus_spec(returns self@.rcx)]
    fn rcx(&self) -> usize {
        self.0.rcx
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { rcx, ..old(self)@ }))]
    fn set_rcx(&mut self, rcx: usize) {
        self.0.rcx = rcx;
    }
    #[verus_spec(returns self@.rdx)]
    fn rdx(&self) -> usize {
        self.0.rdx
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { rdx, ..old(self)@ }))]
    fn set_rdx(&mut self, rdx: usize) {
        self.0.rdx = rdx;
    }
    #[verus_spec(returns self@.rsi)]
    fn rsi(&self) -> usize {
        self.0.rsi
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { rsi, ..old(self)@ }))]
    fn set_rsi(&mut self, rsi: usize) {
        self.0.rsi = rsi;
    }
    #[verus_spec(returns self@.rdi)]
    fn rdi(&self) -> usize {
        self.0.rdi
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { rdi, ..old(self)@ }))]
    fn set_rdi(&mut self, rdi: usize) {
        self.0.rdi = rdi;
    }
    #[verus_spec(returns self@.rip)]
    fn rip(&self) -> usize {
        self.0.rip
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { rip, ..old(self)@ }))]
    fn set_rip(&mut self, rip: usize) {
        self.0.rip = rip;
    }
    #[verus_spec(returns self@.r8)]
    fn r8(&self) -> usize {
        self.0.r8
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { r8, ..old(self)@ }))]
    fn set_r8(&mut self, r8: usize) {
        self.0.r8 = r8;
    }
    #[verus_spec(returns self@.r9)]
    fn r9(&self) -> usize {
        self.0.r9
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { r9, ..old(self)@ }))]
    fn set_r9(&mut self, r9: usize) {
        self.0.r9 = r9;
    }
    #[verus_spec(returns self@.r10)]
    fn r10(&self) -> usize {
        self.0.r10
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { r10, ..old(self)@ }))]
    fn set_r10(&mut self, r10: usize) {
        self.0.r10 = r10;
    }
    #[verus_spec(returns self@.r11)]
    fn r11(&self) -> usize {
        self.0.r11
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { r11, ..old(self)@ }))]
    fn set_r11(&mut self, r11: usize) {
        self.0.r11 = r11;
    }
    #[verus_spec(returns self@.r12)]
    fn r12(&self) -> usize {
        self.0.r12
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { r12, ..old(self)@ }))]
    fn set_r12(&mut self, r12: usize) {
        self.0.r12 = r12;
    }
    #[verus_spec(returns self@.r13)]
    fn r13(&self) -> usize {
        self.0.r13
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { r13, ..old(self)@ }))]
    fn set_r13(&mut self, r13: usize) {
        self.0.r13 = r13;
    }
    #[verus_spec(returns self@.r14)]
    fn r14(&self) -> usize {
        self.0.r14
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { r14, ..old(self)@ }))]
    fn set_r14(&mut self, r14: usize) {
        self.0.r14 = r14;
    }
    #[verus_spec(returns self@.r15)]
    fn r15(&self) -> usize {
        self.0.r15
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { r15, ..old(self)@ }))]
    fn set_r15(&mut self, r15: usize) {
        self.0.r15 = r15;
    }
    #[verus_spec(returns self@.rbp)]
    fn rbp(&self) -> usize {
        self.0.rbp
    }
    #[verus_spec(ensures final(self)@ == (GeneralRegs { rbp, ..old(self)@ }))]
    fn set_rbp(&mut self, rbp: usize) {
        self.0.rbp = rbp;
    }
}
