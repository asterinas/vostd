// SPDX-License-Identifier: MPL-2.0
//! External declaration of the trap-frame interface from tdx-guest 0.4.0.
use vstd::prelude::*;

use tdx_guest::TdxTrapFrame;

verus! {

#[verifier::external_trait_specification]
pub trait ExTdxTrapFrame {
    type ExternalTraitSpecificationFor: TdxTrapFrame;

    fn rax(&self) -> usize;

    fn set_rax(&mut self, rax: usize);

    fn rbx(&self) -> usize;

    fn set_rbx(&mut self, rbx: usize);

    fn rcx(&self) -> usize;

    fn set_rcx(&mut self, rcx: usize);

    fn rdx(&self) -> usize;

    fn set_rdx(&mut self, rdx: usize);

    fn rsi(&self) -> usize;

    fn set_rsi(&mut self, rsi: usize);

    fn rdi(&self) -> usize;

    fn set_rdi(&mut self, rdi: usize);

    fn rip(&self) -> usize;

    fn set_rip(&mut self, rip: usize);

    fn r8(&self) -> usize;

    fn set_r8(&mut self, r8: usize);

    fn r9(&self) -> usize;

    fn set_r9(&mut self, r9: usize);

    fn r10(&self) -> usize;

    fn set_r10(&mut self, r10: usize);

    fn r11(&self) -> usize;

    fn set_r11(&mut self, r11: usize);

    fn r12(&self) -> usize;

    fn set_r12(&mut self, r12: usize);

    fn r13(&self) -> usize;

    fn set_r13(&mut self, r13: usize);

    fn r14(&self) -> usize;

    fn set_r14(&mut self, r14: usize);

    fn r15(&self) -> usize;

    fn set_r15(&mut self, r15: usize);

    fn rbp(&self) -> usize;

    fn set_rbp(&mut self, rbp: usize);
}

} // verus!
