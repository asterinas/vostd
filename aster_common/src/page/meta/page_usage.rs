use core::cmp::PartialEq;
use core::fmt::Debug;
use vstd::prelude::*;

verus! {

pub enum PageState {
    Unused,
    Typed,
    Untyped,
}

#[repr(u8)]
#[derive(Debug, PartialEq, Clone, Copy)]
#[rustc_has_incoherent_inherent_impls]
pub enum PageUsage {
    // The zero variant is reserved for the unused type. Only an unused page
    // can be designated for one of the other purposes.
    #[allow(dead_code)]
    Unused,
    /// The page is reserved or unusable. The kernel should not touch it.
    #[allow(dead_code)]
    Reserved,
    /// The page is used as a frame, i.e., a page of untyped memory.
    Frame,
    /// The page is used by a page table.
    PageTable,
    /// The page stores metadata of other pages.
    Meta,
    /// The page stores the kernel such as kernel code, data, etc.
    Kernel,
}

impl PageUsage {
    pub open spec fn as_u8_spec(&self) -> u8 {
        match self {
            PageUsage::Unused => 0,
            PageUsage::Reserved => 1,
            PageUsage::Frame => 32,
            PageUsage::PageTable => 64,
            PageUsage::Meta => 65,
            PageUsage::Kernel => 66,
        }
    }

    #[verifier::external_body]
    #[verifier::when_used_as_spec(as_u8_spec)]
    pub fn as_u8(&self) -> (res: u8)
        ensures
            res == self.as_u8_spec(),
    {
        *self as u8
    }

    #[verifier::contrib::auto_spec]
    pub fn as_state(&self) -> (res: PageState) {
        match &self {
            PageUsage::Unused => PageState::Unused,
            PageUsage::Frame => PageState::Untyped,
            _ => PageState::Typed,
        }
    }
}

} // verus!
