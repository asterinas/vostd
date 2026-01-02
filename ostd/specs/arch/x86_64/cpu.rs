use vstd::prelude::*;

verus! {

#[derive(Clone, Default, Copy, Debug)]
#[repr(C)]
pub struct CpuExceptionInfo {
    /// The ID of the exception.
    pub id: usize,
    /// The error code associated with the exception.
    pub error_code: usize,
    /// The virtual address where a page fault occurred.
    pub page_fault_addr: usize,
}

} // verus!
