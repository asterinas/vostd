use vstd::prelude::*;
use crate::prelude::*;

use core::fmt::Debug;
use core::clone::Clone;
use core::ops::Range;

verus! {

/// This is a compile-time technique to force the frame developers to distinguish
/// between the kernel global page table instance, process specific user page table
/// instance, and device page table instances.
pub trait PageTableMode: Debug {
    #[allow(non_snake_case)]
    spec fn VADDR_RANGE_spec() -> Range<Vaddr>;

    /// The range of virtual addresses that the page table can manage.
    #[verifier::when_used_as_spec(VADDR_RANGE_spec)]
    #[allow(non_snake_case)]
    #[inline(always)]
    fn VADDR_RANGE() -> (res: Range<Vaddr>)
        ensures
            res == Self::VADDR_RANGE_spec(),
    ;

    #[verifier::inline]
    open spec fn covers_spec(r: &Range<Vaddr>) -> bool {
        (Self::VADDR_RANGE().start <= r.start) && (r.end <= Self::VADDR_RANGE().end)
    }

    /// Check if the given range is covered by the valid virtual address range.
    #[inline(always)]
    #[verifier::when_used_as_spec(covers_spec)]
    #[verifier::external_body]
    fn covers(r: &Range<Vaddr>) -> (res: bool)
        ensures
            res == Self::covers_spec(r),
    {
        (Self::VADDR_RANGE().start <= r.start) && (r.end <= Self::VADDR_RANGE().end)
    }
}

} // verus!
verus! {

use crate::x86_64::mm::MAX_USERSPACE_VADDR;

#[derive(Debug)]
pub struct UserMode {}

impl Clone for UserMode {
    fn clone(&self) -> Self {
        Self {  }
    }
}

impl PageTableMode for UserMode {
    #[verifier::inline]
    open spec fn VADDR_RANGE_spec() -> Range<Vaddr> {
        0..MAX_USERSPACE_VADDR()
    }

    #[inline(always)]
    #[allow(non_snake_case)]
    fn VADDR_RANGE() -> (res: Range<Vaddr>)
        ensures
            res == Self::VADDR_RANGE_spec(),
    {
        0..MAX_USERSPACE_VADDR()
    }
}

} // verus!
verus! {

use crate::x86_64::mm::KERNEL_VADDR_RANGE;

#[derive(Debug)]
pub struct KernelMode {}

impl Clone for KernelMode {
    fn clone(&self) -> Self {
        Self {  }
    }
}

impl PageTableMode for KernelMode {
    #[verifier::inline]
    open spec fn VADDR_RANGE_spec() -> Range<Vaddr> {
        KERNEL_VADDR_RANGE()
    }

    #[inline(always)]
    #[allow(non_snake_case)]
    fn VADDR_RANGE() -> (res: Range<Vaddr>)
        ensures
            res == Self::VADDR_RANGE_spec(),
    {
        KERNEL_VADDR_RANGE()
    }
}

} // verus!
