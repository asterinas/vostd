use vstd::prelude::*;

verus! {

pub struct PageTableFlags { }

#[allow(non_snake_case)]
impl PageTableFlags {

    /// Specifies whether the mapped frame or page table is loaded in memory.
    #[verifier::inline]
    pub open spec fn PRESENT_spec() -> usize {
        0b00000001
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(PRESENT_spec)]
    pub const fn PRESENT() -> (res: usize)
        ensures res == Self::PRESENT_spec()
    {
        0b00000001
    }

    /// Controls whether writes to the mapped frames are allowed.
    #[verifier::inline]
    pub open spec fn WRITABLE_spec() -> usize {
        0b00000010
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(WRITABLE_spec)]
    pub const fn WRITABLE() -> (res: usize)
        ensures res == Self::WRITABLE_spec()
    {
        0b00000010
    }

    /// Controls whether accesses from userspace (i.e. ring 3) are permitted.
    #[verifier::inline]
    pub open spec fn USER_spec() -> usize {
        0b00000100
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(USER_spec)]
    pub const fn USER() -> (res: usize)
        ensures res == Self::USER_spec()
    {
        0b00000100
    }

    /// If this bit is set, a “write-through” policy is used for the cache, else a “write-back” policy is used.
    #[verifier::inline]
    pub open spec fn WRITE_THROUGH_spec() -> usize {
        0b00001000
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(WRITE_THROUGH_spec)]
    pub const fn WRITE_THROUGH() -> (res: usize)
        ensures res == Self::WRITE_THROUGH_spec()
    {
        0b00001000
    }

    /// Disables caching for the pointed entry if cacheable.
    #[verifier::inline]
    pub open spec fn NO_CACHE_spec() -> usize {
        0b00010000
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(NO_CACHE_spec)]
    pub const fn NO_CACHE() -> (res: usize)
        ensures res == Self::NO_CACHE_spec()
    {
        0b00010000
    }

    /// Whether this entry has been used for linear-address translation.
    #[verifier::inline]
    pub open spec fn ACCESSED_spec() -> usize {
        0b00100000
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(ACCESSED_spec)]
    pub const fn ACCESSED() -> (res: usize)
        ensures res == Self::ACCESSED_spec()
    {
        0b00100000
    }

    /// Whether the memory area represented by this entry is modified.
    #[verifier::inline]
    pub open spec fn DIRTY_spec() -> usize {
        0b01000000
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(DIRTY_spec)]
    pub const fn DIRTY() -> (res: usize)
        ensures res == Self::DIRTY_spec()
    {
        0b01000000
    }

    /// Only in the non-starting and non-ending levels, indication of huge page.
    #[verifier::inline]
    pub open spec fn HUGE_spec() -> usize {
        0b10000000
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(HUGE_spec)]
    pub const fn HUGE() -> (res: usize)
        ensures res == Self::HUGE_spec()
    {
        0b10000000
    }

    /// Indicates that the mapping is present in all address spaces, so it isn't flushed from the TLB on an address space switch.
    #[verifier::inline]
    pub open spec fn GLOBAL_spec() -> usize {
        0b00000001_00000000
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(GLOBAL_spec)]
    pub const fn GLOBAL() -> (res: usize)
        ensures res == Self::GLOBAL_spec()
    {
        0b00000001_00000000
    }

    #[verifier::inline]
    pub open spec fn NO_EXECUTE_spec() -> usize {
        1usize << 63
    }

    /// Forbid constute codes on the page. The NXE bits in EFER msr must be set.
    #[inline(always)]
    #[verifier::when_used_as_spec(NO_EXECUTE_spec)]
    pub const fn NO_EXECUTE() -> (res: usize)
        ensures res == Self::NO_EXECUTE_spec()
    {
        1usize << 63
    }

}


}
