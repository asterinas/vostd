use vstd::arithmetic::power2::{lemma2_to64, lemma2_to64_rest};
use vstd::prelude::*;
use vstd::arithmetic::{
    power2::pow2,
    logarithm::{log, lemma_log_pow},
};

verus! {
#[verifier::ext_equal]
#[repr(transparent)]
#[derive(Copy, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct PageTableFlags{
    pub bits: usize,
}

#[allow(non_snake_case)]
impl PageTableFlags {

    #[verifier::inline]
    pub open spec fn bits_spec(&self) -> usize {
        self.bits
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(bits_spec)]
    pub const fn bits(&self) -> usize
        returns self.bits_spec()
    {
        self.bits
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(bits_spec)]
    #[deprecated(note = "Use `bits()` instead. It is now aligned with asterinas")]
    pub const fn value(&self) -> usize
        returns self.bits_spec()
    {
        self.bits
    }

    /// Specifies whether the mapped frame or page table is loaded in memory.
    #[verifier::inline]
    pub open spec fn PRESENT_spec() -> Self {
        Self { bits: 0b00000001 }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(PRESENT_spec)]
    pub const fn PRESENT() -> Self
        returns Self::PRESENT_spec()
    {
        Self { bits: 0b00000001 }
    }

    /// Controls whether writes to the mapped frames are allowed.
    #[verifier::inline]
    pub open spec fn WRITABLE_spec() -> Self {
        Self { bits: 0b00000010 }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(WRITABLE_spec)]
    pub const fn WRITABLE() -> Self
        returns Self::WRITABLE_spec()
    {
        Self { bits: 0b00000010 }
    }

    /// Controls whether accesses from userspace (i.e. ring 3) are permitted.
    #[verifier::inline]
    pub open spec fn USER_spec() -> Self {
        Self { bits: 0b00000100 }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(USER_spec)]
    pub const fn USER() -> Self
        returns Self::USER_spec()
    {
        Self { bits: 0b00000100 }
    }

    /// If this bit is set, a “write-through” policy is used for the cache, else a “write-back” policy is used.
    #[verifier::inline]
    pub open spec fn WRITE_THROUGH_spec() -> Self {
        Self { bits: 0b00001000 }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(WRITE_THROUGH_spec)]
    pub const fn WRITE_THROUGH() -> Self
        returns Self::WRITE_THROUGH_spec()
    {
        Self { bits: 0b00001000 }
    }

    /// Disables caching for the pointed entry if cacheable.
    #[verifier::inline]
    pub open spec fn NO_CACHE_spec() -> Self {
        Self { bits: 0b00010000 }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(NO_CACHE_spec)]
    pub const fn NO_CACHE() -> Self
        returns Self::NO_CACHE_spec()
    {
        Self { bits: 0b00010000 }
    }

    /// Whether this entry has been used for linear-address translation.
    #[verifier::inline]
    pub open spec fn ACCESSED_spec() -> Self {
        Self { bits: 0b00100000 }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(ACCESSED_spec)]
    pub const fn ACCESSED() -> Self
        returns Self::ACCESSED_spec()
    {
        Self { bits: 0b00100000 }
    }

    /// Whether the memory area represented by this entry is modified.
    #[verifier::inline]
    pub open spec fn DIRTY_spec() -> Self {
        Self { bits: 0b01000000 }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(DIRTY_spec)]
    pub const fn DIRTY() -> Self
        returns Self::DIRTY_spec()
    {
        Self { bits: 0b01000000 }
    }

    /// Only in the non-starting and non-ending levels, indication of huge page.
    #[verifier::inline]
    pub open spec fn HUGE_spec() -> Self {
        Self { bits: 0b10000000 }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(HUGE_spec)]
    pub const fn HUGE() -> Self
        returns Self::HUGE_spec()
    {
        Self { bits: 0b10000000 }
    }

    /// Indicates that the mapping is present in all address spaces, so it isn't flushed from the TLB on an address space switch.
    #[verifier::inline]
    pub open spec fn GLOBAL_spec() -> Self {
        Self { bits: 0b00000001_00000000 }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(GLOBAL_spec)]
    pub const fn GLOBAL() -> Self
        returns Self::GLOBAL_spec()
    {
        Self { bits: 0b00000001_00000000 }
    }

    #[verifier::inline]
    pub open spec fn NO_EXECUTE_spec() -> Self {
        Self { bits: 1usize << 63 }
    }

    /// Forbid constute codes on the page. The NXE bits in EFER msr must be set.
    #[inline(always)]
    #[verifier::when_used_as_spec(NO_EXECUTE_spec)]
    pub const fn NO_EXECUTE() -> Self
        returns Self::NO_EXECUTE_spec()
    {
        Self { bits: 1usize << 63 }
    }

    #[verifier::external_body]
    pub proof fn lemma_consts_properties()
        ensures
            Self::PRESENT().bits().ilog2() == 0,
            Self::WRITABLE().bits().ilog2() == 1,
            Self::USER().bits().ilog2() == 2,
            Self::WRITE_THROUGH().bits().ilog2() == 3,
            Self::NO_CACHE().bits().ilog2() == 4,
            Self::ACCESSED().bits().ilog2() == 5,
            Self::DIRTY().bits().ilog2() == 6,
            Self::HUGE().bits().ilog2() == 7,
            Self::GLOBAL().bits().ilog2() == 8,
            Self::NO_EXECUTE().bits().ilog2() == 63,
    {
    }

}


}
