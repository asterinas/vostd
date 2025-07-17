use vstd::arithmetic::power2::{lemma2_to64, lemma2_to64_rest};
use vstd::prelude::*;
use vstd::arithmetic::{
    power2::pow2,
    logarithm::{log, lemma_log_pow},
};
use vstd_extra::extra_num::*;

verus! {
#[verifier::ext_equal]
#[repr(transparent)]
#[derive(Copy, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct PageTableFlags{
    pub bits: usize,
}

#[allow(non_snake_case)]
impl PageTableFlags {


    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn bits(&self) -> usize
        returns self.bits
    {
        self.bits
    }

    #[inline(always)]
    #[verifier::allow_in_spec]
    #[deprecated(note = "Use `bits()` instead. It is now aligned with asterinas.")]
    pub const fn value(&self) -> usize
        returns self.bits
    {
        self.bits
    }

    /// Specifies whether the mapped frame or page table is loaded in memory.
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn PRESENT() -> Self
        returns (Self { bits: 0b00000001 })
    {
        Self { bits: 0b00000001 }
    }

    /// Controls whether writes to the mapped frames are allowed.
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn WRITABLE() -> Self
        returns (Self { bits: 0b00000010 })
    {
        Self { bits: 0b00000010 }
    }

    /// Controls whether accesses from userspace (i.e. ring 3) are permitted.
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn USER() -> Self
        returns (Self { bits: 0b00000100 })
    {
        Self { bits: 0b00000100 }
    }

    /// If this bit is set, a “write-through” policy is used for the cache, else a “write-back” policy is used.
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn WRITE_THROUGH() -> Self
        returns (Self { bits: 0b00001000 })
    {
        Self { bits: 0b00001000 }
    }

    /// Disables caching for the pointed entry if cacheable.
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn NO_CACHE() -> Self
        returns (Self { bits: 0b00010000 })
    {
        Self { bits: 0b00010000 }
    }

    /// Whether this entry has been used for linear-address translation.
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn ACCESSED() -> Self
        returns (Self { bits: 0b00100000 })
    {
        Self { bits: 0b00100000 }
    }

    /// Whether the memory area represented by this entry is modified.
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn DIRTY() -> Self
        returns (Self { bits: 0b01000000 })
    {
        Self { bits: 0b01000000 }
    }

    /// Only in the non-starting and non-ending levels, indication of huge page.
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn HUGE() -> Self
        returns (Self { bits: 0b10000000 })
    {
        Self { bits: 0b10000000 }
    }

    /// Indicates that the mapping is present in all address spaces, so it isn't flushed from the TLB on an address space switch.
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn GLOBAL() -> Self
        returns (Self { bits: 0b00000001_00000000 })
    {
        Self { bits: 0b00000001_00000000 }
    }

    /// Forbid constute codes on the page. The NXE bits in EFER msr must be set.
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn NO_EXECUTE() -> Self
        returns (Self { bits: 1usize << 63 })
    {
        Self { bits: 1usize << 63 }
    }

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
            Self::NO_EXECUTE().bits() == 0x8000_0000_0000_0000,
    {
        lemma_log2_to64();
        assert(1usize << 63 == 0x8000_0000_0000_0000) by (bit_vector);
        assert(Self::NO_EXECUTE().bits() == 0x8000_0000_0000_0000);
    }

}


}
