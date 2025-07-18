use vstd::prelude::*;
use vstd_extra::extra_num::*;

verus! {

#[verifier::ext_equal]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PageProperty {
    /// The flags associated with the page,
    pub flags: PageFlags,
    /// The cache policy for the page.
    pub cache: CachePolicy,
    pub priv_flags: PrivilegedPageFlags,
}

global layout PageProperty is size == 3, align == 1;

}

verus! {

pub broadcast proof fn lemma_page_property_equal_correctness(a: PageProperty,
    b: PageProperty)
    requires #[trigger] a.flags == #[trigger] b.flags,
        a.cache == b.cache,
        a.priv_flags == b.priv_flags,
    ensures
        a == b
{ }

pub broadcast proof fn lemma_page_property_equal_soundness(a: PageProperty, b: PageProperty)
    requires a == b
    ensures #[trigger] a.flags == #[trigger] b.flags,
        a.cache == b.cache,
        a.priv_flags == b.priv_flags,
{ }

}

verus! {

impl PageProperty {

    #[verifier::allow_in_spec]
    pub fn new(flags: PageFlags, cache: CachePolicy) -> Self
        returns (Self {
            flags,
            cache,
            priv_flags: PrivilegedPageFlags::USER(),
        })
    {
        Self {
            flags,
            cache,
            priv_flags: PrivilegedPageFlags::USER(),
        }
    }

    #[verifier::allow_in_spec]
    pub fn new_absent() -> Self
        returns (Self {
            flags: PageFlags::empty(),
            cache: CachePolicy::Writeback,
            priv_flags: PrivilegedPageFlags::empty(),
        })
    {
        Self {
            flags: PageFlags::empty(),
            cache: CachePolicy::Writeback,
            priv_flags: PrivilegedPageFlags::empty(),
        }
    }

}

}

verus! {

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum CachePolicy {
    Uncacheable,
    WriteCombining,
    WriteProtected,
    Writethrough,
    Writeback,
}

#[allow(non_snake_case)]
impl CachePolicy {
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn N() -> usize
        returns (CachePolicy::Writeback.value() + 1) as usize
    {
        (CachePolicy::Writeback.value() + 1) as usize
    }

    #[verifier::inline]
    pub open spec fn value_spec(&self) -> u8 {
        match self {
            CachePolicy::Uncacheable => 0,
            CachePolicy::WriteCombining => 1,
            CachePolicy::WriteProtected => 2,
            CachePolicy::Writethrough => 3,
            CachePolicy::Writeback => 4,
        }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(value_spec)]
    pub const fn value(&self) -> u8
        returns self.value_spec()
    {
        match self {
            CachePolicy::Uncacheable => 0,
            CachePolicy::WriteCombining => 1,
            CachePolicy::WriteProtected => 2,
            CachePolicy::Writethrough => 3,
            CachePolicy::Writeback => 4,
        }
    }
}

}

verus! {

#[verifier::ext_equal]
#[repr(transparent)]
#[derive(Copy, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct PageFlags {
    pub bits: u8,
}

pub broadcast proof fn lemma_page_flags_equal_correctness(a: PageFlags, b: PageFlags)
    requires #[trigger] a.bits == #[trigger] b.bits
    ensures a == b
{ }

pub broadcast proof fn lemma_page_flags_equal_soundness(a: PageFlags, b: PageFlags)
    requires a == b
    ensures #[trigger] a.bits == #[trigger] b.bits
{ }

impl PageFlags {
    pub open spec fn present(self) -> bool {
        self.bits & 0b00000001 != 0
    }

    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn empty() -> Self
        returns (Self { bits: 0 })
    {
        Self { bits: 0 }
    }

    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn bits(&self) -> (res: u8)
        returns self.bits
    {
        self.bits
    }

    #[inline(always)]
    #[verifier::allow_in_spec]
    pub fn from_bits(value: u8) -> (res: Self)
        returns (Self { bits: value })
    {
        Self { bits: value }
    }


    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn R() -> Self
        returns (Self { bits: 0b00000001 })
    {
        Self { bits: 0b00000001 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn W() -> Self
        returns (Self { bits: 0b00000010 })
    {
        Self { bits: 0b00000010 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn X() -> Self
        returns (Self { bits: 0b00000100 })
    {
        Self { bits: 0b00000100 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn RW() -> Self
        returns (Self { bits: Self::R().bits() | Self::W().bits() })
    {
        Self { bits: Self::R().bits() | Self::W().bits() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn RX() -> Self
        returns (Self { bits: Self::R().bits() | Self::X().bits() })
    {
        Self { bits: Self::R().bits() | Self::X().bits() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn RWX() -> Self
        returns (Self { bits: Self::R().bits() | Self::W().bits() | Self::X().bits() })
    {
        Self { bits: Self::R().bits() | Self::W().bits() | Self::X().bits() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn ACCESSED() -> Self
        returns (Self { bits: 0b00001000 })
    {
        Self { bits: 0b00001000 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn DIRTY() -> Self
        returns (Self { bits: 0b00010000 })
    {
        Self { bits: 0b00010000 }
    }

    pub proof fn lemma_consts_properties()
        ensures
            Self::R().bits().ilog2() == 0,
            Self::W().bits().ilog2() == 1,
            Self::X().bits().ilog2() == 2,
            Self::ACCESSED().bits().ilog2() == 3,
            Self::DIRTY().bits().ilog2() == 4,
    {
        lemma_log2_to64();
    }
}

}

verus! {

#[verifier::ext_equal]
#[repr(transparent)]
#[derive(Copy, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct PrivilegedPageFlags {
    pub bits: u8,
}

pub broadcast proof fn lemma_privileged_page_flags_equal_correctness(a: PrivilegedPageFlags, b: PrivilegedPageFlags)
    requires #[trigger] a.bits == #[trigger] b.bits
    ensures a == b
{ }

pub broadcast proof fn lemma_privileged_page_flags_equal_soundness(a: PrivilegedPageFlags, b: PrivilegedPageFlags)
    requires a == b
    ensures #[trigger] a.bits == #[trigger] b.bits
{ }

impl PrivilegedPageFlags {
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn empty() -> Self
        returns (Self { bits: 0 })
    {
        Self { bits: 0 }
    }

    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn bits(&self) -> u8
        returns self.bits
    {
        self.bits
    }

    #[inline(always)]
    #[verifier::allow_in_spec]
    pub fn from_bits(value: u8) -> Self
        returns (Self { bits: value })
    {
        Self { bits: value }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn USER() -> (res: Self)
        returns (Self { bits: 0b00000001 })
    {
        Self { bits: 0b00000001 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn GLOBAL() -> Self
        returns (Self { bits: 0b00000010 })
    {
        Self { bits: 0b00000010 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn SHARED() -> Self
        returns (Self { bits: 0b10000000 })
    {
        Self { bits: 0b10000000 }
    }

    pub proof fn lemma_consts_properties()
        ensures
            Self::USER().bits().ilog2() == 0,
            Self::GLOBAL().bits().ilog2() == 1,
            Self::SHARED().bits().ilog2() == 7,
    {
        lemma_log2_to64();
    }

}

}
