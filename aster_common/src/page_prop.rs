use vstd::prelude::*;

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

    pub open spec fn new_user_spec(flags: PageFlags, cache: CachePolicy) -> Self {
        Self {
            flags,
            cache,
            priv_flags: PrivilegedPageFlags::USER(),
        }
    }

    #[verifier::when_used_as_spec(new_user_spec)]
    pub fn new_user(flags: PageFlags, cache: CachePolicy) -> (res: Self)
        ensures res == Self::new_user_spec(flags, cache)
    {
        Self {
            flags,
            cache,
            priv_flags: PrivilegedPageFlags::USER(),
        }
    }

    pub open spec fn new_absent_spec() -> Self {
        Self {
            flags: PageFlags::empty(),
            cache: CachePolicy::Writeback,
            priv_flags: PrivilegedPageFlags::empty(),
        }
    }

    #[verifier::when_used_as_spec(new_absent_spec)]
    pub fn new_absent() -> (res: Self)
        ensures res == Self::new_absent_spec()
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
    #[verifier::inline]
    pub open spec fn N_spec() -> usize {
        (CachePolicy::Writeback.value() + 1) as usize
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(N_spec)]
    pub const fn N() -> (res: usize)
        ensures res == Self::N_spec()
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
    pub const fn value(&self) -> (res: u8)
        ensures res == self.value()
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


    #[verifier::inline]
    pub open spec fn empty_spec() -> Self {
        Self { bits: 0 }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(empty_spec)]
    pub const fn empty() -> (res: Self)
        ensures res == Self::empty_spec()
    {
        Self { bits: 0 }
    }

    #[verifier::inline]
    pub open spec fn value_spec(&self) -> u8 {
        self.bits
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(value_spec)]
    pub const fn value(&self) -> (res: u8)
        ensures res == self.value_spec()
    {
        self.bits
    }

    #[verifier::inline]
    pub open spec fn from_bits_spec(value: u8) -> Self {
        Self { bits: value }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(from_bits_spec)]
    pub fn from_bits(value: u8) -> (res: Self)
        ensures
            res == Self::from_bits_spec(value),
            res.bits == value,
    {
        Self { bits: value }
    }

    #[allow(non_snake_case)]
    #[verifier::inline]
    pub open spec fn R_spec() -> Self {
        Self { bits: 0b00000001 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::when_used_as_spec(R_spec)]
    pub const fn R() -> (res: Self)
        ensures res == Self::R_spec()
    {
        Self { bits: 0b00000001 }
    }

    #[allow(non_snake_case)]
    #[verifier::inline]
    pub open spec fn W_spec() -> Self {
        Self { bits: 0b00000010 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::when_used_as_spec(W_spec)]
    pub const fn W() -> (res: Self)
        ensures res == Self::W_spec()
    {
        Self { bits: 0b00000010 }
    }

    #[allow(non_snake_case)]
    #[verifier::inline]
    pub open spec fn X_spec() -> Self {
        Self { bits: 0b00000100 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::when_used_as_spec(X_spec)]
    pub const fn X() -> (res: Self)
        ensures res == Self::X_spec()
    {
        Self { bits: 0b00000100 }
    }

    #[allow(non_snake_case)]
    #[verifier::inline]
    pub open spec fn RW_spec() -> Self {
        Self { bits: Self::R().value() | Self::W().value() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::when_used_as_spec(X_spec)]
    pub const fn RW() -> (res: Self)
        ensures res == Self::RW_spec()
    {
        Self { bits: Self::R().value() | Self::W().value() }
    }

    #[allow(non_snake_case)]
    #[verifier::inline]
    pub open spec fn RX_spec() -> Self {
        Self { bits: Self::R().value() | Self::X().value() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::when_used_as_spec(RX_spec)]
    pub const fn RX() -> (res: Self)
        ensures res == Self::RX_spec()
    {
        Self { bits: Self::R().value() | Self::X().value() }
    }

    #[allow(non_snake_case)]
    #[verifier::inline]
    pub open spec fn RWX_spec() -> Self {
        Self { bits: Self::R().value() | Self::W().value() | Self::X().value() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::when_used_as_spec(RWX_spec)]
    pub const fn RWX() -> (res: Self)
        ensures res == Self::RWX_spec()
    {
        Self { bits: Self::R().value() | Self::W().value() | Self::X().value() }
    }

    #[allow(non_snake_case)]
    #[verifier::inline]
    pub open spec fn ACCESSED_spec() -> Self {
        Self { bits: 0b00001000 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::when_used_as_spec(ACCESSED_spec)]
    pub const fn ACCESSED() -> (res: Self)
        ensures res == Self::ACCESSED_spec()
    {
        Self { bits: 0b00001000 }
    }

    #[allow(non_snake_case)]
    #[verifier::inline]
    pub open spec fn DIRTY_spec() -> Self {
        Self { bits: 0b00010000 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::when_used_as_spec(DIRTY_spec)]
    pub const fn DIRTY() -> (res: Self)
        ensures res == Self::DIRTY_spec()
    {
        Self { bits: 0b00010000 }
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
    #[verifier::inline]
    pub open spec fn empty_spec() -> Self {
        Self { bits: 0 }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(empty_spec)]
    pub const fn empty() -> (res: Self)
        ensures res == Self::empty_spec()
    {
        Self { bits: 0 }
    }

    #[verifier::inline]
    pub open spec fn value_spec(&self) -> u8 {
        self.bits
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(value_spec)]
    pub const fn value(&self) -> (res: u8)
        ensures res == self.value_spec()
    {
        self.bits
    }

    #[verifier::inline]
    pub open spec fn from_bits_spec(value: u8) -> Self {
        Self { bits: value }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(from_bits_spec)]
    pub fn from_bits(value: u8) -> (res: Self)
        ensures res == Self::from_bits_spec(value)
    {
        Self { bits: value }
    }

    #[allow(non_snake_case)]
    #[verifier::inline]
    pub open spec fn USER_spec() -> Self {
        Self { bits: 0b00000001 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::when_used_as_spec(USER_spec)]
    pub const fn USER() -> (res: Self)
        ensures res == Self::USER_spec()
    {
        Self { bits: 0b00000001 }
    }

    #[allow(non_snake_case)]
    #[verifier::inline]
    pub open spec fn GLOBAL_spec() -> Self {
        Self { bits: 0b00000010 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::when_used_as_spec(GLOBAL_spec)]
    pub const fn GLOBAL() -> (res: Self)
        ensures res == Self::GLOBAL_spec()
    {
        Self { bits: 0b00000010 }
    }

    #[allow(non_snake_case)]
    #[verifier::inline]
    pub open spec fn SHARED_spec() -> Self {
        Self { bits: 0b10000000 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[verifier::when_used_as_spec(SHARED_spec)]
    pub const fn SHARED() -> (res: Self)
        ensures res == Self::SHARED_spec()
    {
        Self { bits: 0b10000000 }
    }

}

}
