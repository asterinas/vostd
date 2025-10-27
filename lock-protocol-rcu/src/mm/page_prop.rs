use vstd::prelude::*;

// Copied from aster_common
// TODO: Check if it's correct
verus! {

#[verifier::ext_equal]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PageProperty {
    /// Whether the page has a mapping.
    ///
    /// If it is `false`. The page doesn't have a mapping, but may contain
    /// metadata that is marked by the user.
    pub has_map: bool,
    /// The flags associated with the page,
    pub flags: PageFlags,
    /// The cache policy for the page.
    pub cache: CachePolicy,
    pub priv_flags: PrivilegedPageFlags,
}

global layout PageProperty is size == 4, align == 1;

} // verus!
verus! {

pub broadcast proof fn lemma_page_property_equal_correctness(a: PageProperty, b: PageProperty)
    requires
        #[trigger] a.flags == #[trigger] b.flags,
        a.cache == b.cache,
        a.priv_flags == b.priv_flags,
        a.has_map == b.has_map,
    ensures
        a == b,
{
}

pub broadcast proof fn lemma_page_property_equal_soundness(a: PageProperty, b: PageProperty)
    requires
        a == b,
    ensures
        #[trigger] a.flags == #[trigger] b.flags,
        a.cache == b.cache,
        a.priv_flags == b.priv_flags,
{
}

} // verus!
verus! {

impl PageProperty {
    #[vstd::contrib::auto_spec]
    pub fn new(flags: PageFlags, cache: CachePolicy) -> Self {
        Self { has_map: true, flags, cache, priv_flags: PrivilegedPageFlags::USER() }
    }

    #[vstd::contrib::auto_spec]
    pub fn new_absent() -> Self {
        Self {
            has_map: false,
            flags: PageFlags::empty(),
            cache: CachePolicy::Writeback,
            priv_flags: PrivilegedPageFlags::empty(),
        }
    }
}

} // verus!
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
    #[vstd::contrib::auto_spec]
    pub const fn N() -> (res: usize) {
        (CachePolicy::Writeback.value() + 1) as usize
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn value(&self) -> (res: u8) {
        match self {
            CachePolicy::Uncacheable => 0u8,
            CachePolicy::WriteCombining => 1,
            CachePolicy::WriteProtected => 2,
            CachePolicy::Writethrough => 3,
            CachePolicy::Writeback => 4,
        }
    }
}

} // verus!
verus! {

#[verifier::ext_equal]
#[repr(transparent)]
#[derive(Copy, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct PageFlags {
    pub bits: u8,
}

pub broadcast proof fn lemma_page_flags_equal_correctness(a: PageFlags, b: PageFlags)
    requires
        #[trigger] a.bits == #[trigger] b.bits,
    ensures
        a == b,
{
}

pub broadcast proof fn lemma_page_flags_equal_soundness(a: PageFlags, b: PageFlags)
    requires
        a == b,
    ensures
        #[trigger] a.bits == #[trigger] b.bits,
{
}

impl PageFlags {
    pub open spec fn present(self) -> bool {
        self.bits & 0b00000001 != 0
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn empty() -> Self {
        Self { bits: 0 }
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    #[deprecated(note = "Use `bits()` instead. It is now aligned with asterinas.")]
    pub const fn value(&self) -> u8 {
        self.bits
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn bits(&self) -> u8 {
        self.bits
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub fn from_bits(value: u8) -> Self {
        Self { bits: value }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn R() -> Self {
        Self { bits: 0b00000001 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn W() -> Self {
        Self { bits: 0b00000010 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn X() -> Self {
        Self { bits: 0b00000100 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn RW() -> Self {
        Self { bits: Self::R().bits() | Self::W().bits() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn RX() -> Self {
        Self { bits: Self::R().bits() | Self::X().bits() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn RWX() -> Self {
        Self { bits: Self::R().bits() | Self::W().bits() | Self::X().bits() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn ACCESSED() -> Self {
        Self { bits: 0b00001000 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn DIRTY() -> Self {
        Self { bits: 0b00010000 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn AVAIL1() -> Self {
        Self { bits: 0b01000000 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn AVAIL2() -> Self {
        Self { bits: 0b10000000 }
    }
}

} // verus!
verus! {

#[verifier::ext_equal]
#[repr(transparent)]
#[derive(Copy, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct PrivilegedPageFlags {
    pub bits: u8,
}

pub broadcast proof fn lemma_privileged_page_flags_equal_correctness(
    a: PrivilegedPageFlags,
    b: PrivilegedPageFlags,
)
    requires
        #[trigger] a.bits == #[trigger] b.bits,
    ensures
        a == b,
{
}

pub broadcast proof fn lemma_privileged_page_flags_equal_soundness(
    a: PrivilegedPageFlags,
    b: PrivilegedPageFlags,
)
    requires
        a == b,
    ensures
        #[trigger] a.bits == #[trigger] b.bits,
{
}

impl PrivilegedPageFlags {
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn empty() -> (res: Self) {
        Self { bits: 0 }
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    #[deprecated(note = "Use `bits()` instead. It is now aligned with asterinas.")]
    pub const fn value(&self) -> u8 {
        self.bits
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn bits(&self) -> u8 {
        self.bits
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub fn from_bits(value: u8) -> Self {
        Self { bits: value }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn USER() -> Self {
        Self { bits: 0b00000001 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn GLOBAL() -> Self {
        Self { bits: 0b00000010 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn SHARED() -> Self {
        Self { bits: 0b10000000 }
    }
}

} // verus!
