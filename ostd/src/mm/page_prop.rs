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

} // verus!
verus! {

pub broadcast proof fn lemma_page_property_equal_correctness(a: PageProperty, b: PageProperty)
    requires
        #[trigger] a.flags == #[trigger] b.flags,
        a.cache == b.cache,
        a.priv_flags == b.priv_flags,
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
    pub open spec fn new_spec(flags: PageFlags, cache: CachePolicy) -> Self {
        Self { flags, cache, priv_flags: PrivilegedPageFlags::USER() }
    }

    #[verifier::when_used_as_spec(new_spec)]
    pub fn new(flags: PageFlags, cache: CachePolicy) -> (res: Self)
        ensures
            res == Self::new_spec(flags, cache),
    {
        Self { flags, cache, priv_flags: PrivilegedPageFlags::USER() }
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
        ensures
            res == Self::new_absent_spec(),
    {
        Self {
            flags: PageFlags::empty(),
            cache: CachePolicy::Writeback,
            priv_flags: PrivilegedPageFlags::empty(),
        }
    }
}

} // verus!
verus! {

// TODO: Make it more abstract when supporting other architectures.
/// A type to control the cacheability of the main memory.
///
/// The type currently follows the definition as defined by the AMD64 manual.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CachePolicy {
    /// Uncacheable (UC).
    ///
    /// Reads from, and writes to, UC memory are not cacheable.
    /// Reads from UC memory cannot be speculative.
    /// Write-combining to UC memory is not allowed.
    /// Reads from or writes to UC memory cause the write buffers to be written to memory
    /// and be invalidated prior to the access to UC memory.
    ///
    /// The UC memory type is useful for memory-mapped I/O devices
    /// where strict ordering of reads and writes is important.
    Uncacheable,
    /// Write-Combining (WC).
    ///
    /// Reads from, and writes to, WC memory are not cacheable.
    /// Reads from WC memory can be speculative.
    ///
    /// Writes to this memory type can be combined internally by the processor
    /// and written to memory as a single write operation to reduce memory accesses.
    ///
    /// The WC memory type is useful for graphics-display memory buffers
    /// where the order of writes is not important.
    WriteCombining,
    /// Write-Protect (WP).
    ///
    /// Reads from WP memory are cacheable and allocate cache lines on a read miss.
    /// Reads from WP memory can be speculative.
    ///
    /// Writes to WP memory that hit in the cache do not update the cache.
    /// Instead, all writes update memory (write to memory),
    /// and writes that hit in the cache invalidate the cache line.
    /// Write buffering of WP memory is allowed.
    ///
    /// The WP memory type is useful for shadowed-ROM memory
    /// where updates must be immediately visible to all devices that read the shadow locations.
    WriteProtected,
    /// Writethrough (WT).
    ///
    /// Reads from WT memory are cacheable and allocate cache lines on a read miss.
    /// Reads from WT memory can be speculative.
    ///
    /// All writes to WT memory update main memory,
    /// and writes that hit in the cache update the cache line.
    /// Writes that miss the cache do not allocate a cache line.
    /// Write buffering of WT memory is allowed.
    Writethrough,
    /// Writeback (WB).
    ///
    /// The WB memory is the "normal" memory. See detailed descriptions in the manual.
    ///
    /// This type of memory provides the highest-possible performance
    /// and is useful for most software and data stored in system memory (DRAM).
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
    pub const fn value(&self) -> (res: u8)
        ensures
            res == self.value(),
    {
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
    pub const fn empty() -> (res: Self) {
        Self { bits: 0 }
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn value(&self) -> (res: u8) {
        self.bits
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub fn from_bits(value: u8) -> (res: Self)
        ensures
            res.bits == value,
    {
        Self { bits: value }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn R() -> (res: Self) {
        Self { bits: 0b00000001 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn W() -> (res: Self) {
        Self { bits: 0b00000010 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn X() -> (res: Self) {
        Self { bits: 0b00000100 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn RW() -> (res: Self) {
        Self { bits: Self::R().value() | Self::W().value() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn RX() -> (res: Self) {
        Self { bits: Self::R().value() | Self::X().value() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn RWX() -> (res: Self) {
        Self { bits: Self::R().value() | Self::W().value() | Self::X().value() }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn ACCESSED() -> (res: Self) {
        Self { bits: 0b00001000 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn DIRTY() -> (res: Self) {
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
    pub const fn value(&self) -> (res: u8) {
        self.bits
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub fn from_bits(value: u8) -> (res: Self) {
        Self { bits: value }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn USER() -> (res: Self) {
        Self { bits: 0b00000001 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn GLOBAL() -> (res: Self) {
        Self { bits: 0b00000010 }
    }

    #[allow(non_snake_case)]
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn SHARED() -> (res: Self) {
        Self { bits: 0b10000000 }
    }
}

} // verus!
