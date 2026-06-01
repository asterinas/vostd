// SPDX-License-Identifier: MPL-2.0

//! Definitions of page mapping properties.

use vstd::prelude::*;

use core::fmt::Debug;

use bitflags::bitflags;

use core::ops::{Add, BitAnd, BitOr, BitXor, Sub};

verus! {

#[verifier::ext_equal]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PageProperty {
    /// The flags associated with the page,
    pub flags: PageFlags,
    /// The cache policy for the page.
    pub cache: CachePolicy,
    pub priv_flags: PrivilegedPageFlags,
}

global layout PageProperty is size == 3, align == 1;

#[verus_verify]
impl PageProperty {
    /// Creates a new `PageProperty` with the given flags and cache policy for the user.
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::new_user(flags, cache))]
    pub fn new_user(flags: PageFlags, cache: CachePolicy) -> Self
    {
        Self { flags, cache, priv_flags: PrivilegedPageFlags::USER() }
    }

    /// Creates a page property that implies an invalid page without mappings.
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::new_absent())]
    pub fn new_absent() -> Self
    {
        Self {
            flags: PageFlags::empty(),
            cache: CachePolicy::Writeback,
            priv_flags: PrivilegedPageFlags::empty(),
        }
    }
}

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

/* 
bitflags! {
    /// Page protection permissions and access status.
    pub struct PageFlags: u8 {
        /// Readable.
        const R = 0b00000001;
        /// Writable.
        const W = 0b00000010;
        /// Executable.
        const X = 0b00000100;
        /// Readable + writable.
        const RW = Self::R.bits | Self::W.bits;
        /// Readable + executable.
        const RX = Self::R.bits | Self::X.bits;
        /// Readable + writable + executable.
        const RWX = Self::R.bits | Self::W.bits | Self::X.bits;

        /// Has the memory page been read or written.
        const ACCESSED  = 0b00001000;
        /// Has the memory page been written.
        const DIRTY     = 0b00010000;

        /// The first bit available for software use.
        const AVAIL1    = 0b01000000;
        /// The second bit available for software use.
        const AVAIL2    = 0b10000000;
    }
}
*/

#[verifier::ext_equal]
#[repr(transparent)]
#[derive(Copy, Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct PageFlags {
    bits: u8,
}
}

#[verus_verify]
impl PageFlags {
    #[verus_verify]
    #[verus_spec(returns self.bits())]
    pub const fn bits(&self) -> u8 {
        self.bits
    }    

    
    #[verus_spec(ret =>
        ensures ret.bits() == 0, 
        returns Self::empty())]
    pub const fn empty() -> Self {
        Self { bits: 0 }
    }
    
    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret => 
        ensures ret.bits() == 0b00000001,
        returns Self::R())]
    pub const fn R() -> Self {
        Self { bits: 0b00000001 }
    }

    #[verus_verify(dual_spec)]
    #[verus_spec(ret => 
        ensures ret.bits() == 0b00000010,
        returns Self::W())]
    pub const fn W() -> Self {
        Self { bits: 0b00000010 }
    }

    
    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret => 
        ensures ret.bits() == 0b00000100,
        returns Self::X())]
    pub const fn X() -> Self {
        Self { bits: 0b00000100 }
    }

    
    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret => 
        ensures ret.bits() == Self::R().bits() | Self::W().bits(),
        returns Self::RW())]
    pub const fn RW() -> Self {
        Self { bits: Self::R().bits | Self::W().bits }
    }

    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        ensures ret.bits() == Self::R().bits() | Self::X().bits(),
        returns Self::RX())]
    pub const fn RX() -> Self {
        Self { bits: Self::R().bits | Self::X().bits }
    }

    
    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        ensures ret.bits() == Self::R().bits() | Self::W().bits() | Self::X().bits(),
        returns Self::RWX())]
    pub const fn RWX() -> Self {
        Self { bits: Self::R().bits | Self::W().bits | Self::X().bits }
    }

    
    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        ensures ret.bits() == 0b00001000,
        returns Self::ACCESSED())]
    pub const fn ACCESSED() -> Self {
        Self { bits: 0b00001000 }
    }

    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        ensures ret.bits() == 0b00010000,
        returns Self::DIRTY())]
    pub const fn DIRTY() -> Self {
        Self { bits: 0b00010000 }
    }

    
    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        ensures ret.bits() == 0b01000000,
        returns Self::AVAIL1())]
    pub const fn AVAIL1() -> Self {
        Self { bits: 0b01000000 }
    }
    
    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        ensures ret.bits() == 0b10000000,
        returns Self::AVAIL2())]
    pub const fn AVAIL2() -> Self {
        Self { bits: 0b10000000 }
    }

    #[verus_verify(dual_spec)]
    #[verus_spec(returns self.contains(other))]
    pub fn contains(&self, other: Self) -> bool {
        (self.bits & other.bits) == other.bits
    }

    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::from_bits(bits))]
    pub fn from_bits(bits: u8) -> Option<Self> {
        if bits == Self::R().bits() {
            Some(Self::R())
        } else if bits == Self::W().bits() {
            Some(Self::W())
        } else if bits == Self::X().bits() {
            Some(Self::X())
        } else if bits == Self::RW().bits() {
            Some(Self::RW())
        } else if bits == Self::RX().bits() {
            Some(Self::RX())
        } else if bits == Self::RWX().bits() {
            Some(Self::RWX())
        } else if bits == Self::ACCESSED().bits() {
            Some(Self::ACCESSED())
        } else if bits == Self::DIRTY().bits() {
            Some(Self::DIRTY())
        } else if bits == Self::AVAIL1().bits() {
            Some(Self::AVAIL1())
        } else if bits == Self::AVAIL2().bits() {
            Some(Self::AVAIL2())
        } else if bits == Self::empty().bits() {
            Some(Self::empty())
        } else {
            None
        }
    }
}

verus!{
impl Add for PageFlags {
    type Output = Self;

    #[verifier::external_body]
    fn add(self, other: Self) -> Self {
        Self { bits: self.bits + other.bits }
    }
}

impl Sub for PageFlags {
    type Output = Self;

    #[verifier::external_body]
    fn sub(self, other: Self) -> Self {
        Self { bits: self.bits - !other.bits }
    }
}

impl BitOr for PageFlags {
    type Output = Self;

    #[verifier::external_body]
    fn bitor(self, other: Self) -> Self {
        Self { bits: self.bits | other.bits }
    }
}

impl BitAnd for PageFlags {
    type Output = Self;

    #[verifier::external_body]
    fn bitand(self, other: Self) -> Self {
        Self { bits: self.bits & other.bits }
    }
}

impl BitXor for PageFlags {
    type Output = Self;

    #[verifier::external_body]
    fn bitxor(self, other: Self) -> Self {
        Self { bits: self.bits ^ other.bits }
    }
}

/*
bitflags! {
    /// Page property that are only accessible in OSTD.
    pub(crate) struct PrivilegedPageFlags: u8 {
        /// Accessible from user mode.
        const USER      = 0b00000001;
        /// Global page that won't be evicted from TLB with normal TLB flush.
        const GLOBAL    = 0b00000010;

        /// (TEE only) If the page is shared with the host.
        /// Otherwise the page is ensured confidential and not visible outside the guest.
        #[cfg(all(target_arch = "x86_64", feature = "cvm_guest"))]
        const SHARED    = 0b10000000;
    }
}
*/

#[verifier::ext_equal]
#[repr(transparent)]
#[derive(Copy, Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct PrivilegedPageFlags {
    bits: u8,
}
}

#[verus_verify]
impl PrivilegedPageFlags {
    #[verus_verify(dual_spec)]
    #[verus_spec(returns self.bits())]
    pub const fn bits(&self) -> u8 {
        self.bits
    }
    
    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret => 
        ensures ret.bits() == 0,
        returns Self::empty())]
    pub const fn empty() -> Self {
        Self { bits: 0 }
    }

    
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::from_bits(value))]
    pub fn from_bits(value: u8) -> Option<Self> {
        if value == Self::USER().bits() {
            Some(Self::USER())
        } else if value == Self::GLOBAL().bits() {
            Some(Self::GLOBAL())
        } else if value == Self::SHARED().bits() {
            Some(Self::SHARED())
        } else if value == Self::empty().bits() {
            Some(Self::empty())
        } else {
            None
        }
    }

    
    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        ensures ret.bits() == 0b00000001,
        returns Self::USER())]
    pub const fn USER() -> Self {
        Self { bits: 0b00000001 }
    }

    
    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        ensures ret.bits() == 0b00000010,
        returns Self::GLOBAL())]
    pub const fn GLOBAL() -> Self {
        Self { bits: 0b00000010 }
    }

    
    
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        ensures ret.bits() == 0b10000000,
        returns Self::SHARED())]
    pub const fn SHARED() -> Self {
        Self { bits: 0b10000000 }
    }
}