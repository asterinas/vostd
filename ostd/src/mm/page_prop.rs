// SPDX-License-Identifier: MPL-2.0
//! Definitions of page mapping properties.
use vstd::prelude::*;
use vstd_extra::prelude::*;

use core::fmt::Debug;

use bitflags::bitflags;

/// The property of a mapped virtual memory page.
#[verus_verify]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PageProperty {
    /// The flags associated with the page,
    pub flags: PageFlags,
    /// The cache policy for the page.
    pub cache: CachePolicy,
    pub priv_flags: PrivilegedPageFlags,
}

#[verus_verify]
impl PageProperty {
    /// Creates a new `PageProperty` with the given flags and cache policy for the user.
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::new_user(flags, cache))]
    pub fn new_user(flags: PageFlags, cache: CachePolicy) -> Self {
        Self {
            flags,
            cache,
            priv_flags: PrivilegedPageFlags::USER(),
        }
    }

    /// Creates a page property that implies an invalid page without mappings.
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::new_absent())]
    pub fn new_absent() -> Self {
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
#[verus_verify]
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
        //const RW = Self::R.bits | Self::W.bits;
        const RW = 0b00000011;
        /// Readable + executable.
        //const RX = Self::R.bits | Self::X.bits;
        const RX = 0b00000101;
        /// Readable + writable + executable.
        //const RWX = Self::R.bits | Self::W.bits | Self::X.bits;
        const RWX = 0b00000111;
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

bitflags! {
    /// Page property that are only accessible in OSTD.
    pub struct PrivilegedPageFlags: u8 {
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

verus! {

impl Inv for PageProperty {
    open spec fn inv(self) -> bool {
        &&& self.flags.bits() & PageFlags::all().bits() == self.flags.bits()
        &&& self.priv_flags.bits() & PrivilegedPageFlags::all().bits() == self.priv_flags.bits()
    }
}

impl PageProperty {
    /// Adding and removing `AVAIL1` is reversible when it is used as a reserved tag.
    pub proof fn lemma_avail1_tag_encoding(self)
        ensures
            self.flags.union(PageFlags::AVAIL1()).contains(PageFlags::AVAIL1()),
            !self.flags.difference(PageFlags::AVAIL1()).contains(PageFlags::AVAIL1()),
            !self.flags.contains(PageFlags::AVAIL1()) ==> self.flags.difference(PageFlags::AVAIL1())
                == self.flags,
            !self.flags.contains(PageFlags::AVAIL1()) ==> self.flags.union(
                PageFlags::AVAIL1(),
            ).difference(PageFlags::AVAIL1()) == self.flags,
            self.flags.contains(PageFlags::AVAIL1()) ==> self.flags.difference(
                PageFlags::AVAIL1(),
            ).union(PageFlags::AVAIL1()) == self.flags,
    {
        broadcast use PageFlags::lemma_consts;

        let tag = PageFlags::AVAIL1();
        let bits = self.flags.bits();
        let tag_bits = tag.bits();
        assert(((bits | tag_bits) & tag_bits) == tag_bits) by (bit_vector);
        assert(((bits & !tag_bits) & tag_bits) == 0u8) by (bit_vector);
        if !self.flags.contains(tag) {
            assert((bits & tag_bits) != tag_bits);
            assert((bits & tag_bits) == 0u8) by (bit_vector)
                requires
                    tag_bits == 0x40u8,
                    (bits & tag_bits) != tag_bits,
            ;
            assert((bits & !tag_bits) == bits) by (bit_vector)
                requires
                    (bits & tag_bits) == 0u8,
            ;
            assert(((bits | tag_bits) & !tag_bits) == bits) by (bit_vector)
                requires
                    (bits & tag_bits) == 0u8,
            ;
            PageFlags::lemma_eq_from_bits(self.flags.difference(tag), self.flags);
            PageFlags::lemma_eq_from_bits(self.flags.union(tag).difference(tag), self.flags);
        } else {
            assert((bits & tag_bits) == tag_bits);
            assert(((bits & !tag_bits) | tag_bits) == bits) by (bit_vector)
                requires
                    (bits & tag_bits) == tag_bits,
            ;
            PageFlags::lemma_eq_from_bits(self.flags.difference(tag).union(tag), self.flags);
        }
    }
}

} // verus!
