// SPDX-License-Identifier: MPL-2.0
use vstd::{arithmetic::power2::*, prelude::*};
use vstd_extra::{external::ilog2::*, ownership::Inv};

use crate::specs::arch::valid_frame_paddr;

use alloc::fmt;
use core::ops::Range;

use crate::{
    Pod,
    mm::{
        MAX_PADDR, Paddr, PagingConstsTrait, PagingLevel, PodOnce, Vaddr,
        page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags as PrivFlags},
        page_table::PageTableEntryTrait,
    },
};

verus! {

/// Size of a base page on RISC-V.
pub const PAGE_SIZE: usize = 4096;

/// Size of a RISC-V page-table entry.
pub const PTE_SIZE: usize = 8;

/// Number of entries in a RISC-V page-table node.
pub const NR_ENTRIES: usize = 512;

/// Number of translation levels used by the Sv48 configuration.
pub const NR_LEVELS: usize = 4;

/// Width of canonical virtual addresses used by the Sv48 configuration.
pub const ADDRESS_WIDTH: usize = 48;

/// Highest level at which a PTE may directly map a page (Sv48 allows a level-4 leaf).
pub const HIGHEST_TRANSLATION_LEVEL: PagingLevel = 4;

/// Whether virtual addresses use sign extension.
pub const VA_SIGN_EXT: bool = true;

pub(crate) const NR_ENTRIES_PER_PAGE: usize = 512;

#[derive(Clone, Debug, Default)]
pub struct PagingConsts {}

/* Origin Rust:
 * impl PagingConstsTrait for PagingConsts {
 *     const BASE_PAGE_SIZE: usize = 4096;
 *     const NR_LEVELS: PagingLevel = 4;
 *     const ADDRESS_WIDTH: usize = 48;
 *     const VA_SIGN_EXT: bool = true;
 *     const HIGHEST_TRANSLATION_LEVEL: PagingLevel = 4;
 *     const PTE_SIZE: usize = core::mem::size_of::<PageTableEntry>();
 * }
 */

impl PagingConstsTrait for PagingConsts {
    #[verifier::inline]
    open spec fn BASE_PAGE_SIZE_spec() -> usize {
        PAGE_SIZE
    }

    #[inline(always)]
    fn BASE_PAGE_SIZE() -> usize {
        PAGE_SIZE
    }

    #[verifier::inline]
    open spec fn NR_LEVELS_spec() -> PagingLevel {
        NR_LEVELS as PagingLevel
    }

    #[inline(always)]
    fn NR_LEVELS() -> PagingLevel {
        NR_LEVELS as PagingLevel
    }

    #[verifier::inline]
    open spec fn ADDRESS_WIDTH_spec() -> usize {
        ADDRESS_WIDTH
    }

    #[inline(always)]
    fn ADDRESS_WIDTH() -> usize {
        ADDRESS_WIDTH
    }

    #[verifier::inline]
    open spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel {
        HIGHEST_TRANSLATION_LEVEL
    }

    #[inline(always)]
    fn HIGHEST_TRANSLATION_LEVEL() -> PagingLevel {
        HIGHEST_TRANSLATION_LEVEL
    }

    #[verifier::inline]
    open spec fn VA_SIGN_EXT_spec() -> bool {
        VA_SIGN_EXT
    }

    #[inline(always)]
    fn VA_SIGN_EXT() -> bool {
        VA_SIGN_EXT
    }

    #[verifier::inline]
    open spec fn PTE_SIZE_spec() -> usize {
        PTE_SIZE
    }

    #[inline(always)]
    fn PTE_SIZE() -> usize {
        PTE_SIZE
    }

    proof fn lemma_paging_consts_requirements() {
        lemma_pow2_is_pow2_to64();
        lemma2_to64();

        lemma_usize_pow2_ilog2(12);
        lemma_usize_pow2_ilog2(9);
    }
}

pub proof fn lemma_nr_subpage_per_huge_eq_nr_entries()
    ensures
        crate::mm::nr_subpage_per_huge::<PagingConsts>() == NR_ENTRIES,
{
}

} // verus!
bitflags::bitflags! {
    /* #[derive(Pod)]
     * #[repr(C)] */
    /// Possible flags for a page table entry.
    pub struct PageTableFlags: usize {
        /// Specifies whether the mapped frame or page table is valid.
        const VALID = 1usize << 0;
        /// Controls whether reads to the mapped frames are allowed.
        const READABLE = 1usize << 1;
        /// Controls whether writes to the mapped frames are allowed.
        const WRITABLE = 1usize << 2;
        /// Controls whether execution code in the mapped frames are allowed.
        const EXECUTABLE = 1usize << 3;
        /// Controls whether accesses from userspace (i.e. U-mode) are permitted.
        const USER = 1usize << 4;
        /// Indicates that the mapping is present in all address spaces, so it isn't flushed from
        /// the TLB on an address space switch.
        const GLOBAL = 1usize << 5;
        /// Whether the memory area represented by this entry is accessed.
        const ACCESSED = 1usize << 6;
        /// Whether the memory area represented by this entry is modified.
        const DIRTY = 1usize << 7;

        // First bit ignored by MMU.
        const RSV1 = 1usize << 8;
        // Second bit ignored by MMU.
        const RSV2 = 1usize << 9;

        // PBMT: Non-cacheable, idempotent, weakly-ordered (RVWMO), main memory
        const PBMT_NC = 1usize << 61;
        // PBMT: Non-cacheable, non-idempotent, strongly-ordered (I/O ordering), I/O
        const PBMT_IO = 1usize << 62;
        /// Naturally aligned power-of-2
        const NAPOT = 1usize << 63;
    }
}

pub(crate) fn tlb_flush_addr(vaddr: Vaddr) {
    unsafe {
        riscv::asm::sfence_vma(0, vaddr);
    }
}

pub(crate) fn tlb_flush_addr_range(range: &Range<Vaddr>) {
    for vaddr in range.clone().step_by(PAGE_SIZE) {
        tlb_flush_addr(vaddr);
    }
}

pub(crate) fn tlb_flush_all_excluding_global() {
    // TODO: excluding global?
    riscv::asm::sfence_vma_all()
}

pub(crate) fn tlb_flush_all_including_global() {
    riscv::asm::sfence_vma_all()
}

#[verus_verify]
#[derive(Clone, Copy /*Pod, Default*/)]
#[repr(C)]
pub struct PageTableEntry(usize);

// SAFETY: `PageTableEntry` is a `repr(C)` wrapper around `usize` with no padding,
// so every bit pattern is a valid value.
#[verus_verify]
unsafe impl Pod for PageTableEntry {}

verus! {

global layout PageTableEntry is size == 8, align == 8;

impl PageTableEntry {
    pub proof fn lemma_layout()
        ensures
            core::mem::size_of::<PageTableEntry>() == 8,
            core::mem::align_of::<PageTableEntry>() == 8,
            core::mem::size_of::<PageTableEntry>() % core::mem::align_of::<PageTableEntry>() == 0,
    {
        broadcast use VERUS_layout_of_PageTableEntry;

    }

    pub closed spec fn default_spec() -> Self {
        Self(0)
    }
}

/* Implement the derived zero default explicitly to give it a Verus specification.
 * Origin Rust: #[derive(Default)]
 */

impl Default for PageTableEntry {
    #[verus_spec(returns Self::default_spec())]
    fn default() -> Self {
        Self(usize::default())
    }
}

} // verus!
/// Activate the given level 4 page table.
///
/// "satp" register doesn't have a field that encodes the cache policy,
/// so `_root_pt_cache` is ignored.
///
/// # Safety
///
/// Changing the level 4 page table is unsafe, because it's possible to violate memory safety by
/// changing the page mapping.
pub unsafe fn activate_page_table(root_paddr: Paddr, _root_pt_cache: CachePolicy) {
    assert!(root_paddr % PagingConsts::BASE_PAGE_SIZE() == 0);
    let ppn = root_paddr >> 12;
    riscv::register::satp::set(riscv::register::satp::Mode::Sv48, 0, ppn);
}

verus! {

/// Abstracts the active page-table root address.
pub uninterp spec fn current_page_table_paddr_spec() -> Paddr;

} // verus!
#[verus_verify]
#[verifier::external_body]
#[verifier::when_used_as_spec(current_page_table_paddr_spec)]
#[verus_spec(returns current_page_table_paddr_spec())]
pub fn current_page_table_paddr() -> Paddr {
    // The hardware read is trusted; the contract does not model satp transitions.
    riscv::register::satp::read().ppn() << 12
}

#[verus_verify]
impl PageTableEntry {
    const PHYS_ADDR_MASK: usize = 0x003F_FFFF_FFFF_FC00;

    #[verus_spec(returns Self((paddr >> 12) << 10))]
    fn new_paddr(paddr: Paddr) -> Self {
        let ppn = paddr >> 12;
        Self(ppn << 10)
    }
}

/// Parse a bit-flag bits `val` in the representation of `from` to `to` in bits.
macro_rules! parse_flags {
    ($val:expr, $from:expr, $to:expr) => {
        ($val as usize & $from.bits() as usize) >> $from.bits().ilog2() << $to.bits().ilog2()
    };
}

#[verus_verify]
impl PodOnce for PageTableEntry {}

verus! {

impl PageTableEntryTrait for PageTableEntry {
    fn new_absent() -> Self {
        proof {
            assert(Self::default_spec() == Self(0)) by (compute_only);
            assert(Self::new_absent_spec() == Self(0)) by (compute_only);
            assert(Self(0).paddr() == 0) by (compute_only);
            assert(!Self(0).is_present()) by (compute_only);
        }
        Self::default()
    }

    fn is_present(&self) -> bool {
        self.0 & PageTableFlags::VALID().bits() != 0
    }

    open spec fn new_page_req(_paddr: Paddr, _level: PagingLevel, prop: PageProperty) -> bool {
        &&& prop.inv()
        &&& (prop.cache is Writeback || prop.cache is Uncacheable)
        &&& prop.flags.bits() & PageFlags::RWX().bits() != 0
        &&& prop.flags.bits() & (PageFlags::ACCESSED().bits() | PageFlags::DIRTY().bits()) == 0
    }

    fn new_page(paddr: Paddr, _level: PagingLevel, prop: PageProperty) -> Self {
        let mut pte = Self::new_paddr(paddr);
        /* Initialize VALID before set_prop, which now leaves absent entries unchanged.
         * Origin Rust: <none; new executable code>
         */
        pte.0 |= PageTableFlags::VALID().bits();
        proof {
            lemma_page_property_flag_constants();
            assert((((paddr >> 12) << 10) | 1usize) & 1usize != 0) by (bit_vector);
            assert(pte.is_present());
        }
        pte.set_prop(prop);
        proof {
            let raw = (paddr >> 12) << 10;
            assert((raw | 1usize) & Self::PHYS_ADDR_MASK == raw & Self::PHYS_ADDR_MASK)
                by (bit_vector);
            lemma_set_prop_roundtrip(raw, prop);
            lemma_auxiliary_bit_properties(paddr);
            lemma_auxiliary_bit_properties(pte.0);
            assert(((raw & Self::PHYS_ADDR_MASK) >> 10) << 12 == ((((raw | 1usize)
                & Self::PHYS_ADDR_MASK) >> 10) << 12)) by (bit_vector);
            assert(pte == Self::new_page_spec(paddr, _level, prop));
        }
        pte
    }

    fn new_pt(paddr: Paddr) -> Self {
        // In RISC-V, non-leaf PTE should have RWX = 000,
        // and D, A, and U are reserved for future standard use.
        let pte = Self::new_paddr(paddr);
        proof {
            lemma_page_property_flag_constants();
            lemma_auxiliary_bit_properties(paddr);
            let raw = pte.0 | PageTableFlags::VALID().bits();
            lemma_auxiliary_bit_properties(raw);
            assert(raw & 1usize != 0) by (bit_vector)
                requires
                    raw == ((paddr >> 12) << 10) | 1usize,
            ;
            assert(Self::new_pt_spec(paddr) == Self(raw));
            assert(raw & 14usize == 0) by (bit_vector)
                requires
                    raw == ((paddr >> 12) << 10) | 1usize,
            ;
        }
        PageTableEntry(pte.0 | PageTableFlags::VALID().bits())
    }

    fn paddr(&self) -> Paddr {
        proof {
            self.lemma_paddr_is_page_aligned();
        }
        let ppn = (self.0 & Self::PHYS_ADDR_MASK) >> 10;
        ppn << 12
    }

    fn prop(&self) -> PageProperty {
        proof {
            lemma_auxiliary_bit_properties(self.0);
            lemma_page_property_flag_constants();
        }
        let flags = (parse_flags!(self.0, PageTableFlags::READABLE(), PageFlags::R())) | (
        parse_flags!(self.0, PageTableFlags::WRITABLE(), PageFlags::W())) | (
        parse_flags!(self.0, PageTableFlags::EXECUTABLE(), PageFlags::X())) | (
        parse_flags!(self.0, PageTableFlags::ACCESSED(), PageFlags::ACCESSED())) | (
        parse_flags!(self.0, PageTableFlags::DIRTY(), PageFlags::DIRTY())) | (
        parse_flags!(self.0, PageTableFlags::RSV1(), PageFlags::AVAIL1())) | (
        parse_flags!(self.0, PageTableFlags::RSV2(), PageFlags::AVAIL2()));
        let priv_flags = (parse_flags!(self.0, PageTableFlags::USER(), PrivFlags::USER())) | (
        parse_flags!(self.0, PageTableFlags::GLOBAL(), PrivFlags::GLOBAL()));
        let cache = if self.0 & PageTableFlags::PBMT_IO().bits() != 0 {
            CachePolicy::Uncacheable
        } else {
            CachePolicy::Writeback
        };

        proof {
            let raw = self.0;
            assert((flags as u8) & 0xdfu8 == flags as u8) by (bit_vector)
                requires
                    flags == ((raw & 2usize) >> 1 << 0) | ((raw & 4usize) >> 2 << 1) | ((raw
                        & 8usize) >> 3 << 2) | ((raw & 64usize) >> 6 << 3) | ((raw & 128usize) >> 7
                        << 4) | ((raw & 256usize) >> 8 << 6) | ((raw & 512usize) >> 9 << 7),
            ;
            assert((priv_flags as u8) & 3u8 == priv_flags as u8) by (bit_vector)
                requires
                    priv_flags == ((raw & 16usize) >> 4 << 0) | ((raw & 32usize) >> 5 << 1),
            ;
        }
        PageProperty {
            flags: PageFlags::from_bits(flags as u8).unwrap(),
            cache,
            priv_flags: PrivFlags::from_bits(priv_flags as u8).unwrap(),
        }
    }

    open spec fn set_prop_req(self, prop: PageProperty) -> bool {
        &&& prop.inv()
        &&& (prop.cache is Writeback || prop.cache is Uncacheable)
        &&& prop.flags.bits() & PageFlags::RWX().bits() != 0
        &&& prop.flags.bits() & (PageFlags::ACCESSED().bits() | PageFlags::DIRTY().bits()) == 0
    }

    #[verus_spec(
        ensures
            old(self).is_present() ==> final(self).as_usize_spec()
                == Self::raw_set_prop_spec(old(self).as_usize_spec(), prop),
    )]
    fn set_prop(&mut self, prop: PageProperty) {
        /* Honor the trait's no-op contract for absent entries. The original RISC-V
         * implementation unconditionally set VALID, contrary to that contract.
         * Latest Asterinas fixed this by refactoring the page-table entry design:
         * https://github.com/asterinas/asterinas/commit/c77c2686d85a1952683db21d7bd7e287f4e8b883
         * Origin Rust: <none; new executable code>
         */
        if !self.is_present() {
            return;
        }
        proof {
            lemma_page_property_flag_constants();
            assert(old(self).set_prop_req(prop));
        }
        let mut flags = PageTableFlags::VALID().bits()
            | parse_flags!(prop.flags.bits(), PageFlags::R(), PageTableFlags::READABLE())
            | parse_flags!(prop.flags.bits(), PageFlags::W(), PageTableFlags::WRITABLE())
            | parse_flags!(prop.flags.bits(), PageFlags::X(), PageTableFlags::EXECUTABLE())
            | parse_flags!(
                prop.priv_flags.bits(),
                PrivFlags::USER(),
                PageTableFlags::USER()
            )
            | parse_flags!(
                prop.priv_flags.bits(),
                PrivFlags::GLOBAL(),
                PageTableFlags::GLOBAL()
            )
            | parse_flags!(prop.flags.bits(), PageFlags::AVAIL1(), PageTableFlags::RSV1())
            | parse_flags!(prop.flags.bits(), PageFlags::AVAIL2(), PageTableFlags::RSV2());

        let ghost base_flags = flags;
        match prop.cache {
            CachePolicy::Writeback => (),
            CachePolicy::Uncacheable => {
                // Currently, Asterinas uses `Uncacheable` for I/O memory.
                flags |= PageTableFlags::PBMT_IO().bits()
            },
            _ => panic!("unsupported cache policy"),
        }

        self.0 = (self.0 & Self::PHYS_ADDR_MASK) | flags;
        proof {
            let raw = self.0;
            let old_raw = old(self).0;
            let cache = if prop.cache is Uncacheable {
                PageTableFlags::PBMT_IO().bits()
            } else {
                0usize
            };
            let uncacheable = prop.cache is Uncacheable;
            let updated = Self::raw_set_prop_spec(old_raw, prop);
            assert(flags == base_flags | cache) by (bit_vector)
                requires
                    uncacheable ==> flags == base_flags | cache,
                    !uncacheable ==> flags == base_flags && cache == 0usize,
            ;
            assert(raw == updated) by (bit_vector)
                requires
                    raw == (old_raw & Self::PHYS_ADDR_MASK) | flags,
                    flags == base_flags | cache,
                    updated == ((old_raw & Self::PHYS_ADDR_MASK) | base_flags) | cache,
            ;
            lemma_set_prop_roundtrip(old_raw, prop);
        }
    }

    fn is_last(&self, level: PagingLevel) -> bool {
        /* Integer masks avoid Verus's BitOr specification dependency-order issue.
         * Origin Rust:
         * let rwx = PageTableFlags::READABLE() | PageTableFlags::WRITABLE()
         *     | PageTableFlags::EXECUTABLE();
         * level == 1 || (self.0 & rwx.bits()) != 0
         */
        let rwx = PageTableFlags::READABLE().bits() | PageTableFlags::WRITABLE().bits()
            | PageTableFlags::EXECUTABLE().bits();
        level == 1 || (self.0 & rwx) != 0
    }

    closed spec fn new_absent_spec() -> Self {
        Self(0)
    }

    closed spec fn is_present_spec(&self) -> bool {
        self.0 & PageTableFlags::VALID().bits() != 0
    }

    closed spec fn new_page_spec(paddr: Paddr, _level: PagingLevel, prop: PageProperty) -> Self {
        Self(Self::raw_set_prop_spec((paddr >> 12) << 10, prop))
    }

    closed spec fn new_pt_spec(paddr: Paddr) -> Self {
        Self(((paddr >> 12) << 10) | PageTableFlags::VALID().bits())
    }

    closed spec fn paddr_spec(&self) -> Paddr {
        ((self.0 & Self::PHYS_ADDR_MASK) >> 10) << 12
    }

    closed spec fn prop_spec(&self) -> PageProperty {
        let flags = (parse_flags!(self.0, PageTableFlags::READABLE(), PageFlags::R())) | (
        parse_flags!(self.0, PageTableFlags::WRITABLE(), PageFlags::W())) | (
        parse_flags!(self.0, PageTableFlags::EXECUTABLE(), PageFlags::X())) | (
        parse_flags!(self.0, PageTableFlags::ACCESSED(), PageFlags::ACCESSED())) | (
        parse_flags!(self.0, PageTableFlags::DIRTY(), PageFlags::DIRTY())) | (
        parse_flags!(self.0, PageTableFlags::RSV1(), PageFlags::AVAIL1())) | (
        parse_flags!(self.0, PageTableFlags::RSV2(), PageFlags::AVAIL2()));
        let priv_flags = (parse_flags!(self.0, PageTableFlags::USER(), PrivFlags::USER())) | (
        parse_flags!(self.0, PageTableFlags::GLOBAL(), PrivFlags::GLOBAL()));
        PageProperty {
            flags: PageFlags::from_bits(flags as u8)->0,
            cache: if self.0 & PageTableFlags::PBMT_IO().bits() != 0 {
                CachePolicy::Uncacheable
            } else {
                CachePolicy::Writeback
            },
            priv_flags: PrivFlags::from_bits(priv_flags as u8)->0,
        }
    }

    closed spec fn is_last_spec(&self, level: PagingLevel) -> bool {
        level == 1 || (self.0 & (PageTableFlags::READABLE().bits()
            | PageTableFlags::WRITABLE().bits() | PageTableFlags::EXECUTABLE().bits())) != 0
    }

    closed spec fn as_usize_spec(self) -> usize {
        self.0
    }

    proof fn lemma_page_table_entry_properties() {
        Self::lemma_layout();
        lemma_page_property_flag_constants();
        assert(Self::new_absent().paddr() == 0) by (compute_only);
        assert(!Self::new_absent().is_present()) by (compute_only);
        assert forall|level: PagingLevel| 1 < level implies !(#[trigger] Self::new_absent().is_last(
            level,
        )) by {
            assert(Self::new_absent().is_last(level) == (level == 1)) by (compute);
        }
        assert forall|paddr: Paddr, level: PagingLevel, prop: PageProperty|
            #![trigger Self::new_page(paddr, level, prop)]
            Self::new_page_req(paddr, level, prop) && (prop.cache is Writeback
                || prop.cache is Writethrough || prop.cache is Uncacheable) implies {
            &&& Self::new_page(paddr, level, prop).is_present()
            &&& (paddr < MAX_PADDR ==> Self::new_page(paddr, level, prop).paddr() == paddr & !((
            PAGE_SIZE - 1) as usize))
            &&& (paddr < MAX_PADDR && paddr % PAGE_SIZE == 0 ==> Self::new_page(
                paddr,
                level,
                prop,
            ).paddr() == paddr)
            &&& Self::new_page(paddr, level, prop).prop() == prop
            &&& Self::new_page(paddr, level, prop).is_last(level)
        } by {
            let raw = (paddr >> 12) << 10;
            lemma_set_prop_roundtrip(raw, prop);
            lemma_auxiliary_bit_properties(paddr);
            assert(((raw & Self::PHYS_ADDR_MASK) >> 10) << 12 == ((((raw | 1usize)
                & Self::PHYS_ADDR_MASK) >> 10) << 12)) by (bit_vector);
        }
        assert forall|paddr: Paddr|
            #![trigger Self::new_pt(paddr)]
            {
                &&& Self::new_pt(paddr).is_present()
                &&& (paddr < MAX_PADDR ==> Self::new_pt(paddr).paddr() == paddr & !((PAGE_SIZE
                    - 1) as usize))
                &&& (paddr < MAX_PADDR && paddr % PAGE_SIZE == 0 ==> Self::new_pt(paddr).paddr()
                    == paddr)
                &&& forall|level: PagingLevel| 1 < level ==> !Self::new_pt(paddr).is_last(level)
            } by {
            lemma_auxiliary_bit_properties(paddr);
            let raw = ((paddr >> 12) << 10) | 1usize;
            assert(raw & 1usize != 0 && raw & 14usize == 0) by (bit_vector)
                requires
                    raw == ((paddr >> 12) << 10) | 1usize,
            ;
        }
    }

    proof fn lemma_paddr_is_page_aligned(self) {
        lemma_auxiliary_bit_properties(self.0);
    }
}

proof fn lemma_page_property_flag_constants()
    ensures
        PageTableFlags::VALID().bits() == 1,
        PageTableFlags::PBMT_IO().bits() == 0x4000_0000_0000_0000usize,
        PageTableFlags::READABLE().bits() | PageTableFlags::WRITABLE().bits()
            | PageTableFlags::EXECUTABLE().bits() == 14usize,
        PageTableFlags::READABLE().bits() == 0x2,
        PageTableFlags::READABLE().bits().ilog2() == 1,
        PageTableFlags::WRITABLE().bits() == 0x4,
        PageTableFlags::WRITABLE().bits().ilog2() == 2,
        PageTableFlags::EXECUTABLE().bits() == 0x8,
        PageTableFlags::EXECUTABLE().bits().ilog2() == 3,
        PageTableFlags::USER().bits() == 0x10,
        PageTableFlags::USER().bits().ilog2() == 4,
        PageTableFlags::GLOBAL().bits() == 0x20,
        PageTableFlags::GLOBAL().bits().ilog2() == 5,
        PageTableFlags::ACCESSED().bits() == 0x40,
        PageTableFlags::ACCESSED().bits().ilog2() == 6,
        PageTableFlags::DIRTY().bits() == 0x80,
        PageTableFlags::DIRTY().bits().ilog2() == 7,
        PageTableFlags::RSV1().bits() == 0x100,
        PageTableFlags::RSV1().bits().ilog2() == 8,
        PageTableFlags::RSV2().bits() == 0x200,
        PageTableFlags::RSV2().bits().ilog2() == 9,
        PageFlags::R().bits() == 0x1,
        PageFlags::R().bits().ilog2() == 0,
        PageFlags::W().bits() == 0x2,
        PageFlags::W().bits().ilog2() == 1,
        PageFlags::X().bits() == 0x4,
        PageFlags::X().bits().ilog2() == 2,
        PageFlags::ACCESSED().bits() == 0x8,
        PageFlags::ACCESSED().bits().ilog2() == 3,
        PageFlags::DIRTY().bits() == 0x10,
        PageFlags::DIRTY().bits().ilog2() == 4,
        PageFlags::AVAIL1().bits() == 0x40,
        PageFlags::AVAIL1().bits().ilog2() == 6,
        PageFlags::AVAIL2().bits() == 0x80,
        PageFlags::AVAIL2().bits().ilog2() == 7,
        PrivFlags::USER().bits() == 0x1,
        PrivFlags::USER().bits().ilog2() == 0,
        PrivFlags::GLOBAL().bits() == 0x2,
        PrivFlags::GLOBAL().bits().ilog2() == 1,
        PageFlags::all().bits() == 0xdfu8,
        PrivFlags::all().bits() == 0x3u8,
{
    lemma_usize_ilog2_to32();
    assert(PageTableFlags::VALID().bits() == 1) by (compute_only);
    assert(PageTableFlags::PBMT_IO().bits() == 0x4000_0000_0000_0000usize) by (compute_only);
    assert(PageTableFlags::READABLE().bits() | PageTableFlags::WRITABLE().bits()
        | PageTableFlags::EXECUTABLE().bits() == 14usize) by (compute_only);
    assert(PageTableFlags::READABLE().bits() == 0x2) by (compute_only);
    assert(PageTableFlags::WRITABLE().bits() == 0x4) by (compute_only);
    assert(PageTableFlags::EXECUTABLE().bits() == 0x8) by (compute_only);
    assert(PageTableFlags::USER().bits() == 0x10) by (compute_only);
    assert(PageTableFlags::GLOBAL().bits() == 0x20) by (compute_only);
    assert(PageTableFlags::ACCESSED().bits() == 0x40) by (compute_only);
    assert(PageTableFlags::DIRTY().bits() == 0x80) by (compute_only);
    assert(PageTableFlags::RSV1().bits() == 0x100) by (compute_only);
    assert(PageTableFlags::RSV2().bits() == 0x200) by (compute_only);
    broadcast use PageFlags::lemma_consts, PrivFlags::lemma_consts;

    assert((0u8 | 0x1u8 | 0x2u8 | 0x4u8 | 0x3u8 | 0x5u8 | 0x7u8 | 0x8u8 | 0x10u8 | 0x40u8 | 0x80u8)
        == 0xdfu8) by (bit_vector);
    assert((0u8 | 0x1u8 | 0x2u8 | 0u8) == 0x3u8) by (bit_vector);
}

} // verus!
impl fmt::Debug for PageTableEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut f = f.debug_struct("PageTableEntry");
        f.field("raw", &format_args!("{:#x}", self.0))
            .field("paddr", &format_args!("{:#x}", self.paddr()))
            .field("present", &self.is_present())
            .field(
                "flags",
                &PageTableFlags::from_bits_truncate(self.0 & !Self::PHYS_ADDR_MASK),
            )
            .field("prop", &self.prop())
            .finish()
    }
}

pub(crate) fn __memcpy_fallible(dst: *mut u8, src: *const u8, size: usize) -> usize {
    // TODO: implement fallible
    unsafe {
        riscv::register::sstatus::set_sum();
    }
    unsafe { core::ptr::copy(src, dst, size) };
    0
}

pub(crate) fn __memset_fallible(dst: *mut u8, value: u8, size: usize) -> usize {
    // TODO: implement fallible
    unsafe {
        riscv::register::sstatus::set_sum();
    }
    unsafe { core::ptr::write_bytes(dst, value, size) };
    0
}

verus! {

impl PageTableEntry {
    /// Encodes page properties for construction and present-entry updates, clearing A/D bits.
    pub closed spec fn raw_set_prop_spec(old_raw: usize, prop: PageProperty) -> usize {
        let flags = PageTableFlags::VALID().bits()
            | parse_flags!(prop.flags.bits(), PageFlags::R(), PageTableFlags::READABLE())
            | parse_flags!(prop.flags.bits(), PageFlags::W(), PageTableFlags::WRITABLE())
            | parse_flags!(prop.flags.bits(), PageFlags::X(), PageTableFlags::EXECUTABLE())
            | parse_flags!(prop.priv_flags.bits(), PrivFlags::USER(), PageTableFlags::USER())
            | parse_flags!(prop.priv_flags.bits(), PrivFlags::GLOBAL(), PageTableFlags::GLOBAL())
            | parse_flags!(prop.flags.bits(), PageFlags::AVAIL1(), PageTableFlags::RSV1())
            | parse_flags!(prop.flags.bits(), PageFlags::AVAIL2(), PageTableFlags::RSV2());
        (old_raw & Self::PHYS_ADDR_MASK) | flags | if prop.cache is Uncacheable {
            PageTableFlags::PBMT_IO().bits()
        } else {
            0usize
        }
    }
}

proof fn lemma_set_prop_roundtrip(old_raw: usize, prop: PageProperty)
    requires
        prop.inv(),
        prop.cache is Writeback || prop.cache is Uncacheable,
        prop.flags.bits() & PageFlags::RWX().bits() != 0,
        prop.flags.bits() & (PageFlags::ACCESSED().bits() | PageFlags::DIRTY().bits()) == 0,
    ensures
        PageTableEntry(PageTableEntry::raw_set_prop_spec(old_raw, prop)).prop() == prop,
        PageTableEntry(PageTableEntry::raw_set_prop_spec(old_raw, prop)).paddr() == PageTableEntry(
            old_raw,
        ).paddr(),
        PageTableEntry(PageTableEntry::raw_set_prop_spec(old_raw, prop)).is_present(),
        forall|level: PagingLevel|
            PageTableEntry(PageTableEntry::raw_set_prop_spec(old_raw, prop)).is_last(level),
{
    broadcast use PageFlags::lemma_consts;

    lemma_page_property_flag_constants();
    assert(0x8u8 | 0x10u8 == 0x18u8) by (bit_vector);
    let raw = PageTableEntry::raw_set_prop_spec(old_raw, prop);
    let f = prop.flags.bits();
    let p = prop.priv_flags.bits();
    let cache = if prop.cache is Uncacheable {
        0x4000_0000_0000_0000usize
    } else {
        0usize
    };
    let decoded_flags = (((raw & 2usize) >> 1 << 0) | ((raw & 4usize) >> 2 << 1) | ((raw & 8usize)
        >> 3 << 2) | ((raw & 64usize) >> 6 << 3) | ((raw & 128usize) >> 7 << 4) | ((raw & 256usize)
        >> 8 << 6) | ((raw & 512usize) >> 9 << 7)) as u8;
    let decoded_priv_flags = (((raw & 16usize) >> 4 << 0) | ((raw & 32usize) >> 5 << 1)) as u8;
    assert(decoded_flags == f && decoded_priv_flags == p && raw & 1usize != 0 && raw & 14usize != 0
        && (raw & PageTableEntry::PHYS_ADDR_MASK) == (old_raw & PageTableEntry::PHYS_ADDR_MASK) && (
    raw & 0x4000_0000_0000_0000usize) == cache) by (bit_vector)
        requires
            f & 0xdfu8 == f,
            p & 3u8 == p,
            f & 7u8 != 0,
            f & 0x18u8 == 0,
            cache == 0usize || cache == 0x4000_0000_0000_0000usize,
            raw == (old_raw & PageTableEntry::PHYS_ADDR_MASK) | (1usize | ((f as usize & 1usize)
                >> 0 << 1) | ((f as usize & 2usize) >> 1 << 2) | ((f as usize & 4usize) >> 2 << 3)
                | ((p as usize & 1usize) >> 0 << 4) | ((p as usize & 2usize) >> 1 << 5) | ((
            f as usize & 64usize) >> 6 << 8) | ((f as usize & 128usize) >> 7 << 9)) | cache,
            decoded_flags == (((raw & 2usize) >> 1 << 0) | ((raw & 4usize) >> 2 << 1) | ((raw
                & 8usize) >> 3 << 2) | ((raw & 64usize) >> 6 << 3) | ((raw & 128usize) >> 7 << 4)
                | ((raw & 256usize) >> 8 << 6) | ((raw & 512usize) >> 9 << 7)) as u8,
            decoded_priv_flags == (((raw & 16usize) >> 4 << 0) | ((raw & 32usize) >> 5 << 1)) as u8,
    ;
    PageFlags::lemma_from_bits_bits(decoded_flags);
    PrivFlags::lemma_from_bits_bits(decoded_priv_flags);
    PageFlags::lemma_eq_from_bits(PageTableEntry(raw).prop().flags, prop.flags);
    PrivFlags::lemma_eq_from_bits(PageTableEntry(raw).prop().priv_flags, prop.priv_flags);
}

#[verifier::bit_vector]
proof fn lemma_auxiliary_bit_properties(addr: usize)
    ensures
        (((addr & PageTableEntry::PHYS_ADDR_MASK) >> 10) << 12) % PAGE_SIZE == 0,
        addr % PAGE_SIZE == 0 ==> addr & !((PAGE_SIZE - 1) as usize) == addr,
        addr < MAX_PADDR ==> addr & !((PAGE_SIZE - 1) as usize) < MAX_PADDR,
        addr < MAX_PADDR ==> (((((addr >> 12) << 10) | 1usize) & PageTableEntry::PHYS_ADDR_MASK)
            >> 10) << 12 == addr & !((PAGE_SIZE - 1) as usize),
{
}

} // verus!
