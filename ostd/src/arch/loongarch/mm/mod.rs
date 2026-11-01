// SPDX-License-Identifier: MPL-2.0
use vstd::{arithmetic::power2::*, prelude::*};
use vstd_extra::{external::ilog2::*, ownership::Inv};

use crate::specs::arch::valid_frame_paddr;

use alloc::fmt;
use core::{arch::asm, ops::Range};

use crate::{
    Pod,
    mm::{
        MAX_PADDR, Paddr, PagingConstsTrait, PagingLevel, PodOnce, Vaddr,
        page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags as PrivFlags},
        page_table::PageTableEntryTrait,
    },
};

verus! {

/// Size of a base page on LoongArch.
pub const PAGE_SIZE: usize = 4096;

/// Size of a LoongArch page-table entry.
pub const PTE_SIZE: usize = 8;

/// Number of entries in a LoongArch page-table node.
pub const NR_ENTRIES: usize = 512;

/// Number of page-table levels.
pub const NR_LEVELS: usize = 4;

/// Width of canonical virtual addresses.
pub const ADDRESS_WIDTH: usize = 48;

/// Only base pages are supported by the current LoongArch implementation.
pub const HIGHEST_TRANSLATION_LEVEL: PagingLevel = 1;

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
 *     // TODO: Support huge page
 *     const HIGHEST_TRANSLATION_LEVEL: PagingLevel = 1;
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

} // verus!
/* Use verified bitflags for spec and exec accessors.
 * Origin Rust: bitflags_upstream::bitflags! { ... }
 */
bitflags::bitflags! {
    /* #[derive(Pod)]
     * #[repr(C)] */
    /// Possible flags for a page table entry.
    pub struct PageTableFlags: usize {
        /// Specifies whether the mapped frame is valid.
        const VALID = 1usize << 0;
        /// Whether the memory area represented by this entry is modified.
        const DIRTY = 1usize << 1;
        /// Privilege level corresponding to the page table entry.
        /// When `RPLV` = 0, the page table entry can be accessed by any program
        /// with a privilege level not lower than `PLV`;
        /// When `RPLV` = 1, this page table entry can only be accessed by programs
        /// with privilege level equal to `PLV`.
        const PLVL = 1usize << 2;
        const PLVH = 1usize << 3;
        /// Controls the memory access type of the memory access operation
        /// falling on the address space of the table page entry.
        const MATL = 1usize << 4;
        const MATH = 1usize << 5;
        /// If this entry is a basic page table entry, it is `GLOBAL`,
        /// which means that the mapping is present in all address spaces,
        /// so it isn't flushed from the TLB on an address space switch.
        /// If this entry is a huge page table entry, it is `HUGE`,
        /// which means that the memory area represented by this entry is
        /// a huge page.
        const GLOBAL_OR_HUGE = 1usize << 6;
        /// Specifies whether the mapped frame or page table is loaded in memory.
        /// This flag does not fill in TLB.
        const PRESENT = 1usize << 7;
        /// Controls whether writes to the mapped frames are allowed.
        /// This flag does not fill in TLB.
        const WRITABLE = 1usize << 8;
        // Whether this entry is a basic page table entry.
        const IS_BASIC = 1usize << 9;
        // First bit ignored by MMU.
        const RSV1 = 1usize << 10;
        // Second bit ignored by MMU.
        const RSV2 = 1usize << 11;
        /// If this entry is a huge page table entry, it is `GLOBAL`.
        const GLOBAL_IN_HUGE = 1usize << 12;
        /// Controls whether reads to the mapped frames are not allowed.
        const NOT_READABLE = 1usize << 61;
        /// Controls whether execution code in the mapped frames are not allowed.
        const NOT_EXECUTABLE = 1usize << 62;
        /// Whether the `PageTableEntry` can only be accessed by the privileged level `PLV` field inferred
        const RPLV = 1usize << 63;
    }
}

pub(crate) fn tlb_flush_addr(vaddr: Vaddr) {
    unsafe {
        asm!(
            "invtlb 0, $zero, {}",
            in(reg) vaddr
        );
    }
}

pub(crate) fn tlb_flush_addr_range(range: &Range<Vaddr>) {
    for vaddr in range.clone().step_by(PAGE_SIZE) {
        tlb_flush_addr(vaddr);
    }
}

pub(crate) fn tlb_flush_all_excluding_global() {
    unsafe {
        asm!("invtlb 3, $zero, $zero");
    }
}

pub(crate) fn tlb_flush_all_including_global() {
    unsafe {
        asm!("invtlb 0, $zero, $zero");
    }
}

/// Activates the given level 4 page table.
///
/// "pgdl" or "pgdh" register doesn't have a field that encodes the cache policy,
/// so `_root_pt_cache` is ignored.
///
/// # Safety
///
/// Changing the level 4 page table is unsafe, because it's possible to violate memory safety by
/// changing the page mapping.
pub unsafe fn activate_page_table(root_paddr: Paddr, _root_pt_cache: CachePolicy) {
    assert!(root_paddr % PagingConsts::BASE_PAGE_SIZE() == 0);
    loongArch64::register::pgdl::set_base(root_paddr);
    loongArch64::register::pgdh::set_base(root_paddr);
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
    // The hardware reads are trusted; PGDL/PGDH transitions and their equality
    // are not verified.
    let pgdl = loongArch64::register::pgdl::read().raw();
    let pgdh = loongArch64::register::pgdh::read().raw();
    assert_eq!(
        pgdl, pgdh,
        "Only support to share the same page table for both user and kernel space"
    );
    pgdl
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

impl PageTableEntry {
    closed spec fn is_huge_spec(&self) -> bool {
        self.0 & PageTableFlags::IS_BASIC().bits() == 0 && self.0
            & PageTableFlags::GLOBAL_OR_HUGE().bits() != 0
    }

    closed spec fn is_global_spec(&self) -> bool {
        if self.0 & PageTableFlags::IS_BASIC().bits() != 0 {
            self.0 & PageTableFlags::GLOBAL_OR_HUGE().bits() != 0
        } else {
            self.0 & PageTableFlags::GLOBAL_IN_HUGE().bits() != 0
        }
    }

    const PHYS_ADDR_MASK: usize = 0x0000_FFFF_FFFF_F000;

    #[verifier::when_used_as_spec(is_huge_spec)]
    #[verus_spec(returns self.is_huge_spec())]
    fn is_huge(&self) -> bool {
        if self.0 & PageTableFlags::IS_BASIC().bits() != 0 {
            return false;
        } else {
            return self.0 & PageTableFlags::GLOBAL_OR_HUGE().bits() != 0;
        }
    }

    #[verifier::when_used_as_spec(is_global_spec)]
    #[verus_spec(returns self.is_global_spec())]
    fn is_global(&self) -> bool {
        if self.0 & PageTableFlags::IS_BASIC().bits() != 0 {
            return self.0 & PageTableFlags::GLOBAL_OR_HUGE().bits() != 0;
        } else {
            return self.0 & PageTableFlags::GLOBAL_IN_HUGE().bits() != 0;
        }
    }
}

} // verus!
impl PageTableEntry {
    #[verus_verify(dual_spec)]
    #[verus_spec(returns self.is_user())]
    fn is_user(&self) -> bool {
        self.0 & PageTableFlags::PLVL().bits() != 0 && self.0 & PageTableFlags::PLVH().bits() != 0
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
            assert(Self::new_absent_spec() == Self(0)) by (compute_only);
            assert(Self(0).paddr() == 0) by (compute_only);
            assert(!Self(0).is_present()) by (compute_only);
        }
        Self::default()
    }

    fn is_present(&self) -> bool {
        self.0 & PageTableFlags::VALID().bits() != 0
    }

    open spec fn new_page_req(_paddr: Paddr, level: PagingLevel, prop: PageProperty) -> bool {
        &&& level == 1
        &&& prop.inv()
        &&& (prop.cache is Writeback || prop.cache is WriteCombining)
        &&& prop.flags.contains(PageFlags::DIRTY())
    }

    fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        proof {
            lemma_page_property_flag_constants();
            lemma_raw_properties(paddr);
            lemma_new_page(paddr, prop);
        }
        let flags = if level == 1 {
            PageTableFlags::IS_BASIC().bits()
        } else {
            PageTableFlags::GLOBAL_OR_HUGE().bits()
        };
        /* Initialize VALID and the page type before updating properties.
         * set_prop leaves absent entries unchanged and preserves IS_BASIC.
         * Origin Rust: let mut pte = Self(paddr & Self::PHYS_ADDR_MASK);
         */
        let mut pte = Self(paddr & Self::PHYS_ADDR_MASK | PageTableFlags::VALID().bits() | flags);
        proof {
            let raw = pte.0;
            assert(raw & 512usize == 512usize && raw & 1usize != 0) by (bit_vector)
                requires
                    raw == (paddr & 0x0000_ffff_ffff_f000usize) | 1usize | 512usize,
            ;
        }
        pte.set_prop(prop);
        let pte = pte.0 | flags;
        Self(pte)
    }

    fn new_pt(paddr: Paddr) -> Self {
        proof {
            lemma_new_pt(paddr);
        }
        Self(paddr & Self::PHYS_ADDR_MASK | PageTableFlags::VALID().bits())
    }

    fn paddr(&self) -> Paddr {
        proof {
            self.lemma_paddr_is_page_aligned();
        }
        if self.is_huge() {
            let paddr = (self.0 & Self::PHYS_ADDR_MASK & !PageTableFlags::GLOBAL_IN_HUGE().bits())
                >> 12;
            paddr << 12
        } else {
            let ppn = (self.0 & Self::PHYS_ADDR_MASK) >> 12;
            ppn << 12
        }
    }

    fn prop(&self) -> PageProperty {
        proof {
            lemma_page_property_flag_constants();
        }
        let flags = (parse_flags!(!(self.0), PageTableFlags::NOT_READABLE(), PageFlags::R())) | (
        parse_flags!(self.0, PageTableFlags::WRITABLE(), PageFlags::W())) | (
        parse_flags!(!(self.0), PageTableFlags::NOT_EXECUTABLE(), PageFlags::X()))
        // TODO: How to get the accessed bit in loongarch?
         | (parse_flags!(self.0, PageTableFlags::PRESENT(), PageFlags::ACCESSED())) | (
        parse_flags!(self.0, PageTableFlags::DIRTY(), PageFlags::DIRTY())) | (
        parse_flags!(self.0, PageTableFlags::RSV1(), PageFlags::AVAIL1())) | (
        parse_flags!(self.0, PageTableFlags::RSV2(), PageFlags::AVAIL2()));
        let mut priv_flags = PrivFlags::empty().bits();
        if self.is_user() {
            priv_flags |= PrivFlags::USER().bits();
        }
        if self.is_global() {
            priv_flags |= PrivFlags::GLOBAL().bits();
        }
        let cache = if self.0 & PageTableFlags::MATL().bits() != 0 {
            CachePolicy::Writeback
        } else if self.0 & PageTableFlags::MATH().bits() != 0 {
            CachePolicy::WriteCombining
        } else {
            CachePolicy::Writeback
        };

        proof {
            let raw = self.0;
            let user = self.is_user();
            let global = self.is_global();
            assert((flags as u8) & 0xdfu8 == flags as u8) by (bit_vector)
                requires
                    flags == ((!raw & 0x2000_0000_0000_0000usize) >> 61 << 0) | ((raw & 0x100usize)
                        >> 8 << 1) | ((!raw & 0x4000_0000_0000_0000usize) >> 62 << 2) | ((raw
                        & 0x80usize) >> 7 << 3) | ((raw & 0x2usize) >> 1 << 4) | ((raw & 0x400usize)
                        >> 10 << 6) | ((raw & 0x800usize) >> 11 << 7),
            ;
            let user_flags = if user {
                0u8 | 0x1u8
            } else {
                0u8
            };
            let decoded_priv = self.decoded_priv_flags();
            assert(priv_flags == decoded_priv && priv_flags & 0x3u8 == priv_flags) by (bit_vector)
                requires
                    user_flags == (if user {
                        0u8 | 0x1u8
                    } else {
                        0u8
                    }),
                    priv_flags == (if global {
                        user_flags | 0x2u8
                    } else {
                        user_flags
                    }),
                    decoded_priv == (if user {
                        0x1u8
                    } else {
                        0u8
                    }) | (if global {
                        0x2u8
                    } else {
                        0u8
                    }),
            ;
        }
        PageProperty {
            flags: PageFlags::from_bits(flags as u8).unwrap(),
            cache,
            priv_flags: PrivFlags::from_bits(priv_flags as u8).unwrap(),
        }
    }

    closed spec fn set_prop_req(self, prop: PageProperty) -> bool {
        &&& Self::new_page_req(
            0,
            1,
            prop,
        )
        // Present entries must describe basic pages, whose GLOBAL bit is bit 6.
        &&& self.is_present() ==> self.0 & PageTableFlags::IS_BASIC().bits() != 0
    }

    #[verus_spec(
        ensures
            old(self).is_present() ==> final(self).as_usize_spec()
                == Self::raw_set_prop_spec(old(self).as_usize_spec(), prop),
    )]
    fn set_prop(&mut self, prop: PageProperty) {
        /* Honor the trait's no-op contract for absent entries, as on RISC-V.
         * Origin Rust: <none; new executable code>
         */
        if !self.is_present() {
            return;
        }
        proof {
            lemma_page_property_flag_constants();
            lemma_set_prop_roundtrip(self.0, prop);
        }
        let mut flags =
            PageTableFlags::VALID().bits()
        // FIXME: To avoid the PageModifyFault exception,
        // we set the DIRTY bit to 1 all the time.
         | PageTableFlags::DIRTY().bits()
            | parse_flags!(
                !prop.flags.bits(),
                PageFlags::R(),
                PageTableFlags::NOT_READABLE()
            )
            | parse_flags!(prop.flags.bits(), PageFlags::W(), PageTableFlags::WRITABLE())
            | parse_flags!(
                !prop.flags.bits(),
                PageFlags::X(),
                PageTableFlags::NOT_EXECUTABLE()
            )
            | parse_flags!(prop.flags.bits(), PageFlags::DIRTY(), PageTableFlags::DIRTY())
        // TODO: How to get the accessed bit in loongarch?
         | parse_flags!(prop.flags.bits(), PageFlags::ACCESSED(), PageTableFlags::PRESENT())
            | parse_flags!(prop.flags.bits(), PageFlags::AVAIL1(), PageTableFlags::RSV1())
            | parse_flags!(prop.flags.bits(), PageFlags::AVAIL2(), PageTableFlags::RSV2());
        if prop.priv_flags.contains(PrivFlags::USER()) {
            flags |= PageTableFlags::PLVL().bits();
            flags |= PageTableFlags::PLVH().bits();
        }
        if prop.priv_flags.contains(PrivFlags::GLOBAL()) {
            if self.is_huge() {
                flags |= PageTableFlags::GLOBAL_IN_HUGE().bits();
            } else {
                flags |= PageTableFlags::GLOBAL_OR_HUGE().bits();
            }
        }
        match prop.cache {
            CachePolicy::Writeback => {
                flags |= PageTableFlags::MATL().bits();
            },
            CachePolicy::Uncacheable => (),
            CachePolicy::WriteCombining => {
                flags |= PageTableFlags::MATH().bits();
            },
            _ => panic!("unsupported cache policy"),
        }

        proof {
            let raw = self.0;
            assert((raw & (0x0000_ffff_ffff_f000usize | 512usize)) | flags == (raw
                & 0x0000_ffff_ffff_f000usize) | flags | (raw & 512usize)) by (bit_vector);
        }
        /* Retain the basic-page marker so GLOBAL and address bit 12 keep their
         * basic-page meanings after the property update.
         * Origin Rust: self.0 = (self.0 & Self::PHYS_ADDR_MASK) | flags;
         */
        self.0 = (self.0 & (Self::PHYS_ADDR_MASK | PageTableFlags::IS_BASIC().bits())) | flags;
    }

    fn is_last(&self, level: PagingLevel) -> bool {
        level == 1 || self.is_huge()
    }

    closed spec fn new_absent_spec() -> Self {
        Self(0)
    }

    closed spec fn is_present_spec(&self) -> bool {
        self.0 & PageTableFlags::VALID().bits() != 0
    }

    closed spec fn new_page_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        let flags = if level == 1 {
            PageTableFlags::IS_BASIC().bits()
        } else {
            PageTableFlags::GLOBAL_OR_HUGE().bits()
        };
        Self(
            Self::raw_set_prop_spec(
                (paddr & Self::PHYS_ADDR_MASK) | PageTableFlags::VALID().bits() | flags,
                prop,
            ) | flags,
        )
    }

    closed spec fn new_pt_spec(paddr: Paddr) -> Self {
        Self(paddr & Self::PHYS_ADDR_MASK | PageTableFlags::VALID().bits())
    }

    closed spec fn paddr_spec(&self) -> Paddr {
        if self.is_huge() {
            ((self.0 & Self::PHYS_ADDR_MASK & !PageTableFlags::GLOBAL_IN_HUGE().bits()) >> 12) << 12
        } else {
            ((self.0 & Self::PHYS_ADDR_MASK) >> 12) << 12
        }
    }

    closed spec fn prop_spec(&self) -> PageProperty {
        PageProperty {
            flags: PageFlags::from_bits(self.decoded_flags())->0,
            priv_flags: PrivFlags::from_bits(self.decoded_priv_flags())->0,
            cache: if self.0 & PageTableFlags::MATL().bits() != 0 {
                CachePolicy::Writeback
            } else if self.0 & PageTableFlags::MATH().bits() != 0 {
                CachePolicy::WriteCombining
            } else {
                CachePolicy::Writeback
            },
        }
    }

    closed spec fn is_last_spec(&self, level: PagingLevel) -> bool {
        level == 1 || self.is_huge()
    }

    closed spec fn as_usize_spec(self) -> usize {
        self.0
    }

    proof fn lemma_paddr_is_page_aligned(self) {
        lemma_page_property_flag_constants();
        lemma_raw_properties(self.0);
    }

    proof fn lemma_page_table_entry_properties() {
        Self::lemma_layout();
        assert(Self::new_absent().paddr() == 0) by (compute_only);
        assert(!Self::new_absent().is_present()) by (compute_only);
        assert forall|level: PagingLevel| 1 < level implies !Self::new_absent().is_last(level) by {
            assert(Self::new_absent().is_last(level) == (level == 1)) by (compute);
        }
        assert forall|pa: Paddr, level: PagingLevel, prop: PageProperty|
            #![trigger Self::new_page(pa, level, prop)]
            Self::new_page_req(pa, level, prop) && (prop.cache is Writeback
                || prop.cache is Writethrough || prop.cache is Uncacheable) implies {
            &&& Self::new_page(pa, level, prop).is_present()
            &&& (pa < MAX_PADDR ==> Self::new_page(pa, level, prop).paddr() == pa & !((PAGE_SIZE
                - 1) as usize))
            &&& (pa < MAX_PADDR && pa % PAGE_SIZE == 0 ==> Self::new_page(pa, level, prop).paddr()
                == pa)
            &&& Self::new_page(pa, level, prop).prop() == prop
            &&& Self::new_page(pa, level, prop).is_last(level)
        } by {
            lemma_new_page(pa, prop);
        }
        assert forall|pa: Paddr|
            #![trigger Self::new_pt(pa)]
            {
                &&& Self::new_pt(pa).is_present()
                &&& (pa < MAX_PADDR ==> Self::new_pt(pa).paddr() == pa & !((PAGE_SIZE
                    - 1) as usize))
                &&& (pa < MAX_PADDR && pa % PAGE_SIZE == 0 ==> Self::new_pt(pa).paddr() == pa)
                &&& forall|level: PagingLevel| 1 < level ==> !Self::new_pt(pa).is_last(level)
            } by {
            lemma_new_pt(pa);
        }
    }
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

pub(in crate::arch) fn paddr_to_daddr(pa: Paddr) -> usize {
    const DEVICE_LINEAR_MAPPING_BASE_VADDR: usize = 0x8000_0000_0000_0000;
    pa + DEVICE_LINEAR_MAPPING_BASE_VADDR
}

pub(crate) unsafe fn __memcpy_fallible(dst: *mut u8, src: *const u8, size: usize) -> usize {
    // TODO: implement fallible
    unsafe { core::ptr::copy(src, dst, size) };
    0
}

pub(crate) unsafe fn __memset_fallible(dst: *mut u8, value: u8, size: usize) -> usize {
    // TODO: implement fallible
    unsafe { core::ptr::write_bytes(dst, value, size) };
    0
}
// Auxiliary definitions and lemmas about bit properties of page table entries and flags.
verus! {

pub proof fn lemma_nr_subpage_per_huge_eq_nr_entries()
    ensures
        crate::mm::nr_subpage_per_huge::<PagingConsts>() == NR_ENTRIES,
{
}

impl PageTableEntry {
    pub proof fn lemma_layout()
        ensures
            core::mem::size_of::<PageTableEntry>() == 8,
            core::mem::align_of::<PageTableEntry>() == 8,
            core::mem::size_of::<PageTableEntry>() % core::mem::align_of::<PageTableEntry>() == 0,
    {
        broadcast use VERUS_layout_of_PageTableEntry;

    }

    closed spec fn decoded_flags(self) -> u8 {
        ((parse_flags!(!self.0, PageTableFlags::NOT_READABLE(), PageFlags::R())) | (
        parse_flags!(self.0, PageTableFlags::WRITABLE(), PageFlags::W())) | (
        parse_flags!(!self.0, PageTableFlags::NOT_EXECUTABLE(), PageFlags::X())) | (
        parse_flags!(self.0, PageTableFlags::PRESENT(), PageFlags::ACCESSED())) | (
        parse_flags!(self.0, PageTableFlags::DIRTY(), PageFlags::DIRTY())) | (
        parse_flags!(self.0, PageTableFlags::RSV1(), PageFlags::AVAIL1())) | (
        parse_flags!(self.0, PageTableFlags::RSV2(), PageFlags::AVAIL2()))) as u8
    }

    closed spec fn decoded_priv_flags(self) -> u8 {
        (if self.is_user() {
            PrivFlags::USER().bits()
        } else {
            0u8
        }) | (if self.is_global() {
            PrivFlags::GLOBAL().bits()
        } else {
            0u8
        })
    }

    /// Models property updates that preserve the address and IS_BASIC.
    pub closed spec fn raw_set_prop_spec(raw: usize, prop: PageProperty) -> usize {
        let flags = PageTableFlags::VALID().bits() | PageTableFlags::DIRTY().bits()
            | parse_flags!(!prop.flags.bits(), PageFlags::R(), PageTableFlags::NOT_READABLE())
            | parse_flags!(prop.flags.bits(), PageFlags::W(), PageTableFlags::WRITABLE())
            | parse_flags!(!prop.flags.bits(), PageFlags::X(), PageTableFlags::NOT_EXECUTABLE())
            | parse_flags!(prop.flags.bits(), PageFlags::DIRTY(), PageTableFlags::DIRTY())
            | parse_flags!(prop.flags.bits(), PageFlags::ACCESSED(), PageTableFlags::PRESENT())
            | parse_flags!(prop.flags.bits(), PageFlags::AVAIL1(), PageTableFlags::RSV1())
            | parse_flags!(prop.flags.bits(), PageFlags::AVAIL2(), PageTableFlags::RSV2());
        let flags = if prop.priv_flags.contains(PrivFlags::USER()) {
            flags | PageTableFlags::PLVL().bits() | PageTableFlags::PLVH().bits()
        } else {
            flags
        };
        let flags = if prop.priv_flags.contains(PrivFlags::GLOBAL()) {
            flags | if Self(raw).is_huge() {
                PageTableFlags::GLOBAL_IN_HUGE().bits()
            } else {
                PageTableFlags::GLOBAL_OR_HUGE().bits()
            }
        } else {
            flags
        };
        let flags = flags | match prop.cache {
            CachePolicy::Writeback => PageTableFlags::MATL().bits(),
            CachePolicy::WriteCombining => PageTableFlags::MATH().bits(),
            _ => 0usize,
        };
        (raw & Self::PHYS_ADDR_MASK) | flags | (raw & PageTableFlags::IS_BASIC().bits())
    }
}

/// Checks page-flag masks and bit positions.
proof fn lemma_page_property_flag_constants()
    ensures
        PageTableFlags::VALID().bits() == 1,
        PageTableFlags::VALID().bits().ilog2() == 0,
        PageTableFlags::DIRTY().bits() == 2,
        PageTableFlags::DIRTY().bits().ilog2() == 1,
        PageTableFlags::PLVL().bits() == 4,
        PageTableFlags::PLVL().bits().ilog2() == 2,
        PageTableFlags::PLVH().bits() == 8,
        PageTableFlags::PLVH().bits().ilog2() == 3,
        PageTableFlags::MATL().bits() == 16,
        PageTableFlags::MATL().bits().ilog2() == 4,
        PageTableFlags::MATH().bits() == 32,
        PageTableFlags::MATH().bits().ilog2() == 5,
        PageTableFlags::GLOBAL_OR_HUGE().bits() == 64,
        PageTableFlags::GLOBAL_OR_HUGE().bits().ilog2() == 6,
        PageTableFlags::PRESENT().bits() == 128,
        PageTableFlags::PRESENT().bits().ilog2() == 7,
        PageTableFlags::WRITABLE().bits() == 256,
        PageTableFlags::WRITABLE().bits().ilog2() == 8,
        PageTableFlags::IS_BASIC().bits() == 512,
        PageTableFlags::IS_BASIC().bits().ilog2() == 9,
        PageTableFlags::RSV1().bits() == 1024,
        PageTableFlags::RSV1().bits().ilog2() == 10,
        PageTableFlags::RSV2().bits() == 2048,
        PageTableFlags::RSV2().bits().ilog2() == 11,
        PageTableFlags::GLOBAL_IN_HUGE().bits() == 4096,
        PageTableFlags::GLOBAL_IN_HUGE().bits().ilog2() == 12,
        PageTableFlags::NOT_READABLE().bits() == 2305843009213693952,
        PageTableFlags::NOT_READABLE().bits().ilog2() == 61,
        PageTableFlags::NOT_EXECUTABLE().bits() == 4611686018427387904,
        PageTableFlags::NOT_EXECUTABLE().bits().ilog2() == 62,
        PageTableFlags::RPLV().bits() == 9223372036854775808,
        PageTableFlags::RPLV().bits().ilog2() == 63,
        PageFlags::R().bits() == 1,
        PageFlags::R().bits().ilog2() == 0,
        PageFlags::W().bits() == 2,
        PageFlags::W().bits().ilog2() == 1,
        PageFlags::X().bits() == 4,
        PageFlags::X().bits().ilog2() == 2,
        PageFlags::ACCESSED().bits() == 8,
        PageFlags::ACCESSED().bits().ilog2() == 3,
        PageFlags::DIRTY().bits() == 16,
        PageFlags::DIRTY().bits().ilog2() == 4,
        PageFlags::AVAIL1().bits() == 64,
        PageFlags::AVAIL1().bits().ilog2() == 6,
        PageFlags::AVAIL2().bits() == 128,
        PageFlags::AVAIL2().bits().ilog2() == 7,
        PrivFlags::USER().bits() == 1,
        PrivFlags::USER().bits().ilog2() == 0,
        PrivFlags::GLOBAL().bits() == 2,
        PrivFlags::GLOBAL().bits().ilog2() == 1,
        PageFlags::all().bits() == 0xdfu8,
        PrivFlags::all().bits() == 3u8,
{
    lemma_usize_ilog2_to32();
    assert(PageTableFlags::VALID().bits() == 1) by (compute_only);
    assert(PageTableFlags::DIRTY().bits() == 2) by (compute_only);
    assert(PageTableFlags::PLVL().bits() == 4) by (compute_only);
    assert(PageTableFlags::PLVH().bits() == 8) by (compute_only);
    assert(PageTableFlags::MATL().bits() == 16) by (compute_only);
    assert(PageTableFlags::MATH().bits() == 32) by (compute_only);
    assert(PageTableFlags::GLOBAL_OR_HUGE().bits() == 64) by (compute_only);
    assert(PageTableFlags::PRESENT().bits() == 128) by (compute_only);
    assert(PageTableFlags::WRITABLE().bits() == 256) by (compute_only);
    assert(PageTableFlags::IS_BASIC().bits() == 512) by (compute_only);
    assert(PageTableFlags::RSV1().bits() == 1024) by (compute_only);
    assert(PageTableFlags::RSV2().bits() == 2048) by (compute_only);
    assert(PageTableFlags::GLOBAL_IN_HUGE().bits() == 4096) by (compute_only);
    assert(PageTableFlags::NOT_READABLE().bits() == 2305843009213693952) by (compute_only);
    assert(PageTableFlags::NOT_EXECUTABLE().bits() == 4611686018427387904) by (compute_only);
    assert(PageTableFlags::RPLV().bits() == 9223372036854775808) by (compute_only);
    broadcast use PageFlags::lemma_consts, PrivFlags::lemma_consts;

    lemma2_to64_rest();
    lemma_usize_pow2_ilog2(61);
    lemma_usize_pow2_ilog2(62);
    lemma_usize_pow2_ilog2(63);
    assert((0u8 | 0x1u8 | 0x2u8 | 0x4u8 | 0x3u8 | 0x5u8 | 0x7u8 | 0x8u8 | 0x10u8 | 0x40u8 | 0x80u8)
        == 0xdfu8) by (bit_vector);
    assert((0u8 | 0x1u8 | 0x2u8 | 0u8) == 0x3u8) by (bit_vector);
}

#[verifier::bit_vector]
proof fn lemma_raw_properties(raw: usize)
    ensures
        (raw & PageTableEntry::PHYS_ADDR_MASK) & 1usize == 0,
        (raw & PageTableEntry::PHYS_ADDR_MASK) & PageTableEntry::PHYS_ADDR_MASK == raw
            & PageTableEntry::PHYS_ADDR_MASK,
        ((raw & PageTableEntry::PHYS_ADDR_MASK) >> 12) << 12 == raw
            & PageTableEntry::PHYS_ADDR_MASK,
        (((raw & PageTableEntry::PHYS_ADDR_MASK) >> 12) << 12) % PAGE_SIZE == 0,
        (((raw & PageTableEntry::PHYS_ADDR_MASK & !0x1000usize) >> 12) << 12) % PAGE_SIZE == 0,
        raw % PAGE_SIZE == 0 ==> raw & !0xfffusize == raw,
        raw < MAX_PADDR ==> raw & PageTableEntry::PHYS_ADDR_MASK == raw & !0xfffusize,
        raw < MAX_PADDR ==> raw & PageTableEntry::PHYS_ADDR_MASK < MAX_PADDR,
        (raw & PageTableEntry::PHYS_ADDR_MASK) & 0x240usize == 0,
        (raw & PageTableEntry::PHYS_ADDR_MASK) & 0x40usize == 0,
        (raw & PageTableEntry::PHYS_ADDR_MASK) & 0x200usize == 0,
        (raw & PageTableEntry::PHYS_ADDR_MASK | 1usize) & 1usize != 0,
        (raw & PageTableEntry::PHYS_ADDR_MASK | 1usize) & 0x240usize == 0,
        (raw & PageTableEntry::PHYS_ADDR_MASK | 1usize) & 0x40usize == 0,
        (raw & PageTableEntry::PHYS_ADDR_MASK | 1usize) & 0x200usize == 0,
        (raw & PageTableEntry::PHYS_ADDR_MASK | 1usize) & PageTableEntry::PHYS_ADDR_MASK == raw
            & PageTableEntry::PHYS_ADDR_MASK,
{
}

/// Expands ordinary-page encoding into literal masks for bit_vector proofs.
/// The preserved IS_BASIC bit is added separately; lemma_encoding_models_match
/// relates this expression to raw_set_prop_spec for non-huge entries.
#[verifier::inline]
spec fn encode_bits(raw: usize, f: u8, p: u8, cache: usize) -> usize {
    let flags = 1usize | 2usize | (((!f) as usize & 1usize) >> 0 << 61) | ((f as usize & 2usize)
        >> 1 << 8) | (((!f) as usize & 4usize) >> 2 << 62) | ((f as usize & 16usize) >> 4 << 1) | ((
    f as usize & 8usize) >> 3 << 7) | ((f as usize & 64usize) >> 6 << 10) | ((f as usize & 128usize)
        >> 7 << 11);
    let flags = if p & 1u8 == 1u8 {
        flags | 4usize | 8usize
    } else {
        flags
    };
    let flags = if p & 2u8 == 2u8 {
        flags | 64usize
    } else {
        flags
    };
    (raw & 0x0000_ffff_ffff_f000usize) | (flags | cache)
}

/// Expands decoded_flags into literal masks for bit_vector proofs.
#[verifier::inline]
spec fn decode_bits(raw: usize) -> u8 {
    (((!raw & 0x2000_0000_0000_0000usize) >> 61 << 0) | ((raw & 256usize) >> 8 << 1) | ((!raw
        & 0x4000_0000_0000_0000usize) >> 62 << 2) | ((raw & 128usize) >> 7 << 3) | ((raw & 2usize)
        >> 1 << 4) | ((raw & 1024usize) >> 10 << 6) | ((raw & 2048usize) >> 11 << 7)) as u8
}

#[verifier::bit_vector]
proof fn lemma_encoded_bits(raw: usize, f: u8, p: u8, cache: usize)
    requires
        f & 0xdfu8 == f,
        f & 16u8 != 0,
        p & 3u8 == p,
        cache == 16usize || cache == 32usize,
    ensures
        decode_bits(encode_bits(raw, f, p, cache)) == f,
        decode_bits(encode_bits(raw, f, p, cache) | 512usize) == f,
        encode_bits(raw, f, p, cache) & 1usize != 0,
        encode_bits(raw, f, p, cache) & 512usize == 0,
        encode_bits(raw, f, p, cache) & 0x0000_ffff_ffff_f000usize == raw
            & 0x0000_ffff_ffff_f000usize,
        (encode_bits(raw, f, p, cache) | 512usize) & 0x0000_ffff_ffff_f000usize == raw
            & 0x0000_ffff_ffff_f000usize,
        (encode_bits(raw, f, p, cache) | 512usize) & 512usize != 0,
        (encode_bits(raw, f, p, cache) | 512usize) & 1usize != 0,
        (encode_bits(raw, f, p, cache) & 12usize == 12usize) == (p & 1u8 != 0),
        ((encode_bits(raw, f, p, cache) | 512usize) & 12usize == 12usize) == (p & 1u8 != 0),
        (encode_bits(raw, f, p, cache) & 4usize != 0 && encode_bits(raw, f, p, cache) & 8usize != 0)
            == (p & 1u8 != 0),
        ((encode_bits(raw, f, p, cache) | 512usize) & 4usize != 0 && (encode_bits(raw, f, p, cache)
            | 512usize) & 8usize != 0) == (p & 1u8 != 0),
        (p & 1u8 == 1u8) == (p & 1u8 != 0),
        (p & 2u8 == 2u8) == (p & 2u8 != 0),
        (encode_bits(raw, f, p, cache) & 64usize != 0) == (p & 2u8 != 0),
        ((encode_bits(raw, f, p, cache) | 512usize) & 64usize != 0) == (p & 2u8 != 0),
        encode_bits(raw, f, p, cache) & 48usize == cache,
        (encode_bits(raw, f, p, cache) | 512usize) & 48usize == cache,
        (encode_bits(raw, f, p, cache) & 16usize != 0) == (cache == 16usize),
        (encode_bits(raw, f, p, cache) & 32usize != 0) == (cache == 32usize),
        ((encode_bits(raw, f, p, cache) | 512usize) & 16usize != 0) == (cache == 16usize),
        ((encode_bits(raw, f, p, cache) | 512usize) & 32usize != 0) == (cache == 32usize),
        p & 2u8 == 0 && raw & 4096usize == 0 ==> encode_bits(raw, f, p, cache) & 4096usize == 0,
{
}

/// Relates the literal bit expressions to the named-flag models for non-huge entries.
proof fn lemma_encoding_models_match(raw: usize, prop: PageProperty)
    requires
        PageTableEntry::new_page_req(0, 1, prop),
        !PageTableEntry(raw).is_huge(),
    ensures
        PageTableEntry::raw_set_prop_spec(raw, prop) == encode_bits(
            raw,
            prop.flags.bits(),
            prop.priv_flags.bits(),
            if prop.cache is Writeback {
                16usize
            } else {
                32usize
            },
        ) | (raw & PageTableFlags::IS_BASIC().bits()),
        PageTableEntry(raw).decoded_flags() == decode_bits(raw),
        PageTableEntry(PageTableEntry::raw_set_prop_spec(raw, prop)).decoded_flags() == decode_bits(
            PageTableEntry::raw_set_prop_spec(raw, prop),
        ),
{
    lemma_page_property_flag_constants();
    let p = prop.priv_flags.bits();
    assert((p & 1u8 == 1u8) == (p & 1u8 != 0) && (p & 2u8 == 2u8) == (p & 2u8 != 0))
        by (bit_vector);
}

proof fn lemma_decoded_prop(raw: usize, prop: PageProperty)
    requires
        prop.inv(),
        PageTableEntry(raw).decoded_flags() == prop.flags.bits(),
        PageTableEntry(raw).decoded_priv_flags() == prop.priv_flags.bits(),
        PageTableEntry(raw).prop().cache == prop.cache,
    ensures
        PageTableEntry(raw).prop() == prop,
{
    PageFlags::lemma_from_bits_bits(prop.flags.bits());
    PrivFlags::lemma_from_bits_bits(prop.priv_flags.bits());
    PageFlags::lemma_eq_from_bits(PageTableEntry(raw).prop().flags, prop.flags);
    PrivFlags::lemma_eq_from_bits(PageTableEntry(raw).prop().priv_flags, prop.priv_flags);
}

proof fn lemma_set_prop_roundtrip(raw: usize, prop: PageProperty)
    requires
        PageTableEntry(raw).set_prop_req(prop),
        PageTableEntry(raw).is_present(),
    ensures
        PageTableEntry(PageTableEntry::raw_set_prop_spec(raw, prop)).prop() == prop,
        PageTableEntry(PageTableEntry::raw_set_prop_spec(raw, prop)).paddr() == PageTableEntry(
            raw,
        ).paddr(),
        PageTableEntry(PageTableEntry::raw_set_prop_spec(raw, prop)).is_present(),
        !PageTableEntry(PageTableEntry::raw_set_prop_spec(raw, prop)).is_huge(),
{
    lemma_page_property_flag_constants();
    lemma_raw_properties(raw);
    let f = prop.flags.bits();
    let p = prop.priv_flags.bits();
    let cache = if prop.cache is Writeback {
        16usize
    } else {
        32usize
    };
    lemma_encoded_bits(raw, f, p, cache);
    lemma_encoding_models_match(raw, prop);
    let updated = PageTableEntry::raw_set_prop_spec(raw, prop);
    assert(raw & 512usize == 512usize) by (bit_vector)
        requires
            raw & 512usize != 0,
    ;
    let decoded_priv = PageTableEntry(updated).decoded_priv_flags();
    assert(decoded_priv == p) by (bit_vector)
        requires
            p & 3u8 == p,
            decoded_priv == (if p & 1u8 != 0 {
                1u8
            } else {
                0u8
            }) | (if p & 2u8 != 0 {
                2u8
            } else {
                0u8
            }),
    ;
    lemma_decoded_prop(updated, prop);
}

proof fn lemma_new_page(pa: Paddr, prop: PageProperty)
    requires
        PageTableEntry::new_page_req(pa, 1, prop),
    ensures
        PageTableEntry::new_page(pa, 1, prop).prop() == prop,
        PageTableEntry::new_page(pa, 1, prop).is_present(),
        PageTableEntry::new_page(pa, 1, prop).is_last(1),
        pa < MAX_PADDR ==> PageTableEntry::new_page(pa, 1, prop).paddr() == pa & !0xfffusize,
        pa < MAX_PADDR && pa % PAGE_SIZE == 0 ==> PageTableEntry::new_page(pa, 1, prop).paddr()
            == pa,
{
    lemma_page_property_flag_constants();
    lemma_raw_properties(pa);
    let raw = (pa & PageTableEntry::PHYS_ADDR_MASK) | 1usize | 512usize;
    lemma_raw_properties(raw);
    assert(raw & 512usize == 512usize && raw & 64usize == 0 && raw & PageTableEntry::PHYS_ADDR_MASK
        == pa & PageTableEntry::PHYS_ADDR_MASK) by (bit_vector)
        requires
            raw == (pa & 0x0000_ffff_ffff_f000usize) | 1usize | 512usize,
    ;
    let f = prop.flags.bits();
    let p = prop.priv_flags.bits();
    let cache = if prop.cache is Writeback {
        16usize
    } else {
        32usize
    };
    lemma_encoded_bits(raw, f, p, cache);
    lemma_encoding_models_match(raw, prop);
    let updated = PageTableEntry::new_page(pa, 1, prop).0;
    assert(updated == encode_bits(raw, f, p, cache) | 512usize) by (bit_vector)
        requires
            updated == (encode_bits(raw, f, p, cache) | 512usize) | 512usize,
    ;
    let decoded_priv = PageTableEntry(updated).decoded_priv_flags();
    assert(decoded_priv == p) by (bit_vector)
        requires
            p & 3u8 == p,
            decoded_priv == (if p & 1u8 != 0 {
                1u8
            } else {
                0u8
            }) | (if p & 2u8 != 0 {
                2u8
            } else {
                0u8
            }),
    ;
    lemma_decoded_prop(updated, prop);
}

/// Proves child-table entries preserve the address and are non-leaf.
proof fn lemma_new_pt(pa: Paddr)
    ensures
        PageTableEntry::new_pt(pa).is_present(),
        pa < MAX_PADDR ==> PageTableEntry::new_pt(pa).paddr() == pa & !0xfffusize,
        pa < MAX_PADDR && pa % PAGE_SIZE == 0 ==> PageTableEntry::new_pt(pa).paddr() == pa,
        pa < MAX_PADDR ==> valid_frame_paddr(PageTableEntry::new_pt(pa).paddr()),
        forall|level: PagingLevel| 1 < level ==> !PageTableEntry::new_pt(pa).is_last(level),
{
    lemma_page_property_flag_constants();
    lemma_raw_properties(pa);
    let raw = (pa & PageTableEntry::PHYS_ADDR_MASK) | PageTableFlags::VALID().bits();
}

} // verus!
