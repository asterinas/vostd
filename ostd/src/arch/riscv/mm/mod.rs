// SPDX-License-Identifier: MPL-2.0
use alloc::fmt;
use core::ops::Range;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd_extra::panic::{may_panic, panic_diverge};
use vstd_extra::prelude::*;

use crate::specs::{
    arch::{valid_frame_paddr, MAX_PADDR, PAGE_SIZE},
    riscv_arch::RiscvPteModel,
};
use crate::{
    mm::{
        page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags as PrivFlags},
        page_table::PageTableEntryTrait,
        Paddr, PagingConstsTrait, PagingLevel, PodOnce, Vaddr,
    },
    Pod,
};

verus! {

pub(crate) const NR_ENTRIES_PER_PAGE: usize = 512;

#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Debug, Default)]
pub struct PagingConsts {}

impl PagingConstsTrait for PagingConsts {
    #[verifier::inline]
    open spec fn BASE_PAGE_SIZE_spec() -> usize {
        4096
    }

    #[inline(always)]
    fn BASE_PAGE_SIZE() -> usize {
        4096
    }

    #[verifier::inline]
    open spec fn NR_LEVELS_spec() -> PagingLevel {
        4
    }

    #[inline(always)]
    fn NR_LEVELS() -> PagingLevel {
        4
    }

    #[verifier::inline]
    open spec fn ADDRESS_WIDTH_spec() -> usize {
        48
    }

    #[inline(always)]
    fn ADDRESS_WIDTH() -> usize {
        48
    }

    #[verifier::inline]
    open spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel {
        4
    }

    #[inline(always)]
    fn HIGHEST_TRANSLATION_LEVEL() -> PagingLevel {
        4
    }

    #[verifier::inline]
    open spec fn VA_SIGN_EXT_spec() -> bool {
        true
    }

    #[inline(always)]
    fn VA_SIGN_EXT() -> bool {
        true
    }

    #[verifier::inline]
    open spec fn PTE_SIZE_spec() -> usize {
        8
    }

    #[inline(always)]
    fn PTE_SIZE() -> usize {
        8
    }

    proof fn lemma_paging_consts_requirements() {
        lemma_pow2_is_pow2_to64();
        lemma2_to64();
        lemma2_to64_rest();

        vstd::layout::unsigned_int_max_values();
        vstd_extra::external::ilog2::lemma_usize_pow2_ilog2(9);
        vstd_extra::external::ilog2::lemma_usize_pow2_ilog2(12);
        lemma_pow2_adds(9, 39);
    }
}

pub(crate) proof fn lemma_nr_subpage_per_huge_eq_nr_entries()
    ensures
        crate::mm::nr_subpage_per_huge::<PagingConsts>() == NR_ENTRIES_PER_PAGE,
{
}

bitflags::bitflags! {
    /// Possible flags for a page table entry.
    pub struct PageTableFlags: usize {
        /// Specifies whether the mapped frame or page table is valid.
        const VALID =           1usize << 0;
        /// Controls whether reads to the mapped frames are allowed.
        const READABLE =        1usize << 1;
        /// Controls whether writes to the mapped frames are allowed.
        const WRITABLE =        1usize << 2;
        /// Controls whether execution code in the mapped frames are allowed.
        const EXECUTABLE =      1usize << 3;
        /// Controls whether accesses from userspace (i.e. U-mode) are permitted.
        const USER =            1usize << 4;
        /// Indicates that the mapping is present in all address spaces, so it isn't flushed from
        /// the TLB on an address space switch.
        const GLOBAL =          1usize << 5;
        /// Whether the memory area represented by this entry is accessed.
        const ACCESSED =        1usize << 6;
        /// Whether the memory area represented by this entry is modified.
        const DIRTY =           1usize << 7;

        // First bit ignored by MMU.
        const RSV1 =            1usize << 8;
        // Second bit ignored by MMU.
        const RSV2 =            1usize << 9;

        // PBMT: Non-cacheable, idempotent, weakly-ordered (RVWMO), main memory
        const PBMT_NC =         1usize << 61;
        // PBMT: Non-cacheable, non-idempotent, strongly-ordered (I/O ordering), I/O
        const PBMT_IO =         1usize << 62;
        /// Naturally aligned power-of-2
        const NAPOT =           1usize << 63;
    }
}

proof fn lemma_riscv_page_property_flag_constants()
    ensures
        PageTableFlags::VALID().bits() == 0x1usize,
        PageTableFlags::READABLE().bits() == 0x2usize,
        PageTableFlags::WRITABLE().bits() == 0x4usize,
        PageTableFlags::EXECUTABLE().bits() == 0x8usize,
        PageTableFlags::USER().bits() == 0x10usize,
        PageTableFlags::GLOBAL().bits() == 0x20usize,
        PageTableFlags::ACCESSED().bits() == 0x40usize,
        PageTableFlags::DIRTY().bits() == 0x80usize,
        PageTableFlags::RSV1().bits() == 0x100usize,
        PageTableFlags::RSV2().bits() == 0x200usize,
        PageTableFlags::PBMT_IO().bits() == 0x4000_0000_0000_0000usize,
        PageTableFlags::VALID().bits().ilog2() == 0u32,
        PageTableFlags::READABLE().bits().ilog2() == 1u32,
        PageTableFlags::WRITABLE().bits().ilog2() == 2u32,
        PageTableFlags::EXECUTABLE().bits().ilog2() == 3u32,
        PageTableFlags::USER().bits().ilog2() == 4u32,
        PageTableFlags::GLOBAL().bits().ilog2() == 5u32,
        PageTableFlags::ACCESSED().bits().ilog2() == 6u32,
        PageTableFlags::DIRTY().bits().ilog2() == 7u32,
        PageTableFlags::RSV1().bits().ilog2() == 8u32,
        PageTableFlags::RSV2().bits().ilog2() == 9u32,
        PageFlags::R().bits() == 0x1u8,
        PageFlags::W().bits() == 0x2u8,
        PageFlags::X().bits() == 0x4u8,
        PageFlags::ACCESSED().bits() == 0x8u8,
        PageFlags::DIRTY().bits() == 0x10u8,
        PageFlags::AVAIL1().bits() == 0x40u8,
        PageFlags::AVAIL2().bits() == 0x80u8,
        PageFlags::all().bits() == 0xDFu8,
        PageFlags::R().bits().ilog2() == 0u32,
        PageFlags::W().bits().ilog2() == 1u32,
        PageFlags::X().bits().ilog2() == 2u32,
        PageFlags::ACCESSED().bits().ilog2() == 3u32,
        PageFlags::DIRTY().bits().ilog2() == 4u32,
        PageFlags::AVAIL1().bits().ilog2() == 6u32,
        PageFlags::AVAIL2().bits().ilog2() == 7u32,
        PrivFlags::USER().bits() == 0x1u8,
        PrivFlags::GLOBAL().bits() == 0x2u8,
        PrivFlags::all().bits() == 0x3u8,
        PrivFlags::USER().bits().ilog2() == 0u32,
        PrivFlags::GLOBAL().bits().ilog2() == 1u32,
{
    lemma_usize_ilog2_to32();
    lemma_u8_ilog2_to8();
    broadcast use PageTableFlags::lemma_consts;

    PageTableFlags::lemma_all_constant();
    broadcast use PageFlags::lemma_consts;
    broadcast use PrivFlags::lemma_consts;

    PageFlags::lemma_all_constant();
    PrivFlags::lemma_all_constant();
    assert(PageTableFlags::VALID().bits() == 0x1usize) by (compute);
    assert(PageTableFlags::READABLE().bits() == 0x2usize) by (compute);
    assert(PageTableFlags::WRITABLE().bits() == 0x4usize) by (compute);
    assert(PageTableFlags::EXECUTABLE().bits() == 0x8usize) by (compute);
    assert(PageTableFlags::USER().bits() == 0x10usize) by (compute);
    assert(PageTableFlags::GLOBAL().bits() == 0x20usize) by (compute);
    assert(PageTableFlags::ACCESSED().bits() == 0x40usize) by (compute);
    assert(PageTableFlags::DIRTY().bits() == 0x80usize) by (compute);
    assert(PageTableFlags::RSV1().bits() == 0x100usize) by (compute);
    assert(PageTableFlags::RSV2().bits() == 0x200usize) by (compute);
    assert(PageTableFlags::PBMT_IO().bits() == 0x4000_0000_0000_0000usize) by (compute);

    assert((0u8 | 0x1u8 | 0x2u8 | 0x4u8 | 0x3u8 | 0x5u8 | 0x7u8 | 0x8u8 | 0x10u8 | 0x40u8 | 0x80u8)
        == 0xDFu8) by (bit_vector);
    assert((0u8 | 0x1u8 | 0x2u8 | 0u8) == 0x3u8) by (bit_vector);
}

} // verus!
#[cfg(target_arch = "riscv64")]
pub(crate) fn tlb_flush_addr(vaddr: Vaddr) {
    unsafe {
        riscv::asm::sfence_vma(0, vaddr);
    }
}

#[cfg(target_arch = "riscv64")]
pub(crate) fn tlb_flush_addr_range(range: &Range<Vaddr>) {
    for vaddr in range.clone().step_by(PAGE_SIZE) {
        tlb_flush_addr(vaddr);
    }
}

#[cfg(target_arch = "riscv64")]
pub(crate) fn tlb_flush_all_excluding_global() {
    // TODO: excluding global?
    riscv::asm::sfence_vma_all()
}

#[cfg(target_arch = "riscv64")]
pub(crate) fn tlb_flush_all_including_global() {
    riscv::asm::sfence_vma_all()
}

verus! {

#[derive(Clone, Copy)]
#[repr(C)]
pub struct PageTableEntry(usize);

global layout PageTableEntry is size == 8, align == 8;

impl PageTableEntry {
    pub const VALID_BIT: usize = 0x1;

    pub const READABLE_BIT: usize = 0x2;

    pub const WRITABLE_BIT: usize = 0x4;

    pub const EXECUTABLE_BIT: usize = 0x8;

    pub const USER_BIT: usize = 0x10;

    pub const GLOBAL_BIT: usize = 0x20;

    pub const ACCESSED_BIT: usize = 0x40;

    pub const DIRTY_BIT: usize = 0x80;

    pub const RSV1_BIT: usize = 0x100;

    pub const RSV2_BIT: usize = 0x200;

    pub const PBMT_IO_BIT: usize = 0x4000_0000_0000_0000;

    pub const PHYS_ADDR_MASK: usize = 0x003F_FFFF_FFFF_FC00;

    pub proof fn lemma_layout()
        ensures
            core::mem::size_of::<PageTableEntry>() == 8,
            core::mem::align_of::<PageTableEntry>() == 8,
            core::mem::size_of::<PageTableEntry>() % core::mem::align_of::<PageTableEntry>() == 0,
    {
        broadcast use VERUS_layout_of_PageTableEntry;

    }

    closed spec fn default_spec() -> Self {
        Self(0)
    }

    fn new_paddr(paddr: Paddr) -> Self {
        let ppn = paddr >> 12;
        Self(ppn << 10)
    }

    #[inline(always)]
    fn from_raw(raw: usize) -> (res: Self)
        ensures
            res.0 == raw,
    {
        Self(raw)
    }
}

#[verus_verify]
unsafe impl Pod for PageTableEntry {

}

impl Default for PageTableEntry {
    fn default() -> (res: Self)
        returns
            Self::new_absent_spec(),
    {
        Self(0)
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
#[cfg(target_arch = "riscv64")]
pub unsafe fn activate_page_table(root_paddr: Paddr, _root_pt_cache: CachePolicy) {
    assert!(root_paddr % PagingConsts::BASE_PAGE_SIZE() == 0);
    let ppn = root_paddr >> 12;
    riscv::register::satp::set(riscv::register::satp::Mode::Sv48, 0, ppn);
}

#[cfg(target_arch = "riscv64")]
pub fn current_page_table_paddr() -> Paddr {
    riscv::register::satp::read().ppn() << 12
}

/// Parse a bit-flag bits `val` in the representation of `from` to `to` in bits.
macro_rules! parse_flags {
    ($val:expr, $from:expr, $to:expr) => {
        ($val as usize & $from.bits() as usize) >> $from.bits().ilog2() << $to.bits().ilog2()
    };
}

impl PodOnce for PageTableEntry {}

verus! {

impl PageTableEntry {
    #[verifier::inline]
    pub open spec fn raw_property_bits_from_parts_spec(
        page_bits: u8,
        priv_bits: u8,
        cache: CachePolicy,
    ) -> usize {
        Self::VALID_BIT | if page_bits & 0x01u8 != 0 {
            Self::READABLE_BIT
        } else {
            0usize
        } | if page_bits & 0x02u8 != 0 {
            Self::WRITABLE_BIT
        } else {
            0usize
        } | if page_bits & 0x04u8 != 0 {
            Self::EXECUTABLE_BIT
        } else {
            0usize
        } | if page_bits & 0x08u8 != 0 {
            Self::ACCESSED_BIT
        } else {
            0usize
        } | if page_bits & 0x10u8 != 0 {
            Self::DIRTY_BIT
        } else {
            0usize
        } | if priv_bits & 0x01u8 != 0 {
            Self::USER_BIT
        } else {
            0usize
        } | if priv_bits & 0x02u8 != 0 {
            Self::GLOBAL_BIT
        } else {
            0usize
        } | if page_bits & 0x40u8 != 0 {
            Self::RSV1_BIT
        } else {
            0usize
        } | if page_bits & 0x80u8 != 0 {
            Self::RSV2_BIT
        } else {
            0usize
        } | if cache is Uncacheable {
            Self::PBMT_IO_BIT
        } else {
            0usize
        }
    }

    pub open spec fn raw_property_bits_spec(prop: PageProperty) -> usize {
        Self::raw_property_bits_from_parts_spec(
            prop.flags.bits(),
            prop.priv_flags.bits(),
            prop.cache,
        )
    }

    pub open spec fn raw_set_prop_spec(old_raw: usize, prop: PageProperty) -> usize {
        if old_raw & Self::VALID_BIT != 0 {
            (old_raw & Self::PHYS_ADDR_MASK) | Self::raw_property_bits_spec(prop)
        } else {
            old_raw
        }
    }
}

proof fn lemma_riscv_parse_flags(raw: usize)
    ensures
        parse_flags!(raw, PageTableFlags::READABLE(), PageFlags::R()) == if raw & 0x2usize != 0 {
            0x1usize
        } else {
            0usize
        },
        parse_flags!(raw, PageTableFlags::WRITABLE(), PageFlags::W()) == if raw & 0x4usize != 0 {
            0x2usize
        } else {
            0usize
        },
        parse_flags!(raw, PageTableFlags::EXECUTABLE(), PageFlags::X()) == if raw & 0x8usize != 0 {
            0x4usize
        } else {
            0usize
        },
        parse_flags!(raw, PageTableFlags::ACCESSED(), PageFlags::ACCESSED()) == if raw & 0x40usize
            != 0 {
            0x8usize
        } else {
            0usize
        },
        parse_flags!(raw, PageTableFlags::DIRTY(), PageFlags::DIRTY()) == if raw & 0x80usize != 0 {
            0x10usize
        } else {
            0usize
        },
        parse_flags!(raw, PageTableFlags::RSV1(), PageFlags::AVAIL1()) == if raw & 0x100usize != 0 {
            0x40usize
        } else {
            0usize
        },
        parse_flags!(raw, PageTableFlags::RSV2(), PageFlags::AVAIL2()) == if raw & 0x200usize != 0 {
            0x80usize
        } else {
            0usize
        },
        parse_flags!(raw, PageTableFlags::USER(), PrivFlags::USER()) == if raw & 0x10usize != 0 {
            0x1usize
        } else {
            0usize
        },
        parse_flags!(raw, PageTableFlags::GLOBAL(), PrivFlags::GLOBAL()) == if raw & 0x20usize
            != 0 {
            0x2usize
        } else {
            0usize
        },
{
    lemma_riscv_page_property_flag_constants();
    assert(((raw & 0x2usize) >> 1 << 0) == (if raw & 0x2usize != 0 {
        0x1usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((raw & 0x4usize) >> 2 << 1) == (if raw & 0x4usize != 0 {
        0x2usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((raw & 0x8usize) >> 3 << 2) == (if raw & 0x8usize != 0 {
        0x4usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((raw & 0x40usize) >> 6 << 3) == (if raw & 0x40usize != 0 {
        0x8usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((raw & 0x80usize) >> 7 << 4) == (if raw & 0x80usize != 0 {
        0x10usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((raw & 0x100usize) >> 8 << 6) == (if raw & 0x100usize != 0 {
        0x40usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((raw & 0x200usize) >> 9 << 7) == (if raw & 0x200usize != 0 {
        0x80usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((raw & 0x10usize) >> 4 << 0) == (if raw & 0x10usize != 0 {
        0x1usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((raw & 0x20usize) >> 5 << 1) == (if raw & 0x20usize != 0 {
        0x2usize
    } else {
        0usize
    })) by (bit_vector);
}

proof fn lemma_riscv_encode_flags(page_bits: u8, priv_bits: u8)
    ensures
        parse_flags!(page_bits, PageFlags::R(), PageTableFlags::READABLE()) == if page_bits & 0x1u8
            != 0 {
            0x2usize
        } else {
            0usize
        },
        parse_flags!(page_bits, PageFlags::W(), PageTableFlags::WRITABLE()) == if page_bits & 0x2u8
            != 0 {
            0x4usize
        } else {
            0usize
        },
        parse_flags!(page_bits, PageFlags::X(), PageTableFlags::EXECUTABLE()) == if page_bits
            & 0x4u8 != 0 {
            0x8usize
        } else {
            0usize
        },
        parse_flags!(page_bits, PageFlags::ACCESSED(), PageTableFlags::ACCESSED()) == if page_bits
            & 0x8u8 != 0 {
            0x40usize
        } else {
            0usize
        },
        parse_flags!(page_bits, PageFlags::DIRTY(), PageTableFlags::DIRTY()) == if page_bits
            & 0x10u8 != 0 {
            0x80usize
        } else {
            0usize
        },
        parse_flags!(page_bits, PageFlags::AVAIL1(), PageTableFlags::RSV1()) == if page_bits
            & 0x40u8 != 0 {
            0x100usize
        } else {
            0usize
        },
        parse_flags!(page_bits, PageFlags::AVAIL2(), PageTableFlags::RSV2()) == if page_bits
            & 0x80u8 != 0 {
            0x200usize
        } else {
            0usize
        },
        parse_flags!(priv_bits, PrivFlags::USER(), PageTableFlags::USER()) == if priv_bits & 0x1u8
            != 0 {
            0x10usize
        } else {
            0usize
        },
        parse_flags!(priv_bits, PrivFlags::GLOBAL(), PageTableFlags::GLOBAL()) == if priv_bits
            & 0x2u8 != 0 {
            0x20usize
        } else {
            0usize
        },
{
    lemma_riscv_page_property_flag_constants();
    assert((((page_bits as usize) & 0x1usize) >> 0 << 1) == (if page_bits & 0x1u8 != 0 {
        0x2usize
    } else {
        0usize
    })) by (bit_vector);
    assert((((page_bits as usize) & 0x2usize) >> 1 << 2) == (if page_bits & 0x2u8 != 0 {
        0x4usize
    } else {
        0usize
    })) by (bit_vector);
    assert((((page_bits as usize) & 0x4usize) >> 2 << 3) == (if page_bits & 0x4u8 != 0 {
        0x8usize
    } else {
        0usize
    })) by (bit_vector);
    assert((((page_bits as usize) & 0x8usize) >> 3 << 6) == (if page_bits & 0x8u8 != 0 {
        0x40usize
    } else {
        0usize
    })) by (bit_vector);
    assert((((page_bits as usize) & 0x10usize) >> 4 << 7) == (if page_bits & 0x10u8 != 0 {
        0x80usize
    } else {
        0usize
    })) by (bit_vector);
    assert((((page_bits as usize) & 0x40usize) >> 6 << 8) == (if page_bits & 0x40u8 != 0 {
        0x100usize
    } else {
        0usize
    })) by (bit_vector);
    assert((((page_bits as usize) & 0x80usize) >> 7 << 9) == (if page_bits & 0x80u8 != 0 {
        0x200usize
    } else {
        0usize
    })) by (bit_vector);
    assert((((priv_bits as usize) & 0x1usize) >> 0 << 4) == (if priv_bits & 0x1u8 != 0 {
        0x10usize
    } else {
        0usize
    })) by (bit_vector);
    assert((((priv_bits as usize) & 0x2usize) >> 1 << 5) == (if priv_bits & 0x2u8 != 0 {
        0x20usize
    } else {
        0usize
    })) by (bit_vector);
}

#[verifier::bit_vector]
proof fn lemma_riscv_property_bits_writeback(page_bits: u8, priv_bits: u8, flags: usize)
    requires
        flags == 0x1usize | if page_bits & 0x01u8 != 0 {
            0x2usize
        } else {
            0usize
        } | if page_bits & 0x02u8 != 0 {
            0x4usize
        } else {
            0usize
        } | if page_bits & 0x04u8 != 0 {
            0x8usize
        } else {
            0usize
        } | if page_bits & 0x08u8 != 0 {
            0x40usize
        } else {
            0usize
        } | if page_bits & 0x10u8 != 0 {
            0x80usize
        } else {
            0usize
        } | if priv_bits & 0x01u8 != 0 {
            0x10usize
        } else {
            0usize
        } | if priv_bits & 0x02u8 != 0 {
            0x20usize
        } else {
            0usize
        } | if page_bits & 0x40u8 != 0 {
            0x100usize
        } else {
            0usize
        } | if page_bits & 0x80u8 != 0 {
            0x200usize
        } else {
            0usize
        },
    ensures
        flags == PageTableEntry::raw_property_bits_from_parts_spec(
            page_bits,
            priv_bits,
            CachePolicy::Writeback,
        ),
{
}

#[verifier::bit_vector]
proof fn lemma_riscv_property_bits_uncacheable(page_bits: u8, priv_bits: u8, flags: usize)
    requires
        flags == 0x1usize | if page_bits & 0x01u8 != 0 {
            0x2usize
        } else {
            0usize
        } | if page_bits & 0x02u8 != 0 {
            0x4usize
        } else {
            0usize
        } | if page_bits & 0x04u8 != 0 {
            0x8usize
        } else {
            0usize
        } | if page_bits & 0x08u8 != 0 {
            0x40usize
        } else {
            0usize
        } | if page_bits & 0x10u8 != 0 {
            0x80usize
        } else {
            0usize
        } | if priv_bits & 0x01u8 != 0 {
            0x10usize
        } else {
            0usize
        } | if priv_bits & 0x02u8 != 0 {
            0x20usize
        } else {
            0usize
        } | if page_bits & 0x40u8 != 0 {
            0x100usize
        } else {
            0usize
        } | if page_bits & 0x80u8 != 0 {
            0x200usize
        } else {
            0usize
        } | 0x4000_0000_0000_0000usize,
    ensures
        flags == PageTableEntry::raw_property_bits_from_parts_spec(
            page_bits,
            priv_bits,
            CachePolicy::Uncacheable,
        ),
{
}

#[verifier::bit_vector]
proof fn lemma_riscv_set_prop_bits_writeback(
    old_raw: usize,
    new_raw: usize,
    page_bits: u8,
    priv_bits: u8,
)
    requires
        page_bits & 0xDFu8 == page_bits,
        priv_bits & 0x3u8 == priv_bits,
        page_bits & 0x07u8 != 0,
        new_raw == (old_raw & PageTableEntry::PHYS_ADDR_MASK)
            | PageTableEntry::raw_property_bits_from_parts_spec(
            page_bits,
            priv_bits,
            CachePolicy::Writeback,
        ),
    ensures
        RiscvPteModel::paddr_from_raw_spec(new_raw) == RiscvPteModel::paddr_from_raw_spec(old_raw),
        RiscvPteModel::decode_page_flags_spec(new_raw) == page_bits,
        RiscvPteModel::decode_priv_flags_spec(new_raw) == priv_bits,
        new_raw & PageTableEntry::VALID_BIT != 0,
        new_raw & (PageTableEntry::READABLE_BIT | PageTableEntry::WRITABLE_BIT
            | PageTableEntry::EXECUTABLE_BIT) != 0,
        new_raw & PageTableEntry::PBMT_IO_BIT == 0,
{
}

#[verifier::bit_vector]
proof fn lemma_riscv_set_prop_bits_uncacheable(
    old_raw: usize,
    new_raw: usize,
    page_bits: u8,
    priv_bits: u8,
)
    requires
        page_bits & 0xDFu8 == page_bits,
        priv_bits & 0x3u8 == priv_bits,
        page_bits & 0x07u8 != 0,
        new_raw == (old_raw & PageTableEntry::PHYS_ADDR_MASK)
            | PageTableEntry::raw_property_bits_from_parts_spec(
            page_bits,
            priv_bits,
            CachePolicy::Uncacheable,
        ),
    ensures
        RiscvPteModel::paddr_from_raw_spec(new_raw) == RiscvPteModel::paddr_from_raw_spec(old_raw),
        RiscvPteModel::decode_page_flags_spec(new_raw) == page_bits,
        RiscvPteModel::decode_priv_flags_spec(new_raw) == priv_bits,
        new_raw & PageTableEntry::VALID_BIT != 0,
        new_raw & (PageTableEntry::READABLE_BIT | PageTableEntry::WRITABLE_BIT
            | PageTableEntry::EXECUTABLE_BIT) != 0,
        new_raw & PageTableEntry::PBMT_IO_BIT != 0,
{
}

proof fn lemma_riscv_set_prop_roundtrip(old_raw: usize, new_raw: usize, prop: PageProperty)
    requires
        prop.inv(),
        prop.cache is Writeback || prop.cache is Uncacheable,
        prop.flags.bits() & 0x07u8 != 0,
        new_raw == PageTableEntry::raw_set_prop_spec(old_raw, prop),
        old_raw & PageTableEntry::VALID_BIT != 0,
    ensures
        PageTableEntry(new_raw).prop() == prop,
        PageTableEntry(new_raw).paddr() == PageTableEntry(old_raw).paddr(),
        PageTableEntry(new_raw).is_present(),
        forall|level: PagingLevel| PageTableEntry(new_raw).is_last(level),
        forall|level: PagingLevel| #[trigger]
            PageTableEntry(old_raw).is_last(level) ==> PageTableEntry(new_raw).is_last(level),
{
    lemma_riscv_page_property_flag_constants();
    let page_bits = prop.flags.bits();
    let priv_bits = prop.priv_flags.bits();

    assert(new_raw == (old_raw & PageTableEntry::PHYS_ADDR_MASK)
        | PageTableEntry::raw_property_bits_spec(prop));
    assert(PageTableEntry::raw_property_bits_spec(prop)
        == PageTableEntry::raw_property_bits_from_parts_spec(page_bits, priv_bits, prop.cache));
    match prop.cache {
        CachePolicy::Writeback => {
            lemma_riscv_set_prop_bits_writeback(old_raw, new_raw, page_bits, priv_bits);
            assert(RiscvPteModel::decode_cache_spec(new_raw) == CachePolicy::Writeback);
        },
        CachePolicy::Uncacheable => {
            lemma_riscv_set_prop_bits_uncacheable(old_raw, new_raw, page_bits, priv_bits);
            assert(RiscvPteModel::decode_cache_spec(new_raw) == CachePolicy::Uncacheable);
        },
        _ => {},
    }
    assert(PageTableEntry(new_raw).paddr() == RiscvPteModel::paddr_from_raw_spec(new_raw))
        by (compute_only);
    assert(PageTableEntry(old_raw).paddr() == RiscvPteModel::paddr_from_raw_spec(old_raw))
        by (compute_only);
    assert(PageTableEntry(new_raw).is_present() == (new_raw & PageTableEntry::VALID_BIT != 0))
        by (compute_only);
    assert(PageTableEntry(new_raw).is_present());
    assert(RiscvPteModel::decode_page_flags_spec(new_raw) == page_bits);
    assert(RiscvPteModel::decode_priv_flags_spec(new_raw) == priv_bits);
    PageFlags::lemma_from_bits_bits(page_bits);
    PrivFlags::lemma_from_bits_bits(priv_bits);
    PageFlags::lemma_eq_from_bits(PageTableEntry(new_raw).prop().flags, prop.flags);
    PrivFlags::lemma_eq_from_bits(PageTableEntry(new_raw).prop().priv_flags, prop.priv_flags);
    assert(PageTableEntry(new_raw).prop().cache == prop.cache);
    assert(PageTableEntry(new_raw).prop() == prop);
    assert forall|level: PagingLevel| PageTableEntry(new_raw).is_last(level) by {
        assert(PageTableEntry(new_raw).is_last(level));
    }
    assert forall|level: PagingLevel| #[trigger]
        PageTableEntry(old_raw).is_last(level) implies PageTableEntry(new_raw).is_last(level) by {
        assert(PageTableEntry(new_raw).is_last(level));
    }
}

#[verifier::bit_vector]
proof fn lemma_riscv_decoded_flags_wf(raw: usize)
    ensures
        (RiscvPteModel::decode_page_flags_spec(raw) as usize) & 0xDFusize
            == RiscvPteModel::decode_page_flags_spec(raw) as usize,
        (RiscvPteModel::decode_priv_flags_spec(raw) as usize) & 0x3usize
            == RiscvPteModel::decode_priv_flags_spec(raw) as usize,
        RiscvPteModel::decode_page_flags_spec(raw) as usize <= 0xFFusize,
        RiscvPteModel::decode_priv_flags_spec(raw) as usize <= 0xFFusize,
{
}

#[verifier::bit_vector]
proof fn lemma_riscv_paddr_encoding_for_current(paddr: Paddr)
    requires
        paddr < MAX_PADDR,
    ensures
        RiscvPteModel::paddr_from_raw_spec((paddr >> 12) << 10) == paddr & !((PAGE_SIZE
            - 1) as usize),
        valid_frame_paddr(RiscvPteModel::paddr_from_raw_spec((paddr >> 12) << 10)),
{
}

impl PageTableEntryTrait for PageTableEntry {
    fn new_absent() -> Self {
        proof {
            lemma_riscv_page_property_flag_constants();
            assert(Self::default_spec() == Self::new_absent_spec()) by (compute_only);
            assert(0usize % PAGE_SIZE == 0) by (compute_only);
            assert(0 < MAX_PADDR) by (compute_only);
            assert(Self(0).paddr() == 0) by (compute_only);
            assert(!Self(0).is_present()) by (bit_vector);
        }
        Self(0)
    }

    fn is_present(&self) -> bool {
        proof {
            lemma_riscv_page_property_flag_constants();
            assert(self.is_present_spec() == (self.0 & 0x1usize != 0)) by (compute_only);
        }
        self.0 & PageTableFlags::VALID().bits() != 0
    }

    closed spec fn new_absent_spec() -> Self {
        Self::default_spec()
    }

    closed spec fn is_present_spec(&self) -> bool {
        RiscvPteModel { raw: self.0 }.is_present_spec()
    }

    closed spec fn new_page_spec(paddr: Paddr, _level: PagingLevel, prop: PageProperty) -> Self {
        Self(Self::raw_set_prop_spec(((paddr >> 12) << 10) | Self::VALID_BIT, prop))
    }

    open spec fn new_page_req(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> bool {
        RiscvPteModel::new_page_req(paddr, level, prop)
    }

    fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        let initial_pte = Self::from_raw(((paddr >> 12) << 10) | 1usize);
        proof {
            assert(Self::new_page_req(paddr, level, prop));
            assert(RiscvPteModel::new_page_req(paddr, level, prop));
            assert(paddr < MAX_PADDR);
            assert(paddr % PAGE_SIZE == 0);
            assert(initial_pte.0 == ((paddr >> 12) << 10) | 1usize);
            let ghost initial_raw = initial_pte.as_usize();
            assert(initial_raw == ((paddr >> 12) << 10) | 1usize);
            assert(initial_pte.paddr() == paddr & !((PAGE_SIZE - 1) as usize)) by {
                lemma_riscv_paddr_encoding_for_current(paddr);
                assert(initial_pte.paddr() == RiscvPteModel::paddr_from_raw_spec(initial_pte.0))
                    by (compute_only);
                assert(initial_pte.paddr() == RiscvPteModel::paddr_from_raw_spec(initial_raw));
                assert(RiscvPteModel::paddr_from_raw_spec(initial_raw)
                    == RiscvPteModel::paddr_from_raw_spec((paddr >> 12) << 10)) by (bit_vector)
                    requires
                        initial_raw == ((paddr >> 12) << 10) | 1usize,
                ;
            }
            assert(paddr & !((PAGE_SIZE - 1) as usize) == paddr) by (bit_vector)
                requires
                    paddr % PAGE_SIZE == 0,
            ;
            assert(initial_pte.paddr() == paddr);
            assert(valid_frame_paddr(initial_pte.paddr()));
            assert(initial_pte.0 == initial_raw);
            assert(initial_pte.is_present() == (initial_pte.0 & Self::VALID_BIT != 0))
                by (compute_only);
            assert(initial_raw & Self::VALID_BIT != 0) by (bit_vector)
                requires
                    initial_raw == ((paddr >> 12) << 10) | 1usize,
            ;
            assert(initial_pte.is_present());
        }
        let mut pte = initial_pte;
        pte.set_prop(prop);
        proof {
            lemma_riscv_paddr_encoding_for_current(paddr);
            assert(pte.as_usize() == Self::raw_set_prop_spec(
                ((paddr >> 12) << 10) | Self::VALID_BIT,
                prop,
            ));
            assert(pte.as_usize() == Self::new_page_spec(paddr, level, prop).as_usize_spec());
            assert(pte == Self::new_page_spec(paddr, level, prop));
            assert(pte.is_present());
            assert(pte.prop() == prop);
            assert(pte.paddr() == paddr & !((PAGE_SIZE - 1) as usize));
            assert(valid_frame_paddr(pte.paddr()));
            assert(pte.is_last(level));
        }
        pte
    }

    closed spec fn new_pt_spec(paddr: Paddr) -> Self {
        Self(((paddr >> 12) << 10) | Self::VALID_BIT)
    }

    fn new_pt(paddr: Paddr) -> Self {
        // In RISC-V, non-leaf PTE should have RWX = 000,
        // and D, A, and U are reserved for future standard use.
        let pte = Self::from_raw((paddr >> 12) << 10);
        let res = Self::from_raw(pte.0 | Self::VALID_BIT);
        proof {
            lemma_riscv_paddr_encoding_for_current(paddr);
            assert(res.as_usize() == ((paddr >> 12) << 10) | Self::VALID_BIT);
            assert(res.as_usize() == Self::new_pt_spec(paddr).as_usize_spec());
            assert(res == Self::new_pt_spec(paddr));
            let ghost res_raw = res.as_usize();
            assert(res_raw == ((paddr >> 12) << 10) | Self::VALID_BIT);
            assert(res.paddr() == RiscvPteModel::paddr_from_raw_spec(res.0)) by (compute_only);
            assert(res.0 == res_raw);
            assert(RiscvPteModel::paddr_from_raw_spec(res_raw)
                == RiscvPteModel::paddr_from_raw_spec((paddr >> 12) << 10)) by (bit_vector)
                requires
                    res_raw == ((paddr >> 12) << 10) | Self::VALID_BIT,
            ;
            assert(RiscvPteModel::paddr_from_raw_spec((paddr >> 12) << 10) == paddr & !((PAGE_SIZE
                - 1) as usize));
            assert(res.paddr() == paddr & !((PAGE_SIZE - 1) as usize));
            assert(paddr % PAGE_SIZE == 0 ==> res.paddr() == paddr) by {
                if paddr % PAGE_SIZE == 0 {
                    assert(paddr & !((PAGE_SIZE - 1) as usize) == paddr) by (bit_vector)
                        requires
                            PAGE_SIZE == 4096usize,
                            paddr % PAGE_SIZE == 0,
                    ;
                    assert(res.paddr() == paddr);
                }
            }
            assert(valid_frame_paddr(res.paddr()));
            assert(res.is_present() == (res.0 & Self::VALID_BIT != 0)) by (compute_only);
            assert(res_raw & Self::VALID_BIT != 0) by (bit_vector)
                requires
                    res_raw == ((paddr >> 12) << 10) | Self::VALID_BIT,
            ;
            assert(res.0 & Self::VALID_BIT != 0);
            assert(res_raw & Self::VALID_BIT != 0) by (bit_vector)
                requires
                    res_raw == ((paddr >> 12) << 10) | Self::VALID_BIT,
            ;
            assert(res.is_present());
            assert forall|level: PagingLevel| !res.is_last(level) by {
                assert(res_raw & 0xEusize == 0usize) by (bit_vector)
                    requires
                        res_raw == ((paddr >> 12) << 10) | Self::VALID_BIT,
                ;
                assert(res.as_usize() & 0xEusize == 0usize);
                assert(res.is_last(level) == (res.as_usize() & 0xEusize != 0)) by (compute_only);
                assert(!res.is_last(level));
            }
        }
        res
    }

    closed spec fn paddr_spec(&self) -> Paddr {
        RiscvPteModel { raw: self.0 }.paddr_spec()
    }

    fn paddr(&self) -> Paddr {
        proof {
            self.lemma_paddr_is_page_aligned();
        }
        let ppn = (self.0 & Self::PHYS_ADDR_MASK) >> 10;
        ppn << 12
    }

    closed spec fn prop_spec(&self) -> PageProperty {
        RiscvPteModel { raw: self.0 }.prop_spec()
    }

    fn prop(&self) -> PageProperty {
        proof {
            lemma_riscv_page_property_flag_constants();
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
            lemma_riscv_parse_flags(self.0);
            lemma_riscv_decoded_flags_wf(self.0);
            assert(flags == RiscvPteModel::decode_page_flags_spec(self.0) as usize);
            assert(priv_flags == RiscvPteModel::decode_priv_flags_spec(self.0) as usize);
            assert(flags & 0xDFusize == flags);
            assert(priv_flags & 0x3usize == priv_flags);
            assert(flags <= 0xFFusize);
            assert(priv_flags <= 0xFFusize);
            assert((flags as u8) & 0xDFu8 == flags as u8) by (bit_vector)
                requires
                    flags & 0xDFusize == flags,
                    flags <= 0xFFusize,
            ;
            assert((priv_flags as u8) & 0x3u8 == priv_flags as u8) by (bit_vector)
                requires
                    priv_flags & 0x3usize == priv_flags,
                    priv_flags <= 0xFFusize,
            ;
            assert((flags as u8) & PageFlags::all().bits() == flags as u8);
            assert((priv_flags as u8) & PrivFlags::all().bits() == priv_flags as u8);
            PageFlags::lemma_from_bits_bits(flags as u8);
            PrivFlags::lemma_from_bits_bits(priv_flags as u8);
        }

        PageProperty {
            flags: PageFlags::from_bits(flags as u8).unwrap(),
            cache,
            priv_flags: PrivFlags::from_bits(priv_flags as u8).unwrap(),
        }
    }

    open spec fn set_prop_req(self, prop: PageProperty) -> bool {
        RiscvPteModel::set_prop_req(prop)
    }

    fn set_prop(&mut self, prop: PageProperty)
        ensures
            old(self).is_present() ==> final(self).as_usize() == Self::raw_set_prop_spec(
                old(self).as_usize(),
                prop,
            ),
            old(self).is_present() ==> forall|level: PagingLevel| final(self).is_last(level),
    {
        proof {
            lemma_riscv_page_property_flag_constants();
        }
        if !self.is_present() {
            return;
        }
        let page_bits = prop.flags.bits();
        let priv_bits = prop.priv_flags.bits();
        let base_flags = Self::VALID_BIT | if page_bits & 0x01u8 != 0 {
            Self::READABLE_BIT
        } else {
            0usize
        } | if page_bits & 0x02u8 != 0 {
            Self::WRITABLE_BIT
        } else {
            0usize
        } | if page_bits & 0x04u8 != 0 {
            Self::EXECUTABLE_BIT
        } else {
            0usize
        } | if page_bits & 0x08u8 != 0 {
            Self::ACCESSED_BIT
        } else {
            0usize
        } | if page_bits & 0x10u8 != 0 {
            Self::DIRTY_BIT
        } else {
            0usize
        } | if priv_bits & 0x01u8 != 0 {
            Self::USER_BIT
        } else {
            0usize
        } | if priv_bits & 0x02u8 != 0 {
            Self::GLOBAL_BIT
        } else {
            0usize
        } | if page_bits & 0x40u8 != 0 {
            Self::RSV1_BIT
        } else {
            0usize
        } | if page_bits & 0x80u8 != 0 {
            Self::RSV2_BIT
        } else {
            0usize
        };
        let mut flags = base_flags;
        proof {
            lemma_riscv_encode_flags(page_bits, priv_bits);
            assert(page_bits == prop.flags.bits());
            assert(priv_bits == prop.priv_flags.bits());
        }

        match prop.cache {
            CachePolicy::Writeback => {
                proof {
                    reveal(PageTableEntry::raw_property_bits_spec);
                    assert(prop.cache is Writeback);
                    assert(!(prop.cache is Uncacheable));
                    assert((if prop.cache is Uncacheable {
                        Self::PBMT_IO_BIT
                    } else {
                        0usize
                    }) == 0usize);
                    assert(flags == base_flags);
                    lemma_riscv_property_bits_writeback(page_bits, priv_bits, flags);
                    assert(Self::raw_property_bits_from_parts_spec(
                        page_bits,
                        priv_bits,
                        CachePolicy::Writeback,
                    ) == Self::raw_property_bits_from_parts_spec(page_bits, priv_bits, prop.cache));
                    assert(Self::raw_property_bits_from_parts_spec(page_bits, priv_bits, prop.cache)
                        == Self::raw_property_bits_spec(prop));
                }
            },
            CachePolicy::Uncacheable => {
                // Currently, Asterinas uses `Uncacheable` for I/O memory.
                flags |= Self::PBMT_IO_BIT;
                proof {
                    reveal(PageTableEntry::raw_property_bits_spec);
                    assert(prop.cache is Uncacheable);
                    assert(flags == base_flags | Self::PBMT_IO_BIT);
                    lemma_riscv_property_bits_uncacheable(page_bits, priv_bits, flags);
                    assert(Self::raw_property_bits_from_parts_spec(
                        page_bits,
                        priv_bits,
                        CachePolicy::Uncacheable,
                    ) == Self::raw_property_bits_from_parts_spec(page_bits, priv_bits, prop.cache));
                    assert(Self::raw_property_bits_from_parts_spec(page_bits, priv_bits, prop.cache)
                        == Self::raw_property_bits_spec(prop));
                }
            },
            _ => panic_diverge(),
        }

        self.0 = (self.0 & Self::PHYS_ADDR_MASK) | flags;
        proof {
            reveal(PageTableEntry::raw_set_prop_spec);
            assert(old(self).is_present());
            match prop.cache {
                CachePolicy::Writeback => {
                    lemma_riscv_property_bits_writeback(page_bits, priv_bits, flags);
                    assert(Self::raw_property_bits_from_parts_spec(
                        page_bits,
                        priv_bits,
                        CachePolicy::Writeback,
                    ) == Self::raw_property_bits_spec(prop));
                },
                CachePolicy::Uncacheable => {
                    lemma_riscv_property_bits_uncacheable(page_bits, priv_bits, flags);
                    assert(Self::raw_property_bits_from_parts_spec(
                        page_bits,
                        priv_bits,
                        CachePolicy::Uncacheable,
                    ) == Self::raw_property_bits_spec(prop));
                },
                _ => {},
            }
            assert(flags == Self::raw_property_bits_spec(prop));
            assert(self.as_usize() == (old(self).as_usize() & Self::PHYS_ADDR_MASK) | flags);
            assert(self.as_usize() == Self::raw_set_prop_spec(old(self).as_usize(), prop));
            lemma_riscv_set_prop_roundtrip(old(self).as_usize(), self.as_usize(), prop);
        }
    }

    closed spec fn is_last_spec(&self, level: PagingLevel) -> bool {
        RiscvPteModel { raw: self.0 }.is_last_spec(level)
    }

    fn is_last(&self, level: PagingLevel) -> bool {
        proof {
            lemma_riscv_page_property_flag_constants();
            assert(self.is_last_spec(level) == (self.0 & 0xEusize != 0)) by (compute_only);
        }
        let rwx = PageTableFlags::READABLE() | PageTableFlags::WRITABLE()
            | PageTableFlags::EXECUTABLE();
        (self.0 & rwx.bits()) != 0
    }

    closed spec fn as_usize_spec(self) -> usize {
        self.0
    }

    fn as_usize(self) -> usize {
        self.0
    }

    fn from_usize(pte_raw: usize) -> Self {
        Self(pte_raw)
    }

    proof fn lemma_page_table_entry_properties() {
        lemma_riscv_page_property_flag_constants();
        Self::lemma_layout();
        assert(core::mem::size_of::<Self>() == 8);
        assert(core::mem::align_of::<Self>() == 8);
        assert(8usize % 8usize == 0) by (compute_only);
        assert(valid_frame_paddr(Self::new_absent().paddr())) by (compute_only);
        assert(!Self::new_absent().is_present()) by (compute_only);
        assert forall|level: PagingLevel|
            #![trigger Self::new_absent().is_last(level)]
            1 < level ==> !Self::new_absent().is_last(level) by {
            assert(!Self::new_absent().is_last(level)) by (compute_only);
        }
        assert forall|paddr: Paddr, level: PagingLevel, prop: PageProperty|
            #![trigger Self::new_page(paddr, level, prop)]
            Self::new_page_req(paddr, level, prop) && (prop.cache is Writeback
                || prop.cache is Writethrough || prop.cache is Uncacheable) ==> {
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
            if Self::new_page_req(paddr, level, prop) && (prop.cache is Writeback
                || prop.cache is Writethrough || prop.cache is Uncacheable) {
                let old_raw = ((paddr >> 12) << 10) | Self::VALID_BIT;
                let pte = Self::new_page(paddr, level, prop);
                let raw = pte.as_usize();
                reveal(<PageTableEntry as PageTableEntryTrait>::new_page_req);
                assert(Self::new_page_req(paddr, level, prop));
                assert(prop.inv());
                assert(prop.cache is Writeback || prop.cache is Uncacheable);
                assert(prop.flags.bits() & 0x07u8 != 0);
                assert(pte.0 == raw);
                reveal(<PageTableEntry as PageTableEntryTrait>::new_page_spec);
                reveal(PageTableEntry::raw_set_prop_spec);
                assert(pte.0 == Self::raw_set_prop_spec(old_raw, prop));
                assert(raw == Self::raw_set_prop_spec(old_raw, prop));
                assert(Self::VALID_BIT == 1usize) by (compute_only);
                assert(old_raw & Self::VALID_BIT != 0) by (bit_vector)
                    requires
                        old_raw == ((paddr >> 12) << 10) | Self::VALID_BIT,
                        Self::VALID_BIT == 1usize,
                ;
                lemma_riscv_set_prop_roundtrip(old_raw, raw, prop);
                assert(pte == PageTableEntry(raw));
                assert(pte.is_present());
                assert(pte.prop() == prop);
                assert(pte.is_last(level));
                if paddr < MAX_PADDR {
                    lemma_riscv_paddr_encoding_for_current(paddr);
                    assert(PageTableEntry(old_raw).paddr() == RiscvPteModel::paddr_from_raw_spec(
                        old_raw,
                    )) by (compute_only);
                    assert(RiscvPteModel::paddr_from_raw_spec(old_raw)
                        == RiscvPteModel::paddr_from_raw_spec((paddr >> 12) << 10)) by (bit_vector)
                        requires
                            old_raw == ((paddr >> 12) << 10) | Self::VALID_BIT,
                    ;
                    assert(PageTableEntry(old_raw).paddr() == paddr & !((PAGE_SIZE - 1) as usize));
                    assert(pte.paddr() == paddr & !((PAGE_SIZE - 1) as usize));
                    if paddr % PAGE_SIZE == 0 {
                        assert(paddr & !((PAGE_SIZE - 1) as usize) == paddr) by (bit_vector)
                            requires
                                PAGE_SIZE == 4096usize,
                                paddr % PAGE_SIZE == 0,
                        ;
                        assert(pte.paddr() == paddr);
                    }
                }
            }
        }
        assert forall|paddr: Paddr|
            #![trigger Self::new_pt(paddr)]
            {
                &&& Self::new_pt(paddr).is_present()
                &&& (paddr < MAX_PADDR ==> Self::new_pt(paddr).paddr() == paddr & !((PAGE_SIZE
                    - 1) as usize))
                &&& (paddr < MAX_PADDR && paddr % PAGE_SIZE == 0 ==> Self::new_pt(paddr).paddr()
                    == paddr)
                &&& forall|level: PagingLevel| !Self::new_pt(paddr).is_last(level)
            } by {
            let pte = Self::new_pt(paddr);
            let raw = pte.as_usize();
            reveal(<PageTableEntry as PageTableEntryTrait>::new_pt_spec);
            reveal(<PageTableEntry as PageTableEntryTrait>::as_usize_spec);
            assert(pte.0 == ((paddr >> 12) << 10) | Self::VALID_BIT);
            assert(raw == pte.0);
            assert(raw == ((paddr >> 12) << 10) | Self::VALID_BIT);
            assert(pte == PageTableEntry(raw));
            assert(raw & Self::VALID_BIT != 0) by (bit_vector)
                requires
                    raw == ((paddr >> 12) << 10) | Self::VALID_BIT,
            ;
            reveal(<PageTableEntry as PageTableEntryTrait>::is_present_spec);
            assert(pte.is_present() == (raw & Self::VALID_BIT != 0));
            assert(pte.is_present());
            assert(raw & 0xEusize == 0) by (bit_vector)
                requires
                    raw == ((paddr >> 12) << 10) | Self::VALID_BIT,
            ;
            assert forall|level: PagingLevel| !pte.is_last(level) by {
                reveal(<PageTableEntry as PageTableEntryTrait>::is_last_spec);
                assert(pte.is_last(level) == (pte.0 & 0xEusize != 0)) by (compute_only);
                assert(pte.0 == raw);
                assert(pte.is_last(level) == (raw & 0xEusize != 0));
                assert(!pte.is_last(level));
            }
            if paddr < MAX_PADDR {
                lemma_riscv_paddr_encoding_for_current(paddr);
                reveal(<PageTableEntry as PageTableEntryTrait>::paddr_spec);
                assert(pte.paddr() == RiscvPteModel::paddr_from_raw_spec(raw));
                assert(RiscvPteModel::paddr_from_raw_spec(raw)
                    == RiscvPteModel::paddr_from_raw_spec((paddr >> 12) << 10)) by (bit_vector)
                    requires
                        raw == ((paddr >> 12) << 10) | Self::VALID_BIT,
                ;
                assert(pte.paddr() == paddr & !((PAGE_SIZE - 1) as usize));
                if paddr % PAGE_SIZE == 0 {
                    assert(paddr & !((PAGE_SIZE - 1) as usize) == paddr) by (bit_vector)
                        requires
                            PAGE_SIZE == 4096usize,
                            paddr % PAGE_SIZE == 0,
                    ;
                    assert(pte.paddr() == paddr);
                }
            }
        }
    }

    proof fn lemma_paddr_is_page_aligned(self) {
        assert(self.paddr() == RiscvPteModel { raw: self.0 }.paddr_spec()) by (compute_only);
        lemma_riscv_pte_paddr_aligned(self.0);
        assert(PAGE_SIZE == 4096usize) by (compute_only);
        assert(self.paddr() % PAGE_SIZE == 0);
    }
}

#[verifier::bit_vector]
proof fn lemma_riscv_pte_paddr_aligned(raw: usize)
    ensures
        RiscvPteModel::paddr_from_raw_spec(raw) % 4096usize == 0,
{
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

#[cfg(target_arch = "riscv64")]
pub(crate) fn __memcpy_fallible(dst: *mut u8, src: *const u8, size: usize) -> usize {
    // TODO: implement fallible
    unsafe {
        riscv::register::sstatus::set_sum();
    }
    unsafe { core::ptr::copy(src, dst, size) };
    0
}

#[cfg(target_arch = "riscv64")]
pub(crate) fn __memset_fallible(dst: *mut u8, value: u8, size: usize) -> usize {
    // TODO: implement fallible
    unsafe {
        riscv::register::sstatus::set_sum();
    }
    unsafe { core::ptr::write_bytes(dst, value, size) };
    0
}
