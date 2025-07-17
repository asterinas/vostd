use core::fmt::Debug;

use vstd::prelude::*;
use vstd::raw_ptr::*;

use vstd_extra::prelude::*;

use super::super::common::*;
use super::page_prop::*;
use super::page_table_flags::PageTableFlags;
use super::page_table_entry_trait::*;

verus! {

#[repr(transparent)]
#[derive(Copy, Debug, PartialEq)]
pub struct PageTableEntry(pub usize);

global layout PageTableEntry is size == 8, align == 8;

impl Clone for PageTableEntry {
    fn clone(&self) -> (res: Self)
        ensures
            res === *self
    {
        Self { 0: self.0 }
    }
}

impl PageTableEntry {
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn PHYS_ADDR_MASK() -> usize
        returns 0xF_FFFF_FFFF_F000 as usize
    {
        0xF_FFFF_FFFF_F000
    }
}

/// Parse a bit-flag bits `val` in the representation of `from` to `to` in bits.
macro_rules! parse_flags {
    ($val:expr, $from:expr, $to:expr) => {
        ($val as usize & $from.bits() as usize) >> $from.bits().ilog2() << $to.bits().ilog2()
    };
}

impl PageTableEntryTrait for PageTableEntry {

    #[verifier::inline]
    open spec fn default_spec() -> Self {
        Self(0)
    }

    #[inline(always)]
    fn default() -> Self
    {
        Self(0)
    }

    open spec fn new_page_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        let addr = paddr & Self::PHYS_ADDR_MASK();
        let hp = Self::format_huge_page(level) as usize;
        let flags = Self::format_flags(prop) as usize;
        Self(addr | hp | flags)
    }

    fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        let addr = paddr & Self::PHYS_ADDR_MASK();
        let hp = Self::format_huge_page(level) as usize;
        let flags = Self::format_flags(prop) as usize;

        proof{
            Self::lemma_page_table_entry_properties();
            Self::lemma_format_flags_properties(prop);
            Self::lemma_format_huge_page_properties(level);
            let present_mask = PageTableFlags::PRESENT().bits();
            assert((addr | hp | flags) & present_mask != 0) by (bit_vector) requires
                flags & present_mask != 0;
            assert(Self(addr | hp | flags).is_last(level));
            assert((addr | hp | flags) & 0xF_FFFF_FFFF_F000 == addr) by (bit_vector) requires
                hp & 0xF_FFFF_FFFF_F000 == 0,
                flags & 0xF_FFFF_FFFF_F000 == 0,
                addr == paddr & 0xF_FFFF_FFFF_F000
                ;
        }

        Self(addr | hp | flags)
    }

    open spec fn new_pt_spec(paddr: Paddr) -> Self {
        let flags = PageTableFlags::PRESENT().bits()
            | PageTableFlags::WRITABLE().bits()
            | PageTableFlags::USER().bits();
        Self(paddr & Self::PHYS_ADDR_MASK() | flags)
    }


    fn new_pt(paddr: Paddr) -> Self
    {
        let flags = PageTableFlags::PRESENT().bits() | PageTableFlags::WRITABLE().bits() | PageTableFlags::USER().bits();
        proof{
            assert((0b1usize| 0b10 | 0b100) & 0xF_FFFF_FFFF_F000 == 0) by (bit_vector);
            assert((0b1usize | 0b10 | 0b100) & 0b1 != 0) by (bit_vector)
                requires flags & 0xF_FFFF_FFFF_F000 == 0;
            assert((paddr & 0xF_FFFF_FFFF_F000 | flags) & 0xF_FFFF_FFFF_F000 == paddr & 0xF_FFFF_FFFF_F000) by (bit_vector)
                requires flags & 0xF_FFFF_FFFF_F000 == 0;
            assert((paddr & 0xF_FFFF_FFFF_F000 | flags) & 0b1 != 0) by (bit_vector)
                requires flags & 0b1 != 0;
        }
        Self(paddr & Self::PHYS_ADDR_MASK() | flags)
    }

    #[verifier::inline]
    open spec fn new_absent_spec() -> Self {
        Self::default()
    }

    #[inline(always)]
    fn new_absent() -> Self
    {
        proof{
            let bit = PageTableFlags::PRESENT().bits();
            assert(0 & bit == 0) by (bit_vector);
        }
        Self::default()
    }

    #[verifier::inline]
    open spec fn as_value_spec(&self) -> u64 {
        self.0 as u64
    }

    #[inline(always)]
    fn as_value(&self) -> u64
    {
        self.0 as u64
    }

    #[verifier::inline]
    open spec fn is_present_spec(&self) -> bool {
        self.0 & PageTableFlags::PRESENT().bits() != 0
    }

    #[inline(always)]
    fn is_present(&self) -> bool
    {
        self.0 & PageTableFlags::PRESENT().bits() != 0
    }

    open spec fn set_prop_spec(&self, prop: PageProperty) -> Self {
        let flags = Self::format_flags(prop);
        Self((self.0 & !Self::PROP_MASK()) | flags)
    }

    fn set_prop(&mut self, prop: PageProperty)
    {
        let flags = Self::format_flags(prop);
        self.0 = self.0 & !Self::PROP_MASK() | flags;
    }

    #[verifier::inline]
    open spec fn paddr_spec(&self) -> Paddr {
        self.0 & Self::PHYS_ADDR_MASK()
    }

    #[inline(always)]
    fn paddr(&self) -> Paddr
    {
        self.0 & Self::PHYS_ADDR_MASK()
    }

    #[verifier::inline]
    open spec fn prop_spec(&self) -> PageProperty {
        let flags: u8 =
            if self.0 & PageTableFlags::PRESENT().bits() == 0 {0} else { PageFlags::R().bits() } |
            if self.0 & PageTableFlags::WRITABLE().bits() == 0 {0} else { PageFlags::W().bits() } |
            if !self.0 & PageTableFlags::NO_EXECUTE().bits() == 0 {0} else { PageFlags::X().bits() } |
            if self.0 & PageTableFlags::ACCESSED().bits() == 0 {0} else { PageFlags::ACCESSED().bits() } |
            if self.0 & PageTableFlags::DIRTY().bits() == 0 {0} else { PageFlags::DIRTY().bits() };
        let priv_flags: u8 =
            if self.0 & PageTableFlags::USER().bits() == 0 {0} else { PrivilegedPageFlags::USER().bits() } |
            if self.0 & PageTableFlags::GLOBAL().bits() == 0 {0} else { PrivilegedPageFlags::GLOBAL().bits() };
        let cache = if self.0 & PageTableFlags::NO_CACHE().bits() != 0 {
            CachePolicy::Uncacheable
        } else if self.0 & PageTableFlags::WRITE_THROUGH().bits() != 0 {
            CachePolicy::Writethrough
        } else {
            CachePolicy::Writeback
        };
        PageProperty {
            flags: PageFlags::from_bits(flags as u8),
            cache,
            priv_flags: PrivilegedPageFlags::from_bits(priv_flags),
        }
    }

    #[inline(always)]
    fn prop(&self) -> PageProperty
    {
        proof{
            lemma_parse_flags_page_table_flags(self.0);
            PageFlags::lemma_consts_properties();
            PrivilegedPageFlags::lemma_consts_properties();
            PageTableFlags::lemma_consts_properties();
        }
        let flags =
            parse_flags!(self.0, PageTableFlags::PRESENT(), PageFlags::R()) |
            parse_flags!(self.0, PageTableFlags::WRITABLE(), PageFlags::W()) |
            parse_flags!(!self.0, PageTableFlags::NO_EXECUTE(), PageFlags::X()) |
            parse_flags!(self.0, PageTableFlags::ACCESSED(), PageFlags::ACCESSED()) |
            parse_flags!(self.0, PageTableFlags::DIRTY(), PageFlags::DIRTY());
        let priv_flags =
            parse_flags!(self.0, PageTableFlags::USER(), PrivilegedPageFlags::USER()) |
            parse_flags!(self.0, PageTableFlags::GLOBAL(), PrivilegedPageFlags::GLOBAL());
        let cache = if self.0 & PageTableFlags::NO_CACHE().bits() != 0 {
            CachePolicy::Uncacheable
        } else if self.0 & PageTableFlags::WRITE_THROUGH().bits() != 0 {
            CachePolicy::Writethrough
        } else {
            CachePolicy::Writeback
        };
        PageProperty {
            flags: PageFlags::from_bits(flags as u8),
            cache,
            priv_flags: PrivilegedPageFlags::from_bits(priv_flags as u8),
        }
    }

    #[verifier::inline]
    open spec fn is_last_spec(&self, level: PagingLevel) -> bool {
        // level == 1 || (self.0 & PageTableFlags::HUGE() != 0)
        level == 1
    }

    #[inline(always)]
    fn is_last(&self, level: PagingLevel) -> bool
    {
        // level == 1 || (self.0 & PageTableFlags::HUGE() != 0)
        level == 1
    }

    #[verifier::external_body]
    proof fn lemma_page_table_entry_properties()
    {
    }

}

#[allow(non_snake_case)]
impl PageTableEntry {
    #[inline(always)]
    #[verifier::allow_in_spec]
    pub const fn PROP_MASK() -> usize
        returns  !Self::PHYS_ADDR_MASK() & !(PageTableFlags::HUGE().bits())
    {
        !Self::PHYS_ADDR_MASK() & !(PageTableFlags::HUGE().bits())
    }

    pub open spec fn encode_cache_spec(cache: CachePolicy) -> usize {
        match cache {
            CachePolicy::Uncacheable => PageTableFlags::NO_CACHE().bits(),
            CachePolicy::Writethrough => PageTableFlags::WRITE_THROUGH().bits(),
            _ => 0,
        }
    }

    #[verifier::when_used_as_spec(encode_cache_spec)]
    pub fn encode_cache(cache: CachePolicy) -> usize
        returns Self::encode_cache_spec(cache)
    {
        match cache {
            CachePolicy::Uncacheable => PageTableFlags::NO_CACHE().bits(),
            CachePolicy::Writethrough => PageTableFlags::WRITE_THROUGH().bits(),
            _ => 0,
        }
    }

    pub open spec fn format_flags_spec(prop: PageProperty) -> usize {
        let flags: u8 = prop.flags.bits();
        let priv_flags: u8 = prop.priv_flags.bits();
        PageTableFlags::PRESENT().bits()
            | if flags & PageFlags::R().bits() == 0 {0} else { PageTableFlags::PRESENT().bits() }
            | if flags & PageFlags::W().bits() == 0 {0} else { PageTableFlags::WRITABLE().bits() }
            | if flags & PageFlags::ACCESSED().bits() == 0 {0} else { PageTableFlags::ACCESSED().bits() }
            | if flags & PageFlags::DIRTY().bits() == 0 {0} else { PageTableFlags::DIRTY().bits() }
            | if !flags & PageFlags::X().bits() == 0 {0} else { PageTableFlags::NO_EXECUTE().bits() }
            | if priv_flags & PrivilegedPageFlags::USER().bits() == 0 {0} else { PageTableFlags::USER().bits() }
            | if priv_flags & PrivilegedPageFlags::GLOBAL().bits() == 0 {0} else { PageTableFlags::GLOBAL().bits() }
            | Self::encode_cache(prop.cache)
    }

    #[verifier::when_used_as_spec(format_flags_spec)]
    pub fn format_flags(prop: PageProperty) -> (res: usize)
        returns Self::format_flags_spec(prop)
    {
        let flags: u8 = prop.flags.bits();
        let priv_flags: u8 = prop.priv_flags.bits();
        proof {
            lemma_parse_flags_page_flags(flags);
            lemma_parse_flags_previleged_page_flags(priv_flags);
            PageFlags::lemma_consts_properties();
            PrivilegedPageFlags::lemma_consts_properties();
            PageTableFlags::lemma_consts_properties();
        }
        PageTableFlags::PRESENT().bits()
            | parse_flags!(flags, PageFlags::R(), PageTableFlags::PRESENT())
            | parse_flags!(flags, PageFlags::W(), PageTableFlags::WRITABLE())
            | parse_flags!(flags, PageFlags::ACCESSED(), PageTableFlags::ACCESSED())
            | parse_flags!(flags, PageFlags::DIRTY(), PageTableFlags::DIRTY())
            | parse_flags!(!flags, PageFlags::X(), PageTableFlags::NO_EXECUTE())
            | parse_flags!(priv_flags, PrivilegedPageFlags::USER(), PageTableFlags::USER())
            | parse_flags!(priv_flags, PrivilegedPageFlags::GLOBAL(), PageTableFlags::GLOBAL())
            | Self::encode_cache(prop.cache)
    }

    proof fn lemma_format_flags_properties(prop: PageProperty)
        ensures
            Self::format_flags(prop) & PageTableFlags::PRESENT().bits() != 0,
            Self::format_flags(prop) & Self::PHYS_ADDR_MASK() == 0,
    {
        let flags: u8 = prop.flags.bits();
        let priv_flags: u8 = prop.priv_flags.bits();
        let flag_1 = if flags & 0b1 == 0 {0} else { 0b1 };
        let flag_2 = if flags & 0b10 == 0 {0} else { 0b10 };
        let flag_3 = if flags & 0b1000 == 0 {0} else { 0b100000 };
        let flag_4 = if flags & 0b10000 == 0 {0} else { 0b1000000 };
        let flag_5 = if !flags & 0b100 == 0 {0} else { 1usize << 63 };
        let flag_6 = if priv_flags & 0b1 == 0 {0} else { 0b100 };
        let flag_7 = if priv_flags & 0b10 == 0 {0} else { 0b1_00000000 };
        let flag_8 = Self::encode_cache(prop.cache);
        let present_mask = PageTableFlags::PRESENT().bits();
        assert(
            (present_mask | flag_1 | flag_2 | flag_3 | flag_4 | flag_5 | flag_6 | flag_7 | flag_8) & present_mask != 0
        ) by (bit_vector) requires
            present_mask == 0b1;
        assert((present_mask | flag_1 | flag_2 | flag_3 | flag_4 | flag_5 | flag_6 | flag_7 | flag_8) & 0xF_FFFF_FFFF_F000 == 0) by (bit_vector)
            requires
                present_mask == 0b1,
                flag_1 == 0 || flag_1 == 0b1,
                flag_2 == 0 || flag_2 == 0b10,
                flag_3 == 0 || flag_3 == 0b100000,
                flag_4 == 0 || flag_4 == 0b1000000,
                flag_5 == 0 || flag_5 == 1usize << 63,
                flag_6 == 0 || flag_6 == 0b100,
                flag_7 == 0 || flag_7 == 0b1_00000000,
                flag_8 == 0 || flag_8 == 0b10000 || flag_8 == 0b1000;
    }

    #[verifier::inline]
    pub open spec fn format_huge_page_spec(level: PagingLevel) -> u64 {
        if level == 1 {
            0
        } else {
            PageTableFlags::HUGE().bits() as u64
        }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(format_huge_page_spec)]
    pub fn format_huge_page(level: PagingLevel) -> u64
        returns Self::format_huge_page_spec(level)
    {
        if level == 1 {
            0
        } else {
            PageTableFlags::HUGE().bits() as u64
        }
    }

    pub proof fn lemma_format_huge_page_properties(level: PagingLevel)
        ensures
            Self::format_huge_page(level) as usize & Self::PHYS_ADDR_MASK() == 0,
    {
        let flag = Self::format_huge_page(level);
        assert(flag & 0xF_FFFF_FFFF_F000 == 0) by (bit_vector)
            requires
                flag == 0 || flag == 0b10000000 as u64;
    }

}

}

macro_rules! declare_parse_flag_const {
    ($name:ident, $from_expr:expr, $from_mask:expr, $from_bit:expr, $from_ty: ty, $to_expr:expr, $to_mask:expr, $to_bit:expr, $to_ty: ty) => {
        verus!{
        proof fn $name(flag: $from_ty)
            ensures
                0 <= parse_flags!(flag, $from_expr, $to_expr) ==
                    if flag & $from_expr.bits() == 0 { 0 } else { $to_expr.bits() } <= $to_ty::MAX,
        {
            PageTableFlags::lemma_consts_properties();
            PageFlags::lemma_consts_properties();
            PrivilegedPageFlags::lemma_consts_properties();

            if flag & $from_mask != 0 {
                assert(flag & $from_mask == $from_mask) by (bit_vector)
                    requires flag & $from_mask != 0;
                assert(($from_mask as usize >> $from_bit << $to_bit) == $to_mask) by (bit_vector);
            }

            if flag & $from_mask == 0 {
                assert(0usize >> $from_bit << $to_bit == 0) by (bit_vector);
            }
        }
    }
    };
}

verus! {

pub proof fn lemma_parse_flags_page_table_flags(flag:usize)
    ensures
        parse_flags!(flag, PageTableFlags::WRITABLE(), PageFlags::W()) == if flag & PageTableFlags::WRITABLE().bits() == 0 {0} else{ PageFlags::W().bits()} <= u8::MAX,
        parse_flags!(flag, PageTableFlags::PRESENT(), PageFlags::R()) == if flag & PageTableFlags::PRESENT().bits() == 0 {0} else{ PageFlags::R().bits()} <= u8::MAX,
        parse_flags!(flag, PageTableFlags::ACCESSED(), PageFlags::ACCESSED()) == if flag & PageTableFlags::ACCESSED().bits() == 0 {0} else{ PageFlags::ACCESSED().bits()} <= u8::MAX,
        parse_flags!(!flag, PageTableFlags::NO_EXECUTE(), PageFlags::X()) == if !flag & PageTableFlags::NO_EXECUTE().bits() == 0 {0} else{ PageFlags::X().bits()} <= u8::MAX,
        parse_flags!(flag, PageTableFlags::DIRTY(), PageFlags::DIRTY()) == if flag & PageTableFlags::DIRTY().bits() == 0 {0} else{ PageFlags::DIRTY().bits()} <= u8::MAX,
        parse_flags!(flag, PageTableFlags::USER(), PrivilegedPageFlags::USER()) == if flag & PageTableFlags::USER().bits() == 0 {0} else{ PrivilegedPageFlags::USER().bits()} <= u8::MAX,
        parse_flags!(flag, PageTableFlags::GLOBAL(), PrivilegedPageFlags::GLOBAL()) == if flag & PageTableFlags::GLOBAL().bits() == 0 {0} else{ PrivilegedPageFlags::GLOBAL().bits()} <= u8::MAX,
    {
        lemma_parse_flag_present(flag);
        lemma_parse_flag_writable(flag);
        lemma_parse_flag_accessed(flag);
        lemma_parse_flag_no_execute(!flag);
        lemma_parse_flag_dirty(flag);
        lemma_parse_flag_user(flag);
        lemma_parse_flag_global(flag);
    }

pub proof fn lemma_parse_flags_page_flags(flag:u8)
    ensures
        parse_flags!(flag, PageFlags::W(), PageTableFlags::WRITABLE()) == if flag & PageFlags::W().bits() == 0 {0} else{ PageTableFlags::WRITABLE().bits()} <= usize::MAX,
        parse_flags!(flag, PageFlags::R(), PageTableFlags::PRESENT()) == if flag & PageFlags::R().bits() == 0 {0} else{ PageTableFlags::PRESENT().bits()} <= usize::MAX,
        parse_flags!(flag, PageFlags::ACCESSED(), PageTableFlags::ACCESSED()) == if flag & PageFlags::ACCESSED().bits() == 0 {0} else{ PageTableFlags::ACCESSED().bits()} <= usize::MAX,
        parse_flags!(!flag, PageFlags::X(), PageTableFlags::NO_EXECUTE()) == if !flag & PageFlags::X().bits() == 0 {0} else{ PageTableFlags::NO_EXECUTE().bits()} <= usize::MAX,
        parse_flags!(flag, PageFlags::DIRTY(), PageTableFlags::DIRTY()) == if flag & PageFlags::DIRTY().bits() == 0 {0} else{ PageTableFlags::DIRTY().bits()} <= usize::MAX,
    {
        lemma_parse_flag_present_inverted(flag);
        lemma_parse_flag_writable_inverted(flag);
        lemma_parse_flag_accessed_inverted(flag);
        lemma_parse_flag_no_execute_inverted(!flag);
        lemma_parse_flag_dirty_inverted(flag);
    }

pub proof fn lemma_parse_flags_previleged_page_flags(flag:u8)
    ensures
        parse_flags!(flag, PrivilegedPageFlags::USER(), PageTableFlags::USER()) == if flag & PrivilegedPageFlags::USER().bits() == 0 {0} else{ PageTableFlags::USER().bits()} <= usize::MAX,
        parse_flags!(flag, PrivilegedPageFlags::GLOBAL(), PageTableFlags::GLOBAL()) == if flag & PrivilegedPageFlags::GLOBAL().bits() == 0 {0} else{ PageTableFlags::GLOBAL().bits()} <= usize::MAX,
    {
        lemma_parse_flag_user_inverted(flag);
        lemma_parse_flag_global_inverted(flag);
    }

}

declare_parse_flag_const!(
    lemma_parse_flag_present,
    PageTableFlags::PRESENT(),
    0b00000001,
    0,
    usize,
    PageFlags::R(),
    0b00000001,
    0,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_present_inverted,
    PageFlags::R(),
    0b00000001,
    0,
    u8,
    PageTableFlags::PRESENT(),
    0b00000001,
    0,
    usize
);

declare_parse_flag_const!(
    lemma_parse_flag_writable,
    PageTableFlags::WRITABLE(),
    0b00000010,
    1,
    usize,
    PageFlags::W(),
    0b00000010,
    1,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_writable_inverted,
    PageFlags::W(),
    0b00000010,
    1,
    u8,
    PageTableFlags::WRITABLE(),
    0b00000010,
    1,
    usize
);

declare_parse_flag_const!(
    lemma_parse_flag_accessed,
    PageTableFlags::ACCESSED(),
    0b00100000,
    5,
    usize,
    PageFlags::ACCESSED(),
    0b00001000,
    3,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_accessed_inverted,
    PageFlags::ACCESSED(),
    0b00001000,
    3,
    u8,
    PageTableFlags::ACCESSED(),
    0b00100000,
    5,
    usize
);

declare_parse_flag_const!(
    lemma_parse_flag_dirty,
    PageTableFlags::DIRTY(),
    0b01000000,
    6,
    usize,
    PageFlags::DIRTY(),
    0b00010000,
    4,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_dirty_inverted,
    PageFlags::DIRTY(),
    0b00010000,
    4,
    u8,
    PageTableFlags::DIRTY(),
    0b01000000,
    6,
    usize
);

declare_parse_flag_const!(
    lemma_parse_flag_user,
    PageTableFlags::USER(),
    0b00000100,
    2,
    usize,
    PrivilegedPageFlags::USER(),
    0b00000001,
    0,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_user_inverted,
    PrivilegedPageFlags::USER(),
    0b00000001,
    0,
    u8,
    PageTableFlags::USER(),
    0b00000100,
    2,
    usize
);

declare_parse_flag_const!(
    lemma_parse_flag_global,
    PageTableFlags::GLOBAL(),
    0b00000001_00000000,
    8,
    usize,
    PrivilegedPageFlags::GLOBAL(),
    0b00000010,
    1,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_global_inverted,
    PrivilegedPageFlags::GLOBAL(),
    0b00000010,
    1,
    u8,
    PageTableFlags::GLOBAL(),
    0b00000001_00000000,
    8,
    usize
);

declare_parse_flag_const!(
    lemma_parse_flag_no_execute,
    PageTableFlags::NO_EXECUTE(),
    1usize << 63,
    63,
    usize,
    PageFlags::X(),
    0b00000100,
    2,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_no_execute_inverted,
    PageFlags::X(),
    0b00000100,
    2,
    u8,
    PageTableFlags::NO_EXECUTE(),
    1usize << 63,
    63,
    usize
);
