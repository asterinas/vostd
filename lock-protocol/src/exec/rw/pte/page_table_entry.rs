use core::fmt::Debug;

use vstd::prelude::*;
use vstd::raw_ptr::*;

use vstd_extra::prelude::*;

use super::super::common::*;
use super::page_prop::*;
use super::page_table_flags::PageTableFlags;
use super::page_table_entry_trait::*;

decl_bms_const!(
    PAGE_FLAG_MAPPING,
    PAGE_FLAG_MAPPING_SPEC,
    u8,
    usize,
    4,
    [
        (PageFlags::R().value(), PageTableFlags::PRESENT()),
        (PageFlags::W().value(), PageTableFlags::WRITABLE()),
        (PageFlags::ACCESSED().value(), PageTableFlags::ACCESSED()),
        (PageFlags::DIRTY().value(), PageTableFlags::DIRTY())
    ]
);

decl_bms_const!(
    PAGE_PRIV_MAPPING,
    PAGE_PRIV_MAPPING_SPEC,
    u8,
    usize,
    2,
    [
        (PrivilegedPageFlags::USER().value(), PageTableFlags::USER()),
        (
            PrivilegedPageFlags::GLOBAL().value(),
            PageTableFlags::GLOBAL()
        )
    ]
);

decl_bms_const!(
    PAGE_INVERTED_FLAG_MAPPING,
    PAGE_INVERTED_FLAG_MAPPING_SPEC,
    u8,
    usize,
    1,
    [(PageFlags::X().value(), PageTableFlags::NO_EXECUTE())]
);

verus! {
    /// Parse a bit-flag bits `val` in the representation of `from` to `to` in bits.
macro_rules! parse_flags {
    ($val:expr, $from:expr, $to:expr) => {
        ($val as usize & $from as usize) >> $from.ilog2() << $to.ilog2()
    };
}

pub proof fn lemma_parse_flags_page_table_flags(flag:usize)
    ensures
        parse_flags!(flag, PageTableFlags::WRITABLE(), PageFlags::W().value()) == if flag & PageTableFlags::WRITABLE() == 0 {0} else{ PageFlags::W().value()} <= u8::MAX,
        parse_flags!(flag, PageTableFlags::PRESENT(), PageFlags::R().value()) == if flag & PageTableFlags::PRESENT() == 0 {0} else{ PageFlags::R().value()} <= u8::MAX,
        parse_flags!(flag, PageTableFlags::ACCESSED(), PageFlags::ACCESSED().value()) == if flag & PageTableFlags::ACCESSED() == 0 {0} else{ PageFlags::ACCESSED().value()} <= u8::MAX,
        parse_flags!(!flag, PageTableFlags::NO_EXECUTE(), PageFlags::X().value()) == if !flag & PageTableFlags::NO_EXECUTE() == 0 {0} else{ PageFlags::X().value()} <= u8::MAX,
        parse_flags!(flag, PageTableFlags::DIRTY(), PageFlags::DIRTY().value()) == if flag & PageTableFlags::DIRTY() == 0 {0} else{ PageFlags::DIRTY().value()} <= u8::MAX,
        parse_flags!(flag, PageTableFlags::USER(), PrivilegedPageFlags::USER().value()) == if flag & PageTableFlags::USER() == 0 {0} else{ PrivilegedPageFlags::USER().value()} <= u8::MAX,
        parse_flags!(flag, PageTableFlags::GLOBAL(), PrivilegedPageFlags::GLOBAL().value()) == if flag & PageTableFlags::GLOBAL() == 0 {0} else{ PrivilegedPageFlags::GLOBAL().value()} <= u8::MAX,
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
        parse_flags!(flag, PageFlags::W().value(), PageTableFlags::WRITABLE()) == if flag & PageFlags::W().value() == 0 {0} else{ PageTableFlags::WRITABLE()} <= usize::MAX,
        parse_flags!(flag, PageFlags::R().value(), PageTableFlags::PRESENT()) == if flag & PageFlags::R().value() == 0 {0} else{ PageTableFlags::PRESENT()} <= usize::MAX,
        parse_flags!(flag, PageFlags::ACCESSED().value(), PageTableFlags::ACCESSED()) == if flag & PageFlags::ACCESSED().value() == 0 {0} else{ PageTableFlags::ACCESSED()} <= usize::MAX,
        parse_flags!(!flag, PageFlags::X().value(), PageTableFlags::NO_EXECUTE()) == if !flag & PageFlags::X().value() == 0 {0} else{ PageTableFlags::NO_EXECUTE()} <= usize::MAX,
        parse_flags!(flag, PageFlags::DIRTY().value(), PageTableFlags::DIRTY()) == if flag & PageFlags::DIRTY().value() == 0 {0} else{ PageTableFlags::DIRTY()} <= usize::MAX,
    {
        lemma_parse_flag_present_inverted(flag);
        lemma_parse_flag_writable_inverted(flag);
        lemma_parse_flag_accessed_inverted(flag);
        lemma_parse_flag_no_execute_inverted(!flag);
        lemma_parse_flag_dirty_inverted(flag);
    }

pub proof fn lemma_parse_flags_previleged_page_flags(flag:u8)
    ensures
        parse_flags!(flag, PrivilegedPageFlags::USER().value(), PageTableFlags::USER()) == if flag & PrivilegedPageFlags::USER().value() == 0 {0} else{ PageTableFlags::USER()} <= usize::MAX,
        parse_flags!(flag, PrivilegedPageFlags::GLOBAL().value(), PageTableFlags::GLOBAL()) == if flag & PrivilegedPageFlags::GLOBAL().value() == 0 {0} else{ PageTableFlags::GLOBAL()} <= usize::MAX,
    {
        lemma_parse_flag_user_inverted(flag);
        lemma_parse_flag_global_inverted(flag);
    }

}

verus! {

#[repr(transparent)]
#[derive(Copy, Debug, PartialEq)]
pub struct PageTableEntry(pub usize);

global layout PageTableEntry is size == 8, align == 8;

extern_const!(
/// Masks of the physical address.
pub PHYS_ADDR_MASK
    [PHYS_ADDR_MASK_SPEC, CONST_PHYS_ADDR_MASK]: usize =
    0xffff_ffff_ffff_f000);

impl Clone for PageTableEntry {
    fn clone(&self) -> (res: Self)
        ensures
            res === *self
    {
        Self { 0: self.0 }
    }
}

#[allow(non_snake_case)]
impl PageTableEntry {

    #[verifier::inline]
    pub open spec fn PROP_MASK_spec() -> usize {
        !PHYS_ADDR_MASK() & !(PageTableFlags::HUGE())
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(PROP_MASK_spec)]
    pub const fn PROP_MASK() -> (res: usize)
        ensures res == Self::PROP_MASK_spec()
    {
        !PHYS_ADDR_MASK() & !(PageTableFlags::HUGE())
    }

    #[verifier::inline]
    pub open spec fn prop_assign_spec(&self, flags: usize) -> Self {
        Self((self.0 & !Self::PROP_MASK()) | flags as usize)
    }

    #[inline(always)]
    pub fn prop_assign(&mut self, flags: usize)
        ensures self.0 == old(self).prop_assign_spec(flags).0
    {
        self.0 = (self.0 & !Self::PROP_MASK()) | flags as usize;
    }

    pub open spec fn encode_cache_spec(cache: CachePolicy) -> usize {
        match cache {
            CachePolicy::Uncacheable => PageTableFlags::NO_CACHE(),
            CachePolicy::Writethrough => PageTableFlags::WRITE_THROUGH(),
            _ => 0,
        }
    }

    #[verifier::when_used_as_spec(encode_cache_spec)]
    pub fn encode_cache(cache: CachePolicy) -> (res: usize)
        ensures res == Self::encode_cache_spec(cache)
    {
        match cache {
            CachePolicy::Uncacheable => PageTableFlags::NO_CACHE(),
            CachePolicy::Writethrough => PageTableFlags::WRITE_THROUGH(),
            _ => 0,
        }
    }

    pub open spec fn format_flags_spec(prop: PageProperty) -> usize {
        let flags: u8 = prop.flags.value();
        let priv_flags: u8 = prop.priv_flags.value();
        PageTableFlags::PRESENT()
            | if flags & PageFlags::R().value() == 0 {0} else { PageTableFlags::PRESENT() }
            | if flags & PageFlags::W().value() == 0 {0} else { PageTableFlags::WRITABLE() }
            | if flags & PageFlags::ACCESSED().value() == 0 {0} else { PageTableFlags::ACCESSED() }
            | if flags & PageFlags::DIRTY().value() == 0 {0} else { PageTableFlags::DIRTY() }
            | if !flags & PageFlags::X().value() == 0 {0} else { PageTableFlags::NO_EXECUTE() }
            | if priv_flags & PrivilegedPageFlags::USER().value() == 0 {0} else { PageTableFlags::USER() }
            | if priv_flags & PrivilegedPageFlags::GLOBAL().value() == 0 {0} else { PageTableFlags::GLOBAL() }
            | Self::encode_cache(prop.cache)
    }

    proof fn lemma_format_flags_present(prop: PageProperty)
        ensures
            Self::format_flags(prop) & PageTableFlags::PRESENT() != 0,
    {
        let flags: u8 = prop.flags.value();
        let priv_flags: u8 = prop.priv_flags.value();
        let flag_1 = if flags & PageFlags::R().value() == 0 {0} else { PageTableFlags::PRESENT() };
        let flag_2 = if flags & PageFlags::W().value() == 0 {0} else { PageTableFlags::WRITABLE() };
        let flag_3 = if flags & PageFlags::ACCESSED().value() == 0 {0} else { PageTableFlags::ACCESSED() };
        let flag_4 = if flags & PageFlags::DIRTY().value() == 0 {0} else { PageTableFlags::DIRTY() };
        let flag_5 = if !flags & PageFlags::X().value() == 0 {0} else { PageTableFlags::NO_EXECUTE() };
        let flag_6 = if priv_flags & PrivilegedPageFlags::USER().value() == 0 {0} else { PageTableFlags::USER() };
        let flag_7 = if priv_flags & PrivilegedPageFlags::GLOBAL().value() == 0 {0} else { PageTableFlags::GLOBAL() };
        let flag_8 = Self::encode_cache(prop.cache);
        assert(
            (PageTableFlags::PRESENT() | flag_1 | flag_2 | flag_3 | flag_4 | flag_5 | flag_6 | flag_7 | flag_8) & PageTableFlags::PRESENT() != 0
        ) by (bit_vector);
    }

    #[verifier::external_body]
    #[verifier::when_used_as_spec(format_flags_spec)]
    pub fn format_flags(prop: PageProperty) -> (res: usize)
        ensures res == Self::format_flags_spec(prop)
    {
        let flags: u8 = prop.flags.value();
        let priv_flags: u8 = prop.priv_flags.value();
        proof {
            lemma_parse_flags_page_flags(flags);
            lemma_parse_flags_previleged_page_flags(priv_flags);
        }
        PageTableFlags::PRESENT()
            | parse_flags!(flags, PageFlags::R().value(), PageTableFlags::PRESENT())
            | parse_flags!(flags, PageFlags::W().value(), PageTableFlags::WRITABLE())
            | parse_flags!(flags, PageFlags::ACCESSED().value(), PageTableFlags::ACCESSED())
            | parse_flags!(flags, PageFlags::DIRTY().value(), PageTableFlags::DIRTY())
            | parse_flags!(!flags, PageFlags::X().value(), PageTableFlags::NO_EXECUTE())
            | parse_flags!(priv_flags, PrivilegedPageFlags::USER().value(), PageTableFlags::USER())
            | parse_flags!(priv_flags, PrivilegedPageFlags::GLOBAL().value(), PageTableFlags::GLOBAL())
            | Self::encode_cache(prop.cache)
    }

    pub open spec fn format_cache_spec(flags: usize) -> CachePolicy {
        if flags & PageTableFlags::NO_CACHE() != 0 {
            CachePolicy::Uncacheable
        } else if flags & PageTableFlags::WRITE_THROUGH() != 0 {
            CachePolicy::Writethrough
        } else {
            CachePolicy::Writeback
        }
    }

    #[verifier::when_used_as_spec(format_cache_spec)]
    pub fn format_cache(flags: usize) -> (res: CachePolicy)
        ensures res == Self::format_cache_spec(flags)
    {
        if flags & PageTableFlags::NO_CACHE() != 0 {
            CachePolicy::Uncacheable
        } else if flags & PageTableFlags::WRITE_THROUGH() != 0 {
            CachePolicy::Writethrough
        } else {
            CachePolicy::Writeback
        }
    }

    pub open spec fn format_property_spec(entry: usize) -> PageProperty {
        let flags: u8 =
            if entry & PageTableFlags::PRESENT() == 0 {0} else { PageFlags::R().value() } |
            if entry & PageTableFlags::WRITABLE() == 0 {0} else { PageFlags::W().value() } |
            if entry & PageTableFlags::ACCESSED() == 0 {0} else { PageFlags::ACCESSED().value() } |
            if entry & PageTableFlags::DIRTY() == 0 {0} else { PageFlags::DIRTY().value() } |
            if !entry & PageTableFlags::NO_EXECUTE() == 0 {0} else { PageFlags::X().value() };
        let priv_flags: u8 =
            if entry & PageTableFlags::USER() == 0 {0} else { PrivilegedPageFlags::USER().value() } |
            if entry & PageTableFlags::GLOBAL() == 0 {0} else { PrivilegedPageFlags::GLOBAL().value() };
        let cache = Self::format_cache(entry);
        PageProperty {
            flags: PageFlags::from_bits(flags as u8),
            cache,
            priv_flags: PrivilegedPageFlags::from_bits(priv_flags),
        }
    }

    #[verifier::external_body]
    #[verifier::when_used_as_spec(format_property_spec)]
    pub fn format_property(entry: usize) -> (res: PageProperty)
        ensures res == Self::format_property_spec(entry)
    {
        proof{
            lemma_parse_flags_page_table_flags(entry);
        }
        let flags =
            parse_flags!(entry, PageTableFlags::PRESENT(), PageFlags::R().value()) |
            parse_flags!(entry, PageTableFlags::WRITABLE(), PageFlags::W().value()) |
            parse_flags!(entry, PageTableFlags::ACCESSED(), PageFlags::ACCESSED().value()) |
            parse_flags!(entry, PageTableFlags::DIRTY(), PageFlags::DIRTY().value()) |
            parse_flags!(!entry, PageTableFlags::NO_EXECUTE(), PageFlags::X().value());
        let priv_flags  =
            parse_flags!(entry, PageTableFlags::USER(), PrivilegedPageFlags::USER().value()) |
            parse_flags!(entry, PageTableFlags::GLOBAL(), PrivilegedPageFlags::GLOBAL().value());
        let cache = Self::format_cache(entry);
        PageProperty {
            flags: PageFlags::from_bits(flags as u8),
            cache,
            priv_flags: PrivilegedPageFlags::from_bits(priv_flags as u8),
        }
    }

    #[verifier::inline]
    pub open spec fn format_huge_page_spec(level: PagingLevel) -> u64 {
        if level == 1 {
            0
        } else {
            PageTableFlags::HUGE() as u64
        }
    }

    #[inline(always)]
    #[verifier::when_used_as_spec(format_huge_page_spec)]
    pub fn format_huge_page(level: PagingLevel) -> (res: u64)
        ensures res == Self::format_huge_page_spec(level)
    {
        if level == 1 {
            0
        } else {
            PageTableFlags::HUGE() as u64
        }
    }

}

}

verus! {

impl PageTableEntryTrait for PageTableEntry {

    #[verifier::inline]
    open spec fn default_spec() -> Self {
        Self(0)
    }

    #[inline(always)]
    fn default() -> (res: Self)
        ensures res == Self::default_spec()
    {
        Self(0)
    }

    #[verifier::inline]
    open spec fn new_absent_spec() -> Self {
        Self::default()
    }

    #[inline(always)]
    fn new_absent() -> Self
    {
        assert(0 & PageTableFlags::PRESENT() == 0) by (bit_vector);
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
        self.0 & PageTableFlags::PRESENT() != 0
    }

    #[inline(always)]
    fn is_present(&self) -> bool
    {
        self.0 & PageTableFlags::PRESENT() != 0
    }

    open spec fn set_prop_spec(&self, prop: PageProperty) -> Self {
        let flags = Self::format_flags(prop);
        self.prop_assign_spec(flags)
    }

    fn set_prop(&mut self, prop: PageProperty)
    {
        let flags = Self::format_flags(prop);
        self.prop_assign(flags)
    }

    open spec fn new_page_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        let addr = paddr & PHYS_ADDR_MASK();
        let hp = Self::format_huge_page(level) as usize;
        let flags = Self::format_flags(prop) as usize;
        Self(addr | hp | flags)
    }

    #[verifier::external_body] // TODO
    fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        let addr = paddr & PHYS_ADDR_MASK();
        let hp = Self::format_huge_page(level) as usize;
        let flags = Self::format_flags(prop) as usize;

        proof{
            Self::lemma_page_table_entry_properties();
            assert(flags & PageTableFlags::PRESENT() != 0) by {
            Self::lemma_format_flags_present(prop);}
            assert((addr | hp | flags) & PageTableFlags::PRESENT() != 0) by (bit_vector) requires
                flags & PageTableFlags::PRESENT() != 0;
            assert(Self(addr | hp | flags).is_last(level));
        }

        Self(addr | hp | flags)
    }

    open spec fn new_pt_spec(paddr: Paddr) -> Self {
        let addr = paddr & PHYS_ADDR_MASK();
        Self(addr | PageTableFlags::PRESENT() | PageTableFlags::WRITABLE() | PageTableFlags::USER())
    }

    #[verifier::external_body] // TODO
    fn new_pt(paddr: Paddr) -> Self {
        let addr = paddr & PHYS_ADDR_MASK();
        proof{
            let bit = addr | PageTableFlags::PRESENT() | PageTableFlags::WRITABLE() | PageTableFlags::USER();
            assert(bit & PageTableFlags::PRESENT() != 0) by (bit_vector);
        }
        Self(addr | PageTableFlags::PRESENT() | PageTableFlags::WRITABLE() | PageTableFlags::USER())
    }

    #[verifier::inline]
    open spec fn paddr_spec(&self) -> Paddr {
        self.0 & PHYS_ADDR_MASK()
    }

    #[inline(always)]
    fn paddr(&self) -> Paddr
    {
        self.0 & PHYS_ADDR_MASK()
    }

    #[verifier::inline]
    open spec fn prop_spec(&self) -> PageProperty {
        Self::format_property(self.0)
    }

    #[inline(always)]
    fn prop(&self) -> (res: PageProperty)
        ensures res == self.prop_spec()
    {
        Self::format_property(self.0)
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

}

macro_rules! declare_parse_flag_const {
    ($name:ident, $from_expr:expr, $from_mask:expr, $from_bit:expr, $from_ty: ty, $to_expr:expr, $to_mask:expr, $to_bit:expr, $to_ty: ty) => {
        verus!{
        proof fn $name(flag: $from_ty)
            ensures
                0 <= parse_flags!(flag, $from_expr, $to_expr) ==
                    if flag & $from_expr == 0 { 0 } else { $to_expr } <= $to_ty::MAX,
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

declare_parse_flag_const!(
    lemma_parse_flag_present,
    PageTableFlags::PRESENT(),
    0b00000001,
    0,
    usize,
    PageFlags::R().value(),
    0b00000001,
    0,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_present_inverted,
    PageFlags::R().value(),
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
    PageFlags::W().value(),
    0b00000010,
    1,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_writable_inverted,
    PageFlags::W().value(),
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
    PageFlags::ACCESSED().value(),
    0b00001000,
    3,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_accessed_inverted,
    PageFlags::ACCESSED().value(),
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
    PageFlags::DIRTY().value(),
    0b00010000,
    4,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_dirty_inverted,
    PageFlags::DIRTY().value(),
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
    PrivilegedPageFlags::USER().value(),
    0b00000001,
    0,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_user_inverted,
    PrivilegedPageFlags::USER().value(),
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
    PrivilegedPageFlags::GLOBAL().value(),
    0b00000010,
    1,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_global_inverted,
    PrivilegedPageFlags::GLOBAL().value(),
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
    PageFlags::X().value(),
    0b00000100,
    2,
    u8
);

declare_parse_flag_const!(
    lemma_parse_flag_no_execute_inverted,
    PageFlags::X().value(),
    0b00000100,
    2,
    u8,
    PageTableFlags::NO_EXECUTE(),
    1usize << 63,
    63,
    usize
);