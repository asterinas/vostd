use vstd::prelude::*;
use vstd::raw_ptr::*;
use crate::prelude::*;

use core::fmt::Debug;

use vstd_extra::prelude::*;

use crate::page_prop::PageFlags;
use super::page_table_flags::PageTableFlags;

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
    fn clone(&self) -> Self {
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
            | flags.map_forward(&PAGE_FLAG_MAPPING)
            | flags.map_invert_forward(&PAGE_INVERTED_FLAG_MAPPING)
            | priv_flags.map_forward(&PAGE_PRIV_MAPPING)
            | Self::encode_cache(prop.cache)
    }

    #[verifier::external_body]
    #[verifier::when_used_as_spec(format_flags_spec)]
    pub fn format_flags(prop: PageProperty) -> (res: usize)
        ensures res == Self::format_flags_spec(prop)
    {
        let flags: u8 = prop.flags.value();
        let priv_flags: u8 = prop.priv_flags.value();
        PageTableFlags::PRESENT()
            | flags.map_forward(&PAGE_FLAG_MAPPING)
            | flags.map_invert_forward(&PAGE_INVERTED_FLAG_MAPPING)
            | priv_flags.map_forward(&PAGE_PRIV_MAPPING)
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
        let flags: u8 = entry.map_backward(&PAGE_FLAG_MAPPING)
                      | entry.map_invert_backward(&PAGE_INVERTED_FLAG_MAPPING);
        let priv_flags: u8 = entry.map_backward(&PAGE_PRIV_MAPPING);
        let cache = Self::format_cache(entry);
        PageProperty {
            flags: PageFlags::from_bits(flags),
            cache,
            priv_flags: PrivilegedPageFlags::from_bits(priv_flags),
        }
    }

    #[verifier::external_body]
    #[verifier::when_used_as_spec(format_property_spec)]
    pub fn format_property(entry: usize) -> (res: PageProperty)
        ensures res == Self::format_property_spec(entry)
    {
        let flags = entry.map_backward(&PAGE_FLAG_MAPPING)
                  | entry.map_invert_backward(&PAGE_INVERTED_FLAG_MAPPING);
        let priv_flags: u8 = entry.map_backward(&PAGE_PRIV_MAPPING);
        let cache = Self::format_cache(entry);
        PageProperty {
            flags: PageFlags::from_bits(flags),
            cache,
            priv_flags: PrivilegedPageFlags::from_bits(priv_flags),
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
    fn new_absent() -> (res: Self)
        ensures res == Self::new_absent_spec()
    {
        Self::default()
    }

    #[verifier::inline]
    open spec fn as_value_spec(&self) -> u64 {
        self.0 as u64
    }

    #[inline(always)]
    fn as_value(&self) -> (res: u64)
            ensures res == self.as_value_spec()
    {
        self.0 as u64
    }

    #[verifier::inline]
    open spec fn is_present_spec(&self) -> bool {
        self.0 & PageTableFlags::PRESENT() != 0
    }

    #[inline(always)]
    fn is_present(&self) -> (res: bool)
        ensures res == self.is_present_spec()
    {
        self.0 & PageTableFlags::PRESENT() != 0
    }

    open spec fn set_prop_spec(&self, prop: PageProperty) -> Self {
        let flags = Self::format_flags(prop);
        self.prop_assign_spec(flags)
    }

    fn set_prop(&mut self, prop: PageProperty)
        ensures self == old(self).set_prop_spec(prop)
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

    fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> (res: Self)
        ensures res == Self::new_page_spec(paddr, level, prop)
    {
        let addr = paddr & PHYS_ADDR_MASK();
        let hp = Self::format_huge_page(level) as usize;
        let flags = Self::format_flags(prop) as usize;
        Self(addr | hp | flags)
    }

    open spec fn new_pt_spec(paddr: Paddr) -> Self {
        let addr = paddr & PHYS_ADDR_MASK();
        Self(addr | PageTableFlags::PRESENT() | PageTableFlags::WRITABLE() | PageTableFlags::USER())
    }

    fn new_pt(paddr: Paddr) -> (res: Self)
        ensures res == Self::new_pt_spec(paddr)
    {
        let addr = paddr & PHYS_ADDR_MASK();
        Self(addr | PageTableFlags::PRESENT() | PageTableFlags::WRITABLE() | PageTableFlags::USER())
    }

    #[verifier::inline]
    open spec fn paddr_spec(&self) -> Paddr {
        self.0 & PHYS_ADDR_MASK()
    }

    #[inline(always)]
    fn paddr(&self) -> (res: Paddr)
        ensures res == self.paddr_spec()
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
        level == 1 || (self.0 & PageTableFlags::HUGE() != 0)
    }

    #[inline(always)]
    fn is_last(&self, level: PagingLevel) -> (res: bool)
        ensures res == self.is_last_spec(level)
    {
        level == 1 || (self.0 & PageTableFlags::HUGE() != 0)
    }

}

}
