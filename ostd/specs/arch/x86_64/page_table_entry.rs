use vstd::prelude::*;
use vstd::raw_ptr::*;

use core::fmt::Debug;

use vstd_extra::prelude::*;

use super::*;
use crate::mm::{
    page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags},
    page_table::*,
    Paddr, PagingLevel,
};
use crate::arch::mm::PageTableFlags;

decl_bms_const!(
    PAGE_FLAG_MAPPING,
    PAGE_FLAG_MAPPING_SPEC,
    u8,
    usize,
    4,
    [
        (PageFlags::R().bits(), PageTableFlags::PRESENT().bits()),
        (PageFlags::W().bits(), PageTableFlags::WRITABLE().bits()),
        (PageFlags::ACCESSED().bits(), PageTableFlags::ACCESSED().bits()),
        (PageFlags::DIRTY().bits(), PageTableFlags::DIRTY().bits())
    ]
);

decl_bms_const!(
    PAGE_PRIV_MAPPING,
    PAGE_PRIV_MAPPING_SPEC,
    u8,
    usize,
    2,
    [
        (PrivilegedPageFlags::USER().bits(), PageTableFlags::USER().bits()),
        (
            PrivilegedPageFlags::GLOBAL().bits(),
            PageTableFlags::GLOBAL().bits()
        )
    ]
);

decl_bms_const!(
    PAGE_INVERTED_FLAG_MAPPING,
    PAGE_INVERTED_FLAG_MAPPING_SPEC,
    u8,
    usize,
    1,
    [(PageFlags::X().bits(), PageTableFlags::NO_EXECUTE().bits())]
);

verus! {

#[repr(transparent)]
#[derive(Copy, Debug, PartialEq)]
pub struct PageTableEntry(pub usize);

global layout PageTableEntry is size == 8, align == 8;

impl crate::specs::mm::pod::Pod for PageTableEntry {}

impl crate::specs::mm::pod::PodOnce for PageTableEntry {}

/// Masks of the physical address.
pub const PHYS_ADDR_MASK: usize = 0xffff_ffff_ffff_f000;

impl Clone for PageTableEntry {
    fn clone(&self) -> Self {
        Self { 0: self.0 }
    }
}

#[allow(non_snake_case)]
impl PageTableEntry {

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn PROP_MASK() -> (res: usize)
    {
        !PHYS_ADDR_MASK & !(PageTableFlags::HUGE().bits())
    }

    #[verifier::inline]
    pub open spec fn prop_assign_spec(self, flags: usize) -> Self {
        Self((self.0 & !Self::PROP_MASK()) | flags as usize)
    }

    #[inline(always)]
    pub fn prop_assign(&mut self, flags: usize)
        ensures final(self).0 == old(self).prop_assign_spec(flags).0
    {
        self.0 = (self.0 & !Self::PROP_MASK()) | flags as usize;
    }

    #[vstd::contrib::auto_spec]
    pub fn encode_cache(cache: CachePolicy) -> (res: usize)
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
            | flags.map_forward(&PAGE_FLAG_MAPPING)
            | flags.map_invert_forward(&PAGE_INVERTED_FLAG_MAPPING)
            | priv_flags.map_forward(&PAGE_PRIV_MAPPING)
            | Self::encode_cache(prop.cache)
    }

    #[verifier::external_body]
    #[verifier::when_used_as_spec(format_flags_spec)]
    pub fn format_flags(prop: PageProperty) -> usize
        returns Self::format_flags_spec(prop)
    {
        let flags: u8 = prop.flags.bits();
        let priv_flags: u8 = prop.priv_flags.bits();
        PageTableFlags::PRESENT().bits()
            | flags.map_forward(&PAGE_FLAG_MAPPING)
            | flags.map_invert_forward(&PAGE_INVERTED_FLAG_MAPPING)
            | priv_flags.map_forward(&PAGE_PRIV_MAPPING)
            | Self::encode_cache(prop.cache)
    }

    #[vstd::contrib::auto_spec]
    pub fn format_cache(flags: usize) -> (res: CachePolicy)
    {
        if flags & PageTableFlags::NO_CACHE().bits() != 0 {
            CachePolicy::Uncacheable
        } else if flags & PageTableFlags::WRITE_THROUGH().bits() != 0 {
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
            flags: PageFlags::from_bits(flags).unwrap(),
            cache,
            priv_flags: PrivilegedPageFlags::from_bits(priv_flags).unwrap(),
        }
    }

    #[verifier::external_body]
    #[verifier::when_used_as_spec(format_property_spec)]
    pub fn format_property(entry: usize) -> PageProperty
        returns Self::format_property_spec(entry)
    {
        let flags = entry.map_backward(&PAGE_FLAG_MAPPING)
                  | entry.map_invert_backward(&PAGE_INVERTED_FLAG_MAPPING);
        let priv_flags: u8 = entry.map_backward(&PAGE_PRIV_MAPPING);
        let cache = Self::format_cache(entry);
        PageProperty {
            flags: PageFlags::from_bits(flags).unwrap(),
            cache,
            priv_flags: PrivilegedPageFlags::from_bits(priv_flags).unwrap(),
        }
    }

    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub fn format_huge_page(level: PagingLevel) -> (res: u64)
    {
        if level == 1 {
            0
        } else {
            PageTableFlags::HUGE().bits() as u64
        }
    }

}

}

verus! {

impl PageTableEntryTrait for PageTableEntry {

    #[verifier::inline]
    open spec fn default_spec() -> Self
    {
        Self { 0: 0 }
    }

    #[inline(always)]
    fn default() -> Self
        returns Self::default_spec()
    {
        Self { 0: 0 }
    }

    #[verifier::inline]
    open spec fn new_absent_spec() -> Self {
        Self::default_spec()
    }

    #[inline(always)]
    #[verifier::external_body]
    fn new_absent() -> (res: Self)
    {
        Self::default()
    }

    #[verifier::inline]
    open spec fn as_usize_spec(self) -> usize {
        self.0 as usize
    }

    #[inline(always)]
    fn as_usize(self) -> usize
        returns self.as_usize_spec()
    {
        self.0 as usize
    }

    #[verifier::inline]
    open spec fn is_present_spec(&self) -> bool {
        self.0 & PageTableFlags::PRESENT().bits() != 0
    }

    #[inline(always)]
    fn is_present(&self) -> bool
        returns self.is_present_spec()
    {
        self.0 & PageTableFlags::PRESENT().bits() != 0
    }

    open spec fn set_prop_spec(&self, prop: PageProperty) -> Self {
        let flags = Self::format_flags(prop);
        self.prop_assign_spec(flags)
    }

    fn set_prop(&mut self, prop: PageProperty)
        ensures *final(self) == old(self).set_prop_spec(prop)
    {
        let flags = Self::format_flags(prop);
        self.prop_assign(flags)
    }

    open spec fn new_page_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        let addr = paddr & PHYS_ADDR_MASK;
        let hp = Self::format_huge_page(level) as usize;
        let flags = Self::format_flags(prop) as usize;
        Self(addr | hp | flags)
    }

    #[verifier::external_body]
    fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> (res: Self)
    {
        let addr = paddr & PHYS_ADDR_MASK;
        let hp = Self::format_huge_page(level) as usize;
        let flags = Self::format_flags(prop) as usize;
        Self(addr | hp | flags)
    }

    open spec fn new_pt_spec(paddr: Paddr) -> Self {
        let addr = paddr & PHYS_ADDR_MASK;
        Self(addr | PageTableFlags::PRESENT().bits() | PageTableFlags::WRITABLE().bits() | PageTableFlags::USER().bits())
    }

    #[verifier::external_body]
    fn new_pt(paddr: Paddr) -> (res: Self)
    {
        let addr = paddr & PHYS_ADDR_MASK;
        Self(addr | PageTableFlags::PRESENT().bits() | PageTableFlags::WRITABLE().bits() | PageTableFlags::USER().bits())
    }

    #[verifier::inline]
    open spec fn paddr_spec(&self) -> Paddr {
        self.0 & PHYS_ADDR_MASK
    }

    #[inline(always)]
    fn paddr(&self) -> Paddr
        returns self.paddr_spec()
    {
        self.0 & PHYS_ADDR_MASK
    }

    #[verifier::inline]
    open spec fn prop_spec(&self) -> PageProperty {
        Self::format_property(self.0)
    }

    #[inline(always)]
    fn prop(&self) -> PageProperty
        returns self.prop_spec()
    {
        Self::format_property(self.0)
    }

    #[verifier::inline]
    open spec fn is_last_spec(&self, level: PagingLevel) -> bool {
        level == 1 || (self.0 & PageTableFlags::HUGE().bits() != 0)
    }

    #[inline(always)]
    fn is_last(&self, level: PagingLevel) -> bool
        returns self.is_last_spec(level)
    {
        level == 1 || (self.0 & PageTableFlags::HUGE().bits() != 0)
    }

    proof fn set_prop_properties(self, prop: PageProperty)
    {
        admit();
    }

    proof fn new_properties()
    {
        admit();
    }

    proof fn axiom_present_paddr_aligned(&self)
    {
        admit();
    }

}

impl PageTableEntry {
    /// Absent (zero) PTE has well-formed paddr for match_pte.
    pub axiom fn absent_pte_paddr_ok()
        ensures
            Self::new_absent_spec().paddr_spec() % crate::specs::arch::mm::PAGE_SIZE == 0,
            Self::new_absent_spec().paddr_spec() < crate::specs::arch::mm::MAX_PADDR;
}

}
