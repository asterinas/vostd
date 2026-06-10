// SPDX-License-Identifier: MPL-2.0
#![expect(dead_code)]

use crate::specs::arch::{MAX_PADDR, NR_ENTRIES, NR_LEVELS};
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd_extra::panic::may_panic;
use vstd_extra::panic::panic_diverge;
use vstd_extra::prelude::*;

use alloc::fmt;
use core::ops::Range;

//use cfg_if::cfg_if;
pub(crate) use util::{__memcpy_fallible, __memset_fallible};
//use x86_64::{instructions::tlb, structures::paging::PhysFrame, VirtAddr};

use crate::specs::arch::PAGE_SIZE;
use crate::{
    mm::{
        page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags as PrivFlags},
        page_table::{PageTableEntryTrait, PageTableFrag},
        Paddr, PagingConstsTrait, PagingLevel, PodOnce, Vaddr,
    },
    Pod,
};

mod util;

verus! {
#[derive(Clone,Debug, Default)]
pub struct PagingConsts {}

impl PagingConstsTrait for PagingConsts {
    // Expansion for BASE_PAGE_SIZE
    #[verifier::inline]
    open spec fn BASE_PAGE_SIZE_spec() -> usize {
        4096
    }

    proof fn lemma_BASE_PAGE_SIZE_properties()
        ensures
            0 < Self::BASE_PAGE_SIZE_spec(),
            is_pow2(Self::BASE_PAGE_SIZE_spec() as int),
    {
        lemma_pow2_is_pow2_to64();
    }

    #[inline(always)]
    fn BASE_PAGE_SIZE() -> (res: usize)
        ensures
            res == Self::BASE_PAGE_SIZE_spec(),
    {
        proof {
            Self::lemma_BASE_PAGE_SIZE_properties();
        }
        4096
    }

    // Expansion for NR_LEVELS
    #[verifier::inline]
    open spec fn NR_LEVELS_spec() -> PagingLevel {
        4
    }

    #[inline(always)]
    fn NR_LEVELS() -> (res: PagingLevel)
        ensures
            res == Self::NR_LEVELS_spec(),
    {
        4
    }

    proof fn lemma_NR_LEVELS_eq()
        ensures
            Self::NR_LEVELS_spec() as int == NR_LEVELS as int,
    {
        // Both sides are concretely 4 for x86_64.
    }

    // Expansion for ADDRESS_WIDTH
    #[verifier::inline]
    open spec fn ADDRESS_WIDTH_spec() -> usize {
        48
    }

    #[inline(always)]
    fn ADDRESS_WIDTH() -> (res: usize)
        ensures
            res == Self::ADDRESS_WIDTH_spec(),
    {
        48
    }

    // Expansion for HIGHEST_TRANSLATION_LEVEL
    #[verifier::inline]
    open spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel {
        2
    }

    #[inline(always)]
    fn HIGHEST_TRANSLATION_LEVEL() -> (res: PagingLevel)
        ensures
            res == Self::HIGHEST_TRANSLATION_LEVEL_spec(),
    {
        2
    }

    #[verifier::inline]
    open spec fn VA_SIGN_EXT_spec() -> bool {
        true
    }

    #[inline(always)]
    fn VA_SIGN_EXT() -> bool {
        true
    }

    // Expansion for PTE_SIZE
    #[verifier::inline]
    open spec fn PTE_SIZE_spec() -> usize {
        8
    }

    proof fn lemma_PTE_SIZE_properties()
        ensures
            0 < Self::PTE_SIZE_spec() <= Self::BASE_PAGE_SIZE(),
            is_pow2(Self::PTE_SIZE_spec() as int),
    {
        lemma_pow2_is_pow2_to64();
    }

    #[inline(always)]
    fn PTE_SIZE() -> (res: usize)
        ensures
            res == Self::PTE_SIZE_spec(),
    {
        proof {
            Self::lemma_PTE_SIZE_properties();
        }
        8
    }
}

pub proof fn lemma_nr_subpage_per_huge_eq_nr_entries()
    ensures
        crate::mm::nr_subpage_per_huge::<PagingConsts>() == NR_ENTRIES,
{
    assert(crate::mm::nr_subpage_per_huge::<PagingConsts>() == 4096usize / 8usize);
    assert(NR_ENTRIES == 512usize);
}
}

verified_bitflags::bitflags! {
    //#[derive(Pod)]
    //#[repr(C)]
    /// Possible flags for a page table entry.
    pub struct PageTableFlags: usize {
        /// Specifies whether the mapped frame or page table is loaded in memory.
        const PRESENT =         1usize << 0;
        /// Controls whether writes to the mapped frames are allowed.
        const WRITABLE =        1usize << 1;
        /// Controls whether accesses from userspace (i.e. ring 3) are permitted.
        const USER =            1usize << 2;
        /// If this bit is set, a “write-through” policy is used for the cache, else a “write-back”
        /// policy is used.
        const WRITE_THROUGH =   1usize << 3;
        /// Disables caching for the pointed entry is cacheable.
        const NO_CACHE =        1usize << 4;
        /// Whether this entry has been used for linear-address translation.
        const ACCESSED =        1usize << 5;
        /// Whether the memory area represented by this entry is modified.
        const DIRTY =           1usize << 6;
        /// In level 2 or 3 it indicates that it map to a huge page.
        /// In level 1, it is the PAT (page attribute table) bit.
        /// We use this bit in level 1, 2 and 3 to indicate that this entry is
        /// "valid". For levels above 3, `PRESENT` is used for "valid".
        const HUGE =            1usize << 7;
        /// Indicates that the mapping is present in all address spaces, so it isn't flushed from
        /// the TLB on an address space switch.
        const GLOBAL =          1usize << 8;
        /// TDX shared bit.
        #[cfg(feature = "cvm_guest")]
        const SHARED =          1usize << 51;

        /// Ignored by the hardware. Free to use.
        const HIGH_IGN1 =       1usize << 52;
        /// Ignored by the hardware. Free to use.
        const HIGH_IGN2 =       1usize << 53;

        /// Forbid execute codes on the page. The NXE bits in EFER msr must be set.
        const NO_EXECUTE =      1usize << 63;
    }
}

/*
/// Flush any TLB entry that contains the map of the given virtual address.
///
/// This flush performs regardless of the global-page bit. So it can flush both global
/// and non-global entries.
pub(crate) fn tlb_flush_addr(vaddr: Vaddr) {
    tlb::flush(VirtAddr::new(vaddr as u64));
}

/// Flush any TLB entry that intersects with the given address range.
pub(crate) fn tlb_flush_addr_range(range: &Range<Vaddr>) {
    for vaddr in range.clone().step_by(PAGE_SIZE) {
        tlb_flush_addr(vaddr);
    }
}

/// Flush all TLB entries except for the global-page entries.
pub(crate) fn tlb_flush_all_excluding_global() {
    tlb::flush_all();
}

/// Flush all TLB entries, including global-page entries.
pub(crate) fn tlb_flush_all_including_global() {
    // SAFETY: updates to CR4 here only change the global-page bit, the side effect
    // is only to invalidate the TLB, which doesn't affect the memory safety.
    unsafe {
        // To invalidate all entries, including global-page
        // entries, disable global-page extensions (CR4.PGE=0).
        x86_64::registers::control::Cr4::update(|cr4| {
            *cr4 -= x86_64::registers::control::Cr4Flags::PAGE_GLOBAL;
        });
        x86_64::registers::control::Cr4::update(|cr4| {
            *cr4 |= x86_64::registers::control::Cr4Flags::PAGE_GLOBAL;
        });
    }
}
*/
verus! {

#[verifier::ext_equal]
#[derive(Clone, Copy/*, Pod, Default*/)]
#[derive(Debug)]
#[repr(C)]
pub struct PageTableEntry(usize);

#[verus_verify]
unsafe impl Pod for PageTableEntry {

}

impl PageTableEntry {
    pub closed spec fn default_spec() -> Self {
        Self(0)
    }
}

impl Default for PageTableEntry {
    fn default() -> (ret: Self)
        ensures
            ret.paddr() == 0,
        returns
            Self::default_spec(),
    {
        proof {
            lemma_page_property_flag_constants();
            assert(Self::default_spec().paddr_spec() == 0) by (compute);
        }
        Self(usize::default())
    }
}

} // verus!
  /*
  /// Activates the given level 4 page table.
  /// The cache policy of the root page table node is controlled by `root_pt_cache`.
  ///
  /// # Safety
  ///
  /// Changing the level 4 page table is unsafe, because it's possible to violate memory safety by
  /// changing the page mapping.
  pub unsafe fn activate_page_table(root_paddr: Paddr, root_pt_cache: CachePolicy) {
      let addr = PhysFrame::from_start_address(x86_64::PhysAddr::new(root_paddr as u64)).unwrap();
      let flags = match root_pt_cache {
          CachePolicy::Writeback => x86_64::registers::control::Cr3Flags::empty(),
          CachePolicy::Writethrough => x86_64::registers::control::Cr3Flags::PAGE_LEVEL_WRITETHROUGH,
          CachePolicy::Uncacheable => x86_64::registers::control::Cr3Flags::PAGE_LEVEL_CACHE_DISABLE,
          _ => panic!("unsupported cache policy for the root page table"),
      };

      // SAFETY: The safety is upheld by the caller.
      unsafe { x86_64::registers::control::Cr3::write(addr, flags) };
  }

  pub fn current_page_table_paddr() -> Paddr {
      x86_64::registers::control::Cr3::read_raw()
          .0
          .start_address()
          .as_u64() as Paddr
  }
  */
verus! {

impl PageTableEntry {
    //cfg_if! {
    //if #[cfg(feature = "cvm_guest")] {
    //    const PHYS_ADDR_MASK: usize = 0x7_FFFF_FFFF_F000;
    //} else {
    const PHYS_ADDR_MASK: usize = 0xF_FFFF_FFFF_F000;

    //}
    //}
    // const PROP_MASK: usize = !Self::PHYS_ADDR_MASK & !PageTableFlags::HUGE.bits();
    const PROP_MASK: usize = !Self::PHYS_ADDR_MASK & !0x80usize;
}

/// Parse a bit-flag bits `val` in the representation of `from` to `to` in bits.
macro_rules! parse_flags {
    ($val:expr, $from:expr, $to:expr) => {
        ($val as usize & $from.bits() as usize) >> $from.bits().ilog2() << $to.bits().ilog2()
    };
}

impl PodOnce for PageTableEntry {

}

impl PageTableEntryTrait for PageTableEntry {
    fn new_absent() -> Self {
        proof {
            lemma_auxiliary_bit_properties(0);
            Self::lemma_page_table_entry_properties();
            assert(Self::default_spec() == Self::new_absent_spec());
        }
        Self::default()
    }

    fn is_present(&self) -> bool {
        // For PT child, `PRESENT` should be set; for huge page, `HUGE` should
        // be set; for the leaf child page, `PAT`, which is the same bit as
        // the `HUGE` bit in upper levels, should be set.
        self.0 & PageTableFlags::PRESENT().bits() != 0 || self.0 & PageTableFlags::HUGE().bits()
            != 0
    }

    open spec fn new_page_req(paddr: Paddr, _level: PagingLevel, prop: PageProperty) -> bool {
        &&& prop.inv()
        &&& prop.flags.bits() & PageFlags::R().bits() == PageFlags::R().bits()
        &&& (!(prop.cache is Writeback || prop.cache is Writethrough || prop.cache is Uncacheable)
            ==> may_panic())
    }

    fn new_page(paddr: Paddr, _level: PagingLevel, prop: PageProperty) -> Self {
        let flags = PageTableFlags::HUGE().bits();
        let mut pte = Self(paddr & Self::PHYS_ADDR_MASK | flags);
        proof {
            lemma_auxiliary_bit_properties(paddr);
            assert(pte.set_prop_req(prop));
            assert((paddr & Self::PHYS_ADDR_MASK | flags) & Self::PHYS_ADDR_MASK
                == paddr & Self::PHYS_ADDR_MASK) by (bit_vector)
                requires
                    flags == PageTableFlags::HUGE().bits();
            assert(paddr < MAX_PADDR ==> (paddr & Self::PHYS_ADDR_MASK | flags)
                & Self::PHYS_ADDR_MASK == paddr & !((PAGE_SIZE - 1) as usize))
                by (bit_vector)
                requires
                    flags == PageTableFlags::HUGE().bits();
            assert(((paddr & Self::PHYS_ADDR_MASK | flags) & PageTableFlags::HUGE().bits()) != 0)
                by (bit_vector)
                requires
                    flags == PageTableFlags::HUGE().bits();
            assert(pte.is_last(_level));
        }
        pte.set_prop(prop);
        pte
    }

    fn new_pt(paddr: Paddr) -> (res: Self) {
        // In x86 if it's an intermediate PTE, it's better to have the same permissions
        // as the most permissive child (to reduce hardware page walk accesses). But we
        // don't have a mechanism to keep it generic across architectures, thus just
        // setting it to be the most permissive.
        let flags = PageTableFlags::PRESENT().bits()
            | PageTableFlags::WRITABLE().bits()
            | PageTableFlags::USER().bits();
        proof {
            Self::lemma_page_table_entry_properties();
            lemma_auxiliary_bit_properties(paddr);
            assert(paddr < MAX_PADDR ==> paddr & Self::PHYS_ADDR_MASK == paddr & !((PAGE_SIZE
                - 1) as usize)) by (bit_vector);
            assert((Self(paddr & Self::PHYS_ADDR_MASK | flags)) == Self::new_pt(paddr));
        }
        Self(paddr & Self::PHYS_ADDR_MASK | flags)
    }

    fn paddr(&self) -> Paddr {
        proof {
            self.lemma_paddr_is_page_aligned();
        }
        self.0 & Self::PHYS_ADDR_MASK
    }

    fn prop(&self) -> PageProperty {
        proof {
            lemma_auxiliary_bit_properties(self.0);
            lemma_page_property_flag_constants();
        }
        let flags = (parse_flags!(self.0, PageTableFlags::PRESENT(), PageFlags::R()))
            | (parse_flags!(self.0, PageTableFlags::WRITABLE(), PageFlags::W()))
            | (parse_flags!(!self.0, PageTableFlags::NO_EXECUTE(), PageFlags::X()))
            | (parse_flags!(self.0, PageTableFlags::ACCESSED(), PageFlags::ACCESSED()))
            | (parse_flags!(self.0, PageTableFlags::DIRTY(), PageFlags::DIRTY()))
            | (parse_flags!(self.0, PageTableFlags::HIGH_IGN1(), PageFlags::AVAIL1()))
            | (parse_flags!(self.0, PageTableFlags::HIGH_IGN2(), PageFlags::AVAIL2()));
        let priv_flags = (parse_flags!(self.0, PageTableFlags::USER(), PrivFlags::USER()))
            | (parse_flags!(self.0, PageTableFlags::GLOBAL(), PrivFlags::GLOBAL()));
        #[cfg(feature = "cvm_guest")]
        let priv_flags =
            priv_flags | (parse_flags!(self.0, PageTableFlags::SHARED(), PrivFlags::SHARED()));
        let cache = if self.0 & PageTableFlags::NO_CACHE().bits() != 0 {
            CachePolicy::Uncacheable
        } else if self.0 & PageTableFlags::WRITE_THROUGH().bits() != 0 {
            CachePolicy::Writethrough
        } else {
            CachePolicy::Writeback
        };
        proof {
            lemma_parse_flags_collorary(self.0);
            lemma_x86_page_flags_wf(self.0, flags);
            assert(flags & PageFlags::all_bits() as usize == flags) by (compute);
            #[cfg(not(feature = "cvm_guest"))]
            {
                lemma_x86_priv_flags_wf(self.0, priv_flags);
            }
            #[cfg(feature = "cvm_guest")]
            {
                lemma_parse_shared_to_priv_shared_equiv_if(self.0);
                lemma_x86_priv_flags_cvm_wf(self.0, priv_flags);
            }
            let spec_prop = self.prop();
            assert(cache == spec_prop.cache);
            assert(PageFlags::from_bits(flags as u8)->0 == spec_prop.flags);
            assert(PrivFlags::from_bits(priv_flags as u8)->0 == spec_prop.priv_flags);
        }
        PageProperty {
            flags: PageFlags::from_bits(flags as u8).unwrap(),
            cache,
            priv_flags: PrivFlags::from_bits(priv_flags as u8).unwrap(),
        }
    }

    open spec fn set_prop_req(self, prop: PageProperty) -> bool {
        &&& prop.inv()
        &&& prop.flags.bits() & PageFlags::R().bits() == PageFlags::R().bits()
        &&& (!(prop.cache is Writeback || prop.cache is Writethrough || prop.cache is Uncacheable)
            ==> may_panic())
    }

    fn set_prop(&mut self, prop: PageProperty)
        ensures
            old(self).is_present() ==> final(self).as_usize() == Self::raw_set_prop_spec(
                old(self).as_usize(),
                prop,
            ),
    {
        proof {
            lemma_auxiliary_bit_properties(0);
            lemma_page_property_flag_constants();
        }
        if !self.is_present() {
            return;
        }
        let mut flags = PageTableFlags::empty().bits();
        flags = flags |
            (parse_flags!(prop.flags.bits(), PageFlags::R(), PageTableFlags::PRESENT()))
            | (parse_flags!(prop.flags.bits(), PageFlags::W(), PageTableFlags::WRITABLE()))
            | (parse_flags!(!prop.flags.bits(), PageFlags::X(), PageTableFlags::NO_EXECUTE()))
            | (parse_flags!(
                prop.flags.bits(),
                PageFlags::ACCESSED(),
                PageTableFlags::ACCESSED()
            ))
            | (parse_flags!(prop.flags.bits(), PageFlags::DIRTY(), PageTableFlags::DIRTY()))
            | (parse_flags!(
                prop.flags.bits(),
                PageFlags::AVAIL1(),
                PageTableFlags::HIGH_IGN1()
            ))
            | (parse_flags!(
                prop.flags.bits(),
                PageFlags::AVAIL2(),
                PageTableFlags::HIGH_IGN2()
            ))
            | (parse_flags!(
                prop.priv_flags.bits(),
                PrivFlags::USER(),
                PageTableFlags::USER()
            ))
            | (parse_flags!(
                prop.priv_flags.bits(),
                PrivFlags::GLOBAL(),
                PageTableFlags::GLOBAL()
            ));
        #[cfg(feature = "cvm_guest")]
        {
            flags = flags |
            parse_flags!(
                prop.priv_flags.bits(),
                PrivFlags::SHARED(),
                PageTableFlags::SHARED()
            );
        }
        proof {
            let ghost cache_flags = if prop.cache is Writethrough {
                PageTableFlags::WRITE_THROUGH().bits()
            } else if prop.cache is Uncacheable {
                PageTableFlags::NO_CACHE().bits()
            } else {
                0usize
            };
            match prop.cache {
                CachePolicy::Writeback => {
                    assert(flags == flags | cache_flags) by (bit_vector)
                        requires
                            cache_flags == 0usize;
                },
                _ => {},
            }
        }
        match prop.cache {
            CachePolicy::Writeback => {},
            CachePolicy::Writethrough => {
                flags |= PageTableFlags::WRITE_THROUGH().bits();
            },
            CachePolicy::Uncacheable => {
                flags |= PageTableFlags::NO_CACHE().bits();
            },
            _ => {
                //panic!("unsupported cache policy");
                panic_diverge();
            },
        }
        proof {
            assert(flags == PageProperty::encode_prop_flags_spec(prop));
        }
        self.0 = self.0 & !Self::PROP_MASK | flags;
        proof {
            lemma_x86_set_prop_roundtrip(old(self).0, flags, prop);
        }
    }

    fn is_last(&self, _level: PagingLevel) -> bool {
        self.0 & PageTableFlags::HUGE().bits() != 0
    }

    fn as_usize(self) -> usize {
        self.0
    }

    open spec fn new_absent_spec() -> Self {
        Self::default_spec()
    }

    open spec fn is_present_spec(&self) -> bool {
        self.as_usize() & PageTableFlags::PRESENT().bits() != 0 || self.as_usize()
            & PageTableFlags::HUGE().bits() != 0
    }

    closed spec fn paddr_spec(&self) -> Paddr {
        self.as_usize() & Self::PHYS_ADDR_MASK
    }

    closed spec fn prop_spec(&self) -> PageProperty {
        PageProperty {
            flags: PageFlags::from_bits(PageProperty::decode_page_flags_spec(self.0))->0,
            cache: PageProperty::decode_cache_spec(self.0),
            priv_flags: PrivFlags::from_bits(PageProperty::decode_priv_flags_spec(self.0))->0,
        }
    }

    closed spec fn new_pt_spec(paddr: Paddr) -> Self {
        let flags = PageTableFlags::PRESENT().bits() | PageTableFlags::WRITABLE().bits()
            | PageTableFlags::USER().bits();
        Self(paddr & Self::PHYS_ADDR_MASK | flags)
    }

    closed spec fn new_page_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        let flags = PageTableFlags::HUGE().bits();
        let pte = paddr & Self::PHYS_ADDR_MASK | flags;
        match prop.cache {
            CachePolicy::Writeback |
            CachePolicy::Writethrough |
            CachePolicy::Uncacheable => Self(Self::raw_set_prop_spec(pte, prop)),
            _ => arbitrary(),
        }
    }

    open spec fn is_last_spec(&self, _level: PagingLevel) -> bool {
        self.as_usize() & PageTableFlags::HUGE().bits() != 0
    }

    closed spec fn as_usize_spec(self) -> usize {
        self.0
    }

    proof fn lemma_page_table_entry_properties() {
        lemma_page_property_flag_constants();
        lemma_auxiliary_bit_properties(0);

        assert forall|level: PagingLevel|
            1 < level implies !(#[trigger]Self::new_absent().is_last(level))
        by {
            assert(Self::new_absent().as_usize() == 0);
        }

        assert forall|paddr: Paddr, level: PagingLevel, prop: PageProperty|
            #![trigger Self::new_page(paddr, level, prop)]
            Self::new_page_req(paddr, level, prop) && (prop.cache is Writeback
                || prop.cache is Writethrough || prop.cache is Uncacheable) implies {
                &&& Self::new_page(paddr, level, prop).is_present()
                &&& (paddr < MAX_PADDR ==> Self::new_page(paddr, level, prop).paddr() == paddr
                    & !((PAGE_SIZE - 1) as usize))
                &&& (paddr < MAX_PADDR && paddr % PAGE_SIZE == 0 ==> Self::new_page(
                    paddr,
                    level,
                    prop,
                ).paddr() == paddr)
                &&& Self::new_page(paddr, level, prop).prop() == prop
                &&& Self::new_page(paddr, level, prop).is_last(level)
            }
        by {
            let raw = paddr & Self::PHYS_ADDR_MASK | PageTableFlags::HUGE().bits();
            let flags = PageProperty::encode_prop_flags_spec(prop);
            lemma_auxiliary_bit_properties(paddr);
            lemma_auxiliary_bit_properties(raw);
            lemma_x86_set_prop_roundtrip(raw, flags, prop);
            assert(raw & Self::PHYS_ADDR_MASK == paddr & Self::PHYS_ADDR_MASK) by (bit_vector)
                requires
                    raw == (paddr & 0xF_FFFF_FFFF_F000usize | 0x80usize),
                    Self::PHYS_ADDR_MASK == 0xF_FFFF_FFFF_F000usize;
            assert(paddr < MAX_PADDR ==> raw & Self::PHYS_ADDR_MASK == paddr & !((PAGE_SIZE
                - 1) as usize)) by (bit_vector)
                requires
                    raw == (paddr & 0xF_FFFF_FFFF_F000usize | 0x80usize),
                    Self::PHYS_ADDR_MASK == 0xF_FFFF_FFFF_F000usize,
                    PAGE_SIZE == 4096usize,
                    MAX_PADDR == 0x8000_0000usize;
            assert(raw & PageTableFlags::HUGE().bits() != 0) by (bit_vector)
                requires
                    raw == (paddr & 0xF_FFFF_FFFF_F000usize | 0x80usize),
                    PageTableFlags::HUGE().bits() == 0x80usize;
            assert(PageTableEntry(raw).is_last(level));
            assert(Self::new_page(paddr, level, prop).is_last(level));
        }

        assert forall|paddr: Paddr| #![trigger Self::new_pt(paddr)] {
                &&& Self::new_pt(paddr).is_present()
                &&& (paddr < MAX_PADDR ==> Self::new_pt(paddr).paddr() == paddr & !((PAGE_SIZE
                    - 1) as usize))
                &&& (paddr < MAX_PADDR && paddr % PAGE_SIZE == 0 ==> Self::new_pt(paddr).paddr()
                    == paddr)
                &&& forall|level: PagingLevel| !Self::new_pt(paddr).is_last(level)
            }
        by {
            let flags = PageTableFlags::PRESENT().bits() | PageTableFlags::WRITABLE().bits()
                | PageTableFlags::USER().bits();
            lemma_auxiliary_bit_properties(paddr);
            assert(flags == 0x7usize) by (bit_vector)
                requires
                    flags == 0x1usize | 0x2usize | 0x4usize;
            assert(paddr < MAX_PADDR ==> (paddr & Self::PHYS_ADDR_MASK | flags)
                & Self::PHYS_ADDR_MASK == paddr & !((PAGE_SIZE - 1) as usize)) by (bit_vector)
                requires
                    Self::PHYS_ADDR_MASK == 0xF_FFFF_FFFF_F000usize,
                    flags == 0x7usize,
                    PAGE_SIZE == 4096usize,
                    MAX_PADDR == 0x8000_0000usize;
            assert((paddr & Self::PHYS_ADDR_MASK | flags) & PageTableFlags::PRESENT().bits() != 0)
                by (bit_vector)
                requires
                    Self::PHYS_ADDR_MASK == 0xF_FFFF_FFFF_F000usize,
                    flags == 0x7usize,
                    PageTableFlags::PRESENT().bits() == 0x1usize;
            assert forall|level: PagingLevel| !Self::new_pt(paddr).is_last(level) by {
                assert((paddr & Self::PHYS_ADDR_MASK | flags) & PageTableFlags::HUGE().bits()
                    == 0) by (bit_vector)
                    requires
                        Self::PHYS_ADDR_MASK == 0xF_FFFF_FFFF_F000usize,
                        flags == 0x7usize,
                        PageTableFlags::HUGE().bits() == 0x80usize;
            }
        }
    }

    proof fn lemma_paddr_is_page_aligned(self) {
        lemma_auxiliary_bit_properties(self.0);
    }
}


impl PageTableEntry {
    pub closed spec fn raw_set_prop_spec(old_raw: usize, prop: PageProperty) -> usize {
        old_raw & !Self::PROP_MASK | PageProperty::encode_prop_flags_spec(prop)
    }
}

// Auxiliary definitions and lemmas about bit properties of page table entries and flags.
impl PageProperty {
    closed spec fn encode_prop_flags_spec(prop: Self) -> usize {
        let flags = PageTableFlags::empty().bits()
            | parse_flags!(prop.flags.bits(), PageFlags::R(), PageTableFlags::PRESENT())
            | parse_flags!(prop.flags.bits(), PageFlags::W(), PageTableFlags::WRITABLE())
            | parse_flags!(!prop.flags.bits(), PageFlags::X(), PageTableFlags::NO_EXECUTE())
            | parse_flags!(prop.flags.bits(), PageFlags::ACCESSED(), PageTableFlags::ACCESSED())
            | parse_flags!(prop.flags.bits(), PageFlags::DIRTY(), PageTableFlags::DIRTY())
            | parse_flags!(prop.flags.bits(), PageFlags::AVAIL1(), PageTableFlags::HIGH_IGN1())
            | parse_flags!(prop.flags.bits(), PageFlags::AVAIL2(), PageTableFlags::HIGH_IGN2())
            | parse_flags!(prop.priv_flags.bits(), PrivFlags::USER(), PageTableFlags::USER())
            | parse_flags!(prop.priv_flags.bits(), PrivFlags::GLOBAL(), PageTableFlags::GLOBAL());
        #[cfg(feature = "cvm_guest")]
        let flags = flags
            | parse_flags!(prop.priv_flags.bits(), PrivFlags::SHARED(), PageTableFlags::SHARED());
        flags | if prop.cache is Writeback {
            0
        } else if prop.cache is Writethrough {
            PageTableFlags::WRITE_THROUGH().bits()
        } else {
            PageTableFlags::NO_CACHE().bits()
        }
    }

    closed spec fn decode_page_flags_spec(raw: usize) -> u8 {
        let flags = if raw & PageTableFlags::PRESENT().bits() != 0 {
            PageFlags::R().bits()
        } else {
            0
        } | if raw & PageTableFlags::WRITABLE().bits() != 0 {
            PageFlags::W().bits()
        } else {
            0
        } | if !raw & PageTableFlags::NO_EXECUTE().bits() != 0 {
            PageFlags::X().bits()
        } else {
            0
        } | if raw & PageTableFlags::ACCESSED().bits() != 0 {
            PageFlags::ACCESSED().bits()
        } else {
            0
        } | if raw & PageTableFlags::DIRTY().bits() != 0 {
            PageFlags::DIRTY().bits()
        } else {
            0
        } | if raw & PageTableFlags::HIGH_IGN1().bits() != 0 {
            PageFlags::AVAIL1().bits()
        } else {
            0
        } | if raw & PageTableFlags::HIGH_IGN2().bits() != 0 {
            PageFlags::AVAIL2().bits()
        } else {
            0
        };
        flags
    }

    closed spec fn decode_priv_flags_spec(raw: usize) -> u8 {
        let priv_flags = if raw & PageTableFlags::USER().bits() != 0 {
            PrivFlags::USER().bits()
        } else {
            0
        } | if raw & PageTableFlags::GLOBAL().bits() != 0 {
            PrivFlags::GLOBAL().bits()
        } else {
            0
        };
        #[cfg(feature = "cvm_guest")]
        let priv_flags = priv_flags | if raw & PageTableFlags::SHARED().bits() != 0 {
            PrivFlags::SHARED().bits()
        } else {
            0
        };
        priv_flags
    }

    closed spec fn decode_cache_spec(raw: usize) -> CachePolicy {
        if raw & PageTableFlags::NO_CACHE().bits() != 0 {
            CachePolicy::Uncacheable
        } else if raw & PageTableFlags::WRITE_THROUGH().bits() != 0 {
            CachePolicy::Writethrough
        } else {
            CachePolicy::Writeback
        }
    }
}

#[verifier::bit_vector]
proof fn lemma_auxiliary_bit_properties(addr: usize)
    ensures
        addr % PAGE_SIZE == 0 ==> addr == (addr & !((PAGE_SIZE - 1) as usize)),
        (addr & PageTableEntry::PHYS_ADDR_MASK) % PAGE_SIZE == 0,
        addr < MAX_PADDR ==> (addr & PageTableEntry::PHYS_ADDR_MASK) < MAX_PADDR,
{
}

proof fn lemma_page_property_flag_constants()
    ensures
        0 & PageTableEntry::PHYS_ADDR_MASK == 0,
        0usize % PAGE_SIZE == 0,
        0 < MAX_PADDR,
        0 & PageTableFlags::PRESENT().bits() == 0,
        0 & PageTableFlags::HUGE().bits() == 0,
        PageTableFlags::PRESENT().bits() == 0x1,
        PageTableFlags::WRITABLE().bits() == 0x2,
        PageTableFlags::USER().bits() == 0x4,
        PageTableFlags::WRITE_THROUGH().bits() == 0x8,
        PageTableFlags::NO_CACHE().bits() == 0x10,
        PageTableFlags::ACCESSED().bits() == 0x20,
        PageTableFlags::DIRTY().bits() == 0x40,
        PageTableFlags::HUGE().bits() == 0x80,
        PageTableFlags::GLOBAL().bits() == 0x100,
        #[cfg(feature = "cvm_guest")]
        (PageTableFlags::SHARED().bits() == 0x0200_0000_0000_0000),
        PageTableFlags::HIGH_IGN1().bits() == 0x0010_0000_0000_0000,
        PageTableFlags::HIGH_IGN2().bits() == 0x0020_0000_0000_0000,
        PageTableFlags::NO_EXECUTE().bits() == 0x8000000000000000,
        PageTableFlags::PRESENT().bits().ilog2() == 0,
        PageTableFlags::WRITABLE().bits().ilog2() == 1,
        PageTableFlags::USER().bits().ilog2() == 2,
        PageTableFlags::WRITE_THROUGH().bits().ilog2() == 3,
        PageTableFlags::NO_CACHE().bits().ilog2() == 4,
        PageTableFlags::ACCESSED().bits().ilog2() == 5,
        PageTableFlags::DIRTY().bits().ilog2() == 6,
        PageTableFlags::HUGE().bits().ilog2() == 7,
        PageTableFlags::GLOBAL().bits().ilog2() == 8,
        #[cfg(feature = "cvm_guest")]
        (PageTableFlags::SHARED().bits().ilog2() == 51),
        PageTableFlags::HIGH_IGN1().bits().ilog2() == 52,
        PageTableFlags::HIGH_IGN2().bits().ilog2() == 53,
        PageTableFlags::NO_EXECUTE().bits().ilog2() == 63,
        PageFlags::R().bits() == 0x1,
        PageFlags::W().bits() == 0x2,
        PageFlags::X().bits() == 0x4,
        PageFlags::ACCESSED().bits() == 0x8,
        PageFlags::DIRTY().bits() == 0x10,
        PageFlags::AVAIL1().bits() == 0x40,
        PageFlags::AVAIL2().bits() == 0x80,
        PageFlags::all_bits() == 0xDFu8,
        PageFlags::R().bits().ilog2() == 0,
        PageFlags::W().bits().ilog2() == 1,
        PageFlags::X().bits().ilog2() == 2,
        PageFlags::ACCESSED().bits().ilog2() == 3,
        PageFlags::DIRTY().bits().ilog2() == 4,
        PageFlags::AVAIL1().bits().ilog2() == 6,
        PageFlags::AVAIL2().bits().ilog2() == 7,
        PrivFlags::USER().bits() == 0x1,
        PrivFlags::GLOBAL().bits() == 0x2,
        #[cfg(not(all(target_arch = "x86_64", feature = "cvm_guest")))]
        PrivFlags::all_bits() == 0x3u8,
        PrivFlags::USER().bits().ilog2() == 0,
        PrivFlags::GLOBAL().bits().ilog2() == 1,
        #[cfg(all(target_arch = "x86_64", feature = "cvm_guest"))]
        (PrivFlags::SHARED().bits() == 0x80),
        #[cfg(all(target_arch = "x86_64", feature = "cvm_guest"))]
        (PrivFlags::all_bits() == 0x83u8),
        #[cfg(all(target_arch = "x86_64", feature = "cvm_guest"))]
        (PrivFlags::SHARED().bits().ilog2() == 7),
{
    lemma_usize_ilog2_to32();
    lemma_u8_ilog2_to8();
    lemma_u64_ilog2_to64();
    assert(0 & PageTableEntry::PHYS_ADDR_MASK == 0) by (compute_only);
    assert(0usize % PAGE_SIZE == 0) by (compute_only);
    assert(0 < MAX_PADDR) by (compute_only);
    assert(PageTableFlags::PRESENT().bits() == 0x1) by (compute);
    assert(PageTableFlags::WRITABLE().bits() == 0x2) by (compute);
    assert(PageTableFlags::USER().bits() == 0x4) by (compute);
    assert(PageTableFlags::WRITE_THROUGH().bits() == 0x8) by (compute);
    assert(PageTableFlags::NO_CACHE().bits() == 0x10) by (compute);
    assert(PageTableFlags::ACCESSED().bits() == 0x20) by (compute);
    assert(PageTableFlags::DIRTY().bits() == 0x40) by (compute);
    assert(PageTableFlags::HUGE().bits() == 0x80) by (compute);
    assert(PageTableFlags::GLOBAL().bits() == 0x100) by (compute);
    assert(0 & PageTableFlags::PRESENT().bits() == 0) by (bit_vector);
    assert(0 & PageTableFlags::HUGE().bits() == 0) by (bit_vector);
    #[cfg(feature = "cvm_guest")]
    {
        assert(PageTableFlags::SHARED().bits() == 0x0200_0000_0000_0000) by (compute);
    }
    assert(PageTableFlags::HIGH_IGN1().bits() == 0x0010_0000_0000_0000) by (compute);
    assert(PageTableFlags::HIGH_IGN2().bits() == 0x0020_0000_0000_0000) by (compute);
    assert(PageTableFlags::NO_EXECUTE().bits() == 0x8000000000000000) by (compute);
    broadcast use PageFlags::lemma_consts;
    broadcast use PrivFlags::lemma_consts;

    assert(PageFlags::all_bits() == 0xDFu8) by (compute);
    #[cfg(not(all(target_arch = "x86_64", feature = "cvm_guest")))]
    assert(PrivFlags::all_bits() == 0x3u8) by (compute);
}

#[cfg(all(target_arch = "x86_64", feature = "cvm_guest"))]
proof fn lemma_parse_shared_to_priv_shared_equiv_if(v: usize)
    ensures
        parse_flags!(v, PageTableFlags::SHARED(), PrivFlags::SHARED()) == if v
            & PageTableFlags::SHARED().bits() != 0 {
            PrivFlags::SHARED().bits() as usize
        } else {
            0usize
        },
{
    lemma_page_property_flag_constants();
    assert(parse_flags!(v, PageTableFlags::SHARED(), PrivFlags::SHARED()) == ((v
        & 0x0200_0000_0000_0000usize) >> 51 << 7)) by (compute);
    assert(((v & 0x0200_0000_0000_0000usize) >> 51 << 7) == (if (v & 0x0200_0000_0000_0000usize)
        != 0 {
        0x80usize
    } else {
        0usize
    })) by (bit_vector);
}

proof fn lemma_parse_flags_equiv_if(v: usize)
    ensures
        parse_flags!(v, PageTableFlags::PRESENT(), PageFlags::R()) == if v
            & PageTableFlags::PRESENT().bits() != 0 {
            PageFlags::R().bits()
        } else {
            0
        },
        parse_flags!(v, PageTableFlags::WRITABLE(), PageFlags::W()) == if v
            & PageTableFlags::WRITABLE().bits() != 0 {
            PageFlags::W().bits()
        } else {
            0
        },
        parse_flags!(!v, PageTableFlags::NO_EXECUTE(), PageFlags::X()) == if !v
            & PageTableFlags::NO_EXECUTE().bits() != 0 {
            PageFlags::X().bits()
        } else {
            0
        },
        parse_flags!(v, PageTableFlags::ACCESSED(), PageFlags::ACCESSED()) == if v
            & PageTableFlags::ACCESSED().bits() != 0 {
            PageFlags::ACCESSED().bits()
        } else {
            0
        },
        parse_flags!(v, PageTableFlags::DIRTY(), PageFlags::DIRTY()) == if v
            & PageTableFlags::DIRTY().bits() != 0 {
            PageFlags::DIRTY().bits()
        } else {
            0
        },
        parse_flags!(v, PageTableFlags::HIGH_IGN1(), PageFlags::AVAIL1()) == if v
            & PageTableFlags::HIGH_IGN1().bits() != 0 {
            PageFlags::AVAIL1().bits()
        } else {
            0
        },
        parse_flags!(v, PageTableFlags::HIGH_IGN2(), PageFlags::AVAIL2()) == if v
            & PageTableFlags::HIGH_IGN2().bits() != 0 {
            PageFlags::AVAIL2().bits()
        } else {
            0
        },
        parse_flags!(v, PageTableFlags::USER(), PrivFlags::USER()) == if v
            & PageTableFlags::USER().bits() != 0 {
            PrivFlags::USER().bits()
        } else {
            0
        },
        parse_flags!(v, PageTableFlags::GLOBAL(), PrivFlags::GLOBAL()) == if v
            & PageTableFlags::GLOBAL().bits() != 0 {
            PrivFlags::GLOBAL().bits()
        } else {
            0
        },
{
    lemma_page_property_flag_constants();
    assert(((v & 0x1usize) >> 0 << 0) == (if (v & 0x1usize) != 0 {
        0x1usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((v & 0x2usize) >> 1 << 1) == (if (v & 0x2usize) != 0 {
        0x2usize
    } else {
        0usize
    })) by (bit_vector);
    assert((((!v & 0x8000_0000_0000_0000usize) >> 63) << 2) == (if (!v & 0x8000_0000_0000_0000usize)
        != 0 {
        0x4usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((v & 0x20usize) >> 5 << 3) == (if (v & 0x20usize) != 0 {
        0x8usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((v & 0x40usize) >> 6 << 4) == (if (v & 0x40usize) != 0 {
        0x10usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((v & 0x0010_0000_0000_0000usize) >> 52 << 6) == (if (v & 0x0010_0000_0000_0000usize)
        != 0 {
        0x40usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((v & 0x0020_0000_0000_0000usize) >> 53 << 7) == (if (v & 0x0020_0000_0000_0000usize)
        != 0 {
        0x80usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((v & 0x4usize) >> 2 << 0) == (if (v & 0x4usize) != 0 {
        0x1usize
    } else {
        0usize
    })) by (bit_vector);
    assert(((v & 0x100usize) >> 8 << 1) == (if (v & 0x100usize) != 0 {
        0x2usize
    } else {
        0usize
    })) by (bit_vector);
}

proof fn lemma_parse_flags_collorary(v: usize)
    ensures
        (parse_flags!(v, PageTableFlags::PRESENT(), PageFlags::R())) | (
        parse_flags!(v, PageTableFlags::WRITABLE(), PageFlags::W())) | (
        parse_flags!(!v, PageTableFlags::NO_EXECUTE(), PageFlags::X())) | (
        parse_flags!(v, PageTableFlags::ACCESSED(), PageFlags::ACCESSED())) | (
        parse_flags!(v, PageTableFlags::DIRTY(), PageFlags::DIRTY())) | (
        parse_flags!(v, PageTableFlags::HIGH_IGN1(), PageFlags::AVAIL1())) | (
        parse_flags!(v, PageTableFlags::HIGH_IGN2(), PageFlags::AVAIL2())) ==
        PageProperty::decode_page_flags_spec(v),
        (parse_flags!(v, PageTableFlags::USER(), PrivFlags::USER())) | (
        parse_flags!(v, PageTableFlags::GLOBAL(), PrivFlags::GLOBAL())) ==
        PageProperty::decode_priv_flags_spec(v),
{
    lemma_parse_flags_equiv_if(v);
}

#[verifier::bit_vector]
proof fn lemma_x86_page_flags_wf(v: usize, flags: usize)
    requires
        flags == (if v & 0x1usize != 0 {
            0x1usize
        } else {
            0
        } | if v & 0x2usize != 0 {
            0x2usize
        } else {
            0
        } | if !v & 0x8000_0000_0000_0000usize != 0 {
            0x4usize
        } else {
            0
        } | if v & 0x20usize != 0 {
            0x8usize
        } else {
            0
        } | if v & 0x40usize != 0 {
            0x10usize
        } else {
            0
        } | if v & 0x0010_0000_0000_0000usize != 0 {
            0x40usize
        } else {
            0
        } | if v & 0x0020_0000_0000_0000usize != 0 {
            0x80usize
        } else {
            0
        }),
    ensures
        flags <= 255usize,
        flags & 0xDFusize == flags,
{
}

#[verifier::bit_vector]
proof fn lemma_x86_priv_flags_wf(v: usize, priv_flags: usize)
    requires
        priv_flags == (if v & 0x4usize != 0 {
            0x1usize
        } else {
            0
        } | if v & 0x100usize != 0 {
            0x2usize
        } else {
            0
        }),
    ensures
        priv_flags <= 255usize,
        priv_flags & 0x3usize == priv_flags,
{
}

#[cfg(feature = "cvm_guest")]
#[verifier::bit_vector]
proof fn lemma_x86_priv_flags_cvm_wf(v: usize, priv_flags: usize)
    requires
        priv_flags == (if v & 0x4usize != 0 {
            0x1usize
        } else {
            0
        } | if v & 0x100usize != 0 {
            0x2usize
        } else {
            0
        } | if v & 0x0200_0000_0000_0000usize != 0 {
            0x80usize
        } else {
            0
        }),
    ensures
        priv_flags <= 255usize,
        priv_flags & 0x83usize == priv_flags,
{
}

/// It is the same as `PageProperty::encode_prop_flags_spec`, but all constants are expanded to support bit_vector.
closed spec fn encode_prop_flags_bv_spec(
    pbits: usize,
    priv_bits: usize,
    cache_flags: usize,
) -> usize {
    (if pbits & 0x1usize != 0 { 0x1usize } else { 0 })
        | (if pbits & 0x2usize != 0 { 0x2usize } else { 0 })
        | (if !pbits & 0x4usize != 0 { 0x8000_0000_0000_0000usize } else { 0 })
        | (if pbits & 0x8usize != 0 { 0x20usize } else { 0 })
        | (if pbits & 0x10usize != 0 { 0x40usize } else { 0 })
        | (if pbits & 0x40usize != 0 { 0x0010_0000_0000_0000usize } else { 0 })
        | (if pbits & 0x80usize != 0 { 0x0020_0000_0000_0000usize } else { 0 })
        | (if priv_bits & 0x1usize != 0 { 0x4usize } else { 0 })
        | (if priv_bits & 0x2usize != 0 { 0x100usize } else { 0 })
        | cache_flags
}

proof fn lemma_encode_prop_flags_matches(
    pbits: u8,
    priv_bits: u8,
    cache_flags: usize,
)
    requires
        cache_flags == 0usize || cache_flags == 0x8usize || cache_flags == 0x10usize,
    ensures
        (PageTableFlags::empty().bits()
            | parse_flags!(pbits, PageFlags::R(), PageTableFlags::PRESENT())
            | parse_flags!(pbits, PageFlags::W(), PageTableFlags::WRITABLE())
            | parse_flags!(!pbits, PageFlags::X(), PageTableFlags::NO_EXECUTE())
            | parse_flags!(pbits, PageFlags::ACCESSED(), PageTableFlags::ACCESSED())
            | parse_flags!(pbits, PageFlags::DIRTY(), PageTableFlags::DIRTY())
            | parse_flags!(pbits, PageFlags::AVAIL1(), PageTableFlags::HIGH_IGN1())
            | parse_flags!(pbits, PageFlags::AVAIL2(), PageTableFlags::HIGH_IGN2())
            | parse_flags!(priv_bits, PrivFlags::USER(), PageTableFlags::USER())
            | parse_flags!(priv_bits, PrivFlags::GLOBAL(), PageTableFlags::GLOBAL())
            | cache_flags)
            == encode_prop_flags_bv_spec(pbits as usize, priv_bits as usize, cache_flags),
{
    lemma_page_property_flag_constants();
    assert((0usize
        | ((pbits as usize & 0x1usize) >> 0 << 0)
        | ((pbits as usize & 0x2usize) >> 1 << 1)
        | (((!pbits) as usize & 0x4usize) >> 2 << 63)
        | ((pbits as usize & 0x8usize) >> 3 << 5)
        | ((pbits as usize & 0x10usize) >> 4 << 6)
        | ((pbits as usize & 0x40usize) >> 6 << 52)
        | ((pbits as usize & 0x80usize) >> 7 << 53)
        | ((priv_bits as usize & 0x1usize) >> 0 << 2)
        | ((priv_bits as usize & 0x2usize) >> 1 << 8)
        | cache_flags)
        == encode_prop_flags_bv_spec(pbits as usize, priv_bits as usize, cache_flags)) by (bit_vector);
}

#[verifier::bit_vector]
proof fn lemma_x86_set_prop_decode_bits(
    old_raw: usize,
    flags: usize,
    pbits: usize,
    priv_bits: usize,
    cache_flags: usize,
)
    requires
        pbits & 0xDFusize == pbits,
        priv_bits & 0x3usize == priv_bits,
        cache_flags == 0usize || cache_flags == 0x8usize || cache_flags == 0x10usize,
        flags == encode_prop_flags_bv_spec(pbits, priv_bits, cache_flags),
    ensures
        flags & PageTableEntry::PHYS_ADDR_MASK == 0,
        pbits & 0x1usize == 0x1usize ==> flags & 0x1usize == 0x1usize,
        {
            let new_raw = old_raw
                & !(!PageTableEntry::PHYS_ADDR_MASK & !PageTableFlags::HUGE().bits())
                | flags;
            let decoded_flags = (if new_raw & 0x1usize != 0 { 0x1usize } else { 0 })
                | (if new_raw & 0x2usize != 0 { 0x2usize } else { 0 })
                | (if !new_raw & 0x8000_0000_0000_0000usize != 0 { 0x4usize } else { 0 })
                | (if new_raw & 0x20usize != 0 { 0x8usize } else { 0 })
                | (if new_raw & 0x40usize != 0 { 0x10usize } else { 0 })
                | (if new_raw & 0x0010_0000_0000_0000usize != 0 { 0x40usize } else { 0 })
                | (if new_raw & 0x0020_0000_0000_0000usize != 0 { 0x80usize } else { 0 });
            decoded_flags == pbits
        },
        {
            let new_raw = old_raw
                & !(!PageTableEntry::PHYS_ADDR_MASK & !PageTableFlags::HUGE().bits())
                | flags;
            let decoded_priv_flags = (if new_raw & 0x4usize != 0 { 0x1usize } else { 0 })
                | (if new_raw & 0x100usize != 0 { 0x2usize } else { 0 });
            decoded_priv_flags == priv_bits
        },
        {
            let new_raw = old_raw
                & !(!PageTableEntry::PHYS_ADDR_MASK & !PageTableFlags::HUGE().bits())
                | flags;
            new_raw & 0x10usize != 0 <==> cache_flags == 0x10usize
        },
        {
            let new_raw = old_raw
                & !(!PageTableEntry::PHYS_ADDR_MASK & !PageTableFlags::HUGE().bits())
                | flags;
            new_raw & 0x8usize != 0 <==> cache_flags == 0x8usize
        },
{
}

proof fn lemma_x86_set_prop_roundtrip(old_raw: usize, flags: usize, prop: PageProperty)
    requires
        prop.inv(),
        prop.flags.bits() & PageFlags::R().bits() == PageFlags::R().bits(),
        prop.cache is Writeback || prop.cache is Writethrough || prop.cache is Uncacheable,
        flags == PageProperty::encode_prop_flags_spec(prop),
    ensures
        PageTableEntry(
            old_raw & !(!PageTableEntry::PHYS_ADDR_MASK & !PageTableFlags::HUGE().bits()) | flags,
        ).prop() == prop,
        PageTableEntry(
            old_raw & !(!PageTableEntry::PHYS_ADDR_MASK & !PageTableFlags::HUGE().bits()) | flags,
        ).paddr() == PageTableEntry(old_raw).paddr(),
        PageTableEntry(
            old_raw & !(!PageTableEntry::PHYS_ADDR_MASK & !PageTableFlags::HUGE().bits()) | flags,
        ).is_present(),
        forall|level: PagingLevel|
            #[trigger] PageTableEntry(old_raw).is_last(level) ==> PageTableEntry(
                old_raw & !(!PageTableEntry::PHYS_ADDR_MASK & !PageTableFlags::HUGE().bits())
                    | flags,
            ).is_last(level),
{
    lemma_page_property_flag_constants();
    let pbits_u8 = prop.flags.bits();
    let priv_bits_u8 = prop.priv_flags.bits();
    let pbits = pbits_u8 as usize;
    let priv_bits = priv_bits_u8 as usize;
    let cache_flags = if prop.cache is Writethrough {
        PageTableFlags::WRITE_THROUGH().bits()
    } else if prop.cache is Uncacheable {
        PageTableFlags::NO_CACHE().bits()
    } else {
        0usize
    };
    lemma_encode_prop_flags_matches(pbits_u8, priv_bits_u8, cache_flags);
    let new_raw = old_raw & !(!PageTableEntry::PHYS_ADDR_MASK & !PageTableFlags::HUGE().bits())
        | flags;
    lemma_x86_set_prop_decode_bits(old_raw, flags, pbits, priv_bits, cache_flags);
    lemma_x86_set_prop_preserves_entry_bits(old_raw, new_raw, flags);
    let decoded_flags = PageProperty::decode_page_flags_spec(new_raw);
    let decoded_priv_flags = PageProperty::decode_priv_flags_spec(new_raw);
    PageFlags::lemma_from_bits_bits(decoded_flags as u8);
    PrivFlags::lemma_from_bits_bits(decoded_priv_flags as u8);
    PageFlags::lemma_eq_from_bits(PageTableEntry(new_raw).prop().flags, prop.flags);
    PrivFlags::lemma_eq_from_bits(PageTableEntry(new_raw).prop().priv_flags, prop.priv_flags);
}

#[verifier::bit_vector]
proof fn lemma_x86_set_prop_preserves_entry_bits(old_raw: usize, new_raw: usize, flags: usize)
    requires
        new_raw == old_raw & !(!PageTableEntry::PHYS_ADDR_MASK & !0x80usize) | flags,
        flags & PageTableEntry::PHYS_ADDR_MASK == 0,
        flags & 0x1usize == 0x1usize,
    ensures
        (new_raw & PageTableEntry::PHYS_ADDR_MASK) == (old_raw & PageTableEntry::PHYS_ADDR_MASK),
        new_raw & 0x1usize != 0 || new_raw & 0x80usize != 0,
        old_raw & 0x80usize != 0 ==> new_raw & 0x80usize != 0,
{
}

} // verus!
  /*
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
  */
