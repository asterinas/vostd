// SPDX-License-Identifier: MPL-2.0
#![expect(dead_code)]

use vstd::prelude::*;
use vstd::vpanic;
use vstd_extra::panic::may_panic;
use vstd_extra::panic::panic_diverge;
use crate::specs::arch::MAX_PADDR;
use vstd_extra::prelude::*;

use alloc::fmt;
use core::ops::Range;

//use cfg_if::cfg_if;
pub(crate) use util::{__memcpy_fallible, __memset_fallible};
//use x86_64::{instructions::tlb, structures::paging::PhysFrame, VirtAddr};

use crate::specs::arch::PAGE_SIZE;
use crate::{
    Pod, mm::{
        Paddr, PagingConstsTrait, PagingLevel, PodOnce, Vaddr, page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags as PrivFlags}, page_table::{PageTableEntryTrait, PageTableFrag}
    }
};

mod util;

verified_bitflags::bitflags! {
    //#[derive(Pod)]
    #[repr(C)]
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
verus!{
#[verifier::ext_equal]
#[derive(Clone, Copy/*, Pod, Default*/)]
#[derive(Debug)]
#[repr(C)]
pub struct PageTableEntry(usize);

#[verus_verify]
unsafe impl Pod for PageTableEntry {}

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
        proof{ lemma_auxiliary_bit_properties(0); }
        Self(usize::default())
    }
}
}

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

verus!{

impl PageTableEntry {
    //cfg_if! {
        //if #[cfg(feature = "cvm_guest")] {
        //    const PHYS_ADDR_MASK: usize = 0x7_FFFF_FFFF_F000;
        //} else {
            const PHYS_ADDR_MASK: usize = 0xF_FFFF_FFFF_F000;
        //}
    //}
    exec const PROP_MASK: usize = !Self::PHYS_ADDR_MASK & !PageTableFlags::HUGE().bits();
}


/// Parse a bit-flag bits `val` in the representation of `from` to `to` in bits.
macro_rules! parse_flags {
    ($val:expr, $from:expr, $to:expr) => {
        ($val as usize & $from.bits() as usize) >> $from.bits().ilog2() << $to.bits().ilog2()
    };
}

impl PodOnce for PageTableEntry {}

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
        self.0 & PageTableFlags::PRESENT().bits() != 0 || self.0 & PageTableFlags::HUGE().bits() != 0
    }

    open spec fn new_page_req(paddr: Paddr, _level: PagingLevel, prop: PageProperty) -> bool {
        ! (prop.cache is Writeback || prop.cache is Writethrough || prop.cache is Uncacheable) ==> may_panic()
    }

    fn new_page(paddr: Paddr, _level: PagingLevel, prop: PageProperty) -> Self {
        let flags = PageTableFlags::HUGE().bits();
        let mut pte = Self(paddr & Self::PHYS_ADDR_MASK | flags);
        pte.set_prop(prop);
        proof{admit();}
        pte
    }

    fn new_pt(paddr: Paddr) -> (res: Self) 
    {
        
        // In x86 if it's an intermediate PTE, it's better to have the same permissions
        // as the most permissive child (to reduce hardware page walk accesses). But we
        // don't have a mechanism to keep it generic across architectures, thus just
        // setting it to be the most permissive.
        let flags = PageTableFlags::PRESENT().bits()
            | PageTableFlags::WRITABLE().bits()
            | PageTableFlags::USER().bits();
        proof{
            admit();
        }
        Self(paddr & Self::PHYS_ADDR_MASK | flags)
    }

    fn paddr(&self) -> Paddr {
        proof { self.lemma_paddr_is_page_aligned(); }
        self.0 & Self::PHYS_ADDR_MASK
    }

    fn prop(&self) -> PageProperty {
        proof {
            lemma_auxiliary_bit_properties(0);
            admit();
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
        PageProperty {
            flags: PageFlags::from_bits(flags as u8).unwrap(),
            cache,
            priv_flags: PrivFlags::from_bits(priv_flags as u8).unwrap(),
        }
    }

    open spec fn set_prop_req(self, prop: PageProperty) -> bool {
        !(prop.cache is Writeback || prop.cache is Writethrough || prop.cache is Uncacheable) ==> may_panic()
    }

    fn set_prop(&mut self, prop: PageProperty) {
        proof {
            lemma_auxiliary_bit_properties(0);
            assert(self.set_prop_req(prop));
        }
        if !self.is_present() {
            return;
        }
        let mut flags = PageTableFlags::empty().bits();
        flags |= (parse_flags!(prop.flags.bits(), PageFlags::R(), PageTableFlags::PRESENT()))
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
            flags |= parse_flags!(
                prop.priv_flags.bits(),
                PrivFlags::SHARED(),
                PageTableFlags::SHARED()
            );
        }
        match prop.cache {
            CachePolicy::Writeback => {}
            CachePolicy::Writethrough => {
                flags |= PageTableFlags::WRITE_THROUGH().bits();
            }
            CachePolicy::Uncacheable => {
                flags |= PageTableFlags::NO_CACHE().bits();
            }
            _ => { 
                //panic!("unsupported cache policy"); 
                assert(!(prop.cache is Writeback || prop.cache is Writethrough || prop.cache is Uncacheable));
                panic_diverge();
            }
        }
        proof {admit();}
        self.0 = self.0 & !Self::PROP_MASK | flags;
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
        self.as_usize() & PageTableFlags::PRESENT().bits() != 0 || self.as_usize() & PageTableFlags::HUGE().bits() != 0
    }

    closed spec fn paddr_spec(&self) -> Paddr {
        self.as_usize() & Self::PHYS_ADDR_MASK
    }

    closed spec fn prop_spec(&self) -> PageProperty {
        let flags = if self.as_usize() & (PageTableFlags::PRESENT().bits() as usize) != 0 {PageFlags::R().bits()} else {0}
            | if self.as_usize() & (PageTableFlags::WRITABLE().bits() as usize) != 0 {PageFlags::W().bits()} else {0}
            | if !self.as_usize() & (PageTableFlags::NO_EXECUTE().bits() as usize) == 0 {PageFlags::X().bits()} else {0}
            | if self.as_usize() & (PageTableFlags::ACCESSED().bits() as usize) != 0 {PageFlags::ACCESSED().bits()} else {0}
            | if self.as_usize() & (PageTableFlags::DIRTY().bits() as usize) != 0 {PageFlags::DIRTY().bits()} else {0}
            | if self.as_usize() & (PageTableFlags::HIGH_IGN1().bits() as usize) != 0 {PageFlags::AVAIL1().bits()} else {0}
            | if self.as_usize() & (PageTableFlags::HIGH_IGN2().bits() as usize) != 0 {PageFlags::AVAIL2().bits()} else {0};
        let priv_flags = if self.as_usize() & (PageTableFlags::USER().bits() as usize) != 0 {PrivFlags::USER().bits()} else {0}
            | if self.as_usize() & (PageTableFlags::GLOBAL().bits() as usize) != 0 {PrivFlags::GLOBAL().bits()} else {0};
        #[cfg(feature = "cvm_guest")]
        let priv_flags = priv_flags | if self.as_usize() & (PageTableFlags::SHARED().bits() as usize) != 0 {PrivFlags::SHARED().bits()} else {0};
        let cache = if self.as_usize() & (PageTableFlags::NO_CACHE().bits() as usize) != 0 {
            CachePolicy::Uncacheable
        } else if self.as_usize() & (PageTableFlags::WRITE_THROUGH().bits() as usize) != 0 {
            CachePolicy::Writethrough
        } else {
            CachePolicy::Writeback
        };
        PageProperty {
            flags: PageFlags::from_bits(flags as u8).unwrap(),
            cache,
            priv_flags: PrivFlags::from_bits(priv_flags as u8).unwrap(),
        }
    }

    closed spec fn new_pt_spec(paddr: Paddr) -> Self {
        let flags = PageTableFlags::PRESENT().bits()
            | PageTableFlags::WRITABLE().bits()
            | PageTableFlags::USER().bits();
        Self(paddr & Self::PHYS_ADDR_MASK | flags)
    }

    closed spec fn new_page_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        let flags = PageTableFlags::HUGE().bits();
        let pte = paddr & Self::PHYS_ADDR_MASK | flags;
        let flags = PageTableFlags::empty().bits()
            | if prop.flags.bits() & PageFlags::R().bits() != 0 {PageTableFlags::PRESENT().bits()} else {0}
            | if prop.flags.bits() & PageFlags::W().bits() != 0 {PageTableFlags::WRITABLE().bits()} else {0}
            | if !prop.flags.bits() & PageFlags::X().bits() != 0 {0} else {PageTableFlags::NO_EXECUTE().bits()}
            | if prop.flags.bits() & PageFlags::ACCESSED().bits() != 0 {PageTableFlags::ACCESSED().bits()} else {0}
            | if prop.flags.bits() & PageFlags::DIRTY().bits() != 0 {PageTableFlags::DIRTY().bits()} else {0}
            | if prop.flags.bits() & PageFlags::AVAIL1().bits() != 0 {PageTableFlags::HIGH_IGN1().bits()} else {0}
            | if prop.flags.bits() & PageFlags::AVAIL2().bits() != 0 {PageTableFlags::HIGH_IGN2().bits()} else {0}
            | if prop.priv_flags.bits() & PrivFlags::USER().bits() != 0 {PageTableFlags::USER().bits()} else {0}
            | if prop.priv_flags.bits() & PrivFlags::GLOBAL().bits() != 0 {PageTableFlags::GLOBAL().bits()} else {0};
        #[cfg(feature = "cvm_guest")]
        let flags = flags | if prop.priv_flags.bits() & PrivFlags::SHARED().bits() != 0 {PageTableFlags::SHARED().bits()} else {0};
        match prop.cache {
            CachePolicy::Writeback => {Self(pte | flags)}
            CachePolicy::Writethrough => {
                let flags = flags | PageTableFlags::WRITE_THROUGH().bits();
                Self(pte | flags)
            }
            CachePolicy::Uncacheable => {
                let flags = flags | PageTableFlags::NO_CACHE().bits();
                Self(pte | flags)
            }
            _ => arbitrary()
        }
    }

    open spec fn is_last_spec(&self, _level: PagingLevel) -> bool {
        self.as_usize() & PageTableFlags::HUGE().bits() != 0
    }
    
    closed spec fn as_usize_spec(self) -> usize {
        self.0
    }

    proof fn lemma_page_table_entry_properties()
    {
        admit();
    }

    proof fn lemma_paddr_is_page_aligned(self)
    {
        lemma_auxiliary_bit_properties(self.0);
    }
}

proof fn lemma_auxiliary_bit_properties(addr: usize)
    ensures
        0 & PageTableEntry::PHYS_ADDR_MASK == 0,
        0 & PageTableFlags::PRESENT().bits() == 0,
        0 & PageTableFlags::HUGE().bits() == 0,
        0usize % PAGE_SIZE == 0,
        0 < MAX_PADDR,
        addr % PAGE_SIZE == 0 ==> addr == (addr & !((PAGE_SIZE - 1) as usize)),
        (addr & PageTableEntry::PHYS_ADDR_MASK) % PAGE_SIZE == 0,
        addr < MAX_PADDR ==> (addr & PageTableEntry::PHYS_ADDR_MASK) < MAX_PADDR,
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
{
    lemma_usize_ilog2_to32();
    lemma_u64_ilog2_to64();
    assert(0 < MAX_PADDR) by (compute);
    assert(0usize % PAGE_SIZE == 0) by (compute);
    assert(0 & PageTableEntry::PHYS_ADDR_MASK == 0) by (compute);
    assert(0 & PageTableFlags::PRESENT().bits() == 0) by (compute);
    assert(0 & PageTableFlags::HUGE().bits() == 0) by (compute);
    assert(addr % PAGE_SIZE == 0 ==> addr == (addr & !((PAGE_SIZE - 1) as usize))) by (bit_vector);
    assert((addr & PageTableEntry::PHYS_ADDR_MASK) % PAGE_SIZE == 0) by (bit_vector);
    assert(addr < MAX_PADDR ==> (addr & PageTableEntry::PHYS_ADDR_MASK) < MAX_PADDR) by (bit_vector);
    assert(PageTableFlags::PRESENT().bits() == 0x1) by (compute);
    assert(PageTableFlags::WRITABLE().bits() == 0x2) by (compute);
    assert(PageTableFlags::USER().bits() == 0x4) by (compute);
    assert(PageTableFlags::WRITE_THROUGH().bits() == 0x8) by (compute);
    assert(PageTableFlags::NO_CACHE().bits() == 0x10) by (compute);
    assert(PageTableFlags::ACCESSED().bits() == 0x20) by (compute);
    assert(PageTableFlags::DIRTY().bits() == 0x40) by (compute);
    assert(PageTableFlags::HUGE().bits() == 0x80) by (compute);
    assert(PageTableFlags::GLOBAL().bits() == 0x100) by (compute);
    assert(PageTableFlags::HIGH_IGN1().bits() == 0x0010_0000_0000_0000) by (compute);
    assert(PageTableFlags::HIGH_IGN2().bits() == 0x0020_0000_0000_0000) by (compute);
    assert(PageTableFlags::NO_EXECUTE().bits() == 0x8000_0000_0000_0000) by (compute);
}
}

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
