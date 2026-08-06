use crate::mm::{
    Paddr, PagingConstsTrait, PagingLevel,
    page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags},
};
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd_extra::{ownership::Inv, prelude::lemma_pow2_is_pow2_to64};

use crate::specs::arch::model::ArchPagingModel;

#[path = "../../../src/arch/riscv/mm/mod.rs"]
pub mod runtime_mm;

verus! {

/// Exclusive physical-address bound represented by an Sv48 PTE's 44-bit PPN.
pub const RISCV_SV48_MAX_PADDR: usize = 0x0100_0000_0000_0000;

/// Proof-side paging constants for the Sv48 mode selected by the RISC-V runtime.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Debug, Default)]
pub struct RiscvSv48PagingConsts;

impl PagingConstsTrait for RiscvSv48PagingConsts {
    #[verifier::inline]
    open spec fn BASE_PAGE_SIZE_spec() -> usize {
        4096
    }

    fn BASE_PAGE_SIZE() -> usize {
        4096
    }

    #[verifier::inline]
    open spec fn NR_LEVELS_spec() -> PagingLevel {
        4
    }

    fn NR_LEVELS() -> PagingLevel {
        4
    }

    #[verifier::inline]
    open spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel {
        4
    }

    fn HIGHEST_TRANSLATION_LEVEL() -> PagingLevel {
        4
    }

    #[verifier::inline]
    open spec fn PTE_SIZE_spec() -> usize {
        8
    }

    fn PTE_SIZE() -> usize {
        8
    }

    #[verifier::inline]
    open spec fn ADDRESS_WIDTH_spec() -> usize {
        48
    }

    fn ADDRESS_WIDTH() -> usize {
        48
    }

    #[verifier::inline]
    open spec fn VA_SIGN_EXT_spec() -> bool {
        true
    }

    fn VA_SIGN_EXT() -> bool {
        true
    }

    proof fn lemma_paging_consts_requirements() {
        lemma_pow2_is_pow2_to64();
        lemma2_to64();
        lemma2_to64_rest();
        assert(usize::BITS == 64) by (compute);
        vstd::layout::unsigned_int_max_values();
        vstd_extra::external::ilog2::lemma_usize_pow2_ilog2(9);
        vstd_extra::external::ilog2::lemma_usize_pow2_ilog2(12);
        lemma_pow2_adds(9, 39);
    }
}

/// Paging-only RISC-V architecture instance. Address-space layout is modeled later.
pub struct RiscvPagingModel;

impl ArchPagingModel for RiscvPagingModel {
    type C = RiscvSv48PagingConsts;

    open spec fn max_paddr_spec() -> Paddr {
        RISCV_SV48_MAX_PADDR
    }

    proof fn lemma_paging_model_requirements() {
        RiscvSv48PagingConsts::lemma_paging_consts_requirements();
        assert(0 < RISCV_SV48_MAX_PADDR) by (compute_only);
        assert(4096 <= RISCV_SV48_MAX_PADDR) by (compute_only);
        assert(RISCV_SV48_MAX_PADDR % 4096 == 0) by (compute_only);
    }
}

/// A proof model of the architectural bits in a RISC-V Sv48 page-table entry.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct RiscvPteModel {
    pub raw: usize,
}

impl RiscvPteModel {
    pub const VALID: usize = 1 << 0;

    pub const READABLE: usize = 1 << 1;

    pub const WRITABLE: usize = 1 << 2;

    pub const EXECUTABLE: usize = 1 << 3;

    pub const USER: usize = 1 << 4;

    pub const GLOBAL: usize = 1 << 5;

    pub const ACCESSED: usize = 1 << 6;

    pub const DIRTY: usize = 1 << 7;

    pub const RSW1: usize = 1 << 8;

    pub const RSW2: usize = 1 << 9;

    pub const PBMT_IO: usize = 1 << 62;

    pub const PHYS_ADDR_MASK: usize = 0x003F_FFFF_FFFF_FC00;

    pub open spec fn paddr_bits(paddr: Paddr) -> usize {
        (paddr >> 12) << 10
    }

    pub open spec fn paddr_from_raw_spec(raw: usize) -> Paddr {
        ((raw & Self::PHYS_ADDR_MASK) >> 10) << 12
    }

    pub open spec fn paddr_spec(self) -> Paddr {
        Self::paddr_from_raw_spec(self.raw)
    }

    pub open spec fn is_present_spec(self) -> bool {
        self.raw & Self::VALID != 0
    }

    pub open spec fn is_last_spec(self, _level: PagingLevel) -> bool {
        self.raw & (Self::READABLE | Self::WRITABLE | Self::EXECUTABLE) != 0
    }

    pub open spec fn encode_page_flags_spec(prop: PageProperty) -> usize {
        (if prop.flags.bits() & 0x01u8 != 0 {
            Self::READABLE
        } else {
            0
        }) | (if prop.flags.bits() & 0x02u8 != 0 {
            Self::WRITABLE
        } else {
            0
        }) | (if prop.flags.bits() & 0x04u8 != 0 {
            Self::EXECUTABLE
        } else {
            0
        }) | (if prop.flags.bits() & 0x08u8 != 0 {
            Self::ACCESSED
        } else {
            0
        }) | (if prop.flags.bits() & 0x10u8 != 0 {
            Self::DIRTY
        } else {
            0
        }) | (if prop.flags.bits() & 0x40u8 != 0 {
            Self::RSW1
        } else {
            0
        }) | (if prop.flags.bits() & 0x80u8 != 0 {
            Self::RSW2
        } else {
            0
        })
    }

    pub open spec fn encode_priv_flags_spec(prop: PageProperty) -> usize {
        (if prop.priv_flags.bits() & 0x01u8 != 0 {
            Self::USER
        } else {
            0
        }) | (if prop.priv_flags.bits() & 0x02u8 != 0 {
            Self::GLOBAL
        } else {
            0
        })
    }

    pub open spec fn encode_cache_spec(prop: PageProperty) -> usize {
        if prop.cache is Uncacheable {
            Self::PBMT_IO
        } else {
            0
        }
    }

    pub open spec fn property_bits_from_parts_spec(
        flags: u8,
        priv_flags: u8,
        cache: CachePolicy,
    ) -> usize {
        Self::VALID | (if flags & 0x01u8 != 0 {
            Self::READABLE
        } else {
            0
        }) | (if flags & 0x02u8 != 0 {
            Self::WRITABLE
        } else {
            0
        }) | (if flags & 0x04u8 != 0 {
            Self::EXECUTABLE
        } else {
            0
        }) | (if flags & 0x08u8 != 0 {
            Self::ACCESSED
        } else {
            0
        }) | (if flags & 0x10u8 != 0 {
            Self::DIRTY
        } else {
            0
        }) | (if flags & 0x40u8 != 0 {
            Self::RSW1
        } else {
            0
        }) | (if flags & 0x80u8 != 0 {
            Self::RSW2
        } else {
            0
        }) | (if priv_flags & 0x01u8 != 0 {
            Self::USER
        } else {
            0
        }) | (if priv_flags & 0x02u8 != 0 {
            Self::GLOBAL
        } else {
            0
        }) | (if cache is Uncacheable {
            Self::PBMT_IO
        } else {
            0
        })
    }

    pub open spec fn property_bits_spec(prop: PageProperty) -> usize {
        Self::property_bits_from_parts_spec(prop.flags.bits(), prop.priv_flags.bits(), prop.cache)
    }

    pub open spec fn decode_page_flags_spec(raw: usize) -> u8 {
        (if raw & Self::READABLE != 0 {
            0x01u8
        } else {
            0
        }) | (if raw & Self::WRITABLE != 0 {
            0x02u8
        } else {
            0
        }) | (if raw & Self::EXECUTABLE != 0 {
            0x04u8
        } else {
            0
        }) | (if raw & Self::ACCESSED != 0 {
            0x08u8
        } else {
            0
        }) | (if raw & Self::DIRTY != 0 {
            0x10u8
        } else {
            0
        }) | (if raw & Self::RSW1 != 0 {
            0x40u8
        } else {
            0
        }) | (if raw & Self::RSW2 != 0 {
            0x80u8
        } else {
            0
        })
    }

    pub open spec fn decode_priv_flags_spec(raw: usize) -> u8 {
        (if raw & Self::USER != 0 {
            0x01u8
        } else {
            0
        }) | (if raw & Self::GLOBAL != 0 {
            0x02u8
        } else {
            0
        })
    }

    pub open spec fn decode_cache_spec(raw: usize) -> CachePolicy {
        if raw & Self::PBMT_IO != 0 {
            CachePolicy::Uncacheable
        } else {
            CachePolicy::Writeback
        }
    }

    pub open spec fn prop_spec(self) -> PageProperty {
        PageProperty {
            flags: PageFlags::from_bits(Self::decode_page_flags_spec(self.raw))->0,
            cache: Self::decode_cache_spec(self.raw),
            priv_flags: PrivilegedPageFlags::from_bits(Self::decode_priv_flags_spec(self.raw))->0,
        }
    }

    pub open spec fn prop_from_raw_spec(raw: usize) -> PageProperty {
        Self { raw }.prop_spec()
    }

    pub open spec fn set_prop_req(prop: PageProperty) -> bool {
        &&& prop.inv()
        &&& (prop.cache is Writeback || prop.cache is Uncacheable)
        &&& prop.flags.bits() & 0x07u8 != 0
    }

    pub open spec fn new_page_req(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> bool {
        &&& 1 <= level <= RiscvSv48PagingConsts::HIGHEST_TRANSLATION_LEVEL()
        &&& paddr % RiscvSv48PagingConsts::BASE_PAGE_SIZE() == 0
        &&& paddr < RISCV_SV48_MAX_PADDR
        &&& Self::set_prop_req(prop)
        &&& (level == 1 || prop.flags.bits() & 0x07u8 != 0)
    }

    pub open spec fn new_absent_spec() -> Self {
        Self { raw: 0 }
    }

    pub open spec fn new_pt_spec(paddr: Paddr) -> Self {
        Self { raw: Self::paddr_bits(paddr) | Self::VALID }
    }

    pub open spec fn new_page_spec(paddr: Paddr, prop: PageProperty) -> Self {
        Self { raw: Self::paddr_bits(paddr) | Self::property_bits_spec(prop) }
    }

    pub open spec fn set_prop_spec(self, prop: PageProperty) -> Self {
        if self.is_present_spec() {
            Self { raw: (self.raw & Self::PHYS_ADDR_MASK) | Self::property_bits_spec(prop) }
        } else {
            self
        }
    }

    pub open spec fn set_prop_raw_spec(old_raw: usize, prop: PageProperty) -> usize {
        Self { raw: old_raw }.set_prop_spec(prop).raw
    }
}

#[verifier::bit_vector]
proof fn lemma_riscv_paddr_encoding_bv(paddr: usize)
    requires
        paddr % 4096usize == 0,
        paddr < RISCV_SV48_MAX_PADDR,
    ensures
        ((((paddr >> 12) << 10) & RiscvPteModel::PHYS_ADDR_MASK) >> 10) << 12 == paddr,
        ((paddr >> 12) << 10) & (RiscvPteModel::VALID | RiscvPteModel::READABLE
            | RiscvPteModel::WRITABLE | RiscvPteModel::EXECUTABLE) == 0,
{
}

/// PPN encoding is lossless for aligned physical addresses representable by Sv48.
pub proof fn lemma_riscv_paddr_roundtrip(paddr: Paddr)
    requires
        paddr % 4096 == 0,
        paddr < RISCV_SV48_MAX_PADDR,
    ensures
        RiscvPteModel::new_pt_spec(paddr).paddr_spec() == paddr,
{
    lemma_riscv_paddr_encoding_bv(paddr);
    assert(RISCV_SV48_MAX_PADDR == 0x0100_0000_0000_0000usize) by (compute_only);
    assert(paddr < 0x0100_0000_0000_0000usize);
    assert(RiscvPteModel::new_pt_spec(paddr).raw == ((paddr >> 12) << 10) | 1usize)
        by (compute_only);
    assert(RiscvPteModel::new_pt_spec(paddr).paddr_spec() == paddr) by {
        assert(((((paddr >> 12) << 10) | 1usize) & RiscvPteModel::PHYS_ADDR_MASK) == (((paddr >> 12)
            << 10) & RiscvPteModel::PHYS_ADDR_MASK)) by (bit_vector);
    }
}

/// A child-table PTE is valid, has no RWX bits, and is never a leaf.
pub proof fn lemma_riscv_new_pt_shape(paddr: Paddr)
    requires
        paddr % 4096 == 0,
        paddr < RISCV_SV48_MAX_PADDR,
    ensures
        RiscvPteModel::new_pt_spec(paddr).is_present_spec(),
        forall|level: PagingLevel| !RiscvPteModel::new_pt_spec(paddr).is_last_spec(level),
{
    lemma_riscv_paddr_encoding_bv(paddr);
    assert(RISCV_SV48_MAX_PADDR == 0x0100_0000_0000_0000usize) by (compute_only);
    assert(paddr < 0x0100_0000_0000_0000usize);
    assert(RiscvPteModel::new_pt_spec(paddr).is_present_spec()) by (bit_vector);
    assert(RiscvPteModel::new_pt_spec(paddr).raw == ((paddr >> 12) << 10) | 1usize)
        by (compute_only);
    assert(((paddr >> 12) << 10) & (RiscvPteModel::READABLE | RiscvPteModel::WRITABLE
        | RiscvPteModel::EXECUTABLE) == 0) by (bit_vector)
        requires
            paddr < 0x0100_0000_0000_0000usize,
            paddr % 4096usize == 0,
    ;
    assert(RiscvPteModel::new_pt_spec(paddr).raw & (RiscvPteModel::READABLE
        | RiscvPteModel::WRITABLE | RiscvPteModel::EXECUTABLE) == 0) by (bit_vector)
        requires
            RiscvPteModel::new_pt_spec(paddr).raw == ((paddr >> 12) << 10) | 1usize,
            ((paddr >> 12) << 10) & (RiscvPteModel::READABLE | RiscvPteModel::WRITABLE
                | RiscvPteModel::EXECUTABLE) == 0,
    ;
    assert forall|level: PagingLevel| !RiscvPteModel::new_pt_spec(paddr).is_last_spec(level) by {
        assert(!RiscvPteModel::new_pt_spec(paddr).is_last_spec(level));
    }
}

} // verus!
