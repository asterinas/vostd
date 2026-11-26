//! External specifications for the [`x86_64` crate](https://crates.io/crates/x86_64)
//! version `0.15.5` descriptor tables, segment selectors, canonical virtual
//! addresses, and privileged table/MSR instructions.
//!
//! Audited against `x86_64 0.15.5` sources (`src/lib.rs`, `src/addr.rs`,
//! `src/structures/mod.rs`, `src/structures/gdt.rs`, `src/structures/tss.rs`,
//! `src/registers/segmentation.rs`, `src/registers/model_specific.rs`,
//! `src/instructions/segmentation.rs`, `src/instructions/tables.rs`).
//!
//! Hardware instructions (`lgdt`, `load_tss`, `Star::write_raw`) and
//! raw-pointer TSS descriptor construction (`Descriptor::tss_segment_unchecked`,
//! which reads `(*tss).iomap_base` from live memory as an `unsafe` caller
//! obligation) are trusted boundaries.
use vstd::{layout::align_of, prelude::*};

use x86_64::{
    PrivilegeLevel, VirtAddr,
    instructions::tables::{lgdt, load_tss},
    registers::{
        model_specific::Star,
        segmentation::{CS, Segment},
    },
    structures::{
        DescriptorTablePointer,
        gdt::{Descriptor, SegmentSelector},
        tss::TaskStateSegment,
    },
};

verus! {

#[verifier::external_type_specification]
pub struct ExPrivilegeLevel(PrivilegeLevel);

#[verifier::external_type_specification]
pub struct ExSegmentSelector(SegmentSelector);

#[verifier::external_type_specification]
pub struct ExDescriptor(Descriptor);

#[verifier::external_type_specification]
pub struct ExDescriptorTablePointer(DescriptorTablePointer);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExVirtAddr(VirtAddr);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExTaskStateSegment(TaskStateSegment);

#[verifier::external_type_specification]
pub struct ExCS(CS);

#[verifier::external_type_specification]
pub struct ExStar(Star);

#[verifier::external_trait_specification]
pub trait ExSegment {
    type ExternalTraitSpecificationFor: Segment;

    fn get_reg() -> SegmentSelector;
}

/// Numeric encoding of an x86 protection ring (`PrivilegeLevel as u16`).
pub open spec fn privilege_level_bits(rpl: PrivilegeLevel) -> u16 {
    match rpl {
        PrivilegeLevel::Ring0 => 0u16,
        PrivilegeLevel::Ring1 => 1u16,
        PrivilegeLevel::Ring2 => 2u16,
        PrivilegeLevel::Ring3 => 3u16,
    }
}

/// Pure model of `SegmentSelector::new(index, rpl)` (`(index << 3) | (rpl as u16)`).
pub open spec fn segment_selector_new_spec(index: u16, rpl: PrivilegeLevel) -> SegmentSelector {
    SegmentSelector((index << 3u16) | privilege_level_bits(rpl))
}

/// Pure model of `SegmentSelector::index(sel)` (`sel.0 >> 3`).
pub open spec fn segment_selector_index_spec(sel: SegmentSelector) -> u16 {
    sel.0 >> 3u16
}

/// Whether `addr` is a 48-bit canonical x86_64 virtual address
/// (bits `48..64` equal bit `47`).
pub open spec fn is_canonical_vaddr(addr: u64) -> bool {
    addr < 0x0000_8000_0000_0000u64 || addr >= 0xFFFF_8000_0000_0000u64
}

/// Spec projection for the raw `u64` stored inside `VirtAddr`.
pub uninterp spec fn virt_addr_as_u64_spec(addr: VirtAddr) -> u64;

#[verifier::when_used_as_spec(segment_selector_new_spec)]
pub assume_specification[ SegmentSelector::new ](index: u16, rpl: PrivilegeLevel) -> SegmentSelector
    returns
        segment_selector_new_spec(index, rpl),
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(segment_selector_index_spec)]
pub assume_specification[ SegmentSelector::index ](sel: SegmentSelector) -> u16
    returns
        segment_selector_index_spec(sel),
    opens_invariants none
    no_unwind
;

pub assume_specification[ <SegmentSelector as PartialEq>::eq ](
    lhs: &SegmentSelector,
    rhs: &SegmentSelector,
) -> bool
    returns
        lhs.0 == rhs.0,
;

pub assume_specification[ VirtAddr::new ](addr: u64) -> (ret: VirtAddr)
    requires
        is_canonical_vaddr(addr),
    ensures
        virt_addr_as_u64_spec(ret) == addr,
    opens_invariants none
    no_unwind when is_canonical_vaddr(addr)
;

pub assume_specification[ TaskStateSegment::new ]() -> TaskStateSegment
    opens_invariants none
    no_unwind
;

pub assume_specification[ Descriptor::tss_segment_unchecked ](tss: *const TaskStateSegment) -> (ret:
    Descriptor)
    requires
        tss.addr() != 0,
        tss.addr() as nat % align_of::<TaskStateSegment>() == 0,
    ensures
        ret matches Descriptor::SystemSegment(low, high) && {
            &&& (low & 0xffffu64) >= 0x67u64
            &&& ((low >> 16u64) & 0xff_ffffu64) == ((tss.addr() as u64) & 0xff_ffffu64)
            &&& ((low >> 40u64) & 0xfu64) == 0b1001u64
            &&& (low & (1u64 << 44u64)) == 0
            &&& ((low >> 45u64) & 0x3u64) == 0
            &&& (low & (1u64 << 47u64)) != 0
            &&& ((low >> 48u64) & 0xffu64) == 0
            &&& (low >> 56u64) == (((tss.addr() as u64) >> 24u64) & 0xffu64)
            &&& high == ((tss.addr() as u64) >> 32u64)
        },
    opens_invariants none
    no_unwind when tss.addr() != 0 && tss.addr() as nat % align_of::<TaskStateSegment>() == 0
;

pub assume_specification[ lgdt ](gdt: &DescriptorTablePointer)
    requires
        virt_addr_as_u64_spec(gdt.base) != 0,
        is_canonical_vaddr(virt_addr_as_u64_spec(gdt.base)),
        gdt.limit % 8 == 7,
    opens_invariants none
    no_unwind
;

pub assume_specification[ load_tss ](sel: SegmentSelector)
    requires
        sel.index() != 0,
        (sel.0 & 0x4u16) == 0,
    opens_invariants none
    no_unwind
;

pub assume_specification[ Star::write_raw ](sysret: u16, syscall: u16)
    requires
        (sysret & 0x7u16) == 3u16,
        (sysret >> 3u16) + 2 < 8192,
        (syscall & 0x7u16) == 0u16,
        (syscall >> 3u16) != 0,
        (syscall >> 3u16) + 1 < 8192,
    opens_invariants none
    no_unwind
;

/// Relates `SegmentSelector::new(index, rpl)` to its GDT index, TI=0 bit, and RPL bits.
pub broadcast proof fn lemma_segment_selector_new(index: u16, rpl: PrivilegeLevel)
    requires
        index < 8192u16,
    ensures
        #![trigger SegmentSelector::new(index, rpl)]
        SegmentSelector::new(index, rpl).index() == index,
        (SegmentSelector::new(index, rpl).0 & 0x7u16) == privilege_level_bits(rpl),
        (SegmentSelector::new(index, rpl).0 & 0x4u16) == 0,
{
    let bits = privilege_level_bits(rpl);
    assert((((index << 3u16) | bits) >> 3u16) == index) by (bit_vector)
        requires
            index < 8192u16,
            bits <= 3u16,
    ;
    assert((((index << 3u16) | bits) & 0x7u16) == bits && (((index << 3u16) | bits) & 0x4u16) == 0)
        by (bit_vector)
        requires
            bits <= 3u16,
    ;
}

} // verus!
