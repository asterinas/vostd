//! External specifications for the [`x86` crate](https://crates.io/crates/x86)
//! constants and MSR accessors. Constant values are trusted to match
//! the crate sources; the original constants are re-exported below. Also models the
//! [`x86_64` crate](https://crates.io/crates/x86_64) MSR accessors, descriptor tables,
//! segment selectors, canonical virtual addresses, and `lgdt`/`load_tss`/`Star` APIs.
use vstd::prelude::*;

use core::arch::x86_64::CpuidResult;
use x86::cpuid::CpuIdResult;

pub use x86::{
    apic::xapic::{
        XAPIC_EOI, XAPIC_ESR, XAPIC_ICR0, XAPIC_ICR1, XAPIC_ID, XAPIC_LVT_TIMER, XAPIC_SVR,
        XAPIC_TIMER_CURRENT_COUNT, XAPIC_TIMER_DIV_CONF, XAPIC_TIMER_INIT_COUNT, XAPIC_VERSION,
    },
    msr::{
        IA32_APIC_BASE, IA32_X2APIC_APICID, IA32_X2APIC_CUR_COUNT, IA32_X2APIC_DIV_CONF,
        IA32_X2APIC_EOI, IA32_X2APIC_ESR, IA32_X2APIC_ICR, IA32_X2APIC_INIT_COUNT,
        IA32_X2APIC_LVT_TIMER, IA32_X2APIC_SIVR, IA32_X2APIC_VERSION,
    },
};
use x86_64::{
    PrivilegeLevel, VirtAddr,
    instructions::tables::{lgdt, load_tss},
    registers::{
        model_specific::{Msr, Star},
        segmentation::{CS, Segment},
    },
    structures::{
        DescriptorTablePointer,
        gdt::{Descriptor, SegmentSelector},
        tss::TaskStateSegment,
    },
};

verus! {

/// Exposes the four u32 result registers.
#[verifier::external_type_specification]
pub struct ExCpuIdResult(CpuIdResult);

/// Exposes the four u32 result registers of the `core::arch` CPUID intrinsics.
#[verifier::external_type_specification]
pub struct ExCpuidResult(CpuidResult);

pub assume_specification[ x86::apic::xapic::XAPIC_ID ] -> u32
    returns
        0x020u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_VERSION ] -> u32
    returns
        0x030u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_EOI ] -> u32
    returns
        0x0B0u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_SVR ] -> u32
    returns
        0x0F0u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_ESR ] -> u32
    returns
        0x280u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_ICR0 ] -> u32
    returns
        0x300u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_ICR1 ] -> u32
    returns
        0x310u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_LVT_TIMER ] -> u32
    returns
        0x320u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_TIMER_INIT_COUNT ] -> u32
    returns
        0x380u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_TIMER_CURRENT_COUNT ] -> u32
    returns
        0x390u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_TIMER_DIV_CONF ] -> u32
    returns
        0x3E0u32,
;

pub assume_specification[ x86::msr::IA32_APIC_BASE ] -> u32
    returns
        0x1bu32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_APICID ] -> u32
    returns
        0x802u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_VERSION ] -> u32
    returns
        0x803u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_EOI ] -> u32
    returns
        0x80bu32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_SIVR ] -> u32
    returns
        0x80fu32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_ESR ] -> u32
    returns
        0x828u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_ICR ] -> u32
    returns
        0x830u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_LVT_TIMER ] -> u32
    returns
        0x832u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_INIT_COUNT ] -> u32
    returns
        0x838u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_CUR_COUNT ] -> u32
    returns
        0x839u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_DIV_CONF ] -> u32
    returns
        0x83eu32,
;

/// [x86::msr::rdmsr](https://docs.rs/x86/0.52.0/x86/msr/fn.rdmsr.html) returns an unconstrained value.
pub assume_specification[ x86::msr::rdmsr ](msr: u32) -> u64
    opens_invariants none
    no_unwind
;

/// [x86::msr::wrmsr](https://docs.rs/x86/0.52.0/x86/msr/fn.wrmsr.html).
pub assume_specification[ x86::msr::wrmsr ](msr: u32, value: u64)
    opens_invariants none
    no_unwind
;

/// Opaque external wrapper for the x86_64 crate's MSR handle.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExMsr(Msr);

/// [`Msr::new`](https://docs.rs/x86_64/0.15.5/x86_64/registers/model_specific/struct.Msr.html#method.new).
pub assume_specification[ Msr::new ](reg: u32) -> Msr
    opens_invariants none
    no_unwind
;

/// [`Msr::read`](https://docs.rs/x86_64/0.15.5/x86_64/registers/model_specific/struct.Msr.html#method.read)
/// returns an unconstrained value.
pub assume_specification[ Msr::read ](msr: &Msr) -> u64
    opens_invariants none
    no_unwind
;

/// [`Msr::write`](https://docs.rs/x86_64/0.15.5/x86_64/registers/model_specific/struct.Msr.html#method.write).
pub assume_specification[ Msr::write ](msr: &mut Msr, value: u64)
    opens_invariants none
    no_unwind
;

pub const X86_CANONICAL_LOWER_END: u64 = 0x0000_8000_0000_0000;

pub const X86_CANONICAL_UPPER_START: u64 = 0xffff_8000_0000_0000;

/// Whether `addr` is a canonical 48-bit virtual address.
pub open spec fn is_canonical_vaddr(addr: u64) -> bool {
    addr < X86_CANONICAL_LOWER_END || addr >= X86_CANONICAL_UPPER_START
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExVirtAddr(VirtAddr);

pub uninterp spec fn virt_addr_as_u64(addr: VirtAddr) -> u64;

/// [`VirtAddr::new`](https://docs.rs/x86_64/0.15.5/x86_64/addr/struct.VirtAddr.html#method.new).
pub assume_specification[ VirtAddr::new ](addr: u64) -> (ret: VirtAddr)
    requires
        is_canonical_vaddr(addr),
    ensures
        virt_addr_as_u64(ret) == addr,
    opens_invariants none
    no_unwind when is_canonical_vaddr(addr)
;

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
pub struct ExTaskStateSegment(TaskStateSegment);

global layout TaskStateSegment is size == 0x68, align == 4;

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

/// [`SegmentSelector::new`](https://docs.rs/x86_64/0.15.5/x86_64/structures/gdt/struct.SegmentSelector.html#method.new).
#[verifier::when_used_as_spec(segment_selector_new_spec)]
pub assume_specification[ SegmentSelector::new ](index: u16, rpl: PrivilegeLevel) -> SegmentSelector
    returns
        segment_selector_new_spec(index, rpl),
    opens_invariants none
    no_unwind
;

/// [`SegmentSelector::index`](https://docs.rs/x86_64/0.15.5/x86_64/structures/gdt/struct.SegmentSelector.html#method.index).
#[verifier::when_used_as_spec(segment_selector_index_spec)]
pub assume_specification[ SegmentSelector::index ](sel: SegmentSelector) -> u16
    returns
        segment_selector_index_spec(sel),
    opens_invariants none
    no_unwind
;

/// Derived `PartialEq` for [`SegmentSelector`](https://docs.rs/x86_64/0.15.5/x86_64/structures/gdt/struct.SegmentSelector.html).
pub assume_specification[ <SegmentSelector as PartialEq>::eq ](
    lhs: &SegmentSelector,
    rhs: &SegmentSelector,
) -> bool
    returns
        lhs.0 == rhs.0,
;

/// [`TaskStateSegment::new`](https://docs.rs/x86_64/0.15.5/x86_64/structures/tss/struct.TaskStateSegment.html#method.new).
pub assume_specification[ TaskStateSegment::new ]() -> TaskStateSegment
    opens_invariants none
    no_unwind
;

/// [`Descriptor::tss_segment_unchecked`](https://docs.rs/x86_64/0.15.5/x86_64/structures/gdt/enum.Descriptor.html#method.tss_segment_unchecked).
/// Trusted boundary: live-memory dereference of `(*tss).iomap_base` and `'static` lifetime remain unmodeled unsafe caller obligations.
pub assume_specification[ Descriptor::tss_segment_unchecked ](tss: *const TaskStateSegment) -> (ret:
    Descriptor)
    requires
        tss.addr() != 0,
        tss.addr() % align_of::<TaskStateSegment>() == 0,
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
    no_unwind when tss.addr() != 0 && tss.addr() % align_of::<TaskStateSegment>() == 0
;

/// [`lgdt`](https://docs.rs/x86_64/0.15.5/x86_64/instructions/tables/fn.lgdt.html).
/// Requires clauses encode the Intel SDM `LGDT` canonical base and integral 8-byte descriptor limit.
pub assume_specification[ lgdt ](gdt: &DescriptorTablePointer)
    requires
        is_canonical_vaddr(virt_addr_as_u64(gdt.base)),
        gdt.limit % 8 == 7,
    opens_invariants none
    no_unwind
;

/// [`load_tss`](https://docs.rs/x86_64/0.15.5/x86_64/instructions/tables/fn.load_tss.html).
/// Requires clauses encode the Intel SDM `LTR` non-null GDT selector constraint (index != 0, TI = 0).
pub assume_specification[ load_tss ](sel: SegmentSelector)
    requires
        sel.index() != 0,
        (sel.0 & 0x4u16) == 0,
    opens_invariants none
    no_unwind
;

/// [`Star::write_raw`](https://docs.rs/x86_64/0.15.5/x86_64/registers/model_specific/struct.Star.html#method.write_raw).
/// Requires clauses encode the Intel SDM `SYSRET`/`SYSCALL` GDT selector layout and RPL obligations.
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

/// Establishes the compiler-checked size and alignment of [`TaskStateSegment`].
pub broadcast proof fn lemma_tss_layout()
    ensures
        #![trigger vstd::layout::size_of::<TaskStateSegment>()]
        #![trigger vstd::layout::align_of::<TaskStateSegment>()]
        vstd::layout::size_of::<TaskStateSegment>() == 0x68,
        vstd::layout::align_of::<TaskStateSegment>() == 4,
{
    broadcast use VERUS_layout_of_TaskStateSegment;

}

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
