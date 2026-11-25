//! External specifications for the [`x86` crate](https://crates.io/crates/x86)
//! constants and MSR accessors. Constant values are trusted to match
//! the crate sources; the original constants are re-exported below. Also models the
//! [`x86_64` crate](https://crates.io/crates/x86_64) MSR accessors.
//!
//! CPU-bound register contracts require a caller-supplied `X86CpuRegisterOwner`.
//! Owner construction and binding to the executing CPU are deferred to a
//! `vstd_extra`-internal bootstrap boundary.
//! spin::Once publication and reads are trusted native operations. Cell identity,
//! witness duplication and agreement are checked; OnceImpl is a different
//! runtime protocol and does not model spin::Once's waiting or poisoning behavior.
use vstd::{prelude::*, resource::Loc};

use crate::{resource::ghost_resource::excl::ExclusiveGhost, resource_invariant::ValueInvariant};

use core::arch::x86_64::CpuidResult;
use spin::once::Once as SpinOnce;
use x86::cpuid::{CpuId, CpuIdResult, FeatureInfo};
use x86_64::registers::{
    control::{Cr0, Cr0Flags, Cr4, Cr4Flags},
    model_specific::{Efer, EferFlags},
    xcontrol::{XCr0, XCr0Flags},
};

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
use x86_64::registers::model_specific::Msr;

mod fpu_once_value {
    use vstd::prelude::*;

    use super::FeatureInfo;

    verus! {

pub trait Sealed {

}

impl Sealed for FeatureInfo {

}

impl Sealed for u64 {

}

impl Sealed for usize {

}

} // verus!
}

verus! {

/// Exposes the four u32 result registers.
#[verifier::external_type_specification]
pub struct ExCpuIdResult(CpuIdResult);

/// Exposes the four u32 result registers of the `core::arch` CPUID intrinsics.
#[verifier::external_type_specification]
pub struct ExCpuidResult(CpuidResult);

// x86_64 0.15.5 and bitflags 2.9.1: these wrappers preserve unknown flag bits.
macro_rules! register_flag_contracts {
    ($external:ident, $flags:ty, $bits:ident, $or:ident) => { verus! {
        #[verifier::external_type_specification]
        #[verifier::external_body]
        pub struct $external($flags);
        pub uninterp spec fn $bits(flags: $flags) -> u64;
        pub assume_specification[ <$flags>::bits ](flags: &$flags) -> u64
            returns $bits(*flags),
            opens_invariants none
            no_unwind
        ;
        // Foreign BitOrSpecImpl cannot be implemented here under Rust's orphan rule.
        #[inline]
        #[verifier::external_body]
        pub fn $or(left: $flags, right: $flags) -> (r: $flags)
            ensures $bits(r) == $bits(left) | $bits(right),
            opens_invariants none
            no_unwind
        { left | right }
    }};
}

register_flag_contracts!(ExCr0Flags, Cr0Flags, cr0_bits, cr0_or);

register_flag_contracts!(ExCr4Flags, Cr4Flags, cr4_bits, cr4_or);

register_flag_contracts!(ExXCr0Flags, XCr0Flags, xcr0_bits, xcr0_or);

macro_rules! register_or_assign_contract {
    ($flags:ty, $bits:ident, $assign:ident) => { verus! {
        #[inline]
        #[verifier::external_body]
        pub fn $assign(left: &mut $flags, right: $flags)
            ensures $bits(*final(left)) == $bits(*old(left)) | $bits(right),
            opens_invariants none
            no_unwind
        { *left |= right; }
    }};
}

register_or_assign_contract!(Cr4Flags, cr4_bits, cr4_or_assign);

register_or_assign_contract!(XCr0Flags, xcr0_bits, xcr0_or_assign);

// Typed external constants are exec-only in Verus; expose their bits at an exec call.
macro_rules! register_flag_constant {
    ($flags:ty, $name:ident, $bits:ident, $value:expr, $get:ident) => { verus! {
        #[inline]
        #[verifier::external_body]
        pub fn $get() -> (r: $flags)
            ensures $bits(r) == $value,
            opens_invariants none
            no_unwind
        { <$flags>::$name }
    }};
}

register_flag_constant!(Cr0Flags, TASK_SWITCHED, cr0_bits, 8u64, cr0_task_switched);

register_flag_constant!(Cr0Flags, EMULATE_COPROCESSOR, cr0_bits, 4u64, cr0_emulate_coprocessor);

register_flag_constant!(Cr4Flags, FSGSBASE, cr4_bits, 0x10000u64, cr4_fsgsbase);

register_flag_constant!(Cr4Flags, OSXSAVE, cr4_bits, 0x40000u64, cr4_osxsave);

register_flag_constant!(Cr4Flags, OSFXSR, cr4_bits, 0x200u64, cr4_osfxsr);

register_flag_constant!(Cr4Flags, OSXMMEXCPT_ENABLE, cr4_bits, 0x400u64, cr4_osxmmexcpt);

register_flag_constant!(Cr4Flags, PAGE_GLOBAL, cr4_bits, 0x80u64, cr4_page_global);

register_flag_constant!(XCr0Flags, SSE, xcr0_bits, 2u64, xcr0_sse);

register_flag_constant!(XCr0Flags, AVX, xcr0_bits, 4u64, xcr0_avx);

register_flag_constant!(XCr0Flags, OPMASK, xcr0_bits, 0x20u64, xcr0_opmask);

register_flag_constant!(XCr0Flags, ZMM_HI256, xcr0_bits, 0x40u64, xcr0_zmm_hi256);

register_flag_constant!(XCr0Flags, HI16_ZMM, xcr0_bits, 0x80u64, xcr0_hi16_zmm);

pub assume_specification[ Cr0Flags::remove ](flags: &mut Cr0Flags, removed: Cr0Flags)
    ensures
        cr0_bits(*final(flags)) == cr0_bits(*old(flags)) & !cr0_bits(removed),
    opens_invariants none
    no_unwind
;

/// Current-CPU configuration for CPU-bound register contracts.
pub ghost struct X86CpuSnapshot {
    pub cpu: nat,
    pub privileged: bool,
    pub pinned: bool,
    pub cr0: u64,
    pub cr4: u64,
    pub efer: u64,
    pub xcr0: u64,
    pub fpu: bool,
    pub xsave: bool,
    pub fsgsbase: bool,
    pub fxsr: bool,
    pub sse: bool,
    pub pge: bool,
    pub nx: bool,
    pub user_xstates: u64,
    pub supervisor_xstates: u64,
    pub max_basic_leaf: u32,
    pub xsave_size_for: spec_fn(u64) -> u32,
    pub x87_control: u16,
    pub x87_status: u16,
    pub x87_tag: u16,
}

/// Exclusive current-CPU authority required by the register contracts.
/// Construction and startup/scheduler binding remain deferred.
pub tracked struct X86CpuRegisterOwner {
    ghost snapshot: X86CpuSnapshot,
}

#[verifier::external]
impl !Send for X86CpuRegisterOwner {

}

#[verifier::external]
impl !Sync for X86CpuRegisterOwner {

}

impl View for X86CpuRegisterOwner {
    type V = X86CpuSnapshot;

    closed spec fn view(&self) -> X86CpuSnapshot {
        self.snapshot
    }
}

impl X86CpuRegisterOwner {
    pub open spec fn kernel_cpu(&self) -> bool {
        self@.privileged && self@.pinned
    }

    pub open spec fn xcr0_readable(&self) -> bool {
        self.kernel_cpu() && self@.xsave && self@.cr4 & 0x40000u64 != 0
    }
}

pub const XCR0_KNOWN_MASK: u64 = 0x40000000000002ff;

pub const CR0_KNOWN_MASK: u64 = 0xe005003f;

pub const CR4_KNOWN_MASK: u64 = 0x1ff7fff;

#[verifier::external_body]
pub fn read_feature_info(Tracked(cpu): Tracked<&X86CpuRegisterOwner>) -> (r: FeatureInfo)
    requires
        cpu.kernel_cpu(),
        cpu@.max_basic_leaf >= 1,
    ensures
        cpu@.xsave == (feature_info_ecx(r) & (1u32 << 26) != 0),
        cpu@.fpu == (feature_info_edx(r) & 1u32 != 0),
    opens_invariants none
    no_unwind when cpu.kernel_cpu() && cpu@.max_basic_leaf >= 1
{
    CpuId::new().get_feature_info().unwrap()
}

#[verifier::external_body]
pub fn read_enabled_xsave_size(Tracked(cpu): Tracked<&X86CpuRegisterOwner>) -> usize
    requires
        cpu.kernel_cpu(),
        cpu@.xsave,
        cpu@.max_basic_leaf >= 0xd,
    returns
        (cpu@.xsave_size_for)(cpu@.xcr0) as usize,
    opens_invariants none
    no_unwind when cpu.kernel_cpu() && cpu@.xsave && cpu@.max_basic_leaf >= 0xd
{
    CpuId::new().get_extended_state_info().unwrap().xsave_area_size_enabled_features() as usize
}

/// Wrapper signatures carry linear CPU authority; assume_specification requires
/// the original Rust signature exactly and cannot add that authority parameter.
#[verifier::external_body]
pub fn read_cr0(Tracked(cpu): Tracked<&X86CpuRegisterOwner>) -> (r: Cr0Flags)
    requires
        cpu.kernel_cpu(),
    ensures
        cr0_bits(r) == cpu@.cr0 & CR0_KNOWN_MASK,
    opens_invariants none
    no_unwind
{
    Cr0::read()
}

#[verifier::external_body]
pub fn read_cr4(Tracked(cpu): Tracked<&X86CpuRegisterOwner>) -> (r: Cr4Flags)
    requires
        cpu.kernel_cpu(),
    ensures
        cr4_bits(r) == cpu@.cr4 & CR4_KNOWN_MASK,
    opens_invariants none
    no_unwind
{
    Cr4::read()
}

#[verifier::external_body]
pub fn read_xcr0(Tracked(cpu): Tracked<&X86CpuRegisterOwner>) -> (r: XCr0Flags)
    requires
        cpu.xcr0_readable(),
    ensures
        xcr0_bits(r) == cpu@.xcr0 & XCR0_KNOWN_MASK,
    opens_invariants none
    no_unwind
{
    XCr0::read()
}

/// Narrow write contract for the original TS/EM-clearing operation only.
#[verifier::external_body]
pub fn clear_cr0_fpu_flags(flags: Cr0Flags, Tracked(cpu): Tracked<&mut X86CpuRegisterOwner>)
    requires
        old(cpu).kernel_cpu(),
        cr0_bits(flags) == (old(cpu)@.cr0 & CR0_KNOWN_MASK) & !12u64,
    ensures
        final(cpu)@ == (X86CpuSnapshot { cr0: old(cpu)@.cr0 & !12u64, ..old(cpu)@ }),
    opens_invariants none
    no_unwind
{
    unsafe {
        Cr0::write(flags);
    }
}

/// Only the five enable bits used by enable_cpu_features are changed.
#[verifier::external_body]
pub fn enable_cr4_flags(flags: Cr4Flags, Tracked(cpu): Tracked<&mut X86CpuRegisterOwner>)
    requires
        old(cpu).kernel_cpu(),
        old(cpu)@.xsave && old(cpu)@.fsgsbase && old(cpu)@.fxsr && old(cpu)@.sse && old(cpu)@.pge,
        cr4_bits(flags) == (old(cpu)@.cr4 & CR4_KNOWN_MASK) | 0x50680u64,
    ensures
        final(cpu)@ == (X86CpuSnapshot { cr4: old(cpu)@.cr4 | 0x50680u64, ..old(cpu)@ }),
    opens_invariants none
    no_unwind
{
    unsafe {
        Cr4::write(flags);
    }
}

pub open spec fn xcr0_flag_groups_valid(bits: u64) -> bool {
    &&& bits & 1u64 != 0
    &&& (bits & 4u64 != 0 ==> bits & 2u64 != 0)
    &&& (bits & 0x18u64 == 0 || bits & 0x18u64 == 0x18u64)
    &&& (bits & 0xe0u64 == 0 || (bits & 0xe0u64 == 0xe0u64 && bits & 4u64 != 0))
}

#[verifier::external_body]
pub fn write_xcr0(flags: XCr0Flags, Tracked(cpu): Tracked<&mut X86CpuRegisterOwner>)
    requires
        old(cpu).xcr0_readable(),
        xcr0_bits(flags) & !XCR0_KNOWN_MASK == 0,
        xcr0_flag_groups_valid(xcr0_bits(flags)),
        ((old(cpu)@.xcr0 & !XCR0_KNOWN_MASK) | xcr0_bits(flags)) & !old(cpu)@.user_xstates == 0,
        xcr0_bits(flags) & !0xe6u64 == (old(cpu)@.xcr0 & XCR0_KNOWN_MASK) & !0xe6u64,
    ensures
        final(cpu)@ == (X86CpuSnapshot {
            xcr0: (old(cpu)@.xcr0 & !XCR0_KNOWN_MASK) | xcr0_bits(flags),
            ..old(cpu)@
        }),
    opens_invariants none
    no_unwind when xcr0_flag_groups_valid(xcr0_bits(flags))
{
    unsafe {
        XCr0::write(flags);
    }
}

#[verifier::external_body]
pub fn enable_nxe(Tracked(cpu): Tracked<&mut X86CpuRegisterOwner>)
    requires
        old(cpu).kernel_cpu(),
        old(cpu)@.nx,
    ensures
        final(cpu)@ == (X86CpuSnapshot { efer: old(cpu)@.efer | 0x800u64, ..old(cpu)@ }),
    opens_invariants none
    no_unwind
{
    unsafe {
        Efer::update(|efer| *efer |= EferFlags::NO_EXECUTE_ENABLE);
    }
}

#[verifier::external_body]
pub fn initialize_x87(Tracked(cpu): Tracked<&mut X86CpuRegisterOwner>)
    requires
        old(cpu).kernel_cpu(),
        old(cpu)@.fpu,
        old(cpu)@.cr0 & 12u64 == 0,
    ensures
        final(cpu)@ == (X86CpuSnapshot {
            x87_control: 0x037f,
            x87_status: 0,
            x87_tag: 0xffff,
            ..old(cpu)@
        }),
    opens_invariants none
    no_unwind
{
    unsafe {
        core::arch::asm!("fninit");
    }
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFeatureInfo(FeatureInfo);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(R)]
pub struct ExSpinOnce<T, R>(SpinOnce<T, R>);

#[verifier::external_type_specification]
pub struct ExSpin(spin::relax::Spin);

pub assume_specification<T, R>[ SpinOnce::<T, R>::new ]() -> SpinOnce<T, R>
    opens_invariants none
    no_unwind
;

/// The ECX/EDX feature words captured in this FeatureInfo value.
pub uninterp spec fn feature_info_ecx(info: FeatureInfo) -> u32;

pub uninterp spec fn feature_info_edx(info: FeatureInfo) -> u32;

pub assume_specification[ FeatureInfo::has_xsave ](info: &FeatureInfo) -> bool
    returns
        feature_info_ecx(*info) & (1u32 << 26) != 0,
    opens_invariants none
    no_unwind
;

pub assume_specification[ FeatureInfo::has_fpu ](info: &FeatureInfo) -> bool
    returns
        feature_info_edx(*info) & 1u32 != 0,
    opens_invariants none
    no_unwind
;

/// Sealed to the immutable payload types reviewed for the three FPU cells.
pub trait FpuOnceValue: fpu_once_value::Sealed {

}

impl FpuOnceValue for FeatureInfo {

}

impl FpuOnceValue for u64 {

}

impl FpuOnceValue for usize {

}

/// Preserves spin::Once's lazy initialization, waiting and poisoning semantics.
/// The predicate is established by every initializer, never by the read itself.
#[verifier::reject_recursive_types(T)]
pub struct FpuOnce<T: FpuOnceValue, F: ValueInvariant<T>> {
    inner: SpinOnce<T>,
    ghost_predicate: Ghost<F>,
    tracked_identity: Tracked<ExclusiveGhost<()>>,
}

/// Completion of this specific cell, produced only after call_once returns.
pub tracked struct FpuOnceInitialized<T: FpuOnceValue> {
    ghost cell: Loc,
    ghost value: T,
}

/// The immutable value published by a cell if its initialization completes.
/// This model alone does not assert that publication has occurred.
uninterp spec fn fpu_once_published_value<T: FpuOnceValue>(cell: Loc) -> T;

impl<T: FpuOnceValue> FpuOnceInitialized<T> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.value == fpu_once_published_value::<T>(self.cell)
    }

    pub closed spec fn cell(&self) -> Loc {
        self.cell
    }

    pub closed spec fn value(&self) -> T {
        self.value
    }

    pub proof fn tracked_duplicate(tracked &self) -> (tracked r: Self)
        ensures
            r.cell() == self.cell(),
            r.value() == self.value(),
    {
        use_type_invariant(self);
        FpuOnceInitialized { cell: self.cell, value: self.value }
    }

    pub proof fn lemma_agree(tracked &self, tracked other: &Self)
        requires
            self.cell() == other.cell(),
        ensures
            self.value() == other.value(),
    {
        use_type_invariant(self);
        use_type_invariant(other);
    }
}

impl<T: FpuOnceValue, F: ValueInvariant<T>> FpuOnce<T, F> {
    pub closed spec fn id(&self) -> Loc {
        self.tracked_identity@.id()
    }

    /// The cell's eventual published value; this does not imply completion.
    pub closed spec fn published_value(&self) -> T {
        fpu_once_published_value::<T>(self.id())
    }

    pub open spec fn value_inv(&self, value: T) -> bool {
        F::inv(value)
    }

    pub const fn new(Ghost(predicate): Ghost<F>) -> Self {
        let tracked identity = ExclusiveGhost::alloc(());
        Self {
            inner: SpinOnce::new(),
            ghost_predicate: Ghost(predicate),
            tracked_identity: Tracked(identity),
        }
    }
}

} // verus!
#[verus_verify]
impl<T: FpuOnceValue, F: ValueInvariant<T>> FpuOnce<T, F> {
    /// A None result is possible before completion, while running, or poisoned.
    /// A None result describes only this observation, not subsequent calls.
    #[verus_verify(external_body)]
    #[verus_spec(r =>
        with Tracked(initialized): Tracked<Option<&FpuOnceInitialized<T>>>
        requires
            initialized matches Some(witness) ==> witness.cell() == self.id(),
        ensures
            r matches Some(value) ==> {
                &&& self.value_inv(*value)
                &&& *value == self.published_value()
            },
            initialized is Some ==> r is Some,
        opens_invariants none
        no_unwind
    )]
    pub fn get(&self) -> Option<&T> {
        self.inner.get()
    }
}

verus! {

impl<T: FpuOnceValue, F: ValueInvariant<T>> FpuOnce<T, F> {
    /// May unwind if the initializer panics or another initializer poisons the cell.
    #[verifier::external_body]
    pub fn call_once<Init: FnOnce() -> T>(&self, f: Init) -> (r: (
        &T,
        Tracked<FpuOnceInitialized<T>>,
    ))
        requires
            f.requires(()),
            forall|value: T| #[trigger] f.ensures((), value) ==> self.value_inv(value),
        ensures
            self.value_inv(*r.0),
            *r.0 == self.published_value(),
            r.1@.cell() == self.id(),
            r.1@.value() == *r.0,
    {
        let value = self.inner.call_once(f);
        let tracked initialized = FpuOnceInitialized { cell: self.id(), value: *value };
        (value, Tracked(initialized))
    }

    pub fn get_initialized(&self, Tracked(initialized): Tracked<&FpuOnceInitialized<T>>) -> (r: &T)
        requires
            initialized.cell() == self.id(),
        ensures
            self.value_inv(*r),
            *r == initialized.value(),
    {
        let value = (#[verus_spec(with Tracked(Some(initialized)))]
        self.get()).unwrap();
        proof {
            let tracked read = FpuOnceInitialized { cell: self.id(), value: *value };
            read.lemma_agree(initialized);
        }
        value
    }
}

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

} // verus!
