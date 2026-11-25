// SPDX-License-Identifier: MPL-2.0
//! CPU execution context control.
use ostd_pod::pod_bytes;
use vstd::{
    array::{axiom_spec_array_fill_for_copy_type, spec_array_fill_for_copy_type},
    prelude::*,
    resource::Loc,
};
use vstd_extra::{
    external::x86::{
        FpuOnce, FpuOnceInitialized, X86CpuRegisterOwner, XCR0_KNOWN_MASK, clear_cr0_fpu_flags,
        cr0_emulate_coprocessor, cr0_or, cr0_task_switched, feature_info_ecx, initialize_x87,
        read_cr0, read_enabled_xsave_size, read_xcr0,
    },
    resource_invariant::ValueInvariant,
};

use crate::{
    arch::{cpu_features_cell_id, cpu_features_ref},
    specs::context::cpu_feature_model,
};

use alloc::boxed::Box;
use core::arch::x86_64::{_fxrstor64, _fxsave64, _xrstor64, _xsave64};

/*use bitflags_upstream::bitflags;*/
/*use cfg_if::cfg_if;*/
use log::debug;
use ostd_pod::Pod;
/*use spin::Once;*/
/*use x86::bits64::segmentation::wrfsbase;*/
/*use x86_64::registers::{
    control::{Cr0, Cr0Flags},
    rflags::RFlags,
    xcontrol::XCr0,
};*/

use crate::{
    arch::{
        CPU_FEATURES,
        /*trap::{RawUserContext, TrapFrame},*/
    },
    /*mm::Vaddr,
    task::scheduler,
    trap::call_irq_callback_functions,
    user::{ReturnReason, UserContextApi, UserContextApiInternal},*/
};

/*cfg_if! {
    if #[cfg(feature = "cvm_guest")] {
        mod tdx;

        use tdx::VirtualizationExceptionHandler;
    }
}*/

pub use x86::cpuid;

/*
/// Userspace CPU context, including general-purpose registers and exception information.
#[derive(Clone, Default, Debug)]
#[repr(C)]
pub struct UserContext {
    user_context: RawUserContext,
    exception: Option<CpuException>,
}

/// General registers.
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
#[repr(C)]
#[expect(missing_docs)]
pub struct GeneralRegs {
    pub rax: usize,
    pub rbx: usize,
    pub rcx: usize,
    pub rdx: usize,
    pub rsi: usize,
    pub rdi: usize,
    pub rbp: usize,
    pub rsp: usize,
    pub r8: usize,
    pub r9: usize,
    pub r10: usize,
    pub r11: usize,
    pub r12: usize,
    pub r13: usize,
    pub r14: usize,
    pub r15: usize,
    pub rip: usize,
    pub rflags: usize,
    pub fsbase: usize,
    pub gsbase: usize,
}

/// Architectural CPU exceptions (x86-64 vectors 0-31).
///
/// For the authoritative specification of each vector, see the
/// Intel® 64 and IA-32 Architectures Software Developer’s Manual,
/// Volume 3 “System Programming Guide”, Chapter 6 “Interrupt and Exception
/// Handling”, in particular Section 6.15 “Exception and Interrupt
/// Reference”.
///
/// Every enum variant corresponds to one exception defined by the
/// Intel/AMD architecture.
/// Variants that naturally carry an error code (or other error information)
/// expose it through their associated data fields.
//
// TODO: Some exceptions (like `AlignmentCheck`) also push an
//       error code onto the stack, but that detail is not yet represented
//       in this type definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CpuException {
    ///  0 – #DE  Divide-by-zero error.
    DivisionError,
    ///  1 – #DB  Debug.
    Debug,
    ///  2 – NMI  Non-maskable interrupt.
    NonMaskableInterrupt,
    ///  3 – #BP  Breakpoint (INT3).
    BreakPoint,
    ///  4 – #OF  Overflow.
    Overflow,
    ///  5 – #BR  Bound-range exceeded.
    BoundRangeExceeded,
    ///  6 – #UD  Invalid or undefined opcode.
    InvalidOpcode,
    ///  7 – #NM  Device not available (FPU/MMX/SSE disabled).
    DeviceNotAvailable,
    ///  8 – #DF  Double fault (always pushes an error code of 0).
    DoubleFault,
    ///  9 – Coprocessor segment overrun (reserved on modern CPUs).
    CoprocessorSegmentOverrun,
    /// 10 – #TS  Invalid TSS.
    InvalidTss(SelectorErrorCode),
    /// 11 – #NP  Segment not present.
    SegmentNotPresent(SelectorErrorCode),
    /// 12 – #SS  Stack-segment fault.
    StackSegmentFault(SelectorErrorCode),
    /// 13 – #GP  General protection fault
    GeneralProtectionFault(Option<SelectorErrorCode>),
    /// 14 – #PF  Page fault.
    PageFault(RawPageFaultInfo),
    // 15: Reserved
    /// 16 – #MF  x87 floating-point exception.
    X87FloatingPointException,
    /// 17 – #AC  Alignment check.
    AlignmentCheck,
    /// 18 – #MC  Machine check.
    MachineCheck,
    /// 19 – #XM / #XF  SIMD/FPU floating-point exception.
    SIMDFloatingPointException,
    /// 20 – #VE  Virtualization exception.
    VirtualizationException,
    /// 21 – #CP  Control protection exception (CET).
    ControlProtectionException,
    // 22-27: Reserved
    /// 28 – #HV  Hypervisor injection exception.
    HypervisorInjectionException,
    /// 29 – #VC  VMM communication exception (SEV-ES GHCB).
    VMMCommunicationException,
    /// 30 – #SX  Security exception.
    SecurityException,
    // 31: Reserved
    /// Catch-all for reserved or undefined vector numbers.
    Reserved,
}

impl CpuException {
    pub(crate) fn new(trap_num: usize, error_code: usize) -> Option<Self> {
        let exception = match trap_num {
            0 => Self::DivisionError,
            1 => Self::Debug,
            2 => Self::NonMaskableInterrupt,
            3 => Self::BreakPoint,
            4 => Self::Overflow,
            5 => Self::BoundRangeExceeded,
            6 => Self::InvalidOpcode,
            7 => Self::DeviceNotAvailable,
            8 => {
                // A double fault will always generate an error code with a value of zero.
                debug_assert_eq!(error_code, 0);
                Self::DoubleFault
            }
            9 => Self::CoprocessorSegmentOverrun,
            10 => Self::InvalidTss(SelectorErrorCode(error_code)),
            11 => Self::SegmentNotPresent(SelectorErrorCode(error_code)),
            12 => Self::StackSegmentFault(SelectorErrorCode(error_code)),
            13 => {
                let error_code = if error_code == 0 {
                    None
                } else {
                    Some(SelectorErrorCode(error_code))
                };
                Self::GeneralProtectionFault(error_code)
            }
            14 => {
                let page_fault_addr = x86_64::registers::control::Cr2::read_raw() as usize;
                Self::PageFault(RawPageFaultInfo {
                    error_code: PageFaultErrorCode::from_bits(error_code).unwrap(),
                    addr: page_fault_addr,
                })
            }
            // Reserved 15
            16 => Self::X87FloatingPointException,
            17 => Self::AlignmentCheck,
            18 => Self::MachineCheck,
            19 => Self::SIMDFloatingPointException,
            20 => Self::VirtualizationException,
            21 => Self::ControlProtectionException,
            // Reserved 22-27
            28 => Self::HypervisorInjectionException,
            29 => Self::VMMCommunicationException,
            30 => Self::SecurityException,
            // Reserved 31
            15 | 22..=27 | 31 => Self::Reserved,
            _ => return None,
        };

        Some(exception)
    }

    const fn type_(&self) -> CpuExceptionType {
        match self {
            Self::Debug => CpuExceptionType::FaultOrTrap,
            Self::NonMaskableInterrupt => CpuExceptionType::Interrupt,
            Self::BreakPoint | Self::Overflow => CpuExceptionType::Trap,
            Self::DoubleFault | Self::MachineCheck => CpuExceptionType::Abort,
            Self::Reserved => CpuExceptionType::Reserved,
            _ => CpuExceptionType::Fault,
        }
    }

    pub(crate) const fn is_cpu_exception(trap_num: usize) -> bool {
        trap_num <= 31
    }
}

/// Selector error code.
///
/// Reference: <https://wiki.osdev.org/Exceptions#Selector_Error_Code>.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SelectorErrorCode(usize);

impl UserContext {
    /// Returns a reference to the general registers.
    pub fn general_regs(&self) -> &GeneralRegs {
        &self.user_context.general
    }

    /// Returns a mutable reference to the general registers
    pub fn general_regs_mut(&mut self) -> &mut GeneralRegs {
        &mut self.user_context.general
    }

    /// Takes the CPU exception out.
    pub fn take_exception(&mut self) -> Option<CpuException> {
        self.exception.take()
    }

    /// Sets thread-local storage pointer.
    pub fn set_tls_pointer(&mut self, tls: usize) {
        self.set_fsbase(tls)
    }

    /// Gets thread-local storage pointer.
    pub fn tls_pointer(&self) -> usize {
        self.fsbase()
    }

    /// Activates thread-local storage pointer on the current CPU.
    ///
    /// # Safety
    ///
    /// The method by itself is safe because the value of the TLS register won't affect kernel code.
    /// But if the user relies on the TLS pointer, make sure that the pointer is correctly set when
    /// entering the user space.
    pub fn activate_tls_pointer(&self) {
        unsafe { wrfsbase(self.fsbase() as u64) }
    }
}

impl UserContextApiInternal for UserContext {
    fn execute<F>(&mut self, mut has_kernel_event: F) -> ReturnReason
    where
        F: FnMut() -> bool,
    {
        // set interrupt flag so that in user mode it can receive external interrupts
        // set ID flag which means cpu support CPUID instruction
        self.user_context.general.rflags |= (RFlags::INTERRUPT_FLAG | RFlags::ID).bits() as usize;

        const SYSCALL_TRAPNUM: usize = 0x100;

        // Return when it is syscall or cpu exception type is Fault or Trap.
        loop {
            scheduler::might_preempt();
            self.user_context.run();

            let exception =
                CpuException::new(self.user_context.trap_num, self.user_context.error_code);
            match exception {
                #[cfg(feature = "cvm_guest")]
                Some(CpuException::VirtualizationException) => {
                    let ve_handler = VirtualizationExceptionHandler::new();
                    // Check out the doc of `VirtualizationExceptionHandler::new` to
                    // see why IRQs must enabled _after_ instantiating a `VirtualizationExceptionHandler`.
                    crate::arch::irq::enable_local();
                    ve_handler.handle(self);
                }
                Some(exception) if exception.type_().is_fault_or_trap() => {
                    crate::arch::irq::enable_local();
                    self.exception = Some(exception);
                    return ReturnReason::UserException;
                }
                Some(exception) => {
                    panic!(
                        "cannot handle user CPU exception: {:?}, trapframe: {:?}",
                        exception,
                        self.as_trap_frame()
                    );
                }
                None if self.user_context.trap_num == SYSCALL_TRAPNUM => {
                    crate::arch::irq::enable_local();
                    return ReturnReason::UserSyscall;
                }
                None => {
                    call_irq_callback_functions(
                        &self.as_trap_frame(),
                        self.as_trap_frame().trap_num,
                    );
                    crate::arch::irq::enable_local();
                }
            }

            if has_kernel_event() {
                break ReturnReason::KernelEvent;
            }
        }
    }

    fn as_trap_frame(&self) -> TrapFrame {
        TrapFrame {
            rax: self.user_context.general.rax,
            rbx: self.user_context.general.rbx,
            rcx: self.user_context.general.rcx,
            rdx: self.user_context.general.rdx,
            rsi: self.user_context.general.rsi,
            rdi: self.user_context.general.rdi,
            rbp: self.user_context.general.rbp,
            rsp: self.user_context.general.rsp,
            r8: self.user_context.general.r8,
            r9: self.user_context.general.r9,
            r10: self.user_context.general.r10,
            r11: self.user_context.general.r11,
            r12: self.user_context.general.r12,
            r13: self.user_context.general.r13,
            r14: self.user_context.general.r14,
            r15: self.user_context.general.r15,
            _pad: 0,
            trap_num: self.user_context.trap_num,
            error_code: self.user_context.error_code,
            rip: self.user_context.general.rip,
            cs: 0,
            rflags: self.user_context.general.rflags,
        }
    }
}

/// As Osdev Wiki defines(<https://wiki.osdev.org/Exceptions>):
/// CPU exceptions are classified as:
///
/// Faults: These can be corrected and the program may continue as if nothing happened.
///
/// Traps: Traps are reported immediately after the execution of the trapping instruction.
///
/// Aborts: Some severe unrecoverable error.
///
/// But there exists some vector which are special. Vector 1 can be both fault or trap and vector 2 is interrupt.
/// So here we also define FaultOrTrap and Interrupt
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum CpuExceptionType {
    /// CPU faults. Faults can be corrected, and the program may continue as if nothing happened.
    Fault,
    /// CPU traps. Traps are reported immediately after the execution of the trapping instruction
    Trap,
    /// Faults or traps
    FaultOrTrap,
    /// CPU interrupts
    Interrupt,
    /// Some severe unrecoverable error
    Abort,
    /// Reserved for future use
    Reserved,
}

impl CpuExceptionType {
    /// Returns whether this exception type is a fault or a trap.
    pub fn is_fault_or_trap(self) -> bool {
        match self {
            CpuExceptionType::Trap | CpuExceptionType::Fault | CpuExceptionType::FaultOrTrap => {
                true
            }
            CpuExceptionType::Abort | CpuExceptionType::Interrupt | CpuExceptionType::Reserved => {
                false
            }
        }
    }
}

/// Architecture-specific data reported with a page-fault exception.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RawPageFaultInfo {
    /// The error code pushed by the CPU for this page fault.
    pub error_code: PageFaultErrorCode,
    /// The linear (virtual) address that triggered the fault (contents of CR2).
    pub addr: Vaddr,
}

bitflags! {
    /// Page Fault error code. Following the Intel Architectures Software Developer's Manual Volume 3
    pub struct PageFaultErrorCode : usize{
        /// 0 if no translation for the linear address.
        const PRESENT       = 1 << 0;
        /// 1 if the access was a write.
        const WRITE         = 1 << 1;
        /// 1 if the access was a user-mode access.
        const USER          = 1 << 2;
        /// 1 if there is no translation for the linear address
        /// because a reserved bit was set.
        const RESERVED      = 1 << 3;
        /// 1 if the access was an instruction fetch.
        const INSTRUCTION   = 1 << 4;
        /// 1 if the access was a data access to a linear address with a protection key for which
        /// the protection-key rights registers disallow access.
        const PROTECTION    = 1 << 5;
        /// 1 if the access was a shadow-stack access.
        const SHADOW_STACK  = 1 << 6;
        /// 1 if there is no translation for the linear address using HLAT paging.
        const HLAT          = 1 << 7;
        /// 1 if the exception is unrelated to paging and resulted from violation of SGX-specific
        /// access-control requirements.
        const SGX           = 1 << 15;
    }
}

impl UserContextApi for UserContext {
    fn trap_number(&self) -> usize {
        self.user_context.trap_num
    }

    fn trap_error_code(&self) -> usize {
        self.user_context.error_code
    }

    fn set_instruction_pointer(&mut self, ip: usize) {
        self.set_rip(ip);
    }

    fn set_stack_pointer(&mut self, sp: usize) {
        self.set_rsp(sp)
    }

    fn stack_pointer(&self) -> usize {
        self.rsp()
    }

    fn instruction_pointer(&self) -> usize {
        self.rip()
    }
}

macro_rules! cpu_context_impl_getter_setter {
    ( $( [ $field: ident, $setter_name: ident] ),*) => {
        impl UserContext {
            $(
                #[doc = concat!("Gets the value of ", stringify!($field))]
                #[inline(always)]
                pub fn $field(&self) -> usize {
                    self.user_context.general.$field
                }

                #[doc = concat!("Sets the value of ", stringify!(field))]
                #[inline(always)]
                pub fn $setter_name(&mut self, $field: usize) {
                    self.user_context.general.$field = $field;
                }
            )*
        }
    };
}

cpu_context_impl_getter_setter!(
    [rax, set_rax],
    [rbx, set_rbx],
    [rcx, set_rcx],
    [rdx, set_rdx],
    [rsi, set_rsi],
    [rdi, set_rdi],
    [rbp, set_rbp],
    [rsp, set_rsp],
    [r8, set_r8],
    [r9, set_r9],
    [r10, set_r10],
    [r11, set_r11],
    [r12, set_r12],
    [r13, set_r13],
    [r14, set_r14],
    [r15, set_r15],
    [rip, set_rip],
    [rflags, set_rflags],
    [fsbase, set_fsbase],
    [gsbase, set_gsbase]
);*/
verus! {

pub tracked struct FpuInitialization {
    features: FpuOnceInitialized<x86::cpuid::FeatureInfo>,
    max_features: FpuOnceInitialized<u64>,
    area_size: FpuOnceInitialized<usize>,
    ghost cpu: nat,
    ghost xcr0: u64,
}

impl FpuInitialization {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.features.cell() == cpu_features_cell_id()
        &&& self.uses_xsave()
        &&& self.max_features.cell() == max_features_cell_id()
        &&& self.max_features.value() == cpu_feature_model().supported_xstates()
        &&& self.area_size.cell() == xsave_size_cell_id()
        &&& 576 <= self.area_size.value() <= MAX_XSAVE_AREA_SIZE
        &&& self.area_size.value() == platform_xsave_area_size()
    }

    /// Exposes initialization guarantees without revealing the cache witnesses.
    pub proof fn lemma_type_inv(tracked &self)
        ensures
            self.uses_xsave(),
            576 <= self.len() <= 4096,
            self.len() == platform_xsave_area_size(),
            self.supported_mask() == cpu_feature_model().supported_xstates(),
    {
        use_type_invariant(self);
    }

    pub closed spec fn len(&self) -> usize {
        self.area_size.value()
    }

    pub closed spec fn supported_mask(&self) -> u64 {
        self.max_features.value()
    }

    pub closed spec fn uses_xsave(&self) -> bool {
        feature_info_ecx(self.features.value()) & (1u32 << 26) != 0
    }

    pub closed spec fn configured_cpu(&self) -> nat {
        self.cpu
    }

    pub closed spec fn configured_xcr0(&self) -> u64 {
        self.xcr0
    }

    /// Relates CPU identity, register access and XSTATE support.
    /// Startup/configuration preconditions bind the cached length to this CPU's
    /// enabled hardware XSAVE size at its current XCR0.
    pub open spec fn enabled_on(&self, cpu: &X86CpuRegisterOwner) -> bool {
        &&& self.configured_cpu() == cpu@.cpu
        &&& self.configured_xcr0() == cpu@.xcr0
        &&& cpu.xcr0_readable()
        &&& cpu_feature_model().matches_xstates(cpu)
        &&& self.supported_mask() == cpu@.user_xstates | cpu@.supervisor_xstates
        &&& self.len() == (cpu@.xsave_size_for)(cpu@.xcr0) as usize
    }
}

pub ghost struct FxSaveState {
    pub control: u16,
    pub status: u16,
    pub tag: u16,
    pub op: u16,
    pub ip: u32,
    pub cs: u32,
    pub dp: u32,
    pub ds: u32,
    pub mxcsr: u32,
    pub mxcsr_mask: u32,
    pub st_space: [u32; 32],
    pub xmm_space: [u32; 64],
    pub padding: [u32; 12],
    pub reserved: [u32; 12],
}

pub ghost struct FpuState {
    pub legacy: FxSaveState,
    pub features: u64,
    pub compaction: u64,
    pub reserved: [u64; 6],
    pub extended_state_area: [u8; MAX_XSAVE_AREA_SIZE - 512 - 64],
}

impl FpuState {
    pub open spec fn initialized(&self, features: u64) -> bool {
        &&& self.legacy.control == 0x037f
        &&& self.legacy.status == 0
        &&& self.legacy.tag == 0xffff
        &&& self.legacy.op == 0
        &&& self.legacy.ip == 0 && self.legacy.cs == 0
        &&& self.legacy.dp == 0 && self.legacy.ds == 0
        &&& self.legacy.mxcsr == 0x1f80 && self.legacy.mxcsr_mask == 0
        &&& self.legacy.st_space@.all(|word: u32| word == 0)
        &&& self.legacy.xmm_space@.all(|word: u32| word == 0)
        &&& self.legacy.padding@.all(|word: u32| word == 0)
        &&& self.legacy.reserved@.all(|word: u32| word == 0)
        &&& self.features == features && self.compaction == 0
        &&& self.reserved@.all(|word: u64| word == 0)
        &&& self.extended_state_area@.all(|byte: u8| byte == 0)
    }

    /// The parts that clone clears rather than copying from its source.
    pub open spec fn has_zeroed_clone_padding(&self, area_size: usize) -> bool {
        let extended_len = if area_size > 512 {
            area_size - 576
        } else {
            0
        };
        self.reserved@.all(|word: u64| word == 0) && self.extended_state_area@[extended_len..].all(
            |byte: u8| byte == 0,
        )
    }

    pub open spec fn copied_from(&self, source: &Self, area_size: usize) -> bool {
        let extended_len = if area_size > 512 {
            area_size - 576
        } else {
            0
        };
        &&& self.legacy == source.legacy
        &&& self.features == source.features
        &&& self.compaction == source.compaction
        &&& self.extended_state_area@[..extended_len] == source.extended_state_area@[..extended_len]
        &&& self.has_zeroed_clone_padding(area_size)
    }
}

/// The FPU context of user task.
///
/// This could be used for saving both legacy and modern state format.
#[derive(Debug)]
pub struct FpuContext {
    xsave_area: Box<XSaveArea>,
    area_size: usize,
}

impl FpuContext {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        self.area_size == 512 || 576 <= self.area_size <= MAX_XSAVE_AREA_SIZE
    }

    /// Exposes byte-view length bounds while keeping the storage representation private.
    pub proof fn lemma_type_inv(&self)
        requires
            self.type_inv(),
        ensures
            self.len() == 512 || 576 <= self.len() <= 4096,
    {
    }

    pub closed spec fn len(&self) -> usize {
        self.area_size
    }

    pub closed spec fn bytes(&self) -> Seq<u8> {
        pod_bytes(*self.xsave_area)[..self.area_size]
    }

    /// Backing bytes outside the slice exposed by as_bytes and as_bytes_mut.
    pub closed spec fn unexposed_bytes(&self) -> Seq<u8> {
        pod_bytes(*self.xsave_area)[self.area_size..]
    }

    pub closed spec fn state(&self) -> FpuState {
        self.xsave_area.state()
    }

    pub open spec fn has_initial_state(&self, features: u64) -> bool {
        self.state().initialized(features)
    }

    pub open spec fn copied_from(&self, source: &Self) -> bool {
        &&& self.len() == source.len()
        &&& source.type_inv()
        &&& self.state().copied_from(&source.state(), source.len())
    }
}

global layout FxSaveArea is size == 512, align == 16;

global layout XSaveArea is size == 4096, align == 64;

} // verus!
#[verus_verify]
impl FpuContext {
    /// Creates a new FPU context.
    #[verus_spec(r =>
        with Tracked(cpu): Tracked<&X86CpuRegisterOwner>, Tracked(init): Tracked<&FpuInitialization>
        requires init.enabled_on(cpu),
        ensures r.len() == init.len(),
                r.has_initial_state((cpu@.xcr0 & XCR0_KNOWN_MASK) & init.supported_mask()),
    )]
    pub fn new() -> Self {
        proof! {
            use_type_invariant(init);
            broadcast use { VERUS_layout_of_FxSaveArea, VERUS_layout_of_XSaveArea };
        }
        let mut area_size = size_of::<FxSaveArea>();
        /* Origin Rust: if CPU_FEATURES.get().unwrap().has_xsave() {
         * Use the completion witness; get_initialized executes the same get/unwrap. */
        if verus_exec_expr! { cpu_features_ref().get_initialized(Tracked(&init.features)) }
            .has_xsave()
        {
            /* Origin Rust: area_size = area_size.max(*XSAVE_AREA_SIZE.get().unwrap());
             * Preserve the read while making its completion obligation explicit. */
            area_size = area_size.max(
                *verus_exec_expr! { xsave_size_ref().get_initialized(Tracked(&init.area_size)) },
            );
        }

        Self {
            xsave_area: Box::new(
                #[verus_spec(with Tracked(cpu), Tracked(init))]
                self::XSaveArea::new(),
            ),
            area_size,
        }
    }
}

impl FpuContext {
    /// Saves CPU's current FPU context to this instance.
    pub fn save(&mut self) {
        let mem_addr = self.as_bytes_mut().as_mut_ptr();

        if CPU_FEATURES.get().unwrap().has_xsave() {
            unsafe { _xsave64(mem_addr, XFEATURE_MASK_USER_RESTORE) };
        } else {
            unsafe { _fxsave64(mem_addr) };
        }

        debug!("Save FPU context");
    }

    /// Loads CPU's FPU context from this instance.
    pub fn load(&mut self) {
        let mem_addr = self.as_bytes().as_ptr();

        if CPU_FEATURES.get().unwrap().has_xsave() {
            let rs_mask = XFEATURE_MASK_USER_RESTORE & XSTATE_MAX_FEATURES.get().unwrap();

            unsafe { _xrstor64(mem_addr, rs_mask) };
        } else {
            unsafe { _fxrstor64(mem_addr) };
        }

        debug!("Load FPU context");
    }
}

#[verus_verify]
impl FpuContext {
    /// Returns the FPU context as a byte slice.
    #[verus_spec(r =>
        ensures r@ == self.bytes(), r.len() == self.len(),
    )]
    pub fn as_bytes(&self) -> &[u8] {
        proof! { use_type_invariant(&*self); broadcast use VERUS_layout_of_XSaveArea; }
        &self.xsave_area.as_bytes()[..self.area_size]
    }

    /// Returns the FPU context as a mutable byte slice.
    #[verus_spec(r =>
        ensures final(self).len() == old(self).len(),
                r.len() == old(self).len(),
                r@ == old(self).bytes(),
                final(r)@ == final(self).bytes(),
                final(self).unexposed_bytes() == old(self).unexposed_bytes(),
    )]
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        proof! { use_type_invariant(&*self); broadcast use VERUS_layout_of_XSaveArea; }
        &mut self.xsave_area.as_bytes_mut()[..self.area_size]
    }
}

/* Origin Rust:
impl Default for FpuContext {
    fn default() -> Self {
        Self::new()
    }
}
 * The standard trait signature cannot carry the CPU and initialization
 * resources required by this body. */
#[verus_verify]
impl FpuContext {
    #[verus_spec(r =>
        with Tracked(cpu): Tracked<&X86CpuRegisterOwner>, Tracked(init): Tracked<&FpuInitialization>
        requires init.enabled_on(cpu),
        ensures r.len() == init.len(),
                r.has_initial_state((cpu@.xcr0 & XCR0_KNOWN_MASK) & init.supported_mask()),
    )]
    pub fn default() -> Self {
        #[verus_spec(with Tracked(cpu), Tracked(init))]
        self::FpuContext::new()
    }
}

/* Origin Rust:
impl Clone for FpuContext {
    fn clone(&self) -> Self {
        let mut xsave_area = Box::new(XSaveArea::new());
        xsave_area.fxsave_area = self.xsave_area.fxsave_area;
        xsave_area.features = self.xsave_area.features;
        xsave_area.compaction = self.xsave_area.compaction;
        if self.area_size > size_of::<FxSaveArea>() {
            let len = self.area_size - size_of::<FxSaveArea>() - 64;
            xsave_area.extended_state_area[..len]
                .copy_from_slice(&self.xsave_area.extended_state_area[..len]);
        }

        Self {
            xsave_area,
            area_size: self.area_size,
        }
    }
}
 * The standard trait signature cannot carry the CPU and initialization
 * resources required by XSaveArea::new. */
#[verus_verify]
impl FpuContext {
    #[verus_spec(r =>
        with Tracked(cpu): Tracked<&X86CpuRegisterOwner>, Tracked(init): Tracked<&FpuInitialization>
        requires cpu.xcr0_readable(),
        ensures r.len() == self.len(), r.copied_from(self),
    )]
    pub fn clone(&self) -> Self {
        proof! {
            use_type_invariant(&*self);
            broadcast use VERUS_layout_of_FxSaveArea;
        }
        let mut xsave_area = Box::new(
            #[verus_spec(with Tracked(cpu), Tracked(init))]
            self::XSaveArea::new(),
        );
        xsave_area.fxsave_area = self.xsave_area.fxsave_area;
        xsave_area.features = self.xsave_area.features;
        xsave_area.compaction = self.xsave_area.compaction;
        if self.area_size > size_of::<FxSaveArea>() {
            let len = self.area_size - size_of::<FxSaveArea>() - 64;
            xsave_area.extended_state_area[..len]
                .copy_from_slice(&self.xsave_area.extended_state_area[..len]);
        }

        proof! {
            let extended_len = if self.area_size > 512 { self.area_size - 576 } else { 0 };
            assert(xsave_area.extended_state_area@[..extended_len]
                == self.xsave_area.extended_state_area@[..extended_len]);
        }

        Self {
            xsave_area,
            area_size: self.area_size,
        }
    }
}

/// The modern FPU context format (as saved and restored by the `XSAVE` and `XRSTOR` instructions).
#[repr(C)]
#[repr(align(64))]
/* Origin Rust: #[derive(Clone, Copy, Debug, Pod)]
 * Keep the same Pod marker impl while supplying an opt-in zero-value model. */
#[derive(Clone, Copy, Debug)]
#[verus_verify]
struct XSaveArea {
    fxsave_area: FxSaveArea,
    features: u64,
    compaction: u64,
    reserved: [u64; 6],
    extended_state_area: [u8; MAX_XSAVE_AREA_SIZE - size_of::<FxSaveArea>() - 64],
}

verus! {

unsafe impl Pod for XSaveArea {
    closed spec fn zeroed_model() -> Option<Self> {
        Some(
            Self {
                fxsave_area: FxSaveArea {
                    control: 0,
                    status: 0,
                    tag: 0,
                    op: 0,
                    ip: 0,
                    cs: 0,
                    dp: 0,
                    ds: 0,
                    mxcsr: 0,
                    mxcsr_mask: 0,
                    st_space: spec_array_fill_for_copy_type(0u32),
                    xmm_space: spec_array_fill_for_copy_type(0u32),
                    padding: spec_array_fill_for_copy_type(0u32),
                    reserved: spec_array_fill_for_copy_type(0u32),
                },
                features: 0,
                compaction: 0,
                reserved: spec_array_fill_for_copy_type(0u64),
                extended_state_area: spec_array_fill_for_copy_type(0u8),
            },
        )
    }
}

} // verus!
#[verus_verify]
impl XSaveArea {
    #[verus_spec(r =>
        with Tracked(cpu): Tracked<&X86CpuRegisterOwner>, Tracked(init): Tracked<&FpuInitialization>
        requires cpu.xcr0_readable(),
        ensures r.state().initialized((cpu@.xcr0 & XCR0_KNOWN_MASK) & init.supported_mask()),
    )]
    fn new() -> Self {
        proof! { use_type_invariant(init); broadcast use { VERUS_layout_of_FxSaveArea, axiom_spec_array_fill_for_copy_type }; }
        /* Origin Rust: let features = if CPU_FEATURES.get().unwrap().has_xsave() {
         * Completion witnesses provide the original get/unwrap's preconditions. */
        let features =
            if verus_exec_expr! { cpu_features_ref().get_initialized(Tracked(&init.features)) }
                .has_xsave()
            {
                /* Origin Rust: XCr0::read().bits() & XSTATE_MAX_FEATURES.get().unwrap()
                 * The same register read carries explicit current-CPU authority. */
                verus_exec_expr! {{
                    let bits = read_xcr0(Tracked(cpu)).bits();
                    bits & *max_features_ref().get_initialized(Tracked(&init.max_features))
                }}
            } else {
                0
            };
        let mut xsave_area = Self::new_zeroed();
        // Set the initial values for the FPU context. Refer to Intel SDM, Table 11-1:
        // "IA-32 and Intel® 64 Processor States Following Power-up, Reset, or INIT (Contd.)".
        xsave_area.fxsave_area.control = 0x037F;
        xsave_area.fxsave_area.tag = 0xFFFF;
        xsave_area.fxsave_area.mxcsr = 0x1F80;
        xsave_area.features = features;

        xsave_area
    }
}

/// The legacy SSE/MMX FPU context format (as saved and restored by the `FXSAVE` and `FXRSTOR` instructions).
#[repr(C)]
#[repr(align(16))]
#[derive(Clone, Copy, Debug, Pod)]
#[verus_verify]
struct FxSaveArea {
    control: u16,         // x87 FPU Control Word
    status: u16,          // x87 FPU Status Word
    tag: u16,             // x87 FPU Tag Word
    op: u16,              // x87 FPU Last Instruction Opcode
    ip: u32,              // x87 FPU Instruction Pointer Offset
    cs: u32,              // x87 FPU Instruction Pointer Selector
    dp: u32,              // x87 FPU Instruction Operand (Data) Pointer Offset
    ds: u32,              // x87 FPU Instruction Operand (Data) Pointer Selector
    mxcsr: u32,           // MXCSR Register State
    mxcsr_mask: u32,      // MXCSR Mask
    st_space: [u32; 32], // x87 FPU or MMX technology registers (ST0-ST7 or MM0-MM7, 128 bits per field)
    xmm_space: [u32; 64], // XMM registers (XMM0-XMM15, 128 bits per field)
    padding: [u32; 12],  // Padding
    reserved: [u32; 12], // Software reserved
}

verus! {

impl XSaveArea {
    closed spec fn state(&self) -> FpuState {
        FpuState {
            legacy: FxSaveState {
                control: self.fxsave_area.control,
                status: self.fxsave_area.status,
                tag: self.fxsave_area.tag,
                op: self.fxsave_area.op,
                ip: self.fxsave_area.ip,
                cs: self.fxsave_area.cs,
                dp: self.fxsave_area.dp,
                ds: self.fxsave_area.ds,
                mxcsr: self.fxsave_area.mxcsr,
                mxcsr_mask: self.fxsave_area.mxcsr_mask,
                st_space: self.fxsave_area.st_space,
                xmm_space: self.fxsave_area.xmm_space,
                padding: self.fxsave_area.padding,
                reserved: self.fxsave_area.reserved,
            },
            features: self.features,
            compaction: self.compaction,
            reserved: self.reserved,
            extended_state_area: self.extended_state_area,
        }
    }
}

} // verus!
/* Origin Rust: <none; new executable code>
 * Check hardware field offsets and tie the allocation size to its capacity. */
const _: () = {
    assert!(size_of::<XSaveArea>() == MAX_XSAVE_AREA_SIZE);
    assert!(core::mem::offset_of!(XSaveArea, fxsave_area) == 0);
    assert!(core::mem::offset_of!(XSaveArea, features) == 512);
    assert!(core::mem::offset_of!(XSaveArea, compaction) == 520);
    assert!(core::mem::offset_of!(XSaveArea, reserved) == 528);
    assert!(core::mem::offset_of!(XSaveArea, extended_state_area) == 576);
    assert!(core::mem::offset_of!(FxSaveArea, tag) == 4);
    assert!(core::mem::offset_of!(FxSaveArea, mxcsr) == 24);
};
verus! {

ghost struct XStateFeaturesInvariant;

impl ValueInvariant<u64> for XStateFeaturesInvariant {
    open spec fn inv(features: u64) -> bool {
        features == cpu_feature_model().supported_xstates()
    }
}

uninterp spec fn max_features_cell_id() -> Loc;

uninterp spec fn xsave_size_cell_id() -> Loc;

} // verus!
/// The XSTATE features (user & supervisor) supported by the processor.
/* Origin Rust: static XSTATE_MAX_FEATURES: Once<u64> = Once::new();
 * Carry a completion witness without changing the published mask. */
#[verus_verify]
static XSTATE_MAX_FEATURES: FpuOnce<u64, XStateFeaturesInvariant> =
    verus_exec_expr! { FpuOnce::new(Ghost(XStateFeaturesInvariant)) };

#[inline]
#[verus_verify(external_body)]
#[verus_spec(r => ensures r.id() == max_features_cell_id())]
fn max_features_ref() -> &'static FpuOnce<u64, XStateFeaturesInvariant> {
    &XSTATE_MAX_FEATURES
}

/// Mask features which are restored when returning to user space.
///
/// X87 | SSE | AVX | OPMASK | ZMM_HI256 | HI16_ZMM
const XFEATURE_MASK_USER_RESTORE: u64 = 0b1110_0111;

verus! {

/// Startup/configuration preconditions relate this shared size to each enabled
/// CPU's xsave_size_for(xcr0); no global equality axiom is assumed.
pub uninterp spec fn platform_xsave_area_size() -> usize;

ghost struct XSaveSizeInvariant;

impl ValueInvariant<usize> for XSaveSizeInvariant {
    open spec fn inv(size: usize) -> bool {
        576 <= size <= 4096 && size == platform_xsave_area_size()
    }
}

} // verus!
/// The real size in bytes of the XSAVE area containing all states enabled by XCRO | IA32_XSS.
/* Origin Rust: static XSAVE_AREA_SIZE: Once<usize> = Once::new();
 * Attach the capacity predicate that every publishing closure must prove. */
#[verus_verify]
static XSAVE_AREA_SIZE: FpuOnce<usize, XSaveSizeInvariant> =
    verus_exec_expr! { FpuOnce::new(Ghost(XSaveSizeInvariant)) };
#[inline]
#[verus_verify(external_body)]
#[verus_spec(r => ensures r.id() == xsave_size_cell_id())]
fn xsave_size_ref() -> &'static FpuOnce<usize, XSaveSizeInvariant> {
    &XSAVE_AREA_SIZE
}

/// The max size in bytes of the XSAVE area.
#[verus_verify]
const MAX_XSAVE_AREA_SIZE: usize = 4096;

#[verus_spec(
    with Tracked(cpu): Tracked<&mut X86CpuRegisterOwner>,
         Tracked(features_initialized): Tracked<&FpuOnceInitialized<x86::cpuid::FeatureInfo>>
         -> result: Tracked<FpuInitialization>
    requires
        old(cpu).xcr0_readable(),
        old(cpu)@.fpu,
        old(cpu)@.max_basic_leaf >= 0xd,
        cpu_feature_model().matches_xstates(old(cpu)),
        576 <= (old(cpu)@.xsave_size_for)(old(cpu)@.xcr0) <= 4096,
        (old(cpu)@.xsave_size_for)(old(cpu)@.xcr0) as usize == platform_xsave_area_size(),
        features_initialized.cell() == cpu_features_cell_id(),
    ensures
        result@.enabled_on(final(cpu)),
        result@.uses_xsave(),
        576 <= result@.len() <= 4096,
        final(cpu)@ == (vstd_extra::external::x86::X86CpuSnapshot {
            cr0: old(cpu)@.cr0 & !12u64,
            x87_control: 0x037f,
            x87_status: 0,
            x87_tag: 0xffff,
            ..old(cpu)@
        }),
)]
pub(in crate::arch) fn enable_essential_features() {
    proof_decl! { let tracked initialized; }
    verus_exec_expr! {{
    /* Origin Rust: XSTATE_MAX_FEATURES.call_once(|| {
     * Bind publication to the cell identity required by the initialization witness. */
    let (_, Tracked(max_features)) = max_features_ref().call_once(
        || -> (r: u64)
            ensures
                XStateFeaturesInvariant::inv(r),
            {
                const XSTATE_CPUID: u32 = 0x0000000d;

                // Find user xstates supported by the processor.
                let res0 = x86::cpuid::cpuid!(XSTATE_CPUID, 0);
                let ghost low0 = res0.eax;
                let ghost high0 = res0.edx;
                assert((low0 as u64) <= u64::MAX - ((high0 as u64) << 32)) by (bit_vector);
                let mut features = res0.eax as u64 + ((res0.edx as u64) << 32);
                assert(low0 as u64 + ((high0 as u64) << 32) == low0 as u64 | ((high0 as u64) << 32))
                    by (bit_vector);

                // Find supervisor xstates supported by the processor.
                let res1 = x86::cpuid::cpuid!(XSTATE_CPUID, 1);
                let ghost low1 = res1.ecx;
                let ghost high1 = res1.edx;
                assert((low1 as u64) <= u64::MAX - ((high1 as u64) << 32)) by (bit_vector);
                features |= res1.ecx as u64 + ((res1.edx as u64) << 32);

                assert(low1 as u64 + ((high1 as u64) << 32) == low1 as u64 | ((high1 as u64) << 32))
                    by (bit_vector);

                features
            },
    );

    /* Origin Rust: XSAVE_AREA_SIZE.call_once(|| {
     *     let cpuid = cpuid::CpuId::new();
     *     let size = cpuid.get_extended_state_info().unwrap()
     *         .xsave_area_size_enabled_features() as usize;
     *     debug_assert!(size <= MAX_XSAVE_AREA_SIZE);
     *     size
     * });
     * The initializer closure must prove its returned size satisfies the capacity bound. */
    let tracked read_cpu = &*cpu;
    let (_, Tracked(area_size)) = xsave_size_ref().call_once(
        || -> (r: usize)
            ensures
                XSaveSizeInvariant::inv(r),
            {
                let size = read_enabled_xsave_size(Tracked(read_cpu));
                debug_assert!(size <= MAX_XSAVE_AREA_SIZE);
                size
            },
    );
    /* Origin Rust: if CPU_FEATURES.get().unwrap().has_fpu() {
     * Use the completion witness returned by the real call_once. */
    if cpu_features_ref().get_initialized(Tracked(features_initialized)).has_fpu() {
        /* Origin Rust: let mut cr0 = Cr0::read();
         * Bind the hardware read to the same CPU resource. */
        let mut cr0 = read_cr0(Tracked(&*cpu));
        /* Origin Rust: cr0.remove(Cr0Flags::TASK_SWITCHED | Cr0Flags::EMULATE_COPROCESSOR);
         * The external BitOr operation requires a contract. */
        assert(8u64 | 4u64 == 12u64) by (bit_vector);
        cr0.remove(cr0_or(cr0_task_switched(), cr0_emulate_coprocessor()));

        unsafe {
            /* Origin Rust: Cr0::write(cr0);
             * Retain the write while carrying the register state transition. */
            let ghost raw_cr0 = cpu@.cr0;
            clear_cr0_fpu_flags(cr0, Tracked(&mut *cpu));
            // Flush out any pending x87 state.
            /* Origin Rust: core::arch::asm!("fninit");
             * Only this hardware instruction remains a trusted boundary. */
            assert((raw_cr0 & !12u64) & 12u64 == 0) by (bit_vector);
            initialize_x87(Tracked(&mut *cpu));
        }
    }
    let tracked features = features_initialized.tracked_duplicate();
    proof {
        initialized = FpuInitialization {
            features,
            max_features,
            area_size,
            cpu: cpu@.cpu,
            xcr0: cpu@.xcr0,
        };
    }
    }}
    proof_with!(|= Tracked(initialized));
    ()
}

verus! {

impl FpuContext {
    pub proof fn lemma_initial_state_bytes(&self, other: &Self, features: u64)
        requires
            self.len() == other.len(),
            self.has_initial_state(features),
            other.has_initial_state(features),
        ensures
            self.bytes() == other.bytes(),
    {
        let left = self.state();
        let right = other.state();
        assert(left.legacy.st_space =~= right.legacy.st_space);
        assert(left.legacy.xmm_space =~= right.legacy.xmm_space);
        assert(left.legacy.padding =~= right.legacy.padding);
        assert(left.legacy.reserved =~= right.legacy.reserved);
        assert(left.reserved =~= right.reserved);
        assert(left.extended_state_area =~= right.extended_state_area);
        self.lemma_same_state_bytes(other);
    }

    /// Byte equality requires the source's zeroed header reserve and inactive tail.
    pub proof fn lemma_copied_bytes(&self, source: &Self)
        requires
            self.copied_from(source),
            source.state().has_zeroed_clone_padding(source.len()),
        ensures
            self.bytes() == source.bytes(),
    {
        let left = self.state();
        let right = source.state();
        let extended_len = if source.len() > 512 {
            source.len() - 576
        } else {
            0
        };
        assert(left.reserved =~= right.reserved);
        assert(left.extended_state_area =~= right.extended_state_area) by {
            assert forall|i: int|
                0 <= i < left.extended_state_area.len() implies left.extended_state_area[i]
                == right.extended_state_area[i] by {
                if i < extended_len {
                    assert(left.extended_state_area@[..extended_len][i]
                        == right.extended_state_area@[..extended_len][i]);
                } else {
                    assert(left.extended_state_area@[extended_len..][i - extended_len] == 0);
                    assert(right.extended_state_area@[extended_len..][i - extended_len] == 0);
                }
            }
        }
        self.lemma_same_state_bytes(source);
    }
}

} // verus!
// Auxiliary representation proofs.
verus! {

impl FpuContext {
    proof fn lemma_same_state_bytes(&self, other: &Self)
        requires
            self.len() == other.len(),
            self.state() == other.state(),
        ensures
            self.bytes() == other.bytes(),
    {
    }
}

} // verus!
