// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;

/* use alloc::boxed::Box;

use bit_field::BitField;
use spin::Once;
use xapic::get_xapic_base_address;

use crate::{cpu::PinCurrentCpu, cpu_local, io::IoMemAllocatorBuilder};

static APIC_TYPE: Once<ApicType> = Once::new(); */

mod x2apic;
mod xapic;

/*
/// Returns a reference to the local APIC instance of the current CPU.
///
/// The reference to the APIC instance will not outlive the given
/// [`PinCurrentCpu`] guard and the APIC instance does not implement
/// [`Sync`], so it is safe to assume that the APIC instance belongs
/// to the current CPU. Note that interrupts are not disabled, so the
/// APIC instance may be accessed concurrently by interrupt handlers.
///
/// At the first time the function is called, the local APIC instance
/// is initialized and enabled if it was not enabled beforehand.
///
/// # Examples
///
/// ```rust
/// use ostd::{
///     arch::x86::kernel::apic,
///     task::disable_preempt,
/// };
///
/// let preempt_guard = disable_preempt();
/// let apic = apic::get_or_init(&preempt_guard as _);
///
/// let ticks = apic.timer_current_count();
/// apic.set_timer_init_count(0);
/// ```
pub fn get_or_init(_guard: &dyn PinCurrentCpu) -> &(dyn Apic + 'static) {
    struct ForceSyncSend<T>(T);

    // SAFETY: `ForceSyncSend` is `Sync + Send`, but accessing its contained value is unsafe.
    unsafe impl<T> Sync for ForceSyncSend<T> {}
    unsafe impl<T> Send for ForceSyncSend<T> {}

    impl<T> ForceSyncSend<T> {
        /// # Safety
        ///
        /// The caller must ensure that its context allows for safe access to `&T`.
        unsafe fn get(&self) -> &T {
            &self.0
        }
    }

    cpu_local! {
        static APIC_INSTANCE: Once<ForceSyncSend<Box<dyn Apic + 'static>>> = Once::new();
    }

    // No races due to `_guard`, but use `current_racy` to avoid calling via the vtable.
    // TODO: Find a better way to make `dyn PinCurrentCpu` easy to use?
    let apic_instance = APIC_INSTANCE.get_on_cpu(crate::cpu::CpuId::current_racy());

    // The APIC instance has already been initialized.
    if let Some(apic) = apic_instance.get() {
        // SAFETY: Accessing `&dyn Apic` is safe as long as we're running on the same CPU on which
        // the APIC instance was created. The `get_on_cpu` method above ensures this.
        return &**unsafe { apic.get() };
    }

    // Initialize the APIC instance now.
    apic_instance.call_once(|| match APIC_TYPE.get().unwrap() {
        ApicType::XApic => {
            let mut xapic = xapic::XApic::new().unwrap();
            xapic.enable();
            let version = xapic.version();
            log::info!(
                "xAPIC ID:{:x}, Version:{:x}, Max LVT:{:x}",
                xapic.id(),
                version & 0xff,
                (version >> 16) & 0xff
            );
            ForceSyncSend(Box::new(xapic))
        }
        ApicType::X2Apic => {
            let mut x2apic = x2apic::X2Apic::new().unwrap();
            x2apic.enable();
            let version = x2apic.version();
            log::info!(
                "x2APIC ID:{:x}, Version:{:x}, Max LVT:{:x}",
                x2apic.id(),
                version & 0xff,
                (version >> 16) & 0xff
            );
            ForceSyncSend(Box::new(x2apic))
        }
    });

    // We've initialized the APIC instance, so this `unwrap` cannot fail.
    let apic = apic_instance.get().unwrap();
    // SAFETY: Accessing `&dyn Apic` is safe as long as we're running on the same CPU on which the
    // APIC instance was created. The initialization above ensures this.
    &**unsafe { apic.get() }
}
*/

verus! {

pub trait Apic: ApicTimer {
    fn id(&self) -> u32;

    fn version(&self) -> u32;

    /// End of Interrupt, this function will inform APIC that this interrupt has been processed.
    fn eoi(&self);

    /// Send a general inter-processor interrupt.
    unsafe fn send_ipi(&self, icr: Icr);
}

pub trait ApicTimer {
    /// Sets the initial timer count, the APIC timer will count down from this value.
    fn set_timer_init_count(&self, value: u64);

    /// Gets the current count of the timer.
    /// The interval can be expressed by the expression: `init_count` - `current_count`.
    fn timer_current_count(&self) -> u64;

    /// Sets the timer register in the APIC.
    /// Bit 0-7:   The interrupt vector of timer interrupt.
    /// Bit 12:    Delivery Status, 0 for Idle, 1 for Send Pending.
    /// Bit 16:    Mask bit.
    /// Bit 17-18: Timer Mode, 0 for One-shot, 1 for Periodic, 2 for TSC-Deadline.
    fn set_lvt_timer(&self, value: u64);

    /// Sets timer divide config register.
    fn set_timer_div_config(&self, div_config: DivideConfig);
}

/*
enum ApicType {
    XApic,
    X2Apic,
}
*/

/// The inter-processor interrupt control register.
///
/// ICR is a 64-bit local APIC register that allows software running on the
/// processor to specify and send IPIs to other processors in the system.
/// To send an IPI, software must set up the ICR to indicate the type of IPI
/// message to be sent and the destination processor or processors. (All fields
/// of the ICR are read-write by software with the exception of the delivery
/// status field, which is read-only.)
///
/// The act of writing to the low doubleword of the ICR causes the IPI to be
/// sent. Therefore, in xapic mode, high doubleword of the ICR needs to be written
/// first and then the low doubleword to ensure the correct interrupt is sent.
///
/// The ICR consists of the following fields:
/// - **Bit 0-7**   Vector                  :The vector number of the interrupt being sent.
/// - **Bit 8-10**  Delivery Mode           :Specifies the type of IPI to be sent.
/// - **Bit 11**    Destination Mode        :Selects either physical or logical destination mode.
/// - **Bit 12**    Delivery Status(RO)     :Indicates the IPI delivery status.
/// - **Bit 13**    Reserved
/// - **Bit 14**    Level                   :Only set 1 for the INIT level de-assert delivery mode.
/// - **Bit 15**    Trigger Mode            :Selects level or edge trigger mode.
/// - **Bit 16-17** Reserved
/// - **Bit 18-19** Destination Shorthand   :Indicates destination set.
/// - **Bit 20-55** Reserved
/// - **Bit 56-63** Destination Field       :Specifies the target processor or processors.
pub struct Icr(u64);

impl Icr {
    /// The raw 64-bit value of the ICR register.
    pub closed spec fn raw_spec(self) -> u64 {
        self.0
    }
}

/// The 64-bit ICR value obtained by or-shifting each encoded field into its
/// position, where `dest_shifted` is the already-shifted destination field
/// (`sh`/`tm`/`lv`/`ds`/`dis`/`dm`/`v` denote the shorthand, trigger mode,
/// level, delivery status, destination mode, delivery mode, and vector bits,
/// respectively).
spec fn icr_or_value(
    dest_shifted: u64,
    sh: u64,
    tm: u64,
    lv: u64,
    ds: u64,
    dis: u64,
    dm: u64,
    v: u64,
) -> u64 {
    dest_shifted | (sh << 18) | (tm << 15) | (lv << 14) | (ds << 12) | (dis << 11) | (dm << 8) | v
}

} // verus!
#[verus_verify]
impl Icr {
    #[verus_spec(ret =>
        ensures
            ret.raw_spec() & 0xff == vector as u64,
            (ret.raw_spec() >> 8) & 0x7 == delivery_mode as u64,
            (ret.raw_spec() >> 11) & 0x1 == destination_mode as u64,
            (ret.raw_spec() >> 12) & 0x1 == delivery_status as u64,
            (ret.raw_spec() >> 14) & 0x1 == level as u64,
            (ret.raw_spec() >> 15) & 0x1 == trigger_mode as u64,
            (ret.raw_spec() >> 18) & 0x3 == destination_shorthand as u64,
            // Bit 13 and bits 16-17 are reserved and always zero.
            ret.raw_spec() & 0x32000 == 0,
            match destination {
                ApicId::XApic(d) => ret.raw_spec() >> 56 == d as u64,
                ApicId::X2Apic(d) => ret.raw_spec() >> 32 == d as u64,
            },
    )]
    #[expect(clippy::too_many_arguments)]
    pub fn new(
        destination: ApicId,
        destination_shorthand: DestinationShorthand,
        trigger_mode: TriggerMode,
        level: Level,
        delivery_status: DeliveryStatus,
        destination_mode: DestinationMode,
        delivery_mode: DeliveryMode,
        vector: u8,
    ) -> Self {
        let dest = match destination {
            ApicId::XApic(d) => (d as u64) << 56,
            ApicId::X2Apic(d) => (d as u64) << 32,
        };
        proof! {
            match destination {
                ApicId::XApic(d) => {
                    assert(dest == ((d as u64) << 56));
                    assert(((d as u64) << 56) & 0xffff_ffff == 0) by (bit_vector);
                    lemma_icr_or_value_field_bits(
                        dest,
                        destination_shorthand as u64,
                        trigger_mode as u64,
                        level as u64,
                        delivery_status as u64,
                        destination_mode as u64,
                        delivery_mode as u64,
                        vector as u64,
                    );
                    lemma_icr_or_value_xapic_dest(
                        d,
                        destination_shorthand as u64,
                        trigger_mode as u64,
                        level as u64,
                        delivery_status as u64,
                        destination_mode as u64,
                        delivery_mode as u64,
                        vector as u64,
                    );
                }
                ApicId::X2Apic(d) => {
                    assert(dest == ((d as u64) << 32));
                    assert(((d as u64) << 32) & 0xffff_ffff == 0) by (bit_vector);
                    lemma_icr_or_value_field_bits(
                        dest,
                        destination_shorthand as u64,
                        trigger_mode as u64,
                        level as u64,
                        delivery_status as u64,
                        destination_mode as u64,
                        delivery_mode as u64,
                        vector as u64,
                    );
                    lemma_icr_or_value_x2apic_dest(
                        d,
                        destination_shorthand as u64,
                        trigger_mode as u64,
                        level as u64,
                        delivery_status as u64,
                        destination_mode as u64,
                        delivery_mode as u64,
                        vector as u64,
                    );
                }
            }
        }
        Icr(dest
            | ((destination_shorthand as u64) << 18)
            | ((trigger_mode as u64) << 15)
            | ((level as u64) << 14)
            | ((delivery_status as u64) << 12)
            | ((destination_mode as u64) << 11)
            | ((delivery_mode as u64) << 8)
            | (vector as u64))
    }

    /// Returns the lower 32 bits of the ICR.
    #[verus_spec(returns self.raw_spec() as u32)]
    pub fn lower(&self) -> u32 {
        self.0 as u32
    }

    /// Returns the higher 32 bits of the ICR.
    #[verus_spec(returns (self.raw_spec() >> 32) as u32)]
    pub fn upper(&self) -> u32 {
        (self.0 >> 32) as u32
    }
}

verus! {

/// The core identifier. ApicId can be divided into Physical ApicId and Logical ApicId.
/// The Physical ApicId is the value read from the LAPIC ID Register, while the Logical ApicId has different
/// encoding modes in XApic and X2Apic.
pub enum ApicId {
    XApic(u8),
    X2Apic(u32),
}

impl ApicId {
    /// The raw 32-bit local APIC ID value, regardless of the variant.
    pub open spec fn raw_id_spec(self) -> u32 {
        match self {
            ApicId::XApic(id) => id as u32,
            ApicId::X2Apic(id) => id,
        }
    }

    /// The logical cluster ID: x2APIC ID\[19:4\].
    pub open spec fn x2apic_logical_cluster_id_spec(self) -> u32 {
        (self.raw_id_spec() >> 4) & 0xffff
    }

    /// The logical field ID: x2APIC ID\[3:0\].
    pub open spec fn x2apic_logical_field_id_spec(self) -> u32 {
        self.raw_id_spec() & 0xf
    }
}

} // verus!
#[verus_verify]
impl ApicId {
    /// Returns the logical x2apic ID.
    ///
    /// In x2APIC mode, the 32-bit logical x2APIC ID, which can be read from
    /// LDR, is derived from the 32-bit local x2APIC ID:
    /// Logical x2APIC ID = [(x2APIC ID\[19:4\] << 16) | (1 << x2APIC ID\[3:0\])]
    #[verus_spec(returns (self.x2apic_logical_cluster_id_spec() << 16)
        | (1u32 << self.x2apic_logical_field_id_spec()))]
    #[expect(unused)]
    pub fn x2apic_logical_id(&self) -> u32 {
        (self.x2apic_logical_cluster_id() << 16) | (1 << self.x2apic_logical_field_id())
    }

    /// Returns the logical x2apic cluster ID.
    ///
    /// Logical cluster ID = x2APIC ID\[19:4\]
    #[verus_spec(ret =>
        ensures
            ret == self.x2apic_logical_cluster_id_spec(),
            ret < 0x10000,
    )]
    pub fn x2apic_logical_cluster_id(&self) -> u32 {
        let apic_id = match *self {
            ApicId::XApic(id) => id as u32,
            ApicId::X2Apic(id) => id,
        };
        /* `bit_field::BitField::get_bits` is a provided trait method, so it
         * cannot be given a Verus specification; the bit extraction is
         * rewritten in the equivalent arithmetic form.
         * Origin Rust: apic_id.get_bits(4..=19)
         */
        proof! {
            assert(((apic_id >> 4) & 0xffff) < 0x10000) by (bit_vector);
        }
        (apic_id >> 4) & 0xffff
    }

    /// Returns the logical x2apic field ID.
    ///
    /// Specifically, the 16-bit logical ID sub-field is derived by the lowest
    /// 4 bits of the x2APIC ID, i.e.,
    /// Logical field ID = x2APIC ID\[3:0\].
    #[verus_spec(ret =>
        ensures
            ret == self.x2apic_logical_field_id_spec(),
            ret < 0x10,
    )]
    pub fn x2apic_logical_field_id(&self) -> u32 {
        let apic_id = match *self {
            ApicId::XApic(id) => id as u32,
            ApicId::X2Apic(id) => id,
        };
        /* `bit_field::BitField::get_bits` is a provided trait method, so it
         * cannot be given a Verus specification; the bit extraction is
         * rewritten in the equivalent arithmetic form.
         * Origin Rust: apic_id.get_bits(0..=3)
         */
        proof! {
            assert((apic_id & 0xf) < 0x10) by (bit_vector);
        }
        apic_id & 0xf
    }
}

/*
impl From<u32> for ApicId {
    fn from(value: u32) -> Self {
        match APIC_TYPE.get().unwrap() {
            ApicType::XApic => ApicId::XApic(value as u8),
            ApicType::X2Apic => ApicId::X2Apic(value),
        }
    }
}
*/

verus! {

/// Indicates whether a shorthand notation is used to specify the destination of
/// the interrupt and, if so, which shorthand is used. Destination shorthands are
/// used in place of the 8-bit destination field, and can be sent by software
/// using a single write to the low doubleword of the ICR.
///
/// Shorthands are defined for the following cases: software self interrupt, IPIs
/// to all processors in the system including the sender, IPIs to all processors
/// in the system excluding the sender.
/* The derives below are added because enum-to-integer casts in `spec` mode
 * require `Copy` (`vstd`'s `spec_cast_integer`); deriving `Copy` on these
 * unit-only enums only adds trait impls.
 * Origin Rust: <none; new derives on the six ICR field enums below>
 */
#[derive(Clone, Copy)]
#[repr(u64)]
pub enum DestinationShorthand {
    NoShorthand = 0b00,
    #[expect(dead_code)]
    MySelf = 0b01,
    AllIncludingSelf = 0b10,
    AllExcludingSelf = 0b11,
}

#[derive(Clone, Copy)]
#[repr(u64)]
pub enum TriggerMode {
    Edge = 0,
    Level = 1,
}

#[derive(Clone, Copy)]
#[repr(u64)]
pub enum Level {
    Deassert = 0,
    Assert = 1,
}

/// Indicates the IPI delivery status (read only), as follows:
/// **0 (Idle)**            Indicates that this local APIC has completed sending any previous IPIs.
/// **1 (Send Pending)**    Indicates that this local APIC has not completed sending the last IPI.
#[derive(Clone, Copy)]
#[repr(u64)]
pub enum DeliveryStatus {
    Idle = 0,
    #[expect(dead_code)]
    SendPending = 1,
}

#[derive(Clone, Copy)]
#[repr(u64)]
pub enum DestinationMode {
    Physical = 0,
    #[expect(dead_code)]
    Logical = 1,
}

#[derive(Clone, Copy)]
#[repr(u64)]
pub enum DeliveryMode {
    /// Delivers the interrupt specified in the vector field to the target processor or processors.
    Fixed = 0b000,
    /// Same as fixed mode, except that the interrupt is delivered to the processor executing at
    /// the lowest priority among the set of processors specified in the destination field. The
    /// ability for a processor to send a lowest priority IPI is model specific and should be
    /// avoided by BIOS and operating system software.
    #[expect(dead_code)]
    LowestPriority = 0b001,
    /// Non-Maskable Interrupt
    #[expect(dead_code)]
    Smi = 0b010,
    _Reserved = 0b011,
    /// System Management Interrupt
    #[expect(dead_code)]
    Nmi = 0b100,
    /// Delivers an INIT request to the target processor or processors, which causes them to
    /// perform an initialization.
    Init = 0b101,
    /// Start-up Interrupt
    StartUp = 0b110,
}

#[derive(Debug)]
pub enum ApicInitError {
    /// No x2APIC or xAPIC found.
    NoApic,
}

/* `DivideConfig as u32` in `XApic::set_timer_div_config` needs `Copy` for the
 * spec-mode enum-to-integer cast (`vstd`'s `spec_cast_integer`); deriving it
 * on this unit-only enum only adds a trait impl.
 * Origin Rust: <none; new derive on DivideConfig>
 */

#[derive(Debug, Clone, Copy)]
#[repr(u32)]
#[expect(dead_code)]
pub enum DivideConfig {
    Divide1 = 0b1011,
    Divide2 = 0b0000,
    Divide4 = 0b0001,
    Divide8 = 0b0010,
    Divide16 = 0b0011,
    Divide32 = 0b1000,
    Divide64 = 0b1001,
    Divide128 = 0b1010,
}

/*
pub fn init(io_mem_builder: &IoMemAllocatorBuilder) -> Result<(), ApicInitError> {
    if x2apic::X2Apic::has_x2apic() {
        log::info!("x2APIC found!");
        APIC_TYPE.call_once(|| ApicType::X2Apic);
        Ok(())
    } else if xapic::XApic::has_xapic() {
        log::info!("xAPIC found!");
        let base_address = get_xapic_base_address();
        io_mem_builder.remove(base_address..(base_address + size_of::<[u32; 256]>()));
        APIC_TYPE.call_once(|| ApicType::XApic);
        Ok(())
    } else {
        log::warn!("Neither x2APIC nor xAPIC found!");
        Err(ApicInitError::NoApic)
    }
}

pub fn exists() -> bool {
    APIC_TYPE.is_completed()
}
*/

// Auxiliary lemmas for the ICR bit-field encoding proofs. Destination facts
// stay named: `by (bit_vector)` cannot encode enum casts.
/// Bit-level facts about the ICR field encoding, for a destination field that
/// occupies bits 32 and above.
proof fn lemma_icr_or_value_field_bits(
    dest_shifted: u64,
    sh: u64,
    tm: u64,
    lv: u64,
    ds: u64,
    dis: u64,
    dm: u64,
    v: u64,
)
    by (bit_vector)
    requires
        (dest_shifted & 0xffff_ffff) == 0,
        sh <= 3,
        tm <= 1,
        lv <= 1,
        ds <= 1,
        dis <= 1,
        dm <= 7,
        v <= 0xff,
    ensures
        (icr_or_value(dest_shifted, sh, tm, lv, ds, dis, dm, v) & 0xff) == v,
        ((icr_or_value(dest_shifted, sh, tm, lv, ds, dis, dm, v) >> 8) & 0x7) == dm,
        ((icr_or_value(dest_shifted, sh, tm, lv, ds, dis, dm, v) >> 11) & 0x1) == dis,
        ((icr_or_value(dest_shifted, sh, tm, lv, ds, dis, dm, v) >> 12) & 0x1) == ds,
        ((icr_or_value(dest_shifted, sh, tm, lv, ds, dis, dm, v) >> 14) & 0x1) == lv,
        ((icr_or_value(dest_shifted, sh, tm, lv, ds, dis, dm, v) >> 15) & 0x1) == tm,
        ((icr_or_value(dest_shifted, sh, tm, lv, ds, dis, dm, v) >> 18) & 0x3) == sh,
        // Bit 13 and bits 16-17 are reserved and always zero.
        (icr_or_value(dest_shifted, sh, tm, lv, ds, dis, dm, v) & 0x32000) == 0,
{
}

/// The xAPIC destination occupies bits 56-63 of the ICR value.
proof fn lemma_icr_or_value_xapic_dest(
    d: u8,
    sh: u64,
    tm: u64,
    lv: u64,
    ds: u64,
    dis: u64,
    dm: u64,
    v: u64,
)
    by (bit_vector)
    requires
        sh <= 3,
        tm <= 1,
        lv <= 1,
        ds <= 1,
        dis <= 1,
        dm <= 7,
        v <= 0xff,
    ensures
        (icr_or_value((d as u64) << 56, sh, tm, lv, ds, dis, dm, v) >> 56) == d as u64,
{
}

/// The x2APIC destination occupies bits 32-63 of the ICR value.
proof fn lemma_icr_or_value_x2apic_dest(
    d: u32,
    sh: u64,
    tm: u64,
    lv: u64,
    ds: u64,
    dis: u64,
    dm: u64,
    v: u64,
)
    by (bit_vector)
    requires
        sh <= 3,
        tm <= 1,
        lv <= 1,
        ds <= 1,
        dis <= 1,
        dm <= 7,
        v <= 0xff,
    ensures
        (icr_or_value((d as u64) << 32, sh, tm, lv, ds, dis, dm, v) >> 32) == d as u64,
{
}

} // verus!
