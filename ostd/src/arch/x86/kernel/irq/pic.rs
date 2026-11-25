// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;
use vstd_extra::info;

/*use log::info;*/

use crate::{
    arch::device::io_port::WriteOnlyAccess,
    io::{IoPort, sensitive_io_port},
};

sensitive_io_port! {
    unsafe {
        static MASTER_CMD: IoPort<u8, WriteOnlyAccess> = IoPort::new(0x20);
        static MASTER_DATA: IoPort<u8, WriteOnlyAccess> = IoPort::new(0x21);
        static SLAVE_CMD: IoPort<u8, WriteOnlyAccess> = IoPort::new(0xA0);
        static SLAVE_DATA: IoPort<u8, WriteOnlyAccess> = IoPort::new(0xA1);
    }
}

crate::const_assert!(MASTER_DATA.port() == 0x21 && SLAVE_DATA.port() == 0xA1);

#[verus_verify]
const IRQ_OFFSET: u8 = 0x20;

verus! {

pub open spec fn mask_writes(master_mask: u8, slave_mask: u8) -> Seq<(u16, u8)> {
    seq![
        (0x20, 0x11),
        (0xA0, 0x11),
        (0x21, 0x20),
        (0xA1, 0x28),
        (0x21, 4),
        (0xA1, 2),
        (0x21, 1),
        (0xA1, 1),
        (0x21, master_mask),
        (0xA1, slave_mask),
    ]
}

} // verus!
/// Initializes and disables the 8259 Programmable Interrupt Controller (PIC).
/// The checked writes consume the prefix of the caller's expected port writes.
#[verus_spec(
    with Tracked(remaining): Tracked<&mut Ghost<Seq<(u16, u8)>>>,
    requires mask_writes(0xff, 0xff).is_prefix_of(old(remaining)@),
    ensures old(remaining)@ == mask_writes(0xff, 0xff) + final(remaining)@,
)]
pub fn init_and_disable() {
    info!("[PIC]: Initializing as disabled");

    #[verus_spec(with Tracked(remaining))]
    self::set_mask(0xff, 0xff);
}

#[verus_spec(
    with Tracked(remaining): Tracked<&mut Ghost<Seq<(u16, u8)>>>,
    requires mask_writes(master_mask, slave_mask).is_prefix_of(old(remaining)@),
    ensures old(remaining)@ == mask_writes(master_mask, slave_mask) + final(remaining)@,
)]
fn set_mask(master_mask: u8, slave_mask: u8) {
    // Start initialization
    #[verus_spec(with Tracked(Some(remaining)))]
    MASTER_CMD.write(0x11);
    #[verus_spec(with Tracked(Some(remaining)))]
    SLAVE_CMD.write(0x11);

    // Set offsets
    // - Map master PIC vector 0x00~0x07 to IRQ number 0x20~0x27
    #[verus_spec(with Tracked(Some(remaining)))]
    MASTER_DATA.write(IRQ_OFFSET);
    // - Map slave PIC vector 0x00~0x07 to IRQ number 0x28~0x2f
    #[verus_spec(with Tracked(Some(remaining)))]
    SLAVE_DATA.write(IRQ_OFFSET + 0x08);

    // Set up cascade (there is a slave PIC at IRQ2)
    #[verus_spec(with Tracked(Some(remaining)))]
    MASTER_DATA.write(4);
    #[verus_spec(with Tracked(Some(remaining)))]
    SLAVE_DATA.write(2);

    // Set up interrupt mode (1 is 8086/88 mode, 2 is auto EOI)
    #[verus_spec(with Tracked(Some(remaining)))]
    MASTER_DATA.write(1);
    #[verus_spec(with Tracked(Some(remaining)))]
    SLAVE_DATA.write(1);

    // Mask interrupts
    #[verus_spec(with Tracked(Some(remaining)))]
    MASTER_DATA.write(master_mask);
    #[verus_spec(with Tracked(Some(remaining)))]
    SLAVE_DATA.write(slave_mask);
    proof! { assert(old(remaining)@ =~= mask_writes(master_mask, slave_mask) + remaining@); }
}
