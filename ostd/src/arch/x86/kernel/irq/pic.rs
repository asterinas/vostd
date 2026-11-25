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

/// Initializes and disables the 8259 Programmable Interrupt Controller (PIC).
#[verus_verify]
pub fn init_and_disable() {
    info!("[PIC]: Initializing as disabled");

    #[verus_spec(with Ghost((0xFFu8, 0xFFu8)))]
    self::set_mask(0xff, 0xff);
}

#[verus_spec(
    with Ghost(masks): Ghost<(u8, u8)>,
    requires (master_mask, slave_mask) == masks,
)]
fn set_mask(master_mask: u8, slave_mask: u8) {
    proof_decl! {
        let tracked mut remaining = Ghost(seq![
            (0x20u16, 0x11u8), (0xA0u16, 0x11u8),
            (0x21u16, 0x20u8), (0xA1u16, 0x28u8),
            (0x21u16, 4u8), (0xA1u16, 2u8),
            (0x21u16, 1u8), (0xA1u16, 1u8),
            (0x21u16, masks.0), (0xA1u16, masks.1),
        ]);
    }
    // Start initialization
    #[verus_spec(with Tracked(Some(&mut remaining)))]
    MASTER_CMD.write(0x11);
    #[verus_spec(with Tracked(Some(&mut remaining)))]
    SLAVE_CMD.write(0x11);

    // Set offsets
    // - Map master PIC vector 0x00~0x07 to IRQ number 0x20~0x27
    #[verus_spec(with Tracked(Some(&mut remaining)))]
    MASTER_DATA.write(IRQ_OFFSET);
    // - Map slave PIC vector 0x00~0x07 to IRQ number 0x28~0x2f
    #[verus_spec(with Tracked(Some(&mut remaining)))]
    SLAVE_DATA.write(IRQ_OFFSET + 0x08);

    // Set up cascade (there is a slave PIC at IRQ2)
    #[verus_spec(with Tracked(Some(&mut remaining)))]
    MASTER_DATA.write(4);
    #[verus_spec(with Tracked(Some(&mut remaining)))]
    SLAVE_DATA.write(2);

    // Set up interrupt mode (1 is 8086/88 mode, 2 is auto EOI)
    #[verus_spec(with Tracked(Some(&mut remaining)))]
    MASTER_DATA.write(1);
    #[verus_spec(with Tracked(Some(&mut remaining)))]
    SLAVE_DATA.write(1);

    // Mask interrupts
    #[verus_spec(with Tracked(Some(&mut remaining)))]
    MASTER_DATA.write(master_mask);
    #[verus_spec(with Tracked(Some(&mut remaining)))]
    SLAVE_DATA.write(slave_mask);
    proof! { assert(remaining@.len() == 0); }
}
