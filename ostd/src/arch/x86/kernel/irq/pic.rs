// SPDX-License-Identifier: MPL-2.0
//! # Verified Properties
//! Port layout, typed access ranges, vector-offset arithmetic and call obligations
//! are verified for arbitrary byte masks. Physical 8259A initialization/masking
//! effects and PIO hardware write ordering are not modeled by these proofs.
//! The original logging call is commented out and does not execute.
use vstd::prelude::*;

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

#[verus_verify]
const IRQ_OFFSET: u8 = 0x20;

/// Initializes and disables the 8259 Programmable Interrupt Controller (PIC).
#[verus_verify]
pub fn init_and_disable() {
    /*info!("[PIC]: Initializing as disabled");*/

    set_mask(0xff, 0xff);
}

#[verus_verify]
fn set_mask(master_mask: u8, slave_mask: u8) {
    // Start initialization
    MASTER_CMD.write(0x11);
    SLAVE_CMD.write(0x11);

    // Set offsets
    // - Map master PIC vector 0x00~0x07 to IRQ number 0x20~0x27
    MASTER_DATA.write(IRQ_OFFSET);
    // - Map slave PIC vector 0x00~0x07 to IRQ number 0x28~0x2f
    proof! {
        assert(IRQ_OFFSET + 0x08 == 0x28);
        assert(IRQ_OFFSET + 0x08 <= u8::MAX);
    }
    SLAVE_DATA.write(IRQ_OFFSET + 0x08);

    // Set up cascade (there is a slave PIC at IRQ2)
    MASTER_DATA.write(4);
    SLAVE_DATA.write(2);

    // Set up interrupt mode (1 is 8086/88 mode, 2 is auto EOI)
    MASTER_DATA.write(1);
    SLAVE_DATA.write(1);

    // Mask interrupts
    MASTER_DATA.write(master_mask);
    SLAVE_DATA.write(slave_mask);
}
