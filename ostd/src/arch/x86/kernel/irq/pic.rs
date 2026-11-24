// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;
use vstd_extra::info;

/*use log::info;*/

use crate::io::recorded_io_ports;

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
#[verus_spec(
    with -> writes: Ghost<Seq<(u16, u8)>>,
    ensures writes@ == mask_writes(0xff, 0xff),
)]
pub fn init_and_disable() {
    info!("[PIC]: Initializing as disabled");

    proof_decl! { let ghost writes; }
    #[verus_spec(with => Ghost(writes))]
    self::set_mask(0xff, 0xff);
    #[verus_spec(with |= Ghost(writes))]
    ()
}

#[verus_spec(
    with -> writes: Ghost<Seq<(u16, u8)>>,
    ensures writes@ == mask_writes(master_mask, slave_mask),
)]
fn set_mask(master_mask: u8, slave_mask: u8) {
    recorded_io_ports! {
        let mut ports;
        unsafe {
            MASTER_CMD = 0x20;
            MASTER_DATA = 0x21;
            SLAVE_CMD = 0xA0;
            SLAVE_DATA = 0xA1;
        }
    }

    // Start initialization
    ports.write(MASTER_CMD, 0x11);
    ports.write(SLAVE_CMD, 0x11);

    // Set offsets
    // - Map master PIC vector 0x00~0x07 to IRQ number 0x20~0x27
    ports.write(MASTER_DATA, IRQ_OFFSET);
    // - Map slave PIC vector 0x00~0x07 to IRQ number 0x28~0x2f
    ports.write(SLAVE_DATA, IRQ_OFFSET + 0x08);

    // Set up cascade (there is a slave PIC at IRQ2)
    ports.write(MASTER_DATA, 4);
    ports.write(SLAVE_DATA, 2);

    // Set up interrupt mode (1 is 8086/88 mode, 2 is auto EOI)
    ports.write(MASTER_DATA, 1);
    ports.write(SLAVE_DATA, 1);

    // Mask interrupts
    ports.write(MASTER_DATA, master_mask);
    ports.write(SLAVE_DATA, slave_mask);
    proof! { assert(ports@ =~= mask_writes(master_mask, slave_mask)); }
    proof_decl! { let ghost history = ports@; }
    #[verus_spec(with |= Ghost(history))]
    ()
}
