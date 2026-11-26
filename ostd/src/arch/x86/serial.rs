// SPDX-License-Identifier: MPL-2.0
//! The console I/O.
use vstd::prelude::*;
use vstd_extra::external::valid_io_port_access;

use super::device::serial::SerialPort;
use crate::io::reserve_io_port_range;

bitflags::bitflags! {
  struct LineSts: u8 {
    const INPUT_FULL = 1;
    const OUTPUT_EMPTY = 1 << 5;
  }
}

#[verus_spec(
    ensures
        CONSOLE_COM1_PORT@ == Seq::new(7, |i: int| (0x3F8 + i) as u16),
        CONSOLE_COM1_PORT@.all(
            |addr: u16| 0x3F8 <= addr < 0x400 && valid_io_port_access::<u8>(addr),
        ),
)]
static CONSOLE_COM1_PORT: SerialPort = unsafe { SerialPort::new(0x3F8) };
reserve_io_port_range!(0x3F8..0x400);

/// Initializes the serial port.
#[verus_spec]
pub(crate) fn init() {
    CONSOLE_COM1_PORT.init();
}

#[verus_spec(ret =>
    ensures
        !ret.contains_unknown_bits(),
)]
fn line_sts() -> LineSts {
    proof! {
        assert forall|bits: u8, mask: u8| #[trigger] ((bits & mask) & !mask) == 0 by {
            assert((bits & mask) & !mask == 0) by (bit_vector);
        }
    }
    LineSts::from_bits_truncate(CONSOLE_COM1_PORT.line_status())
}

/// Sends a byte on the serial port.
// Hardware readiness is not guaranteed, so polling may continue indefinitely.
#[verifier::exec_allows_no_decreases_clause]
#[verus_spec]
pub(crate) fn send(data: u8) {
    match data {
        8 | 0x7F => {
            while !line_sts().contains(LineSts::OUTPUT_EMPTY) {}
            CONSOLE_COM1_PORT.send(8);
            while !line_sts().contains(LineSts::OUTPUT_EMPTY) {}
            CONSOLE_COM1_PORT.send(b' ');
            while !line_sts().contains(LineSts::OUTPUT_EMPTY) {}
            CONSOLE_COM1_PORT.send(8);
        }
        _ => {
            while !line_sts().contains(LineSts::OUTPUT_EMPTY) {}
            CONSOLE_COM1_PORT.send(data);
        }
    }
}
