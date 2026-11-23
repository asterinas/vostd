// SPDX-License-Identifier: MPL-2.0
//! A port-mapped UART. Copied from uart_16550.
#![expect(dead_code)]

use vstd::prelude::*;
use vstd_extra::external::{group_io_port_models, valid_io_port_access};

use crate::{
    arch::device::io_port::{ReadWriteAccess, WriteOnlyAccess},
    io::IoPort,
};
/// A serial port.
///
/// Serial ports are a legacy communications port common on IBM-PC compatible computers.
/// Ref: <https://wiki.osdev.org/Serial_Ports>
#[verus_verify]
pub struct SerialPort {
    /// Data Register
    data: IoPort<u8, ReadWriteAccess>,
    /// Interrupt Enable Register
    int_en: IoPort<u8, WriteOnlyAccess>,
    /// First In First Out Control Register
    fifo_ctrl: IoPort<u8, WriteOnlyAccess>,
    /// Line control Register
    line_ctrl: IoPort<u8, WriteOnlyAccess>,
    /// Modem Control Register
    modem_ctrl: IoPort<u8, WriteOnlyAccess>,
    /// Line status Register
    line_status: IoPort<u8, ReadWriteAccess>,
    /// Modem Status Register
    modem_status: IoPort<u8, ReadWriteAccess>,
}

verus! {

broadcast use group_io_port_models;

impl View for SerialPort {
    type V = Seq<u16>;

    /// Register addresses in offset order, from data through modem status.
    closed spec fn view(&self) -> Seq<u16> {
        seq![
            self.data@,
            self.int_en@,
            self.fifo_ctrl@,
            self.line_ctrl@,
            self.modem_ctrl@,
            self.line_status@,
            self.modem_status@,
        ]
    }
}

} // verus!
#[verus_verify]
impl SerialPort {
    /// Creates a serial port.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the base port is a valid serial base port and that it has
    /// exclusive ownership of the serial ports.
    #[verus_spec(ret =>
        requires
            port <= u16::MAX - 6,
        ensures
            ret@.len() == 7,
            forall|i: int| 0 <= i < 7 ==> {
                &&& #[trigger] ret@[i] == port + i
                &&& valid_io_port_access::<u8>(ret@[i])
            },
    )]
    pub const unsafe fn new(port: u16) -> Self {
        // SAFETY: The safety is upheld by the caller.
        unsafe {
            Self {
                data: IoPort::new(port),
                int_en: IoPort::new(port + 1),
                fifo_ctrl: IoPort::new(port + 2),
                line_ctrl: IoPort::new(port + 3),
                modem_ctrl: IoPort::new(port + 4),
                line_status: IoPort::new(port + 5),
                modem_status: IoPort::new(port + 6),
            }
        }
    }

    /// Initializes the serial port.
    #[verus_spec(
        ensures
            self@.len() == 7,
            forall|i: int| 0 <= i < 5 ==> valid_io_port_access::<u8>(#[trigger] self@[i]),
    )]
    pub fn init(&self) {
        // Disable interrupts
        self.int_en.write(0x00);
        // Enable DLAB
        self.line_ctrl.write(0x80);
        // Set maximum speed to 38400 bps by configuring DLL and DLM
        self.data.write(0x03);
        self.int_en.write(0x00);
        // Disable DLAB and set data word length to 8 bits
        self.line_ctrl.write(0x03);
        // Enable FIFO, clear TX/RX queues and
        // set interrupt watermark at 14 bytes
        self.fifo_ctrl.write(0xC7);
        // Mark data terminal ready, signal request to send
        // and enable auxiliary output #2 (used as interrupt line for CPU)
        self.modem_ctrl.write(0x0B);
        // Enable interrupts
        self.int_en.write(0x01);
    }

    /// Sends data to the data port
    #[inline]
    #[verus_spec(
        ensures
            self@.len() == 7,
            valid_io_port_access::<u8>(self@[0]),
    )]
    pub fn send(&self, data: u8) {
        self.data.write(data);
    }

    /// Receives data from the data port
    #[inline]
    #[verus_spec(
        ensures
            self@.len() == 7,
            valid_io_port_access::<u8>(self@[0]),
    )]
    pub fn recv(&self) -> u8 {
        self.data.read()
    }

    /// Gets line status
    #[inline]
    #[verus_spec(
        ensures
            self@.len() == 7,
            valid_io_port_access::<u8>(self@[5]),
    )]
    pub fn line_status(&self) -> u8 {
        self.line_status.read()
    }
}
