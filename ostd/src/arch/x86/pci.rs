// SPDX-License-Identifier: MPL-2.0
//! PCI bus access
use vstd::prelude::*;

use super::device::io_port::{ReadWriteAccess, WriteOnlyAccess};
use crate::{bus::pci::PciDeviceLocation, io::IoPort, prelude::*};

verus! {

/// x86 is little-endian, so converting a native-endian `u32` to little endian is the identity.
pub assume_specification[ u32::to_le ](value: u32) -> (result: u32)
    ensures
        result == value,
;

exec static PCI_ADDRESS_PORT: IoPort<u32, WriteOnlyAccess>
    ensures
        PCI_ADDRESS_PORT.well_formed(),
{
    unsafe { IoPort::new(0x0CF8) }
}

exec static PCI_DATA_PORT: IoPort<u32, ReadWriteAccess>
    ensures
        PCI_DATA_PORT.well_formed(),
{
    unsafe { IoPort::new(0x0CFC) }
}

} // verus!
#[verus_verify]
const BIT32_ALIGN_MASK: u32 = 0xFFFC;

#[verus_verify]
#[verus_spec(result => ensures result is Ok)]
pub(crate) fn write32(location: &PciDeviceLocation, offset: u32, value: u32) -> Result<()> {
    PCI_ADDRESS_PORT.write(encode_as_port(location) | (offset & BIT32_ALIGN_MASK));
    PCI_DATA_PORT.write(value.to_le());
    Ok(())
}

#[verus_verify]
#[verus_spec(result => ensures result is Ok)]
pub(crate) fn read32(location: &PciDeviceLocation, offset: u32) -> Result<u32> {
    PCI_ADDRESS_PORT.write(encode_as_port(location) | (offset & BIT32_ALIGN_MASK));
    Ok(PCI_DATA_PORT.read().to_le())
}

#[verus_verify]
#[verus_spec(returns true)]
pub(crate) fn has_pci_bus() -> bool {
    true
}

#[verus_verify]
pub(crate) const MSIX_DEFAULT_MSG_ADDR: u32 = 0xFEE0_0000;

#[verus_verify]
#[verus_spec(address =>
    ensures
        address == MSIX_DEFAULT_MSG_ADDR | 0b1_1000
            | ((remapping_index & 0x7FFF) << 5)
            | ((remapping_index & 0x8000) >> 13),
)]
pub(crate) fn construct_remappable_msix_address(remapping_index: u32) -> u32 {
    // Use remappable format. The bits[4:3] should be always set to 1 according to the manual.
    let mut address = MSIX_DEFAULT_MSG_ADDR | 0b1_1000;

    // Interrupt index[14:0] is on address[19:5] and interrupt index[15] is on address[2].
    address |= (remapping_index & 0x7FFF) << 5;
    address |= (remapping_index & 0x8000) >> 13;

    address
}

/// Encodes the bus, device, and function into a port address for use with the PCI I/O port.
#[verus_verify]
#[verus_spec(port =>
    ensures
        port == (1u32 << 31)
            | ((location.bus as u32) << 16)
            | (((location.device as u32) & 0b11111) << 11)
            | (((location.function as u32) & 0b111) << 8),
)]
fn encode_as_port(location: &PciDeviceLocation) -> u32 {
    // 1 << 31: Configuration enable
    (1 << 31)
        | ((location.bus as u32) << 16)
        | (((location.device as u32) & 0b11111) << 11)
        | (((location.function as u32) & 0b111) << 8)
}
