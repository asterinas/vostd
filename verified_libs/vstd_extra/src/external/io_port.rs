//! Specifications for x86 I/O-port access types and traits.
use core::mem::size_of;

use vstd::prelude::*;
use x86_64::{
    instructions::port::{ReadWriteAccess, WriteOnlyAccess},
    structures::port::{PortRead, PortWrite},
};

verus! {

/// Whether `port` is representable in the 16-bit x86 I/O-port address space.
///
/// This is only the ISA-level validity condition. It does not claim that a device decodes the
/// port, that the current CPU context may access it, or that the caller owns it.
pub open spec fn valid_io_port_number(port: int) -> bool {
    0 <= port <= u16::MAX as int
}

/// Whether an access of type `T` is fully contained in the x86 I/O-port address space.
pub open spec fn valid_io_port_access<T>(port: int) -> bool {
    &&& valid_io_port_number(port)
    &&& port + size_of::<T>() <= u16::MAX as int + 1
}

/// Opaque specification boundary for the third-party read/write access marker.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExReadWriteAccess(ReadWriteAccess);

/// Opaque specification boundary for the third-party write-only access marker.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExWriteOnlyAccess(WriteOnlyAccess);

/// Trusted specification boundary for values that can be read from an x86 I/O port.
#[verifier::external_trait_specification]
pub trait ExPortRead {
    type ExternalTraitSpecificationFor: PortRead;

    /// A port read can produce any value supplied by the device.
    unsafe fn read_from_port(port: u16) -> Self where Self: Sized
        requires
            valid_io_port_access::<Self>(port as int),
    ;
}

/// Trusted specification boundary for values that can be written to an x86 I/O port.
#[verifier::external_trait_specification]
pub trait ExPortWrite {
    type ExternalTraitSpecificationFor: PortWrite;

    /// A port write has no modeled logical effect on kernel memory.
    unsafe fn write_to_port(port: u16, value: Self) where Self: Sized
        requires
            valid_io_port_access::<Self>(port as int),
    ;
}

} // verus!
