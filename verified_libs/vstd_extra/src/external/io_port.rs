//! Specifications for x86 I/O-port access types and traits.
use core::mem::size_of;

use vstd::prelude::*;
use x86_64::{
    instructions::port::{ReadWriteAccess, WriteOnlyAccess},
    structures::port::{PortRead, PortWrite},
};

verus! {

/// Whether a `T`-typed access at `port` fits in the PIO byte range `0..=u16::MAX`.
///
/// Uninterpreted: `PortRead`/`PortWrite` are user-implementable, so meaning comes only from
/// the trusted widths in [`group_io_port_models`]. ISA-level fact only — no claim about
/// device decoding, access permission, or ownership.
pub uninterp spec fn valid_io_port_access<T>(port: u16) -> bool;

/// Trusted: `u8` ports are written and read via `outb`/`inb`.
pub broadcast axiom fn axiom_u8_pio_model(port: u16)
    ensures
        #[trigger] valid_io_port_access::<u8>(port) <==> port + size_of::<u8>() <= u16::MAX + 1,
;

/// Trusted: `u16` ports are written and read via `outw`/`inw`.
pub broadcast axiom fn axiom_u16_pio_model(port: u16)
    ensures
        #[trigger] valid_io_port_access::<u16>(port) <==> port + size_of::<u16>() <= u16::MAX + 1,
;

/// Trusted: `u32` ports are written and read via `outl`/`inl`.
pub broadcast axiom fn axiom_u32_pio_model(port: u16)
    ensures
        #[trigger] valid_io_port_access::<u32>(port) <==> port + size_of::<u32>() <= u16::MAX + 1,
;

/// The trusted instances of the PIO model.
pub broadcast group group_io_port_models {
    axiom_u8_pio_model,
    axiom_u16_pio_model,
    axiom_u32_pio_model,
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
            valid_io_port_access::<Self>(port),
    ;
}

/// Trusted specification boundary for values that can be written to an x86 I/O port.
#[verifier::external_trait_specification]
pub trait ExPortWrite {
    type ExternalTraitSpecificationFor: PortWrite;

    /// A port write has no modeled logical effect on kernel memory.
    unsafe fn write_to_port(port: u16, value: Self) where Self: Sized
        requires
            valid_io_port_access::<Self>(port),
    ;
}

} // verus!
