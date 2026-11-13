//! Specifications for x86 I/O-port access types and traits.
use core::mem::size_of;

use vstd::prelude::*;
use x86_64::{
    instructions::port::{ReadWriteAccess, WriteOnlyAccess},
    structures::port::{PortRead, PortWrite},
};

verus! {

/// Whether `T` follows the standard x86 PIO width and address-validity model.
/// Implementing `PortRead` or `PortWrite` alone does not establish this law.
pub uninterp spec fn obeys_io_port_access_spec<T>() -> bool;

/// Whether a `T`-typed access at `port` fits in the PIO byte range `0..=u16::MAX`.
///
/// Uninterpreted: `PortRead`/`PortWrite` are user-implementable, so meaning comes only from
/// the trusted widths in [`group_io_port_models`]. ISA-level fact only — no claim about
/// device decoding, access permission, or ownership.
///
/// Used as a precondition to require full-width bounds validity, which
/// `IoPort::acquire_overlapping` does not check at runtime:
/// <https://github.com/asterinas/asterinas/issues/4209>.
pub uninterp spec fn valid_io_port_access<T>(port: u16) -> bool;

/// Trusted: types obeying the model use a 1-, 2-, or 4-byte access within the PIO space.
pub broadcast axiom fn axiom_io_port_access_spec<T>(port: u16)
    ensures
        #[trigger] obeys_io_port_access_spec::<T>() ==> (#[trigger] valid_io_port_access::<T>(port)
            <==> {
            &&& size_of::<T>() == 1 || size_of::<T>() == 2 || size_of::<T>() == 4
            &&& port + size_of::<T>() <= u16::MAX + 1
        }),
;

/// Trusted: `u8` ports are written and read via `outb`/`inb`.
pub broadcast axiom fn axiom_u8_obeys_io_port_access_spec()
    ensures
        #[trigger] obeys_io_port_access_spec::<u8>(),
;

/// Trusted: `u16` ports are written and read via `outw`/`inw`.
pub broadcast axiom fn axiom_u16_obeys_io_port_access_spec()
    ensures
        #[trigger] obeys_io_port_access_spec::<u16>(),
;

/// Trusted: `u32` ports are written and read via `outl`/`inl`.
pub broadcast axiom fn axiom_u32_obeys_io_port_access_spec()
    ensures
        #[trigger] obeys_io_port_access_spec::<u32>(),
;

/// The trusted instances of the PIO model.
pub broadcast group group_io_port_models {
    axiom_io_port_access_spec,
    axiom_u8_obeys_io_port_access_spec,
    axiom_u16_obeys_io_port_access_spec,
    axiom_u32_obeys_io_port_access_spec,
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
