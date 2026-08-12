// SPDX-License-Identifier: MPL-2.0
//! I/O port access.
pub use x86_64::{
    instructions::port::{
        PortReadAccess as IoPortReadAccess, PortWriteAccess as IoPortWriteAccess, ReadOnlyAccess,
        ReadWriteAccess, WriteOnlyAccess,
    },
    structures::port::{PortRead, PortWrite},
};

use vstd::prelude::*;

verus! {

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
    unsafe fn read_from_port(port: u16) -> Self where Self: Sized;
}

/// Trusted specification boundary for values that can be written to an x86 I/O port.
#[verifier::external_trait_specification]
pub trait ExPortWrite {
    type ExternalTraitSpecificationFor: PortWrite;

    /// A port write has no modeled logical effect on kernel memory.
    unsafe fn write_to_port(port: u16, value: Self) where Self: Sized;
}

} // verus!
