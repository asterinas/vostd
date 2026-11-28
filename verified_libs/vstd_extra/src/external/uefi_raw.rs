// SPDX-License-Identifier: MPL-2.0
//! External specifications for uefi-raw 0.8.0's memory type codes.
//!
//! `MemoryType` is a transparent wrapper around a public `u32`. The
//! associated constant values are trusted to match the definitions in
//! `table::boot`.
//! See <https://docs.rs/uefi-raw/0.8.0/uefi_raw/table/boot/struct.MemoryType.html>.
use vstd::prelude::*;

pub use ::uefi_raw::table::boot::MemoryType;

verus! {

#[verifier::external_type_specification]
pub struct ExMemoryType(MemoryType);

} // verus!
macro_rules! specify_memory_type_constants {
    ($($name:ident = $value:literal),+ $(,)?) => {
        verus! {
            $(
                pub assume_specification[ MemoryType::$name ] -> MemoryType
                    returns
                        MemoryType($value),
                ;
            )+
        }
    };
}

specify_memory_type_constants! {
    RESERVED = 0,
    LOADER_CODE = 1,
    LOADER_DATA = 2,
    BOOT_SERVICES_CODE = 3,
    BOOT_SERVICES_DATA = 4,
    RUNTIME_SERVICES_CODE = 5,
    RUNTIME_SERVICES_DATA = 6,
    CONVENTIONAL = 7,
    UNUSABLE = 8,
    ACPI_RECLAIM = 9,
    ACPI_NON_VOLATILE = 10,
    MMIO = 11,
    MMIO_PORT_SPACE = 12,
    PERSISTENT_MEMORY = 14,
    UNACCEPTED = 15,
}
