// SPDX-License-Identifier: MPL-2.0
//! External type specifications for the `acpi` crate.
use vstd::prelude::*;

verus! {

/// Verus proxy for the ACPI System Description Table header.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExSdtHeader(::acpi::sdt::SdtHeader);

} // verus!
