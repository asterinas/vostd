// SPDX-License-Identifier: MPL-2.0
//! External specifications for the `acpi` crate (`acpi = 5.2.0`).
use core::ptr::NonNull;

use ::acpi::{AcpiError, AcpiHandler, AcpiTables, PhysicalMapping, rsdp::Rsdp, sdt::SdtHeader};
use vstd::{layout::size_of, prelude::*};

verus! {

/// Verus proxy for the ACPI System Description Table header.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExSdtHeader(SdtHeader);

/// Verus proxy for `acpi::AcpiError`.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAcpiError(AcpiError);

/// Verus proxy for `acpi::rsdp::Rsdp`.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRsdp(Rsdp);

/// External trait specification for `acpi::AcpiHandler` (`acpi 5.2.0`, `src/handler.rs`).
///
/// `map_physical_region` is intentionally omitted here because declaring it with return type
/// `PhysicalMapping<Self, T>` triggers a Verus `recursive_types.rs` trait-impl SCC cycle
/// through `PhysicalMapping::<Self, T>::new`.
#[verifier::external_trait_specification]
pub trait ExAcpiHandler: Clone {
    type ExternalTraitSpecificationFor: AcpiHandler;

    fn unmap_physical_region<T>(region: &PhysicalMapping<Self, T>) where Self: AcpiHandler;
}

/// Verus proxy for `acpi::PhysicalMapping<H, T>`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(H)]
#[verifier::reject_recursive_types(T)]
pub struct ExPhysicalMapping<H: AcpiHandler, T>(PhysicalMapping<H, T>);

/// Spec-level field projections for `acpi::PhysicalMapping<H, T>`.
pub trait PhysicalMappingSpec<H: AcpiHandler, T> {
    spec fn physical_start_spec(&self) -> usize;

    spec fn virtual_start_spec(&self) -> NonNull<T>;

    spec fn region_length_spec(&self) -> usize;

    spec fn mapped_length_spec(&self) -> usize;

    spec fn handler_spec(&self) -> H;
}

impl<H: AcpiHandler, T> PhysicalMappingSpec<H, T> for PhysicalMapping<H, T> {
    uninterp spec fn physical_start_spec(&self) -> usize;

    uninterp spec fn virtual_start_spec(&self) -> NonNull<T>;

    uninterp spec fn region_length_spec(&self) -> usize;

    uninterp spec fn mapped_length_spec(&self) -> usize;

    uninterp spec fn handler_spec(&self) -> H;
}

/// Audited against `acpi 5.2.0`, `src/handler.rs:38-62`:
/// stores all five arguments verbatim and cannot panic.
/// Enforces the documented length invariants (`region_length >= size_of::<T>()` and
/// `mapped_length >= region_length`); physical-memory validity remains the `unsafe` caller obligation.
pub assume_specification<H: AcpiHandler, T>[ PhysicalMapping::<H, T>::new ](
    physical_start: usize,
    virtual_start: NonNull<T>,
    region_length: usize,
    mapped_length: usize,
    handler: H,
) -> (ret: PhysicalMapping<H, T>)
    requires
        size_of::<T>() <= region_length <= mapped_length,
    ensures
        ret.physical_start_spec() == physical_start,
        ret.virtual_start_spec() == virtual_start,
        ret.region_length_spec() == region_length,
        ret.mapped_length_spec() == mapped_length,
        ret.handler_spec() == handler,
    opens_invariants none
    no_unwind
;

/// Spec wrapper used by `#[verifier::when_used_as_spec]` for `PhysicalMapping::physical_start`.
#[verifier::inline]
pub open spec fn physical_start_spec_wrapper<H: AcpiHandler, T>(
    mapping: &PhysicalMapping<H, T>,
) -> usize {
    mapping.physical_start_spec()
}

/// Audited against `acpi 5.2.0`, `src/handler.rs:64-66`:
/// returns `self.physical_start` and cannot panic.
#[verifier::when_used_as_spec(physical_start_spec_wrapper)]
pub assume_specification<H: AcpiHandler, T>[ PhysicalMapping::<H, T>::physical_start ](
    mapping: &PhysicalMapping<H, T>,
) -> usize
    returns
        mapping.physical_start_spec(),
    opens_invariants none
    no_unwind
;

/// Verus proxy for `acpi::AcpiTables<H>`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(H)]
pub struct ExAcpiTables<H: AcpiHandler>(AcpiTables<H>);

/// Spec-level field projections for `acpi::AcpiTables<H>`.
pub trait AcpiTablesSpec<H: AcpiHandler> {
    spec fn revision_spec(&self) -> u8;

    spec fn handler_spec(&self) -> H;
}

impl<H: AcpiHandler> AcpiTablesSpec<H> for AcpiTables<H> {
    uninterp spec fn revision_spec(&self) -> u8;

    uninterp spec fn handler_spec(&self) -> H;
}

/// Model-validity predicate for `acpi::AcpiHandler` implementations whose
/// `map_physical_region`, `unmap_physical_region`, and `Clone` operations are
/// pure, free of interior mutability, and map physical addresses deterministically
/// over the current boot-time physical memory layout.
///
/// Only handlers satisfying this predicate may use the pure functional table-lookup
/// models (`acpi_tables_from_rsdp_spec`, `acpi_tables_from_rsdt_spec`, and
/// `rsdp_search_on_bios_spec`).
pub uninterp spec fn obeys_acpi_handler_model<H: AcpiHandler>() -> bool;

/// Caller validity obligation for `AcpiTables::from_rsdp`: `address` is a readable RSDP
/// physical address and its root table address satisfies the handler's `map_physical_region`
/// safety and address preconditions.
pub uninterp spec fn valid_acpi_rsdp<H: AcpiHandler>(handler: H, address: usize) -> bool;

/// Modeled firmware result of `AcpiTables::from_rsdp(handler, address)`.
pub uninterp spec fn acpi_tables_from_rsdp_spec<H: AcpiHandler>(
    handler: H,
    address: usize,
) -> Result<AcpiTables<H>, AcpiError>;

/// Caller validity obligation for `AcpiTables::from_rsdt`: `address` is a readable RSDT/XSDT
/// physical address whose header and table length satisfy the handler's `map_physical_region`
/// safety and address preconditions.
pub uninterp spec fn valid_acpi_rsdt<H: AcpiHandler>(
    handler: H,
    revision: u8,
    address: usize,
) -> bool;

/// Modeled firmware result of `AcpiTables::from_rsdt(handler, revision, address)`.
pub uninterp spec fn acpi_tables_from_rsdt_spec<H: AcpiHandler>(
    handler: H,
    revision: u8,
    address: usize,
) -> Result<AcpiTables<H>, AcpiError>;

/// Caller validity obligation for `Rsdp::search_for_on_bios`: the platform is BIOS-compatible
/// and the handler's `map_physical_region` safety and address preconditions hold across the
/// BIOS probe windows.
pub uninterp spec fn valid_bios_rsdp_search<H: AcpiHandler>(handler: H) -> bool;

/// Modeled firmware result of `Rsdp::search_for_on_bios(handler)`.
pub uninterp spec fn rsdp_search_on_bios_spec<H: AcpiHandler>(handler: H) -> Result<
    PhysicalMapping<H, Rsdp>,
    AcpiError,
>;

/// Audited against `acpi 5.2.0`, `src/lib.rs:205-211`:
/// maps the RSDP at `address`, validates it, and maps the root RSDT/XSDT.
pub assume_specification<H: AcpiHandler>[ AcpiTables::<H>::from_rsdp ](
    handler: H,
    address: usize,
) -> (ret: Result<AcpiTables<H>, AcpiError>)
    requires
        obeys_acpi_handler_model::<H>(),
        valid_acpi_rsdp(handler, address),
    ensures
        ret matches Ok(tables) ==> tables.handler_spec() == handler,
    returns
        acpi_tables_from_rsdp_spec(handler, address),
;

/// Audited against `acpi 5.2.0`, `src/lib.rs:260-277`:
/// maps and validates the RSDT (`revision == 0`) or XSDT (`revision != 0`) at `address`.
pub assume_specification<H: AcpiHandler>[ AcpiTables::<H>::from_rsdt ](
    handler: H,
    revision: u8,
    address: usize,
) -> (ret: Result<AcpiTables<H>, AcpiError>)
    requires
        obeys_acpi_handler_model::<H>(),
        valid_acpi_rsdt(handler, revision, address),
    ensures
        ret matches Ok(tables) ==> {
            &&& tables.revision_spec() == revision
            &&& tables.handler_spec() == handler
        },
    returns
        acpi_tables_from_rsdt_spec(handler, revision, address),
;

/// Audited against `acpi 5.2.0`, `src/rsdp.rs:55-98`:
/// probes BIOS memory windows for a valid RSDP and maps it if found.
pub assume_specification<H: AcpiHandler>[ Rsdp::search_for_on_bios ](handler: H) -> Result<
    PhysicalMapping<H, Rsdp>,
    AcpiError,
>
    requires
        obeys_acpi_handler_model::<H>(),
        valid_bios_rsdp_search(handler),
    returns
        rsdp_search_on_bios_spec(handler),
;

} // verus!
