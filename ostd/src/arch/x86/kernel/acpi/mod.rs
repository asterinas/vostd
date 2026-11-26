// SPDX-License-Identifier: MPL-2.0
pub mod dmar;
pub mod remapping;

use vstd::{layout::size_of, prelude::*};
use vstd_extra::external::acpi::{
    AcpiTablesSpec, PhysicalMappingSpec, acpi_tables_from_rsdp_spec, acpi_tables_from_rsdt_spec,
    obeys_acpi_handler_model, rsdp_search_on_bios_spec, valid_acpi_rsdp, valid_acpi_rsdt,
    valid_bios_rsdp_search,
};

use crate::{boot::EarlyBootInfoInit, mm::kspace::LINEAR_MAPPING_BASE_VADDR};

use core::ptr::NonNull;

use acpi::{AcpiHandler, AcpiTables, rsdp::Rsdp};
/* use log::warn; */

use crate::{
    boot::{self, BootloaderAcpiArg},
    mm::paddr_to_vaddr,
};

verus! {

/// Reviewed pure-handler instance: [`AcpiMemoryHandler`] is a zero-sized marker struct
/// with value-preserving `Clone`, no interior mutability, and deterministic linear-mapping
/// `map_physical_region` over the boot-time physical memory layout.
pub broadcast axiom fn axiom_acpi_memory_handler_obeys_model()
    ensures
        #[trigger] obeys_acpi_handler_model::<AcpiMemoryHandler>(),
;

/// Whether firmware ACPI tables satisfy the safety and lookup preconditions of [`get_acpi_tables`].
pub(crate) open spec fn valid_bootloader_acpi_tables(arg: BootloaderAcpiArg) -> bool {
    match arg {
        BootloaderAcpiArg::Rsdp(addr) => {
            &&& valid_acpi_rsdp(AcpiMemoryHandler {  }, addr)
            &&& acpi_tables_from_rsdp_spec(AcpiMemoryHandler {  }, addr) is Ok
        },
        BootloaderAcpiArg::Rsdt(addr) => {
            &&& valid_acpi_rsdt(AcpiMemoryHandler {  }, 0, addr)
            &&& acpi_tables_from_rsdt_spec(AcpiMemoryHandler {  }, 0, addr) is Ok
        },
        BootloaderAcpiArg::Xsdt(addr) => {
            &&& valid_acpi_rsdt(AcpiMemoryHandler {  }, 1, addr)
            &&& acpi_tables_from_rsdt_spec(AcpiMemoryHandler {  }, 1, addr) is Ok
        },
        BootloaderAcpiArg::NotProvided => {
            &&& valid_bios_rsdp_search(AcpiMemoryHandler {  })
            &&& rsdp_search_on_bios_spec(AcpiMemoryHandler {  }) matches Ok(map) ==> {
                &&& valid_acpi_rsdp(AcpiMemoryHandler {  }, map.physical_start())
                &&& acpi_tables_from_rsdp_spec(AcpiMemoryHandler {  }, map.physical_start()) is Ok
            }
        },
    }
}

/// Modeled result of [`get_acpi_tables`] for a given [`BootloaderAcpiArg`].
pub(crate) open spec fn expected_acpi_tables(arg: BootloaderAcpiArg) -> Option<
    AcpiTables<AcpiMemoryHandler>,
> {
    match arg {
        BootloaderAcpiArg::Rsdp(addr) => Some(
            acpi_tables_from_rsdp_spec(AcpiMemoryHandler {  }, addr)->Ok_0,
        ),
        BootloaderAcpiArg::Rsdt(addr) => Some(
            acpi_tables_from_rsdt_spec(AcpiMemoryHandler {  }, 0, addr)->Ok_0,
        ),
        BootloaderAcpiArg::Xsdt(addr) => Some(
            acpi_tables_from_rsdt_spec(AcpiMemoryHandler {  }, 1, addr)->Ok_0,
        ),
        BootloaderAcpiArg::NotProvided => match rsdp_search_on_bios_spec(AcpiMemoryHandler {  }) {
            Ok(map) => Some(
                acpi_tables_from_rsdp_spec(AcpiMemoryHandler {  }, map.physical_start())->Ok_0,
            ),
            Err(_) => None,
        },
    }
}

} // verus!
#[verus_verify]
#[derive(Debug, Clone)]
pub struct AcpiMemoryHandler {}

#[verus_verify]
impl AcpiHandler for AcpiMemoryHandler {
    // Trusted: see `ExAcpiHandler` for why this contract bypasses the trait spec.
    #[verifier::assume_compatibility_with_trait_spec]
    #[verus_spec(ret =>
        requires
            physical_address + LINEAR_MAPPING_BASE_VADDR < usize::MAX,
            size >= size_of::<T>(),
        ensures
            ret.physical_start() == physical_address,
            ret.virtual_start_spec().as_ptr().addr() == paddr_to_vaddr(physical_address),
            ret.region_length_spec() == size,
            ret.mapped_length_spec() == size,
            ret.handler_spec() == *self,
    )]
    unsafe fn map_physical_region<T>(
        &self,
        physical_address: usize,
        size: usize,
    ) -> acpi::PhysicalMapping<Self, T> {
        proof! {
            assert(LINEAR_MAPPING_BASE_VADDR > 0) by (compute_only);
        }
        /* Verus does not support casting `usize` directly to `*mut T`.
         * Origin Rust: let virtual_address = NonNull::new(paddr_to_vaddr(physical_address) as *mut T).unwrap();
         */
        let virtual_address = NonNull::new(core::ptr::with_exposed_provenance_mut::<T>(
            paddr_to_vaddr(physical_address),
        ))
        .unwrap();

        // SAFETY: The caller should guarantee that `physical_address..physical_address + size` is
        // part of the ACPI table. Then the memory region is mapped to `virtual_address` and is
        // valid for read and immutable dereferencing.
        // FIXME: The caller guarantee only holds if we trust the hardware to provide a valid ACPI
        // table. Otherwise, if the table is corrupted, it may reference arbitrary memory regions.
        unsafe {
            acpi::PhysicalMapping::new(physical_address, virtual_address, size, size, self.clone())
        }
    }

    fn unmap_physical_region<T>(_region: &acpi::PhysicalMapping<Self, T>) {}
}

#[verus_spec(ret =>
    with Tracked(boot_info): Tracked<&EarlyBootInfoInit>
    requires
        valid_bootloader_acpi_tables(boot_info@.acpi_arg),
    ensures
        ret matches Some(tables) ==> {
            &&& tables.handler_spec() == (AcpiMemoryHandler {})
            &&& boot_info@.acpi_arg is Rsdt ==> tables.revision_spec() == 0
            &&& boot_info@.acpi_arg is Xsdt ==> tables.revision_spec() == 1
        },
    returns expected_acpi_tables(boot_info@.acpi_arg),
)]
pub(crate) fn get_acpi_tables() -> Option<AcpiTables<AcpiMemoryHandler>> {
    proof! {
        broadcast use axiom_acpi_memory_handler_obeys_model;
    }
    /* Verus cannot reference `spin::Once` static `EARLY_INFO` directly.
     * Origin Rust: let acpi_tables = match boot::EARLY_INFO.get().unwrap().acpi_arg {
     */
    let acpi_tables = match (#[verus_spec(with Tracked(boot_info))]
    boot::get_early_info())
    .unwrap()
    .acpi_arg
    {
        BootloaderAcpiArg::Rsdp(addr) => unsafe {
            AcpiTables::from_rsdp(AcpiMemoryHandler {}, addr).unwrap()
        },
        BootloaderAcpiArg::Rsdt(addr) => unsafe {
            AcpiTables::from_rsdt(AcpiMemoryHandler {}, 0, addr).unwrap()
        },
        BootloaderAcpiArg::Xsdt(addr) => unsafe {
            AcpiTables::from_rsdt(AcpiMemoryHandler {}, 1, addr).unwrap()
        },
        BootloaderAcpiArg::NotProvided => {
            // We search by ourselves if the bootloader decides not to provide a rsdp location.
            let rsdp = unsafe { Rsdp::search_for_on_bios(AcpiMemoryHandler {}) };
            match rsdp {
                Ok(map) => unsafe {
                    AcpiTables::from_rsdp(AcpiMemoryHandler {}, map.physical_start()).unwrap()
                },
                Err(_) => {
                    /* warn!("ACPI info not found!"); */
                    return None;
                }
            }
        }
    };

    Some(acpi_tables)
}
