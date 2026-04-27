// SPDX-License-Identifier: MPL-2.0
// mod dma_coherent;
mod dma_stream;
#[cfg(ktest)]
mod test;

use alloc::collections::BTreeSet;
use vstd::{predicate::Predicate as DataPredicate, prelude::*};

use crate::sync::{
    AtomicDataWithOwner, Once, PreemptDisabled, SpinLock, SpinLockGuard, TrivialPred,
};

use super::Paddr;

verus! {

pub tracked struct DmaMappingSetOwner {}

impl DataPredicate<SpinLock<BTreeSet<Paddr>, PreemptDisabled>> for DmaMappingSetOwner {
    open spec fn predicate(&self, v: SpinLock<BTreeSet<Paddr>, PreemptDisabled>) -> bool {
        v.wf()
    }
}

/// Set of all physical addresses with dma mapping.
exec static DMA_MAPPING_SET: Once<
    SpinLock<BTreeSet<Paddr>, PreemptDisabled>,
    DmaMappingSetOwner,
    TrivialPred,
>
    ensures
        DMA_MAPPING_SET.wf(),
{
    Once::new(Ghost(TrivialPred))
}

#[inline(always)]
pub fn init() {
    let lock = SpinLock::new(BTreeSet::new());

    proof {
        use_type_invariant(&lock);
    }

    let data = AtomicDataWithOwner::new(lock, Tracked(DmaMappingSetOwner {  }));

    DMA_MAPPING_SET.init(data);
}

/// The device address.
///
/// If a device performs DMA to read or write system
/// memory, the addresses used by the device are device addresses.
/// Daddr can distinguish the address space used by cpu side and
/// the address space used by device side.
pub type Daddr = usize;

#[derive(PartialEq)]
pub enum DmaType {
    Direct,
    Iommu,
}

#[derive(Debug, PartialEq)]
pub enum DmaError {
    InvalidArgs,
    AlreadyMapped,
}

/// A trait for types that have mapped address in the device address space.
pub trait HasDaddr {
    /// Gets the base address of the mapping in the
    /// device address space.
    fn daddr(&self) -> Daddr;
}

#[verifier::inline]
pub open spec fn is_valid_daddr(d: Daddr) -> bool {
    true
}

/// Checks whether the physical addresses has dma mapping.
/// Fail if they have been mapped, otherwise insert them.
#[verus_spec(
    requires
        start_paddr + num_pages * crate::mm::PAGE_SIZE <= usize::MAX,
)]
fn check_and_insert_dma_mapping(start_paddr: Paddr, num_pages: usize) -> bool {
    match DMA_MAPPING_SET.get() {
        None => false,
        Some(mapping_set) => {
            let mut mapping_set = mapping_set.lock();
            let mut i = 0;

            #[verus_spec(
                invariant
                    i <= num_pages,
                    start_paddr + num_pages * crate::mm::PAGE_SIZE <= usize::MAX,
                decreases
                    num_pages - i,
            )]
            while i < num_pages {
                let paddr = start_paddr + (i * crate::mm::PAGE_SIZE);
                if mapping_set.contains(&paddr) {
                    return false;
                }
                i += 1;
            }

            i = 0;
            #[verus_spec(
                invariant
                    i <= num_pages,
                    start_paddr + num_pages * crate::mm::PAGE_SIZE <= usize::MAX,
                decreases
                    num_pages - i,
            )]
            while i < num_pages {
                let paddr = start_paddr + (i * crate::mm::PAGE_SIZE);
                // Failure: complex arguments to $mut parameters are currently unsupported
                // mapping_set.insert(paddr);
                i += 1;
            }

            true
        },
    }
}

#[verifier::external_body]
pub fn dma_type() -> DmaType {
    unimplemented!()
}

} // verus!
/*
use alloc::collections::BTreeSet;

pub use dma_coherent::DmaCoherent;
pub use dma_stream::{DmaDirection, DmaStream, DmaStreamSlice};
use inherit_methods_macro::inherit_methods;
use spin::Once;

use super::Paddr;
use crate::{arch::iommu::has_dma_remapping, mm::PAGE_SIZE, sync::SpinLock};




#[inherit_methods(from = "(**self)")]
impl<T: HasDaddr> HasDaddr for &T {
    fn daddr(&self) -> Daddr;
}

/// Set of all physical addresses with dma mapping.
static DMA_MAPPING_SET: Once<SpinLock<BTreeSet<Paddr>>> = Once::new();

pub fn dma_type() -> DmaType {
    if has_dma_remapping() {
        DmaType::Iommu
    } else {
        DmaType::Direct
    }
}

pub fn init() {
    DMA_MAPPING_SET.call_once(|| SpinLock::new(BTreeSet::new()));
}

/// Checks whether the physical addresses has dma mapping.
/// Fail if they have been mapped, otherwise insert them.
fn check_and_insert_dma_mapping(start_paddr: Paddr, num_pages: usize) -> bool {
    let mut mapping_set = DMA_MAPPING_SET.get().unwrap().disable_irq().lock();
    // Ensure that the addresses used later will not overflow
    start_paddr.checked_add(num_pages * PAGE_SIZE).unwrap();
    for i in 0..num_pages {
        let paddr = start_paddr + (i * PAGE_SIZE);
        if mapping_set.contains(&paddr) {
            return false;
        }
    }
    for i in 0..num_pages {
        let paddr = start_paddr + (i * PAGE_SIZE);
        mapping_set.insert(paddr);
    }
    true
}

/// Removes a physical address from the dma mapping set.
fn remove_dma_mapping(start_paddr: Paddr, num_pages: usize) {
    let mut mapping_set = DMA_MAPPING_SET.get().unwrap().disable_irq().lock();
    // Ensure that the addresses used later will not overflow
    start_paddr.checked_add(num_pages * PAGE_SIZE).unwrap();
    for i in 0..num_pages {
        let paddr = start_paddr + (i * PAGE_SIZE);
        mapping_set.remove(&paddr);
    }
}
*/
