// SPDX-License-Identifier: MPL-2.0
use vstd::{predicate::Predicate, prelude::*};
use vstd_extra::ownership::Inv;

use crate::{
    error::Error,
    mm::{
        dma::Daddr,
        frame::segment::USegment,
        io::{VmIo, VmIoOwner, VmReader},
        Paddr,
    },
    sync::{AtomicDataWithOwner, PreemptDisabled, RoArc, RwArc, RwLockReadGuard},
};

use super::HasDaddr;

verus! {

/// A streaming DMA mapping. Users must synchronize data
/// before reading or after writing to ensure consistency.
///
/// The mapping is automatically destroyed when this object
/// is dropped.
pub struct DmaStream {
    pub inner: RwArc<DmaStreanInnerAtomic>,
}

impl Inv for DmaStream {
    open spec fn inv(self) -> bool {
        true
    }
}

impl DmaStream {

}

/// The inner part of a [`DmaStream`].
pub struct DmaStreamInner {
    // Note that <dyn Trait> is not supported in verus.
    // pub segment: USegment,
    pub start_daddr: Daddr,
    /// TODO: remove this field when on x86.
    #[expect(unused)]
    pub is_cache_coherent: bool,
    pub direction: DmaDirection,
}

pub tracked struct DmaStreaInnerOwner {}

pub type DmaStreanInnerAtomic = AtomicDataWithOwner<DmaStreamInner, DmaStreaInnerOwner>;

#[verus_verify]
impl DmaStream {
    /// Returns the starting device address of the DMA stream.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The caller must hold the [`DmaStreaInnerOwner`] invariant for the inner data of the [`DmaStream`].
    /// ## Postconditions
    /// - The returned device address is equal to the `start_daddr` field of the inner data of the [`DmaStream`].
    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        ensures
            r == this@.data.start_daddr,
    )]
    pub fn daddr(this: &RwLockReadGuard<DmaStreanInnerAtomic, PreemptDisabled>) -> Daddr {
        this.data.start_daddr
    }

    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        ensures
            r == this@.data.direction,
    )]
    pub fn direction(this: &RwLockReadGuard<DmaStreanInnerAtomic, PreemptDisabled>) -> DmaDirection {
        this.data.direction
    }

    /// Returns the physical address corresponding to the starting device address of the DMA stream.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The caller must hold the [`DmaStreaInnerOwner`] invariant for the inner data of the [`DmaStream`].
    /// ## Postconditions
    /// - The returned physical address is equal to the `start_daddr` field of the inner data of the [`DmaStream`].
    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        ensures
            // r == this@.data.start_daddr,
    )]
    pub fn paddr(this: &RwLockReadGuard<DmaStreanInnerAtomic, PreemptDisabled>) -> Paddr {
        0
    }

    /// Returns a reader to read data from it.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The caller must hold the [`DmaStreaInnerOwner`] invariant for the inner data of the [`DmaStream`].
    /// - The `direction` field of the inner data of the [`DmaStream`] must not be [`DmaDirection::ToDevice`].
    /// ## Postconditions
    /// - Returns a `VmReader` that can read data from the DMA stream.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> reader_owner: Tracked<VmIoOwner<'a>>,
        requires
            this@.inv(),
            this@.data.direction != DmaDirection::ToDevice,
    )]
    pub fn reader<'a>(this: &'a RwLockReadGuard<DmaStreanInnerAtomic, PreemptDisabled>) -> VmReader<'a> {

    }
}

impl Predicate<DmaStreamInner> for DmaStreaInnerOwner {
    #[verifier::inline]
    open spec fn predicate(&self, v: DmaStreamInner) -> bool {
        // 1. The `start_daddr` field of the inner data must be within the valid device address range.
        &&& 0 <= v.start_daddr <= 0xFFFF_FFFF_FFFF
    }
}

/// `DmaDirection` limits the data flow direction of [`DmaStream`] and
/// prevents users from reading and writing to [`DmaStream`] unexpectedly.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum DmaDirection {
    /// Data flows to the device
    ToDevice,
    /// Data flows from the device
    FromDevice,
    /// Data flows both from and to the device
    Bidirectional,
}

// impl VmIo for DmaStream {

// }

} // verus!
