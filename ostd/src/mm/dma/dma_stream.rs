// SPDX-License-Identifier: MPL-2.0
use vstd::{predicate::Predicate, prelude::*};
use vstd_extra::ownership::{Inv, OwnerOf};

use crate::{
    error::Error,
    mm::{
        dma::{dma_type, Daddr, DmaType},
        frame::{segment::SegmentOwner, untyped::AnyUFrameMeta, Segment},
        io::{VmIo, VmIoOwner, VmReader, VmWriter},
        Paddr,
    },
    specs::arch::PAGE_SIZE,
    sync::{AtomicDataWithOwner, PreemptDisabled, RoArc, RwArc, RwLockReadGuard},
};

use super::{check_and_insert_dma_mapping, is_valid_daddr, DmaError, HasDaddr};

verus! {

/// A streaming DMA mapping. Users must synchronize data
/// before reading or after writing to ensure consistency.
///
/// The mapping is automatically destroyed when this object
/// is dropped.
///
/// # Notes
///
/// Due to some verification limitations on the runtime-checked
/// atomic data structures used in the inner part of this struct,
/// we slightly modified the method implementation of the struct
/// where we wrap each method with another layer of method with
/// property checks that convinces the verifier that we have called
/// the method with the correct preconditions.
///
/// Consider the following example:
///
///
/// ```rust,ignore
/// impl<M: AnyUFrameMeta + ?Sized> DmaStream<M> {
///     pub fn some_func(&self) -> SomeThing {
///         let inner = self.inner.do_something();
///     }
/// }
/// ```
///
/// We cannot directly reason about any runtime properties on `self.inner`
/// as no [`view`] can be defined on such types! Thus we do a workaround
/// as the [`deref`]ed type of `self.inner` is [`RwLockReadGuard`] which
/// can be defined with a [`view`], we wrap the method with another layer
/// of method as follows:
///
/// ```rust,ignore
/// impl<M: AnyUFrameMeta + ?Sized> DmaStream<M> {
///     pub fn some_func(&self) -> SomeThing {
///         let inner = self.inner.deref();
///         if check_inner() {
///             return self.some_func_inner(inner);
///         }
///     }
///
///     #[inline(always)]
///     #[verus_spec(r =>
///         requires
///             this@.inv(),
///         ensures
///             r == this@.data.some_field,
///     )]
///     fn some_func_inner(this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>) -> SomeThing {
///         this.data.some_field
///     }
/// }
/// ```
///
/// [`view`]: vstd::view::View::view
pub struct DmaStream<M: AnyUFrameMeta + ?Sized> {
    pub inner: RwArc<DmaStreanInnerAtomic<M>>,
}

impl<M: AnyUFrameMeta + ?Sized> Inv for DmaStream<M> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<M: AnyUFrameMeta + ?Sized> DmaStream<M> {

}

/// The inner part of a [`DmaStream`].
pub struct DmaStreamInner<M: AnyUFrameMeta + ?Sized> {
    /// Verus does not support trait object so we
    /// require the caller to provide an explicit
    /// type parameter `M` to represent the metadata
    /// of the segment.
    pub segment: Segment<M>,
    pub start_daddr: Daddr,
    /// TODO: remove this field when on x86.
    #[expect(unused)]
    pub is_cache_coherent: bool,
    pub direction: DmaDirection,
}

pub tracked struct DmaStreaInnerOwner<M: AnyUFrameMeta + ?Sized> {
    pub tracked segment_owner: SegmentOwner<M>,
}

pub type DmaStreanInnerAtomic<M> = AtomicDataWithOwner<DmaStreamInner<M>, DmaStreaInnerOwner<M>>;

#[verus_verify]
impl<M: AnyUFrameMeta + ?Sized + OwnerOf> DmaStream<M> {
    /// Establishes DMA stream mapping for a given [`Segment<M>`].
    ///
    /// The method fails if the segment already belongs to a DMA mapping.
    #[verus_spec(r =>
        with
            Tracked(segment_owner): Tracked<SegmentOwner<M>>,
        requires
            segment.inv(),
            segment.inv_with(&segment_owner),
    )]
    pub fn map(segment: Segment<M>, direction: DmaDirection, is_cache_coherent: bool) -> Result<
        Self,
        DmaError,
    > {
        let start_paddr = segment.start_paddr();
        let frame_count = segment.size() / PAGE_SIZE;

        if !check_and_insert_dma_mapping(start_paddr, frame_count) {
            return Err(DmaError::AlreadyMapped);
        }
        let start_daddr = match dma_type() {
            DmaType::Direct => {
                // todo: if crate::arch::if_tdx_enabled!...
                // unprotect_gpa_range()
                start_paddr as Daddr
            },
            DmaType::Iommu => {
                let mut i = 0;

                #[verus_spec(
                    invariant
                        i <= frame_count,
                        segment.inv(),
                        start_paddr == segment.start_paddr(),
                        frame_count == segment.size() / PAGE_SIZE,
                    decreases
                        frame_count - i,
                )]
                while i < frame_count {
                    let paddr = start_paddr + i * PAGE_SIZE;

                    // iommu::map...

                    i += 1;
                }

                start_paddr as Daddr
            },
        };

        let tracked inner_owner = DmaStreaInnerOwner {
            segment_owner,
        };

        let inner = AtomicDataWithOwner::new(
            DmaStreamInner {
                segment,
                start_daddr,
                is_cache_coherent,
                direction,
            },
            Tracked(inner_owner),
        );

        let stream = DmaStream {
            inner: RwArc::new(inner),
        };

        Ok(stream)
    }

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
    pub fn daddr(this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>) -> Daddr {
        this.start_daddr
    }

    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        ensures
            r == this@.data.direction,
    )]
    pub fn direction(
        this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>,
    ) -> DmaDirection {
        this.direction
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
        returns
            this@.data.segment.start_paddr(),
    )]
    pub fn paddr(this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>) -> Paddr {
        this.segment.start_paddr()
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
          ensures
            r.inv(),
            reader_owner@.inv(),
            reader_owner@.inv_with_reader(r),
    )]
    pub fn reader<'a>(
        this: &'a RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>,
    ) -> VmReader<'a> {
        proof_decl! {
            let tracked reader_owner: Tracked<VmIoOwner<'a>>;
        }

        proof_with!(=> Tracked(reader_owner));
        let reader = this.segment.reader();

        proof_with!(|= Tracked(reader_owner));
        reader
    }

    /// Returns a writer to write data to it.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The caller must hold the [`DmaStreaInnerOwner`] invariant for the inner data of the [`DmaStream`].
    /// - The `direction` field of the inner data of the [`DmaStream`] must not be [`DmaDirection::FromDevice`].
    /// ## Postconditions
    /// - Returns a `VmWriter` that can write data to the DMA stream.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> writer_owner: Tracked<VmIoOwner<'a>>,
        requires
            this@.inv(),
            this@.data.direction != DmaDirection::FromDevice,
          ensures
            r.inv(),
            writer_owner@.inv(),
            writer_owner@.inv_with_writer(r),
    )]
    pub fn writer<'a>(
        this: &'a RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>,
    ) -> VmWriter<'a> {
        proof_decl! {
            let tracked writer_owner: Tracked<VmIoOwner<'a>>;
        }

        proof_with!(=> Tracked(writer_owner));
        let writer = this.segment.writer();

        proof_with!(|= Tracked(writer_owner));
        writer
    }
}

impl<M: AnyUFrameMeta + ?Sized> Inv for DmaStreamInner<M> {
    open spec fn inv(self) -> bool {
        &&& self.segment.inv()
        &&& is_valid_daddr(self.start_daddr)
    }
}

impl<M: AnyUFrameMeta + ?Sized> Inv for DmaStreaInnerOwner<M> {
    open spec fn inv(self) -> bool {
        &&& self.segment_owner.inv()
    }
}

impl<M: AnyUFrameMeta + ?Sized> Predicate<DmaStreamInner<M>> for DmaStreaInnerOwner<M> {
    #[verifier::inline]
    open spec fn predicate(&self, v: DmaStreamInner<M>) -> bool {
        &&& v.inv()
        &&& v.segment.inv_with(&self.segment_owner)
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
