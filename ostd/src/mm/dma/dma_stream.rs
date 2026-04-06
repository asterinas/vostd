use core::ops::Deref;

// SPDX-License-Identifier: MPL-2.0
use vstd::{predicate::Predicate, prelude::*};
use vstd_extra::array_ptr::{ArrayPtr, PointsToArray};
use vstd_extra::ownership::{Inv, OwnerOf};

use crate::mm::vm_space::vm_space_specs::VmSpaceOwner;
use crate::{
    error::Error,
    mm::{
        dma::{dma_type, Daddr, DmaType},
        frame::{segment::SegmentOwner, untyped::AnyUFrameMeta, AnyFrameMeta, Segment},
        io::{VmIo, VmIoOwner, VmReader, VmWriter},
        Paddr,
    },
    specs::{arch::PAGE_SIZE, mm::virt_mem_newer::MemView},
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

/// The tracked owner for the inner part of a [`DmaStream`].
/// 
/// This is a placeholder but for the completeness of the [`VmIo`] trait.
/// The "real" owner is tracked via the [`RwArc`] of the inner part of the
/// [`DmaStream`].
/// 
/// The caller must hold the invariant of the inner part to call any
/// method that can read or write data from the DMA stream.
pub struct DmaStreamVmIoOwner<M>(pub core::marker::PhantomData<M>);

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

/// The owner of the inner part of a [`DmaStream`].
pub tracked struct DmaStreamInnerOwner<M: AnyUFrameMeta + ?Sized> {
    pub segment_owner: SegmentOwner<M>,
    // Here we put the [`VmSpaceOwner`] as a proof field to make sure
    // the caller holds the invariant of the  writers which require
    // the invariant of the [`VmSpaceOwner`] to be held.
    // pub vm_space_owner: VmSpaceOwner<'_>,
}

pub type DmaStreanInnerAtomic<M> = AtomicDataWithOwner<DmaStreamInner<M>, DmaStreamInnerOwner<M>>;

#[verus_verify]
impl<'a, M: AnyUFrameMeta + ?Sized + OwnerOf> DmaStream<M> {
    /// Establishes DMA stream mapping for a given [`Segment<M>`].
    ///
    /// The method fails if the segment already belongs to a DMA mapping.
    #[verus_spec(r =>
        with
            Tracked(segment_owner): Tracked<SegmentOwner<M>>,
            // Tracked(vm_space_owner): Tracked<VmSpaceOwner<'_>>,
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

        let tracked inner_owner = DmaStreamInnerOwner { segment_owner, /* vm_space_owner */ };

        let inner = AtomicDataWithOwner::new(
            DmaStreamInner { segment, start_daddr, is_cache_coherent, direction },
            Tracked(inner_owner),
        );

        let stream = DmaStream { inner: RwArc::new(inner) };

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
        returns
            this@.data.start_daddr,
    )]
    pub fn daddr(this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>) -> Daddr {
        this.start_daddr
    }

    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        returns
            this@.data.direction,
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

impl<M: AnyUFrameMeta + ?Sized> Inv for DmaStreamInnerOwner<M> {
    open spec fn inv(self) -> bool {
        &&& self.segment_owner.inv()
    }
}

impl<M: AnyUFrameMeta + ?Sized> DmaStream<M> {
    #[inline(always)]
    pub fn read_inner(&self) -> RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled> {
        self.inner.read()
    }
}

#[verus_verify]
impl<M: AnyUFrameMeta + ?Sized + OwnerOf> DmaStream<M> {
    #[verus_spec(r =>
        requires
            old(writer).inv(),
        ensures
            this@.data.direction == DmaDirection::ToDevice ==> {
                &&& r == Err::<(), Error>(Error::AccessDenied)
                &&& *writer == *old(writer)
            },
    )]
    pub fn read_inner_vmio(
        this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>,
        offset: usize,
        writer: &mut VmWriter<'_>,
    ) -> core::result::Result<(), Error> {
        match this.direction {
            DmaDirection::ToDevice => return Err(Error::AccessDenied),
            _ => {},
        }
        let Some(size) = this.segment.range.end.checked_sub(this.segment.range.start) else {
            return Err(Error::InvalidArgs);
        };
        match size.checked_sub(offset) {
            Some(remain) if remain >= writer.avail() => {},
            _ => return Err(Error::InvalidArgs),
        }
        Err(Error::InvalidArgs)
    }

    #[verus_spec(r =>
        requires
            old(reader).inv(),
        ensures
            this@.data.direction == DmaDirection::FromDevice ==> {
                &&& r == Err::<(), Error>(Error::AccessDenied)
                &&& *reader == *old(reader)
            },
    )]
    pub fn write_inner_vmio(
        this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>,
        offset: usize,
        reader: &mut VmReader<'_>,
    ) -> core::result::Result<(), Error> {
        match this.direction {
            DmaDirection::FromDevice => return Err(Error::AccessDenied),
            _ => {},
        }
        let Some(size) = this.segment.range.end.checked_sub(this.segment.range.start) else {
            return Err(Error::InvalidArgs);
        };
        match size.checked_sub(offset) {
            Some(remain) if remain >= reader.remain() => {},
            _ => return Err(Error::InvalidArgs),
        }
        Err(Error::InvalidArgs)
    }
}

impl<M: AnyUFrameMeta + ?Sized> Predicate<DmaStreamInner<M>> for DmaStreamInnerOwner<M> {
    #[verifier::inline]
    open spec fn predicate(&self, v: DmaStreamInner<M>) -> bool {
        &&& v.inv()
        &&& v.segment.inv_with(&self.segment_owner)
    }
}

/// [`DmaDirection`] limits the data flow direction of [`DmaStream`] and
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

impl<M: AnyUFrameMeta + ?Sized + Send + Sync + OwnerOf> VmIo<DmaStreamVmIoOwner<M>> for DmaStream<M> {
    closed spec fn obeys_vmio_spec() -> bool {
        true
    }

    closed spec fn obeys_vmio_read_requires() -> bool {
        true
    }

    closed spec fn obeys_vmio_write_requires() -> bool {
        true
    }

    closed spec fn obeys_vmio_read_spec() -> bool {
        true
    }

    closed spec fn obeys_vmio_write_spec() -> bool {
        true
    }

    open spec fn read_requires(
        self,
        offset: usize,
        writer: VmWriter<'_>,
        writer_own: VmIoOwner<'_>,
        owner: DmaStreamVmIoOwner<M>,
    ) -> bool {
        &&& self.inv()
        &&& writer.inv()
        &&& writer_own.inv()
        &&& writer_own.inv_with_writer(writer)
    }

    open spec fn write_requires(
        self,
        offset: usize,
        reader: VmReader<'_>,
        reader_own: VmIoOwner<'_>,
        owner: DmaStreamVmIoOwner<M>,
    ) -> bool {
        &&& self.inv()
        &&& reader.inv()
        &&& reader_own.inv()
        &&& reader_own.inv_with_reader(reader)
    }

    open spec fn read_spec(
        self,
        offset: usize,
        old_writer: VmWriter<'_>,
        new_writer: VmWriter<'_>,
        old_writer_own: VmIoOwner<'_>,
        new_writer_own: VmIoOwner<'_>,
        old_owner: DmaStreamVmIoOwner<M>,
        new_owner: DmaStreamVmIoOwner<M>,
        r: core::result::Result<(), Error>,
    ) -> bool {
        self.inv()
    }

    open spec fn write_spec(
        self,
        offset: usize,
        old_reader: VmReader<'_>,
        new_reader: VmReader<'_>,
        old_reader_own: VmIoOwner<'_>,
        new_reader_own: VmIoOwner<'_>,
        old_owner: DmaStreamVmIoOwner<M>,
        new_owner: DmaStreamVmIoOwner<M>,
        r: core::result::Result<(), Error>,
    ) -> bool {
        self.inv()
    }

    fn read(
        &self,
        offset: usize,
        writer: &mut VmWriter<'_>,
        Tracked(_writer_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(_owner): Tracked<&mut DmaStreamVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        let inner = self.read_inner();
        DmaStream::read_inner_vmio(&inner, offset, writer)
    }

    fn write(
        &self,
        offset: usize,
        reader: &mut VmReader<'_>,
        Tracked(_reader_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(_owner): Tracked<&mut DmaStreamVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        let inner = self.read_inner();
        DmaStream::write_inner_vmio(&inner, offset, reader)
    }

    #[verifier::external_body]
    fn read_byte<const N: usize>(
        &self,
        offset: usize,
        bytes: ArrayPtr<u8, N>,
        Tracked(_bytes_owner): Tracked<&mut PointsToArray<u8, N>>,
        Tracked(_owner): Tracked<&mut DmaStreamVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        let _ = offset;
        let _ = bytes;
        Err(Error::AccessDenied)
    }
}

} // verus!
