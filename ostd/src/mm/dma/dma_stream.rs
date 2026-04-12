use core::{marker::PhantomData, ops::Deref};

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
        io::{VmIo, VmIoMemView, VmIoOwner, VmReader, VmWriter},
        kspace::{KERNEL_BASE_VADDR, KERNEL_END_VADDR, VMALLOC_BASE_VADDR},
        paddr_to_vaddr, Paddr,
    },
    specs::{
        arch::{
            kspace::{lemma_max_paddr_range, lemma_paddr_to_vaddr_properties},
            PAGE_SIZE,
        },
        mm::virt_mem_newer::{MemView, VirtPtr},
    },
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
}

pub type DmaStreanInnerAtomic<M> = AtomicDataWithOwner<DmaStreamInner<M>, DmaStreamInnerOwner<M>>;

#[verus_verify]
impl<M: AnyUFrameMeta + ?Sized + OwnerOf> DmaStream<M> {
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

        let tracked inner_owner = DmaStreamInnerOwner {
            segment_owner,  /* vm_space_owner */
        };

        let inner = AtomicDataWithOwner::new(
            DmaStreamInner { segment, start_daddr, is_cache_coherent, direction },
            Tracked(inner_owner),
        );

        let stream = DmaStream { inner: RwArc::new(inner) };

        Ok(stream)
    }

    /// Returns the starting device address from a read guard.
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
    fn daddr_inner(this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>) -> Daddr {
        this.start_daddr
    }

    /// Returns the DMA direction from a read guard.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The caller must hold the [`DmaStreaInnerOwner`] invariant for the inner data of the [`DmaStream`].
    /// ## Postconditions
    /// - The returned direction is equal to the `direction` field of the inner data of the [`DmaStream`].
    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        returns
            this@.data.direction,
    )]
    fn direction_inner(
        this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>,
    ) -> DmaDirection {
        this.direction
    }

    /// Returns the physical address corresponding to the starting device address
    /// from a read guard.
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
    fn paddr_inner(this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>) -> Paddr {
        this.segment.start_paddr()
    }

    /// Returns the number of frames from a read guard.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The caller must hold the [`DmaStreaInnerOwner`] invariant for the inner data of the [`DmaStream`].
    /// ## Postconditions
    /// - The returned frame count matches the size of the inner segment.
    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        returns
            this@.data.segment.size() / PAGE_SIZE,
    )]
    fn nframes_inner(this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>) -> usize {
        this.segment.size() / PAGE_SIZE
    }

    /// Returns the number of bytes from a read guard.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The caller must hold the [`DmaStreaInnerOwner`] invariant for the inner data of the [`DmaStream`].
    /// ## Postconditions
    /// - The returned byte count matches the size of the inner segment.
    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        returns
            this@.data.segment.size(),
    )]
    fn nbytes_inner(this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>) -> usize {
        this.segment.size()
    }

    /// Returns a reader to read data from it using a read guard.
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
            reader_owner@.is_kernel,
            reader_owner@.has_read_view(),
            reader_owner@.read_view_initialized(),
            r.wf(reader_owner@),
            KERNEL_BASE_VADDR <= r.cursor.range@.start,
            r.cursor.range@.end <= KERNEL_END_VADDR,
    )]
    fn reader_inner<'a>(
        this: RwLockReadGuard<'a, DmaStreanInnerAtomic<M>, PreemptDisabled>,
    ) -> VmReader<'a> {
        proof_decl! {
            let ghost id: nat;
            let tracked mut reader_owner: VmIoOwner<'a>;
        }
        proof {
            lemma_max_paddr_range();
            lemma_paddr_to_vaddr_properties(this@.data.segment.start_paddr_spec());
        }

        let vaddr = paddr_to_vaddr(this.segment.start_paddr());
        let len = this.segment.size();
        let ghost range = vaddr..(vaddr + len) as usize;
        let ptr = VirtPtr { vaddr, range: Ghost(range) };
        proof {
            assert(KERNEL_BASE_VADDR > 0) by (compute_only);
            assert(vaddr > 0);
            assert(VMALLOC_BASE_VADDR <= KERNEL_END_VADDR) by (compute_only);
            assert(ptr.inv());
        }

        let reader = unsafe {
            proof_with!(Ghost(id) => Tracked(reader_owner));
            VmReader::from_kernel_space(ptr, len)
        };
        proof {
            let tracked inner = this.tracked_borrow();
            let tracked owner = inner.permission.borrow();
            let tracked mem_view = owner.segment_owner.borrow_kernel_mem_view(this@.data.segment);
            reader_owner.mem_view = Some(VmIoMemView::ReadView(mem_view));
        }
        proof_with!(|= Tracked(reader_owner));
        reader
    }

    /// Returns a writer to write data to it using a read guard.
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
            writer_owner@.is_kernel,
            writer_owner@.has_write_view(),
            r.wf(writer_owner@),
            KERNEL_BASE_VADDR <= r.cursor.range@.start,
            r.cursor.range@.end <= KERNEL_END_VADDR,
    )]
    fn writer_inner<'a>(
        this: RwLockReadGuard<'a, DmaStreanInnerAtomic<M>, PreemptDisabled>,
    ) -> VmWriter<'a> {
        proof_decl! {
            let ghost id: nat;
            let tracked mut writer_owner: VmIoOwner<'a>;
        }
        proof {
            lemma_max_paddr_range();
            lemma_paddr_to_vaddr_properties(this@.data.segment.start_paddr_spec());
        }

        let vaddr = paddr_to_vaddr(this.segment.start_paddr());
        let len = this.segment.size();
        let ghost range = vaddr..(vaddr + len) as usize;
        let ptr = VirtPtr { vaddr, range: Ghost(range) };
        proof {
            assert(KERNEL_BASE_VADDR > 0) by (compute_only);
            assert(vaddr > 0);
            assert(VMALLOC_BASE_VADDR <= KERNEL_END_VADDR) by (compute_only);
            assert(ptr.inv());
        }

        let writer = unsafe {
            proof_with!(Ghost(id), Tracked(false) => Tracked(writer_owner));
            VmWriter::from_kernel_space(ptr, len)
        };
        proof {
            let tracked inner = this.tracked_borrow();
            let tracked owner = inner.permission.borrow();
            let tracked mem_view = owner.segment_owner.produce_kernel_mem_view(this@.data.segment);
            writer_owner.mem_view = Some(VmIoMemView::WriteView(mem_view));
        }
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
    /// Acquires a read guard for the inner DMA stream state.
    ///
    /// This method is the glue layer between [`RwArc`] and the guard-based
    /// inner helpers.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The inner [`RwArc`] is well-formed.
    /// ## Postconditions
    /// - The inner [`RwArc`] remains well-formed.
    /// - The returned read guard satisfies the inner invariant.
    #[inline(always)]
    #[verifier::external_body]
    #[verus_spec(r =>
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            r@.inv(),
    )]
    pub fn read_inner(&self) -> RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled> {
        self.inner.read()
    }
}

#[verus_verify]
impl<M: AnyUFrameMeta + ?Sized + OwnerOf> DmaStream<M> {
    /// Returns the starting device address.
    ///
    /// This is a glue-layer wrapper over [`Self::daddr_inner`].
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The inner [`RwArc`] is well-formed.
    /// ## Postconditions
    /// - The inner [`RwArc`] remains well-formed.
    #[inline(always)]
    #[verus_spec(r =>
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
    )]
    pub fn daddr(&self) -> Daddr {
        let inner = self.read_inner();
        Self::daddr_inner(&inner)
    }

    /// Returns the DMA direction.
    ///
    /// This is a glue-layer wrapper over [`Self::direction_inner`].
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The inner [`RwArc`] is well-formed.
    /// ## Postconditions
    /// - The inner [`RwArc`] remains well-formed.
    #[inline(always)]
    #[verus_spec(r =>
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
    )]
    pub fn direction(&self) -> DmaDirection {
        let inner = self.read_inner();
        Self::direction_inner(&inner)
    }

    /// Returns the starting physical address.
    ///
    /// This is a glue-layer wrapper over [`Self::paddr_inner`].
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The inner [`RwArc`] is well-formed.
    /// ## Postconditions
    /// - The inner [`RwArc`] remains well-formed.
    #[inline(always)]
    #[verus_spec(r =>
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
    )]
    pub fn paddr(&self) -> Paddr {
        let inner = self.read_inner();
        Self::paddr_inner(&inner)
    }

    // /// Returns the underlying [`Segment<M>`].
    // ///
    // /// This cannot currently mirror the simplified API because the segment
    // /// is accessed through a temporary `RwLockReadGuard`, so an `&Segment<M>`
    // /// would be tied to the guard rather than to `&self`.
    // pub fn segment(&self) -> &Segment<M> {
    //     let inner = self.read_inner();
    //     &inner.segment
    // }

    /// Returns the number of frames.
    #[inline(always)]
    #[verus_spec(r =>
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
    )]
    pub fn nframes(&self) -> usize {
        let inner = self.read_inner();
        Self::nframes_inner(&inner)
    }

    /// Returns the number of bytes.
    #[inline(always)]
    #[verus_spec(r =>
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
    )]
    pub fn nbytes(&self) -> usize {
        let inner = self.read_inner();
        Self::nbytes_inner(&inner)
    }

    /// Returns a reader to read data from it.
    ///
    /// This is a glue-layer wrapper over [`Self::reader_inner`].
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The inner [`RwArc`] is well-formed.
    /// ## Postconditions
    /// - The inner [`RwArc`] remains well-formed.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> reader_perm: Tracked<Option<VmIoOwner<'a>>>,
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            r is Ok ==> {
                &&& r.unwrap().inv()
                &&& reader_perm@ is Some
                &&& reader_perm@.unwrap().inv()
                &&& reader_perm@.unwrap().is_kernel
                &&& reader_perm@.unwrap().has_read_view()
                &&& r.unwrap().wf(reader_perm@.unwrap())
                &&& KERNEL_BASE_VADDR <= r.unwrap().cursor.range@.start
                &&& r.unwrap().cursor.range@.end <= KERNEL_END_VADDR
            },
    )]
    pub fn reader<'a>(&'a self) -> core::result::Result<VmReader<'a>, Error> {
        let inner = self.read_inner();

        if matches!(inner.direction, DmaDirection::ToDevice) {
            proof_with!(|= Tracked(None));
            Err(Error::AccessDenied)
        } else {
            proof_with!(=> Tracked(reader_perm));
            let reader = Self::reader_inner(inner);
            // The reader stores raw address state plus a phantom lifetime. The
            // stream owns the segment, so tying the phantom lifetime to `self`
            // is the public API boundary.
            proof_with!(|= Tracked(Some(reader_perm)));
            Ok(
                VmReader {
                    id: reader.id,
                    cursor: reader.cursor,
                    end: reader.end,
                    phantom: PhantomData,
                },
            )
        }
    }

    /// Returns a writer to write data to it.
    ///
    /// This is a glue-layer wrapper over [`Self::writer_inner`].
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The inner [`RwArc`] is well-formed.
    /// ## Postconditions
    /// - The inner [`RwArc`] remains well-formed.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> writer_perm: Tracked<Option<VmIoOwner<'a>>>,
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            r is Ok ==> {
                &&& r.unwrap().inv()
                &&& writer_perm@ is Some
                &&& writer_perm@.unwrap().inv()
                &&& writer_perm@.unwrap().is_kernel
                &&& writer_perm@.unwrap().has_write_view()
                &&& r.unwrap().wf(writer_perm@.unwrap())
            },
    )]
    pub fn writer<'a>(&'a self) -> core::result::Result<VmWriter<'a>, Error> {
        let inner = self.read_inner();

        if matches!(inner.direction, DmaDirection::FromDevice) {
            proof_with!(|= Tracked(None));
            Err(Error::AccessDenied)
        } else {
            proof_with!(=> Tracked(writer_perm));
            let writer = Self::writer_inner(inner);

            proof_with!(|= Tracked(Some(writer_perm)));
            Ok(
                VmWriter {
                    id: writer.id,
                    cursor: writer.cursor,
                    end: writer.end,
                    phantom: PhantomData,
                },
            )
        }
    }

    #[verus_spec(r =>
        requires
            old(writer).inv(),
        ensures
            this@.data.direction == DmaDirection::ToDevice ==> {
                &&& r == Err::<(), Error>(Error::AccessDenied)
                &&& *final(writer) == *old(writer)
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
                &&& *final(reader) == *old(reader)
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
        &&& self.inv()
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

impl<M: AnyUFrameMeta + ?Sized + Send + Sync + OwnerOf> VmIo<DmaStreamVmIoOwner<M>> for DmaStream<
    M,
> {
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
        &&& self.inner.wf()
        &&& writer.inv()
        &&& writer_own.inv()
        &&& writer.wf(writer_own)
        &&& writer_own.mem_view matches Some(VmIoMemView::WriteView(_))
        &&& writer.cursor.vaddr > 0
        &&& (writer.cursor.range@.end <= KERNEL_BASE_VADDR || KERNEL_END_VADDR
            <= writer.cursor.range@.start)
    }

    open spec fn write_requires(
        self,
        offset: usize,
        reader: VmReader<'_>,
        reader_own: VmIoOwner<'_>,
        owner: DmaStreamVmIoOwner<M>,
    ) -> bool {
        &&& self.inv()
        &&& self.inner.wf()
        &&& reader.inv()
        &&& reader_own.inv()
        &&& reader.wf(reader_own)
        &&& reader_own.mem_view matches Some(VmIoMemView::ReadView(_))
        &&& reader_own.read_view_initialized()
        &&& reader.cursor.vaddr > 0
        &&& (reader.cursor.range@.end <= KERNEL_BASE_VADDR || KERNEL_END_VADDR
            <= reader.cursor.range@.start)
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
        &&& self.inv()
        &&& new_owner == old_owner
        &&& new_writer.inv()
        &&& new_writer_own.inv()
        &&& new_writer.wf(new_writer_own)
        &&& match r {
            Ok(_) => {
                &&& new_writer.avail_spec() == 0
                &&& new_writer.cursor.vaddr == old_writer.cursor.vaddr + old_writer.avail_spec()
                &&& new_writer_own.range@.start == old_writer_own.range@.start
                    + old_writer.avail_spec()
            },
            Err(_) => {
                &&& new_writer == old_writer
                &&& new_writer_own == old_writer_own
            },
        }
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
        &&& self.inv()
        &&& new_owner == old_owner
        &&& new_reader.inv()
        &&& new_reader_own.inv()
        &&& new_reader.wf(new_reader_own)
        &&& match r {
            Ok(_) => {
                &&& new_reader.remain_spec() == 0
                &&& new_reader.cursor.vaddr == old_reader.cursor.vaddr + old_reader.remain_spec()
                &&& new_reader_own.range@.start == old_reader_own.range@.start
                    + old_reader.remain_spec()
            },
            Err(_) => {
                &&& new_reader == old_reader
                &&& new_reader_own == old_reader_own
            },
        }
    }

    #[verus_spec()]
    fn read(
        &self,
        offset: usize,
        writer: &mut VmWriter<'_>,
        Tracked(writer_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut DmaStreamVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        let inner = self.read_inner();
        if matches!(inner.direction, DmaDirection::ToDevice) {
            return Err(Error::AccessDenied);
        }
        proof_decl! {
            let tracked mut reader_own;
        }
        let mut reader = {
            #[verus_spec(with => Tracked(reader_own))]
            Self::reader_inner(inner)
        };

        let Some(remain) = reader.remain().checked_sub(offset) else {
            return Err(Error::InvalidArgs);
        };
        let len = writer.avail();
        if remain < len {
            return Err(Error::InvalidArgs);
        }
        if len == 0 {
            proof {
                assert(writer.avail_spec() == 0);
            }
            return Ok(());
        }
        reader.advance(offset);
        proof {
            reader_own.advance(offset);

            assert(reader.remain_spec() >= len);
            assert(KERNEL_BASE_VADDR > 0) by (compute_only);
            assert(reader.cursor.vaddr > 0);
            assert(writer.cursor.range@.start >= reader.cursor.range@.end
                || reader.cursor.range@.start >= writer.cursor.range@.end);
        }

        proof_with!(Tracked(&mut reader_own), Tracked(&mut *writer_own));
        let copied = reader.read(writer);

        proof {
            assert(copied == len);
            assert(len == old(writer).avail_spec());
            assert(writer.avail_spec() == 0);
            assert(writer.cursor.vaddr == old(writer).cursor.vaddr + old(writer).avail_spec());
            assert(writer_own.range@.start == old(writer_own).range@.start + old(writer).avail_spec());
            assert(*owner == *old(owner));
        }

        Ok(())
    }

    fn write(
        &self,
        offset: usize,
        reader: &mut VmReader<'_>,
        Tracked(reader_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut DmaStreamVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        let inner = self.read_inner();
        if matches!(inner.direction, DmaDirection::FromDevice) {
            return Err(Error::AccessDenied);
        }
        proof_decl! {
            let tracked mut writer_own;
        }
        let mut writer = {
            #[verus_spec(with => Tracked(writer_own))]
            Self::writer_inner(inner)
        };

        let Some(avail) = writer.avail().checked_sub(offset) else {
            return Err(Error::InvalidArgs);
        };
        let len = reader.remain();
        if avail < len {
            return Err(Error::InvalidArgs);
        }
        if len == 0 {
            proof {
                assert(reader.remain_spec() == 0);
            }
            return Ok(());
        }
        writer.advance(offset);
        proof {
            writer_own.advance(offset);

            assert(writer.avail_spec() >= len);
            assert(KERNEL_BASE_VADDR > 0) by (compute_only);
            assert(writer.cursor.vaddr > 0);
            assert(writer.cursor.range@.start >= reader.cursor.range@.end
                || reader.cursor.range@.start >= writer.cursor.range@.end);
        }
        let copied = {
            #[verus_spec(with Tracked(&mut writer_own), Tracked(&mut *reader_own))]
            writer.write(reader)
        };
        proof {
            assert(copied == len);
            assert(len == old(reader).remain_spec());
            assert(reader.remain_spec() == 0);
            assert(reader.cursor.vaddr == old(reader).cursor.vaddr + old(reader).remain_spec());
            assert(reader_own.range@.start == old(reader_own).range@.start + old(reader).remain_spec());
            assert(*owner == *old(owner));
        }

        Ok(())
    }

    #[verifier::external_body]
    fn read_byte<const N: usize>(
        &self,
        offset: usize,
        bytes: ArrayPtr<u8, N>,
        Tracked(_bytes_owner): Tracked<&mut PointsToArray<u8, N>>,
        Tracked(_owner): Tracked<&mut DmaStreamVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        Err(Error::AccessDenied)
    }
}

} // verus!
