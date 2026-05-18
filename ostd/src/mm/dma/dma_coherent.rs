// SPDX-License-Identifier: MPL-2.0

use core::marker::PhantomData;

use vstd::{predicate::Predicate, prelude::*};
use vstd_extra::array_ptr::{ArrayPtr, PointsToArray};
use vstd_extra::ownership::{Inv, OwnerOf};

use crate::{
    error::Error,
    mm::{
        dma::{dma_type, Daddr, DmaType},
        frame::{segment::SegmentOwner, untyped::AnyUFrameMeta, Segment},
        io::{VmIo, VmIoMemView, VmIoOnce, VmIoOwner, VmReader, VmWriter},
        kspace::{KERNEL_BASE_VADDR, KERNEL_END_VADDR, VMALLOC_BASE_VADDR},
        paddr_to_vaddr, HasPaddr, Paddr,
    },
    specs::{
        arch::{
            kspace::{lemma_max_paddr_range, lemma_paddr_to_vaddr_properties},
            PAGE_SIZE,
        },
        mm::pod::PodOnce,
        mm::virt_mem_newer::VirtPtr,
    },
    sync::{AtomicDataWithOwner, PreemptDisabled, RwArc, RwLockReadGuard},
};

use super::{check_and_insert_dma_mapping, is_valid_daddr, DmaError, HasDaddr};

verus! {

/// A coherent (or consistent) DMA mapping,
/// which guarantees that the device and the CPU can
/// access the data in parallel.
///
/// The mapping will be destroyed automatically when
/// the object is dropped.
pub struct DmaCoherent<M: AnyUFrameMeta + ?Sized> {
    pub inner: RwArc<DmaCoherentInnerAtomic<M>>,
}

/// The tracked owner for the inner part of a [`DmaCoherent`].
///
/// This mirrors [`DmaStreamVmIoOwner`](super::dma_stream::DmaStreamVmIoOwner):
/// the real memory ownership lives in the inner `RwArc`, and this token is
/// only the public `VmIo` permission parameter.
pub struct DmaCoherentVmIoOwner<M: ?Sized>(pub PhantomData<M>);

/// The inner part of a [`DmaCoherent`].
pub struct DmaCoherentInner<M: AnyUFrameMeta + ?Sized> {
    /// Verus does not support trait objects here, so the metadata type is
    /// represented explicitly by `M`.
    pub segment: Segment<M>,
    pub start_daddr: Daddr,
    /// TODO: restore cache-policy switching once the page-table API is verified.
    #[expect(unused)]
    pub is_cache_coherent: bool,
}

/// The owner of the inner part of a [`DmaCoherent`].
pub tracked struct DmaCoherentInnerOwner<M: AnyUFrameMeta + ?Sized> {
    pub segment_owner: SegmentOwner<M>,
}

pub type DmaCoherentInnerAtomic<M> =
    AtomicDataWithOwner<DmaCoherentInner<M>, DmaCoherentInnerOwner<M>>;

impl<M: AnyUFrameMeta + ?Sized> Inv for DmaCoherent<M> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<M: AnyUFrameMeta + ?Sized> Inv for DmaCoherentInner<M> {
    open spec fn inv(self) -> bool {
        &&& self.segment.inv()
        &&& is_valid_daddr(self.start_daddr)
    }
}

impl<M: AnyUFrameMeta + ?Sized> Inv for DmaCoherentInnerOwner<M> {
    open spec fn inv(self) -> bool {
        self.segment_owner.inv()
    }
}

#[verus_verify]
impl<M: AnyUFrameMeta + ?Sized + OwnerOf> DmaCoherent<M> {
    /// Creates a coherent DMA mapping backed by `segment`.
    ///
    /// The `is_cache_coherent` argument specifies whether the target device can
    /// access main memory in a CPU-cache-coherent way.
    #[verus_spec(r =>
        with
            Tracked(segment_owner): Tracked<SegmentOwner<M>>,
        requires
            segment.inv(),
            segment.inv_with(&segment_owner),
        ensures
            r matches Ok(r) ==> r.inner.wf(),
    )]
    pub fn map(segment: Segment<M>, is_cache_coherent: bool) -> Result<Self, DmaError> {
        let start_paddr = segment.start_paddr();
        let frame_count = segment.size() / PAGE_SIZE;

        if !check_and_insert_dma_mapping(start_paddr, frame_count) {
            return Err(DmaError::AlreadyMapped);
        }

        let start_daddr = match dma_type() {
            DmaType::Direct => {
                // TODO: restore TDX GPA sharing once the arch hook is verified.
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
                    let _paddr = start_paddr + i * PAGE_SIZE;
                    // TODO: restore iommu::map once the IOMMU API is verified.
                    i += 1;
                }

                start_paddr as Daddr
            },
        };

        let tracked inner_owner = DmaCoherentInnerOwner { segment_owner };

        let inner = RwArc::new(AtomicDataWithOwner::new(
            DmaCoherentInner { segment, start_daddr, is_cache_coherent },
            Tracked(inner_owner),
        ));

        Ok(DmaCoherent { inner })
    }

    /// Returns the starting device address from a read guard.
    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        returns
            this@.data.start_daddr,
    )]
    fn daddr_inner(this: &RwLockReadGuard<DmaCoherentInnerAtomic<M>, PreemptDisabled>) -> Daddr {
        this.start_daddr
    }

    /// Returns the starting physical address from a read guard.
    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        returns
            this@.data.segment.start_paddr(),
    )]
    fn paddr_inner(this: &RwLockReadGuard<DmaCoherentInnerAtomic<M>, PreemptDisabled>) -> Paddr {
        this.segment.start_paddr()
    }

    /// Returns the number of frames from a read guard.
    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        returns
            this@.data.segment.size() / PAGE_SIZE,
    )]
    fn nframes_inner(this: &RwLockReadGuard<DmaCoherentInnerAtomic<M>, PreemptDisabled>) -> usize {
        this.segment.size() / PAGE_SIZE
    }

    /// Returns the number of bytes from a read guard.
    #[inline(always)]
    #[verus_spec(r =>
        requires
            this@.inv(),
        returns
            this@.data.segment.size(),
    )]
    fn nbytes_inner(this: &RwLockReadGuard<DmaCoherentInnerAtomic<M>, PreemptDisabled>) -> usize {
        this.segment.size()
    }

    /// Returns a reader to read data from it using a read guard.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> reader_owner: Tracked<VmIoOwner<'a>>,
        requires
            this@.inv(),
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
        this: RwLockReadGuard<'a, DmaCoherentInnerAtomic<M>, PreemptDisabled>,
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
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> writer_owner: Tracked<VmIoOwner<'a>>,
        requires
            this@.inv(),
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
        this: RwLockReadGuard<'a, DmaCoherentInnerAtomic<M>, PreemptDisabled>,
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

impl<M: AnyUFrameMeta + ?Sized> DmaCoherent<M> {
    /// Acquires a read guard for the inner DMA-coherent state.
    #[inline(always)]
    #[verifier::external_body]
    #[verus_spec(r =>
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            r@.inv(),
    )]
    pub fn read_inner(&self) -> RwLockReadGuard<DmaCoherentInnerAtomic<M>, PreemptDisabled> {
        self.inner.read()
    }
}

#[verus_verify]
impl<M: AnyUFrameMeta + ?Sized + OwnerOf> DmaCoherent<M> {
    /// Returns the starting device address.
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

    /// Returns the starting physical address.
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

    /// Returns the number of bytes in the DMA mapping.
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
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> reader_perm: Tracked<VmIoOwner<'a>>,
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            r.inv(),
            reader_perm@.inv(),
            reader_perm@.is_kernel,
            reader_perm@.has_read_view(),
            r.wf(reader_perm@),
            KERNEL_BASE_VADDR <= r.cursor.range@.start,
            r.cursor.range@.end <= KERNEL_END_VADDR,
    )]
    pub fn reader<'a>(&'a self) -> VmReader<'a> {
        let inner = self.read_inner();
        proof_with!(=> Tracked(reader_perm));
        let reader = Self::reader_inner(inner);
        proof_with!(|= Tracked(reader_perm));
        VmReader { id: reader.id, cursor: reader.cursor, end: reader.end, phantom: PhantomData }
    }

    /// Returns a writer to write data into it.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> writer_perm: Tracked<VmIoOwner<'a>>,
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            r.inv(),
            writer_perm@.inv(),
            writer_perm@.is_kernel,
            writer_perm@.has_write_view(),
            r.wf(writer_perm@),
    )]
    pub fn writer<'a>(&'a self) -> VmWriter<'a> {
        let inner = self.read_inner();
        proof_with!(=> Tracked(writer_perm));
        let writer = Self::writer_inner(inner);
        proof_with!(|= Tracked(writer_perm));
        VmWriter { id: writer.id, cursor: writer.cursor, end: writer.end, phantom: PhantomData }
    }
}

impl<M: AnyUFrameMeta + ?Sized> Predicate<DmaCoherentInner<M>> for DmaCoherentInnerOwner<M> {
    #[verifier::inline]
    open spec fn predicate(&self, v: DmaCoherentInner<M>) -> bool {
        &&& self.inv()
        &&& v.inv()
        &&& v.segment.inv_with(&self.segment_owner)
    }
}

#[verus_verify]
impl<M: AnyUFrameMeta + ?Sized> Clone for DmaCoherent<M> {
    #[verus_spec]
    fn clone(&self) -> Self
        returns
            DmaCoherent { inner: self.inner },
    {
        DmaCoherent { inner: self.inner.clone() }
    }
}

impl<M: AnyUFrameMeta + ?Sized + OwnerOf> HasDaddr for DmaCoherent<M> {
    #[inline]
    fn daddr(&self) -> Daddr {
        self.daddr()
    }
}

impl<M: AnyUFrameMeta + ?Sized + OwnerOf> HasPaddr for DmaCoherent<M> {
    #[inline]
    fn paddr(&self) -> Paddr {
        self.paddr()
    }
}

impl<M: AnyUFrameMeta + ?Sized + Send + Sync + OwnerOf> VmIo<DmaCoherentVmIoOwner<M>> for DmaCoherent<
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
        owner: DmaCoherentVmIoOwner<M>,
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
        owner: DmaCoherentVmIoOwner<M>,
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
        old_owner: DmaCoherentVmIoOwner<M>,
        new_owner: DmaCoherentVmIoOwner<M>,
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
        old_owner: DmaCoherentVmIoOwner<M>,
        new_owner: DmaCoherentVmIoOwner<M>,
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

    fn read(
        &self,
        offset: usize,
        writer: &mut VmWriter<'_>,
        Tracked(writer_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut DmaCoherentVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        proof_decl! {
            let tracked mut reader_own;
        }
        let mut reader = {
            let inner = self.read_inner();
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

            assert(reader.inv());
            assert(writer.inv());
            assert(reader_own.inv());
            assert(writer_own.inv());
            assert(reader.wf(reader_own));
            assert(writer.wf(*writer_own));
            assert(reader_own.mem_view matches Some(VmIoMemView::ReadView(_)));
            assert(reader_own.read_view_initialized());
            assert(writer_own.mem_view matches Some(VmIoMemView::WriteView(_)));
            assert(reader.remain_spec() >= len);
            assert(KERNEL_BASE_VADDR > 0) by (compute_only);
            assert(reader.cursor.vaddr > 0);
            assert(writer.cursor.vaddr > 0);
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
            assert(writer_own.range@.start == old(writer_own).range@.start + old(
                writer,
            ).avail_spec());
            assert(*owner == *old(owner));
        }

        Ok(())
    }

    fn write(
        &self,
        offset: usize,
        reader: &mut VmReader<'_>,
        Tracked(reader_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut DmaCoherentVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        proof_decl! {
            let tracked mut writer_own;
        }
        let mut writer = {
            let inner = self.read_inner();
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
            assert(reader_own.range@.start == old(reader_own).range@.start + old(
                reader,
            ).remain_spec());
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
        Tracked(_owner): Tracked<&mut DmaCoherentVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        Err(Error::AccessDenied)
    }
}

impl<M: AnyUFrameMeta + ?Sized + Send + Sync + OwnerOf> VmIoOnce for DmaCoherent<M> {
    closed spec fn obeys_vmio_once_read_requires() -> bool {
        true
    }

    closed spec fn obeys_vmio_once_write_requires() -> bool {
        true
    }

    closed spec fn obeys_vmio_once_read_ensures() -> bool {
        true
    }

    closed spec fn obeys_vmio_once_write_ensures() -> bool {
        true
    }

    #[verifier::external_body]
    fn read_once<T: PodOnce>(&self, offset: usize) -> core::result::Result<T, Error> {
        self.reader().skip(offset).read_once()
    }

    #[verifier::external_body]
    fn write_once<T: PodOnce>(&self, offset: usize, new_val: &T) -> core::result::Result<(), Error> {
        self.writer().skip(offset).write_once(new_val)
    }
}

} // verus!
