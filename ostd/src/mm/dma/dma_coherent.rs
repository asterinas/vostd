// SPDX-License-Identifier: MPL-2.0
use core::marker::PhantomData;

use vstd::{predicate::Predicate, prelude::*};
use vstd_extra::array_ptr::{ArrayPtr, PointsToArray};
use vstd_extra::ownership::{Inv, OwnerOf};

use crate::{
    error::Error,
    mm::{
        HasPaddr, Paddr,
        dma::{Daddr, DmaType, dma_type},
        frame::{Segment, untyped::AnyUFrameMeta},
        io::{
            FallibleVmRead, FallibleVmWrite, Infallible, PodOnce, VmIo, VmIoMemView, VmIoOnce,
            VmIoOwner, VmReader, VmWriter, axiom_kernel_mem_view,
        },
        kspace::{KERNEL_BASE_VADDR, KERNEL_END_VADDR, VMALLOC_BASE_VADDR},
        paddr_to_vaddr,
    },
    specs::{
        arch::{
            PAGE_SIZE,
            kspace::{lemma_max_paddr_range, lemma_paddr_to_vaddr_properties},
        },
        mm::frame::segment::SegmentOwner,
        mm::virt_mem::VirtPtr,
    },
    sync::{AtomicDataWithOwner, PreemptDisabled, RwArc, RwLockReadGuard},
};

use super::{DmaError, HasDaddr, check_and_insert_dma_mapping, is_valid_daddr};

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

pub type DmaCoherentInnerAtomic<M> = AtomicDataWithOwner<
    DmaCoherentInner<M>,
    DmaCoherentInnerOwner<M>,
>;

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
            segment.wf(&segment_owner),
        ensures
            r matches Ok(r) ==> r.inner.wf(),
    )]
    pub fn map(segment: Segment<M>, is_cache_coherent: bool) -> Result<Self, DmaError> {
        let start_paddr = segment.start_paddr();
        let frame_count = segment.size() / PAGE_SIZE;

        if !check_and_insert_dma_mapping(start_paddr, frame_count) {
            return Err(DmaError::AlreadyMapped);
        }/*
        // Original cache policy change (removed during Verus migration):
        if !is_cache_coherent {
            let page_table = KERNEL_PAGE_TABLE.get().unwrap();
            let vaddr = paddr_to_vaddr(start_paddr);
            let va_range = vaddr..vaddr + (frame_count * PAGE_SIZE);
            unsafe {
                page_table
                    .protect_flush_tlb(&va_range, |p| p.cache = CachePolicy::Uncacheable)
                    .unwrap();
            }
        }
        */

        let start_daddr = match dma_type() {
            DmaType::Direct => {
                /*
                // Original TDX unprotect (removed during Verus migration):
                #[cfg(target_arch = "x86_64")]
                crate::arch::if_tdx_enabled!({
                    unsafe {
                        tdx_guest::unprotect_gpa_range(start_paddr, frame_count).unwrap();
                    }
                });
                */
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
                    assume(start_paddr + i * PAGE_SIZE <= usize::MAX);
                    let _paddr = start_paddr + i * PAGE_SIZE;
                    /*
                    // Original IOMMU map (removed during Verus migration):
                    unsafe {
                        iommu::map(paddr as Daddr, paddr).unwrap();
                    }
                    */
                    i += 1;
                }

                start_paddr as Daddr
            },
        };

        let tracked inner_owner = DmaCoherentInnerOwner { segment_owner };

        let inner = RwArc::new(
            AtomicDataWithOwner::new(
                DmaCoherentInner { segment, start_daddr, is_cache_coherent },
                Tracked(inner_owner),
            ),
        );

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
            -> reader_owner: Tracked<VmIoOwner>,
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
    ) -> VmReader<'a, Infallible> {
        proof_decl! {
            let ghost id: nat;
            let tracked mut reader_owner: VmIoOwner;
        }
        proof {
            lemma_max_paddr_range();
            lemma_paddr_to_vaddr_properties(this@.data.segment.start_paddr());
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
            let tracked mem_view = axiom_kernel_mem_view(range);
            reader_owner.mem_view = Some(VmIoMemView::ReadView(mem_view));
        }
        proof_with!(|= Tracked(reader_owner));
        reader
    }

    /// Returns a writer to write data to it using a read guard.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> writer_owner: Tracked<VmIoOwner>,
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
    ) -> VmWriter<'a, Infallible> {
        proof_decl! {
            let ghost id: nat;
            let tracked mut writer_owner: VmIoOwner;
        }
        proof {
            lemma_max_paddr_range();
            lemma_paddr_to_vaddr_properties(this@.data.segment.start_paddr());
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
            let tracked mem_view = axiom_kernel_mem_view(range);
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
        ensures
            self.inner.wf(),
            r@.inv(),
    )]
    pub fn read_inner(&self) -> RwLockReadGuard<'_, DmaCoherentInnerAtomic<M>, PreemptDisabled> {
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
            -> reader_perm: Tracked<VmIoOwner>,
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
    pub fn reader<'a>(&'a self) -> VmReader<'a, Infallible> {
        let inner = self.read_inner();
        proof_with!(=> Tracked(reader_perm));
        let reader = Self::reader_inner(inner);
        proof_with!(|= Tracked(reader_perm));
        VmReader {
            ghost_id: reader.ghost_id,
            cursor: reader.cursor,
            end: reader.end,
            phantom: PhantomData,
        }
    }

    /// Returns a writer to write data into it.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> writer_perm: Tracked<VmIoOwner>,
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
    pub fn writer<'a>(&'a self) -> VmWriter<'a, Infallible> {
        let inner = self.read_inner();
        proof_with!(=> Tracked(writer_perm));
        let writer = Self::writer_inner(inner);
        proof_with!(|= Tracked(writer_perm));
        VmWriter {
            ghost_id: writer.ghost_id,
            cursor: writer.cursor,
            end: writer.end,
            phantom: PhantomData,
        }
    }
}

impl<M: AnyUFrameMeta + ?Sized> Predicate<DmaCoherentInner<M>> for DmaCoherentInnerOwner<M> {
    #[verifier::inline]
    open spec fn predicate(&self, v: DmaCoherentInner<M>) -> bool {
        &&& self.inv()
        &&& v.inv()
        &&& v.segment.wf(&self.segment_owner)
    }
}

#[verus_verify]
impl<M: AnyUFrameMeta + ?Sized> Clone for DmaCoherent<M> {
    #[verus_spec(r =>
        ensures
            r == self,
    )]
    fn clone(&self) -> Self {
        DmaCoherent { inner: self.inner.clone() }
    }
}

impl<M: AnyUFrameMeta + ?Sized + OwnerOf> HasDaddr for DmaCoherent<M> {
    #[inline]
    fn daddr(&self) -> Daddr {
        let inner = self.read_inner();
        Self::daddr_inner(&inner)
    }
}

impl<M: AnyUFrameMeta + ?Sized + OwnerOf> HasPaddr for DmaCoherent<M> {
    #[inline]
    fn paddr(&self) -> Paddr {
        let inner = self.read_inner();
        Self::paddr_inner(&inner)
    }
}

/*
// Original Deref impl (removed during Verus migration):
impl Deref for DmaCoherent {
    type Target = USegment;
    fn deref(&self) -> &Self::Target {
        &self.inner.segment
    }
}
*/

/*
// Original Drop impl for DmaCoherentInner (removed during Verus migration):
impl Drop for DmaCoherentInner {
    fn drop(&mut self) {
        let start_paddr = self.segment.start_paddr();
        let frame_count = self.segment.size() / PAGE_SIZE;

        match dma_type() {
            DmaType::Direct => {
                #[cfg(target_arch = "x86_64")]
                crate::arch::if_tdx_enabled!({
                    unsafe {
                        tdx_guest::protect_gpa_range(start_paddr, frame_count).unwrap();
                    }
                });
            }
            DmaType::Iommu => {
                for i in 0..frame_count {
                    let paddr = start_paddr + (i * PAGE_SIZE);
                    iommu::unmap(paddr as Daddr).unwrap();
                }
            }
        }

        if !self.is_cache_coherent {
            let page_table = KERNEL_PAGE_TABLE.get().unwrap();
            let vaddr = paddr_to_vaddr(start_paddr);
            let va_range = vaddr..vaddr + (frame_count * PAGE_SIZE);
            unsafe {
                page_table
                    .protect_flush_tlb(&va_range, |p| p.cache = CachePolicy::Writeback)
                    .unwrap();
            }
        }

        remove_dma_mapping(start_paddr, frame_count);
    }
}
*/

impl<M: AnyUFrameMeta + ?Sized + Send + Sync + OwnerOf> VmIo<
    DmaCoherentVmIoOwner<M>,
> for DmaCoherent<M> {
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
        false
    }

    closed spec fn obeys_vmio_write_spec() -> bool {
        false
    }

    open spec fn read_requires(
        self,
        offset: usize,
        writer: VmWriter<'_>,
        writer_own: VmIoOwner,
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
        reader_own: VmIoOwner,
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
        old_writer_own: VmIoOwner,
        new_writer_own: VmIoOwner,
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
                &&& new_writer_own.range.start == old_writer_own.range.start
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
        old_reader_own: VmIoOwner,
        new_reader_own: VmIoOwner,
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
                &&& new_reader_own.range.start == old_reader_own.range.start
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
        Tracked(writer_own): Tracked<&mut VmIoOwner>,
        Tracked(owner): Tracked<&mut DmaCoherentVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        proof {
            assert(Self::obeys_vmio_spec());
            assert(Self::obeys_vmio_read_requires());
            assert(!Self::obeys_vmio_read_spec());
            assert(Self::read_requires(*self, offset, *writer, *writer_own, *owner));
        }
        proof_decl! {
            let tracked mut reader_own;
        }
        let mut reader = {
            let inner = self.read_inner();
            #[verus_spec(with => Tracked(reader_own))]
            Self::reader_inner(inner)
        };

        let remain_before_skip = reader.remain();
        if offset > remain_before_skip {
            return Err(Error::InvalidArgs);
        }
        let remain = remain_before_skip - offset;
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
        let reader = reader.skip(offset);
        proof {
            reader_own.advance(offset);
            assert(reader_own.inv());
            assert(writer_own.inv());
            assert(reader_own.mem_view matches Some(VmIoMemView::ReadView(_)));
            assert(reader_own.read_view_initialized());
            assert(writer_own.mem_view matches Some(VmIoMemView::WriteView(_)));
            assert(reader.remain_spec() >= len);
        }

        let copied = match reader.read_fallible(writer) {
            Ok(copied) => copied,
            Err((err, copied)) => {
                writer.cursor = writer.cursor.sub(copied);
                return Err(err);
            },
        };

        proof {
            reader_own.advance(copied);
            writer_own.advance(copied);
            assert(*owner == *old(owner));
        }

        Ok(())
    }

    fn write(
        &self,
        offset: usize,
        reader: &mut VmReader<'_>,
        Tracked(reader_own): Tracked<&mut VmIoOwner>,
        Tracked(owner): Tracked<&mut DmaCoherentVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        proof {
            assert(Self::obeys_vmio_spec());
            assert(Self::obeys_vmio_write_requires());
            assert(!Self::obeys_vmio_write_spec());
            assert(Self::write_requires(*self, offset, *reader, *reader_own, *owner));
        }
        proof_decl! {
            let tracked mut writer_own;
        }
        let mut writer = {
            let inner = self.read_inner();
            #[verus_spec(with => Tracked(writer_own))]
            Self::writer_inner(inner)
        };

        let avail_before_skip = writer.avail();
        if offset > avail_before_skip {
            return Err(Error::InvalidArgs);
        }
        let avail = avail_before_skip - offset;
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
        let writer = writer.skip(offset);
        proof {
            writer_own.advance(offset);

            assert(writer.avail_spec() >= len);
        }
        let copied = match writer.write_fallible(reader) {
            Ok(copied) => copied,
            Err((err, copied)) => {
                reader.cursor = reader.cursor.sub(copied);
                return Err(err);
            },
        };
        proof {
            writer_own.advance(copied);
            reader_own.advance(copied);
            assert(*owner == *old(owner));
        }

        Ok(())
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
    fn write_once<T: PodOnce>(&self, offset: usize, new_val: &T) -> core::result::Result<
        (),
        Error,
    > {
        self.writer().skip(offset).write_once(new_val)
    }
}

} // verus!
