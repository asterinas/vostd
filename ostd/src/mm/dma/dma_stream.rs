use core::{marker::PhantomData, ops::Range};

// SPDX-License-Identifier: MPL-2.0
use vstd::{predicate::Predicate, prelude::*};

use vstd_extra::external::convert::AsRefSpec;
use vstd_extra::ownership::{Inv, OwnerOf};

use crate::mm::vm_space::vm_space_specs::VmSpaceOwner;
use crate::{
    error::Error,
    mm::{
        Paddr,
        dma::{Daddr, DmaType, dma_type},
        frame::{AnyFrameMeta, Segment, untyped::AnyUFrameMeta},
        io::{
            FallibleVmRead, FallibleVmWrite, Infallible, VmIo, VmReader, VmWriter,
            axiom_kernel_mem_view,
        },
        kspace::{KERNEL_BASE_VADDR, KERNEL_END_VADDR, VMALLOC_BASE_VADDR},
        paddr_to_vaddr,
    },
    specs::{
        arch::{PAGE_SIZE, lemma_max_paddr_range, lemma_paddr_to_vaddr_properties},
        mm::io::{VmIoMemView, VmIoOwner},
        mm::virt_mem::{MemView, VirtPtr},
    },
    sync::{AtomicDataWithOwner, PreemptDisabled, RoArc, RwArc, RwLockReadGuard},
};

use super::{DmaError, HasDaddr, check_and_insert_dma_mapping, is_valid_daddr};

verus! {

/// A streaming DMA mapping. Users must synchronize data
/// before reading or after writing to ensure consistency.
///
/// The mapping is automatically destroyed when this object
/// is dropped.
///
/// # Notes
///
/// The runtime state is held behind an [`RwArc`]. The implementation keeps a
/// small local bridge for acquiring a read guard with the invariant visible to
/// Verus, while the public methods keep the executable data access inline.
pub struct DmaStream<M: AnyUFrameMeta + ?Sized> {
    pub inner: RwArc<DmaStreanInnerAtomic<M>>,
}

/// A slice of streaming DMA mapping.
pub struct DmaStreamSlice<Dma, M: AnyUFrameMeta + ?Sized> {
    pub stream: Dma,
    pub offset: usize,
    pub len: usize,
    pub _marker: PhantomData<M>,
}

impl<M: AnyUFrameMeta + ?Sized + OwnerOf, Dma: AsRef<DmaStream<M>>> Inv for DmaStreamSlice<Dma, M> {
    #[verifier::inline]
    open spec fn inv(self) -> bool {
        &&& self.len != 0
        &&& self.stream.as_ref_spec().inner.wf()
    }
}

#[verus_verify]
impl<M: AnyUFrameMeta + ?Sized, Dma: AsRef<DmaStream<M>>> DmaStreamSlice<Dma, M> {
    /// Constructs a `DmaStreamSlice` from the [`DmaStream`].
    #[verus_spec(returns
        (Self {
            stream,
            offset,
            len,
            _marker: PhantomData,
        }),
    )]
    #[inline]
    pub fn new(stream: Dma, offset: usize, len: usize) -> Self {
        /*
        // Original bounds assertions (removed during Verus migration):
        assert!(offset < stream.as_ref().nbytes());
        assert!(offset + len <= stream.as_ref().nbytes());
        */
        Self { stream, offset, len, _marker: PhantomData }
    }

    /// Returns the underlying `DmaStream`.
    #[inline]
    pub fn stream(&self) -> &DmaStream<M> {
        self.stream.as_ref()
    }

    /// Returns the offset of the slice.
    #[verus_spec(returns self.offset)]
    #[inline]
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Returns the number of bytes.
    #[verus_spec(returns self.len)]
    #[inline]
    pub fn nbytes(&self) -> usize {
        self.len
    }

    /// Synchronizes the streaming DMA mapping with the device for the slice.
    #[verifier::external_body]
    #[inline]
    pub fn sync(&self) -> Result<(), Error> where M: OwnerOf {
        self.stream.as_ref().sync(self.offset..self.offset + self.len)
    }

    #[verus_spec(
        requires
            self.inv(),
        returns
            /* */
    )]
    #[verifier::external_body]
    #[inline]
    pub fn daddr(&self) -> Daddr where M: OwnerOf {
        self.stream.as_ref().daddr() + self.offset
    }

    /// Returns a reader to read data from the slice.
    #[inline]
    #[verus_spec(r =>
        with
            -> reader_perm: Tracked<Option<VmIoOwner>>,
        requires
            self.inv(),
        ensures
            self.inv(),
            r is Ok ==> {
                &&& r.unwrap().inv()
                &&& r.unwrap().remain_spec() == self.len
                &&& reader_perm@ is Some
                &&& reader_perm@->0.inv()
                &&& reader_perm@->0.is_kernel
                &&& reader_perm@->0.has_read_view()
                &&& reader_perm@->0.read_view_initialized()
                &&& r.unwrap().wf(reader_perm@->0)
                &&& KERNEL_BASE_VADDR <= r.unwrap().cursor.range@.start
                &&& r.unwrap().cursor.range@.end <= KERNEL_END_VADDR
            },
    )]
    pub fn reader<'a>(&'a self) -> Result<VmReader<'a, Infallible>, Error> where M: OwnerOf {
        let inner = self.stream.as_ref().read_inner();

        if matches!(inner.direction, DmaDirection::ToDevice) {
            proof_with!(|= Tracked(None));
            Err(Error::AccessDenied)
        } else {
            match self.offset.checked_add(self.len) {
                None => {
                    proof_with!(|= Tracked(None));
                    Err(Error::InvalidArgs)
                },
                Some(end) if end > inner.segment.size() => {
                    proof_with!(|= Tracked(None));
                    Err(Error::InvalidArgs)
                },
                Some(_) => {
                    proof_decl! {
                        let ghost id: nat;
                        let tracked mut reader_perm: VmIoOwner;
                    }
                    proof {
                        lemma_max_paddr_range();
                        lemma_paddr_to_vaddr_properties(inner@.data.segment.start_paddr());
                    }

                    let base_vaddr = paddr_to_vaddr(inner.segment.start_paddr());
                    match base_vaddr.checked_add(self.offset) {
                        None => {
                            proof_with!(|= Tracked(None));
                            Err(Error::InvalidArgs)
                        },
                        Some(vaddr) => match vaddr.checked_add(self.len) {
                            None => {
                                proof_with!(|= Tracked(None));
                                Err(Error::InvalidArgs)
                            },
                            Some(end_vaddr) => {
                                let ghost range = vaddr..end_vaddr as usize;
                                let ptr = VirtPtr { vaddr, range: Ghost(range) };
                                proof {
                                    assert(KERNEL_BASE_VADDR > 0) by (compute_only);
                                    assert(vaddr > 0);
                                    assert(VMALLOC_BASE_VADDR <= KERNEL_END_VADDR)
                                        by (compute_only);
                                    assert(ptr.inv());
                                }

                                let reader = unsafe {
                                    proof_with!(Ghost(id) => Tracked(reader_perm));
                                    VmReader::from_kernel_space(ptr, self.len)
                                };
                                proof {
                                    let tracked mem_view = axiom_kernel_mem_view(range);
                                    reader_perm.mem_view = Some(VmIoMemView::ReadView(mem_view));
                                }
                                proof_with!(|= Tracked(Some(reader_perm)));
                                Ok(reader)
                            },
                        },
                    }
                },
            }
        }
    }

    /// Returns a writer to write data into the slice.
    #[inline]
    #[verus_spec(r =>
        with
            -> writer_perm: Tracked<Option<VmIoOwner>>,
        requires
            self.inv(),
        ensures
            self.inv(),
            r is Ok ==> {
                &&& r.unwrap().inv()
                &&& r.unwrap().avail_spec() == self.len
                &&& writer_perm@ is Some
                &&& writer_perm@->0.inv()
                &&& writer_perm@->0.is_kernel
                &&& writer_perm@->0.has_write_view()
                &&& r.unwrap().wf(writer_perm@->0)
                &&& KERNEL_BASE_VADDR <= r.unwrap().cursor.range@.start
                &&& r.unwrap().cursor.range@.end <= KERNEL_END_VADDR
            },
    )]
    pub fn writer<'a>(&'a self) -> Result<VmWriter<'a, Infallible>, Error> where M: OwnerOf {
        let inner = self.stream.as_ref().read_inner();

        if matches!(inner.direction, DmaDirection::FromDevice) {
            proof_with!(|= Tracked(None));
            Err(Error::AccessDenied)
        } else {
            match self.offset.checked_add(self.len) {
                None => {
                    proof_with!(|= Tracked(None));
                    Err(Error::InvalidArgs)
                },
                Some(end) if end > inner.segment.size() => {
                    proof_with!(|= Tracked(None));
                    Err(Error::InvalidArgs)
                },
                Some(_) => {
                    proof_decl! {
                        let ghost id: nat;
                        let tracked mut writer_perm: VmIoOwner;
                    }
                    proof {
                        lemma_max_paddr_range();
                        lemma_paddr_to_vaddr_properties(inner@.data.segment.start_paddr());
                    }

                    let base_vaddr = paddr_to_vaddr(inner.segment.start_paddr());
                    match base_vaddr.checked_add(self.offset) {
                        None => {
                            proof_with!(|= Tracked(None));
                            Err(Error::InvalidArgs)
                        },
                        Some(vaddr) => match vaddr.checked_add(self.len) {
                            None => {
                                proof_with!(|= Tracked(None));
                                Err(Error::InvalidArgs)
                            },
                            Some(end_vaddr) => {
                                let ghost range = vaddr..end_vaddr as usize;
                                let ptr = VirtPtr { vaddr, range: Ghost(range) };
                                proof {
                                    assert(VMALLOC_BASE_VADDR <= KERNEL_END_VADDR)
                                        by (compute_only);
                                }

                                let writer = unsafe {
                                    proof_with!(Ghost(id), Tracked(false) => Tracked(writer_perm));
                                    VmWriter::from_kernel_space(ptr, self.len)
                                };
                                proof {
                                    let tracked mem_view = axiom_kernel_mem_view(range);
                                    writer_perm.mem_view = Some(VmIoMemView::WriteView(mem_view));
                                }
                                proof_with!(|= Tracked(Some(writer_perm)));
                                Ok(writer)
                            },
                        },
                    }
                },
            }
        }
    }
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
    pub _marker: core::marker::PhantomData<M>,
}

pub type DmaStreanInnerAtomic<M> = AtomicDataWithOwner<DmaStreamInner<M>, DmaStreamInnerOwner<M>>;

#[verus_verify]
impl<M: AnyUFrameMeta + ?Sized + OwnerOf> DmaStream<M> {
    /// Establishes DMA stream mapping for a given [`Segment<M>`].
    ///
    /// The method fails if the segment already belongs to a DMA mapping.
    #[verus_spec(r =>
        requires
            segment.inv(),
        ensures
            r matches Ok(r) ==> r.inner.wf(),
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
                /*
                // Original TDX unprotect (removed during Verus migration):
                #[cfg(target_arch = "x86_64")]
                crate::arch::if_tdx_enabled!({
                    unsafe {
                        crate::arch::tdx_guest::unprotect_gpa_range(start_paddr, frame_count)
                            .unwrap();
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
                    let paddr = start_paddr + i * PAGE_SIZE;

                    /*
                    // Original IOMMU map (removed during Verus migration):
                    unsafe {
                        iommu::map(paddr as Daddr, paddr)->0;
                    }
                    */

                    i += 1;
                }

                start_paddr as Daddr
            },
        };

        let tracked inner_owner = DmaStreamInnerOwner { _marker: core::marker::PhantomData::<M> };

        let inner = RwArc::new(
            AtomicDataWithOwner::new(
                DmaStreamInner { segment, start_daddr, is_cache_coherent, direction },
                Tracked(inner_owner),
            ),
        );

        let stream = DmaStream { inner };

        Ok(stream)
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
        true
    }
}

#[verus_verify]
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
        ensures
            self.inner.wf(),
            r@.inv(),
    )]
    pub fn read_inner(&self) -> RwLockReadGuard<'_, DmaStreanInnerAtomic<M>, PreemptDisabled> {
        self.inner.read()
    }
}

#[verus_verify]
impl<M: AnyUFrameMeta + ?Sized + OwnerOf> DmaStream<M> {
    /// Returns the starting device address.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The inner [`RwArc`] is well-formed.
    /// ## Postconditions
    /// - The inner [`RwArc`] remains well-formed.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> inner_snapshot: Ghost<DmaStreamInner<M>>,
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            inner_snapshot@.inv(),
            r == inner_snapshot@.start_daddr,
    )]
    pub fn daddr(&self) -> Daddr {
        let inner = self.read_inner();
        let r = inner.start_daddr;
        let ghost inner_data = inner@.data;
        proof_with!(|= Ghost(inner_data));
        r
    }

    /// Returns the DMA direction.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The inner [`RwArc`] is well-formed.
    /// ## Postconditions
    /// - The inner [`RwArc`] remains well-formed.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> inner_snapshot: Ghost<DmaStreamInner<M>>,
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            inner_snapshot@.inv(),
            r == inner_snapshot@.direction,
    )]
    pub fn direction(&self) -> DmaDirection {
        let inner = self.read_inner();
        let r = inner.direction;
        let ghost inner_data = inner@.data;
        proof_with!(|= Ghost(inner_data));
        r
    }

    /// Synchronizes the streaming DMA mapping with the device.
    ///
    /// This method should be called under one of the two conditions:
    /// 1. The data of the stream DMA mapping has been updated by the device side.
    ///    The CPU side needs to call the `sync` method before reading data (e.g., using [`read_bytes`]).
    /// 2. The data of the stream DMA mapping has been updated by the CPU side
    ///    (e.g., using [`write_bytes`]).
    ///    Before the CPU side notifies the device side to read, it must call the `sync` method first.
    ///
    /// [`read_bytes`]: Self::read_bytes
    /// [`write_bytes`]: Self::write_bytes
    pub fn sync(&self, _byte_range: Range<usize>) -> Result<(), Error> {
        /*
        // Original sync() with cache-line flushing (removed during Verus migration):
        cfg_if::cfg_if! {
            if #[cfg(target_arch = "x86_64")]{
                Ok(())
            } else {
                if _byte_range.end > self.nbytes() {
                    return Err(Error::InvalidArgs);
                }
                if self.inner.is_cache_coherent {
                    return Ok(());
                }
                let start_va = crate::mm::paddr_to_vaddr(self.inner.segment.start_paddr()) as *const u8;
                for i in _byte_range.step_by(64) {
                    todo!()
                }
                Ok(())
            }
        }
        */
        Ok(())
    }

    /// Returns the starting physical address.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The inner [`RwArc`] is well-formed.
    /// ## Postconditions
    /// - The inner [`RwArc`] remains well-formed.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> inner_snapshot: Ghost<DmaStreamInner<M>>,
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            inner_snapshot@.inv(),
            r == inner_snapshot@.segment.start_paddr(),
    )]
    pub fn paddr(&self) -> Paddr {
        let inner = self.read_inner();
        let r = inner.segment.start_paddr();
        let ghost inner_data = inner@.data;
        proof_with!(|= Ghost(inner_data));
        r
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
        with
            -> inner_snapshot: Ghost<DmaStreamInner<M>>,
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            inner_snapshot@.inv(),
            r == inner_snapshot@.segment.size() / PAGE_SIZE,
    )]
    pub fn nframes(&self) -> usize {
        let inner = self.read_inner();
        let r = inner.segment.size() / PAGE_SIZE;
        let ghost inner_data = inner@.data;
        proof_with!(|= Ghost(inner_data));
        r
    }

    /// Returns the number of bytes.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> inner_snapshot: Ghost<DmaStreamInner<M>>,
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            inner_snapshot@.inv(),
            r == inner_snapshot@.segment.size(),
    )]
    pub fn nbytes(&self) -> usize {
        let inner = self.read_inner();
        let r = inner.segment.size();
        let ghost inner_data = inner@.data;
        proof_with!(|= Ghost(inner_data));
        r
    }

    /// Returns a reader to read data from it.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The inner [`RwArc`] is well-formed.
    /// ## Postconditions
    /// - The inner [`RwArc`] remains well-formed.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> reader_perm: Tracked<Option<VmIoOwner>>,
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            r is Ok ==> {
                &&& r.unwrap().inv()
                &&& reader_perm@ is Some
                &&& reader_perm@->0.inv()
                &&& reader_perm@->0.is_kernel
                &&& reader_perm@->0.has_read_view()
                &&& reader_perm@->0.read_view_initialized()
                &&& r.unwrap().wf(reader_perm@->0)
                &&& KERNEL_BASE_VADDR <= r.unwrap().cursor.range@.start
                &&& r.unwrap().cursor.range@.end <= KERNEL_END_VADDR
            },
    )]
    pub fn reader<'a>(&'a self) -> core::result::Result<VmReader<'a, Infallible>, Error> {
        let inner = self.read_inner();

        if matches!(inner.direction, DmaDirection::ToDevice) {
            proof_with!(|= Tracked(None));
            Err(Error::AccessDenied)
        } else {
            proof_decl! {
                let ghost id: nat;
                let tracked mut reader_perm: VmIoOwner;
            }
            proof {
                lemma_max_paddr_range();
                lemma_paddr_to_vaddr_properties(inner@.data.segment.start_paddr());
            }

            let vaddr = paddr_to_vaddr(inner.segment.start_paddr());
            let len = inner.segment.size();
            let ghost range = vaddr..(vaddr + len) as usize;
            let ptr = VirtPtr { vaddr, range: Ghost(range) };
            proof {
                assert(VMALLOC_BASE_VADDR <= KERNEL_END_VADDR) by (compute_only);
            }

            let reader = unsafe {
                proof_with!(Ghost(id) => Tracked(reader_perm));
                VmReader::from_kernel_space(ptr, len)
            };
            proof {
                let tracked mem_view = axiom_kernel_mem_view(range);
                reader_perm.mem_view = Some(VmIoMemView::ReadView(mem_view));
            }
            proof_with!(|= Tracked(Some(reader_perm)));
            Ok(reader)
        }
    }

    /// Returns a writer to write data to it.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The inner [`RwArc`] is well-formed.
    /// ## Postconditions
    /// - The inner [`RwArc`] remains well-formed.
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> writer_perm: Tracked<Option<VmIoOwner>>,
        requires
            self.inner.wf(),
        ensures
            self.inner.wf(),
            r is Ok ==> {
                &&& r.unwrap().inv()
                &&& writer_perm@ is Some
                &&& writer_perm@->0.inv()
                &&& writer_perm@->0.is_kernel
                &&& writer_perm@->0.has_write_view()
                &&& r.unwrap().wf(writer_perm@->0)
                &&& KERNEL_BASE_VADDR <= r.unwrap().cursor.range@.start
                &&& r.unwrap().cursor.range@.end <= KERNEL_END_VADDR
            },
    )]
    pub fn writer<'a>(&'a self) -> core::result::Result<VmWriter<'a, Infallible>, Error> {
        let inner = self.read_inner();

        if matches!(inner.direction, DmaDirection::FromDevice) {
            proof_with!(|= Tracked(None));
            Err(Error::AccessDenied)
        } else {
            proof_decl! {
                let ghost id: nat;
                let tracked mut writer_perm: VmIoOwner;
            }
            proof {
                lemma_max_paddr_range();
                lemma_paddr_to_vaddr_properties(inner@.data.segment.start_paddr());
            }

            let vaddr = paddr_to_vaddr(inner.segment.start_paddr());
            let len = inner.segment.size();
            let ghost range = vaddr..(vaddr + len) as usize;
            let ptr = VirtPtr { vaddr, range: Ghost(range) };
            proof {
                assert(KERNEL_BASE_VADDR > 0) by (compute_only);
                assert(vaddr > 0);
                assert(VMALLOC_BASE_VADDR <= KERNEL_END_VADDR) by (compute_only);
                assert(ptr.inv());
            }

            let writer = unsafe {
                proof_with!(Ghost(id), Tracked(false) => Tracked(writer_perm));
                VmWriter::from_kernel_space(ptr, len)
            };
            proof {
                let tracked mem_view = axiom_kernel_mem_view(range);
                writer_perm.mem_view = Some(VmIoMemView::WriteView(mem_view));
            }
            proof_with!(|= Tracked(Some(writer_perm)));
            Ok(writer)
        }
    }
}

impl<M: AnyUFrameMeta + ?Sized> Predicate<DmaStreamInner<M>> for DmaStreamInnerOwner<M> {
    #[verifier::inline]
    open spec fn predicate(&self, v: DmaStreamInner<M>) -> bool {
        &&& self.inv()
        &&& v.inv()
    }
}

/*
// Original Drop impl for DmaStreamInner (removed during Verus migration):
impl Drop for DmaStreamInner {
    fn drop(&mut self) {
        let start_paddr = self.segment.start_paddr();
        let frame_count = self.segment.size() / PAGE_SIZE;

        match dma_type() {
            DmaType::Direct => {
                #[cfg(target_arch = "x86_64")]
                crate::arch::if_tdx_enabled!({
                    unsafe {
                        crate::arch::tdx_guest::protect_gpa_range(start_paddr, frame_count)
                            .unwrap();
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

        remove_dma_mapping(start_paddr, frame_count);
    }
}
*/

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
        reader_own: VmIoOwner,
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
        old_writer_own: VmIoOwner,
        new_writer_own: VmIoOwner,
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
                &&& new_reader_own.range.start == old_reader_own.range.start
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
        Tracked(writer_own): Tracked<&mut VmIoOwner>,
        Tracked(owner): Tracked<&mut DmaStreamVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        proof {
            assert(!Self::obeys_vmio_read_spec());
            assert(Self::read_requires(*self, offset, *writer, *writer_own, *owner));
        }
        proof_decl! {
            let tracked reader_own_opt;
        }
        let mut reader = match {
            #[verus_spec(with => Tracked(reader_own_opt))]
            self.reader()
        } {
            Ok(reader) => reader,
            Err(err) => {
                return Err(err);
            },
        };
        let tracked mut reader_own = reader_own_opt.tracked_unwrap();

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
            return Ok(());
        }
        let reader = reader.skip(offset);
        proof {
            reader_own.advance(offset);
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
        }

        Ok(())
    }

    fn write(
        &self,
        offset: usize,
        reader: &mut VmReader<'_>,
        Tracked(reader_own): Tracked<&mut VmIoOwner>,
        Tracked(owner): Tracked<&mut DmaStreamVmIoOwner<M>>,
    ) -> core::result::Result<(), Error> {
        proof {
            assert(Self::obeys_vmio_spec());
            assert(Self::obeys_vmio_write_requires());
            assert(!Self::obeys_vmio_write_spec());
            assert(Self::write_requires(*self, offset, *reader, *reader_own, *owner));
        }
        proof_decl! {
            let tracked writer_own_opt;
        }
        let mut writer = match {
            #[verus_spec(with => Tracked(writer_own_opt))]
            self.writer()
        } {
            Ok(writer) => writer,
            Err(err) => {
                return Err(err);
            },
        };
        let tracked mut writer_own = writer_own_opt.tracked_unwrap();

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

impl<
    M: AnyUFrameMeta + ?Sized + Send + Sync + OwnerOf,
    Dma: AsRef<DmaStream<M>> + Send + Sync,
> VmIo<()> for DmaStreamSlice<Dma, M> {
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
        owner: (),
    ) -> bool {
        &&& self.inv()
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
        owner: (),
    ) -> bool {
        &&& self.inv()
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
        old_owner: (),
        new_owner: (),
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
        old_writer_own: VmIoOwner,
        new_writer_own: VmIoOwner,
        old_owner: (),
        new_owner: (),
        r: core::result::Result<(), Error>,
    ) -> bool {
        &&& self.inv()
        &&& new_owner == old_owner
        &&& new_reader.inv()
        &&& new_writer_own.inv()
        &&& new_reader.wf(new_writer_own)
        &&& match r {
            Ok(_) => {
                &&& new_reader.remain_spec() == 0
                &&& new_reader.cursor.vaddr == old_reader.cursor.vaddr + old_reader.remain_spec()
                &&& new_writer_own.range.start == old_writer_own.range.start
                    + old_reader.remain_spec()
            },
            Err(_) => {
                &&& new_reader == old_reader
                &&& new_writer_own == old_writer_own
            },
        }
    }

    #[verus_spec()]
    fn read(
        &self,
        offset: usize,
        writer: &mut VmWriter<'_>,
        Tracked(writer_own): Tracked<&mut VmIoOwner>,
        Tracked(owner): Tracked<&mut ()>,
    ) -> (r: core::result::Result<(), Error>) {
        proof {
            assert(!Self::obeys_vmio_read_spec());
            assert(Self::read_requires(*self, offset, *writer, *writer_own, *owner));
        }
        proof_decl! {
            let tracked reader_own_opt;
        }
        let mut reader = match {
            #[verus_spec(with => Tracked(reader_own_opt))]
            self.reader()
        } {
            Ok(reader) => reader,
            Err(err) => {
                return Err(err);
            },
        };
        let tracked mut reader_own = reader_own_opt.tracked_unwrap();

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
            return Ok(());
        }
        let reader = reader.skip(offset);
        proof {
            reader_own.advance(offset);
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
        }

        Ok(())
    }

    #[verus_spec()]
    fn write(
        &self,
        offset: usize,
        reader: &mut VmReader,
        Tracked(reader_own): Tracked<&mut VmIoOwner>,
        Tracked(owner): Tracked<&mut ()>,
    ) -> (r: core::result::Result<(), Error>)
        ensures
            Self::obeys_vmio_write_spec() ==> Self::write_spec(
                *self,
                offset,
                *old(reader),
                *final(reader),
                *old(reader_own),
                *final(reader_own),
                *old(owner),
                *final(owner),
                r,
            ),
    {
        proof {
            assert(Self::write_requires(*self, offset, *reader, *reader_own, *owner));
        }
        proof_decl! {
            let tracked writer_own_opt;
        }
        let mut writer = match {
            #[verus_spec(with => Tracked(writer_own_opt))]
            self.writer()
        } {
            Ok(writer) => writer,
            Err(err) => {
                return Err(err);
            },
        };
        let tracked mut slice_writer_own = writer_own_opt.tracked_unwrap();

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
            return Ok(());
        }
        let writer = writer.skip(offset);
        proof {
            slice_writer_own.advance(offset);
        }
        let copied = match writer.write_fallible(reader) {
            Ok(copied) => copied,
            Err((err, copied)) => {
                reader.cursor = reader.cursor.sub(copied);
                return Err(err);
            },
        };
        proof {
            slice_writer_own.advance(copied);
            reader_own.advance(copied);
        }

        Ok(())
    }
}

/*
// Original AsRef<DmaStream> for DmaStream (removed during Verus migration):
impl AsRef<DmaStream> for DmaStream {
    fn as_ref(&self) -> &DmaStream {
        self
    }
}
*/
/*
// Original HasPaddr for DmaStreamSlice (removed during Verus migration):
impl<Dma: AsRef<DmaStream>> HasPaddr for DmaStreamSlice<Dma> {
    fn paddr(&self) -> Paddr {
        self.stream.as_ref().paddr() + self.offset
    }
}
*/
/*
// Original Clone for DmaStreamSlice (removed during Verus migration):
impl<Dma: AsRef<DmaStream> + Clone> Clone for DmaStreamSlice<Dma> {
    fn clone(&self) -> Self {
        Self {
            stream: self.stream.clone(),
            offset: self.offset,
            len: self.len,
        }
    }
}
*/
} // verus!
