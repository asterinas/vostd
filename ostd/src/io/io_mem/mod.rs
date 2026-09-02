// SPDX-License-Identifier: MPL-2.0
//! I/O memory and its allocator that allocates memory I/O (MMIO) to device drivers.
use crate::specs::arch::PAGE_SIZE;
use crate::specs::{
    mm::{io::VmIoOwner, virt_mem::VirtPtr},
    task::AnyAtomicGuard,
};
use vstd::prelude::*;

mod allocator;

use core::ops::{Deref, Range};

use align_ext::AlignExt;

pub(crate) use self::allocator::IoMemAllocatorBuilder;
pub(super) use self::allocator::init;
use crate::{
    Error,
    mm::{
        FallibleVmRead, FallibleVmWrite, HasPaddr, Infallible, /*PAGE_SIZE,*/ Paddr, PodOnce,
        VmIo, VmIoOnce, VmReader, VmWriter,
        kspace::kvirt_area::KVirtArea,
        page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags},
    },
    prelude::*,
};

/// I/O memory.
#[derive(Debug, Clone)]
#[verus_verify]
pub struct IoMem {
    kvirt_area: Arc<KVirtArea>,
    // The actually used range for MMIO is `kvirt_area.start + offset..kvirt_area.start + offset + limit`
    offset: usize,
    limit: usize,
    pa: Paddr,
}

verus! {

#[verus_verify]
impl IoMem {
    /// Logical physical-address projection used by verified callers.
    pub closed spec fn paddr_spec(&self) -> Paddr {
        self.pa
    }

    /// Logical byte length used by verified callers.
    pub closed spec fn length_spec(&self) -> usize {
        self.limit
    }

    /// Logical offset into the page-aligned mapping.
    pub closed spec fn offset_spec(&self) -> usize {
        self.offset
    }
}

} // verus!
#[verus_verify]
impl HasPaddr for IoMem {
    #[verus_spec(result => ensures result == self.paddr_spec())]
    fn paddr(&self) -> Paddr {
        self.pa
    }
}

#[verus_verify]
impl IoMem {
    /// Acquires an `IoMem` instance for the given range.
    #[verus_spec(result =>
        requires
            vstd::arithmetic::power2::is_pow2(PAGE_SIZE as int),
            range.start < range.end,
            range.end <= usize::MAX - (PAGE_SIZE - 1),
            allocator::io_mem_range_registered(range),
        ensures
            result is Ok ==> result->Ok_0.paddr_spec() == range.start,
            result is Ok ==> result->Ok_0.length_spec()
                == vstd_extra::external::range::range_usize_len_spec(&range),
    )]
    pub fn acquire(range: Range<Paddr>) -> Result<IoMem> {
        allocator::IO_MEM_ALLOCATOR
            .get()
            /* .unwrap() */
            .ok_or(Error::AccessDenied)?
            .acquire(range)
            .ok_or(Error::AccessDenied)
    }

    /// Returns the physical address of the I/O memory.
    #[verus_verify]
    #[verus_spec(result => ensures result == self.paddr_spec())]
    pub fn paddr(&self) -> Paddr {
        self.pa
    }

    /// Returns the length of the I/O memory region.
    #[verus_verify]
    #[verus_spec(result => ensures result == self.length_spec())]
    pub fn length(&self) -> usize {
        self.limit
    }

    /// Slices the `IoMem`, returning another `IoMem` representing the subslice.
    ///
    /// # Panics
    ///
    /// This method will panic if the range is empty or out of bounds.
    #[verus_verify]
    #[verus_spec(result =>
        requires
            range.start < range.end,
            range.end <= self.length_spec(),
            self.offset_spec() + range.start <= usize::MAX,
            self.paddr_spec() + range.start <= usize::MAX,
        ensures
            result.offset_spec() == self.offset_spec() + range.start,
            result.length_spec() == range.end - range.start,
            result.paddr_spec() == self.paddr_spec() + range.start,
    )]
    pub fn slice(&self, range: Range<usize>) -> Self {
        // This ensures `range.start < range.end` and `range.end <= limit`.
        /*
        assert!(!range.is_empty() && range.end <= self.limit);
        */
        vstd_extra::assert!(range.start < range.end && range.end <= self.limit);

        // We've checked the range is in bounds, so we can construct the new `IoMem` safely.
        Self {
            kvirt_area: self.kvirt_area.clone(),
            offset: self.offset + range.start,
            /* limit: range.len(), */
            limit: vstd_extra::external::range::range_usize_len(&range),
            pa: self.pa + range.start,
        }
    }

    /// Creates a new `IoMem`.
    ///
    /// # Safety
    ///
    /// - The given physical address range must be in the I/O memory region.
    /// - Reading from or writing to I/O memory regions may have side effects. Those side effects
    ///   must not cause soundness problems (e.g., they must not corrupt the kernel memory).
    #[verifier::external_body]
    #[verus_spec(result =>
        requires
            vstd::arithmetic::power2::is_pow2(PAGE_SIZE as int),
            range.start <= range.end,
            range.end <= usize::MAX - (PAGE_SIZE - 1),
        ensures
            result.paddr_spec() == range.start,
            result.length_spec()
                == vstd_extra::external::range::range_usize_len_spec(&range),
    )]
    pub(crate) unsafe fn new(range: Range<Paddr>, flags: PageFlags, cache: CachePolicy) -> Self {
        let first_page_start = range.start.align_down(PAGE_SIZE);
        let last_page_end = range.end.align_up(PAGE_SIZE);

        let frames_range = first_page_start..last_page_end;
        let area_size = frames_range.len();

        #[cfg(target_arch = "x86_64")]
        let priv_flags = crate::arch::if_tdx_enabled!({
            assert!(
                first_page_start == range.start && last_page_end == range.end,
                "I/O memory is not page aligned, which cannot be unprotected in TDX: {:#x?}..{:#x?}",
                range.start,
                range.end,
            );

            let num_pages = area_size / PAGE_SIZE;
            // SAFETY:
            //  - The range `first_page_start..last_page_end` is always page aligned.
            //  - FIXME: We currently do not limit the I/O memory allocator with the maximum GPA,
            //    so the address range may not fall in the GPA limit.
            //  - FIXME: The I/O memory can be at a high address, so it may not be contained in the
            //    linear mapping.
            //  - The caller guarantees that operations on the I/O memory do not have any side
            //    effects that may cause soundness problems, so the pages can safely be viewed as
            //    untyped memory.
            unsafe { crate::arch::tdx_guest::unprotect_gpa_range(first_page_start, num_pages).unwrap() };

            PrivilegedPageFlags::SHARED
        } else {
            PrivilegedPageFlags::empty()
        });
        #[cfg(not(target_arch = "x86_64"))]
        let priv_flags = PrivilegedPageFlags::empty();

        let prop = PageProperty {
            flags,
            cache,
            priv_flags,
        };

        // SAFETY: The caller of `IoMem::new()` ensures that the given
        // physical address range is I/O memory, so it is safe to map.
        // Original Rust:
        // let kva = unsafe { KVirtArea::map_untracked_frames(area_size, 0, frames_range, prop) };
        let kva = unsafe {
            KVirtArea::map_untracked_frames::<AnyAtomicGuard>(area_size, 0, frames_range, prop)
        };

        Self {
            kvirt_area: Arc::new(kva),
            offset: range.start - first_page_start,
            limit: range.len(),
            pa: range.start,
        }
    }
}

// For now, we reuse `VmReader` and `VmWriter` to access I/O memory.
//
// Note that I/O memory is not normal typed or untyped memory. Strictly speaking, it is not
// "memory", but rather I/O ports that communicate directly with the hardware. However, this code
// is in OSTD, so we can rely on the implementation details of `VmReader` and `VmWriter`, which we
// know are also suitable for accessing I/O memory.

impl IoMem {
    fn reader(&self) -> VmReader<'_, Infallible> {
        // SAFETY: The constructor of the `IoMem` structure has already ensured the
        // safety of reading from the mapped physical address, and the mapping is valid.
        unsafe {
            VmReader::from_kernel_space(
                /* Original Rust:
                (self.kvirt_area.deref().start() + self.offset) as *mut u8, */
                VirtPtr::from_vaddr(self.kvirt_area.deref().start() + self.offset, self.limit),
                self.limit,
            )
        }
    }

    fn writer(&self) -> VmWriter<'_, Infallible> {
        // SAFETY: The constructor of the `IoMem` structure has already ensured the
        // safety of writing to the mapped physical address, and the mapping is valid.
        unsafe {
            VmWriter::from_kernel_space(
                /* Original Rust:
                (self.kvirt_area.deref().start() + self.offset) as *mut u8, */
                VirtPtr::from_vaddr(self.kvirt_area.deref().start() + self.offset, self.limit),
                self.limit,
            )
        }
    }
}

verus! {

/* Original Rust: impl VmIo for IoMem { */
impl VmIo<()> for IoMem {
    closed spec fn obeys_vmio_spec() -> bool {
        false
    }

    closed spec fn obeys_vmio_read_spec() -> bool {
        false
    }

    closed spec fn obeys_vmio_write_spec() -> bool {
        false
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
        r: Result<()>,
    ) -> bool {
        false
    }

    open spec fn write_spec(
        self,
        offset: usize,
        old_reader: VmReader<'_>,
        new_reader: VmReader<'_>,
        old_reader_own: VmIoOwner,
        new_reader_own: VmIoOwner,
        old_owner: (),
        new_owner: (),
        r: Result<()>,
    ) -> bool {
        false
    }

    /// Device reads are a trusted hardware boundary; the range checks and cursor updates remain
    /// identical to the original implementation.
    #[verifier::external_body]
    /* Original Rust: fn read(&self, offset: usize, writer: &mut VmWriter) -> Result<()> { */
    fn read(
        &self,
        offset: usize,
        writer: &mut VmWriter,
        Tracked(_writer_own): Tracked<&mut VmIoOwner>,
        Tracked(_owner): Tracked<&mut ()>,
    ) -> Result<()> {
        let offset = offset + self.offset;
        if self.limit.checked_sub(offset).is_none_or(|remain| remain < writer.avail()) {
            return Err(Error::InvalidArgs);
        }
        self.reader().skip(offset).read_fallible(writer).map_err(|(e, _)| e)?;
        debug_assert!(!writer.has_avail());

        Ok(())
    }

    /// Device writes are a trusted hardware boundary for the same reason as [`Self::read`].
    #[verifier::external_body]
    /* Original Rust: fn write(&self, offset: usize, reader: &mut VmReader) -> Result<()> { */
    fn write(
        &self,
        offset: usize,
        reader: &mut VmReader,
        Tracked(_reader_own): Tracked<&mut VmIoOwner>,
        Tracked(_owner): Tracked<&mut ()>,
    ) -> Result<()> {
        let offset = offset + self.offset;
        if self.limit.checked_sub(offset).is_none_or(|remain| remain < reader.remain()) {
            return Err(Error::InvalidArgs);
        }
        self.writer().skip(offset).write_fallible(reader).map_err(|(e, _)| e)?;
        debug_assert!(!reader.has_remain());

        Ok(())
    }
}

impl VmIoOnce for IoMem {
    closed spec fn obeys_vmio_once_read_requires() -> bool {
        false
    }

    closed spec fn obeys_vmio_once_write_requires() -> bool {
        false
    }

    closed spec fn obeys_vmio_once_read_ensures() -> bool {
        false
    }

    closed spec fn obeys_vmio_once_write_ensures() -> bool {
        false
    }

    #[verifier::external_body]
    fn read_once<T: PodOnce>(&self, offset: usize) -> Result<T> {
        self.reader().skip(offset).read_once()
    }

    #[verifier::external_body]
    fn write_once<T: PodOnce>(&self, offset: usize, new_val: &T) -> Result<()> {
        self.writer().skip(offset).write_once(new_val)
    }
}

} // verus!
impl Drop for IoMem {
    fn drop(&mut self) {
        // TODO: Multiple `IoMem` instances should not overlap, we should refactor the driver code and
        // remove the `Clone` and `IoMem::slice`. After refactoring, the `Drop` can be implemented to recycle
        // the `IoMem`.
    }
}
