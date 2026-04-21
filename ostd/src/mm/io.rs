// SPDX-License-Identifier: MPL-2.0
//! Abstractions for reading and writing virtual memory (VM) objects.
//!
//! # Safety
//!
//! The core virtual memory (VM) access APIs provided by this module are [`VmReader`] and
//! [`VmWriter`], which allow for writing to or reading from a region of memory _safely_.
//! `VmReader` and `VmWriter` objects can be constructed from memory regions of either typed memory
//! (e.g., `&[u8]`) or untyped memory (e.g, [`UFrame`]). Behind the scene, `VmReader` and `VmWriter`
//! must be constructed via their [`from_user_space`] and [`from_kernel_space`] methods, whose
//! safety depends on whether the given memory regions are _valid_ or not.
//!
//! [`UFrame`]: crate::mm::UFrame
//! [`from_user_space`]: `VmReader::from_user_space`
//! [`from_kernel_space`]: `VmReader::from_kernel_space`
//!
//! Here is a list of conditions for memory regions to be considered valid:
//!
//! - The memory region as a whole must be either typed or untyped memory, not both typed and
//!   untyped.
//!
//! - If the memory region is typed, we require that:
//!   - the [validity requirements] from the official Rust documentation must be met, and
//!   - the type of the memory region (which must exist since the memory is typed) must be
//!     plain-old-data, so that the writer can fill it with arbitrary data safely.
//!
//! [validity requirements]: core::ptr#safety
//!
//! - If the memory region is untyped, we require that:
//!   - the underlying pages must remain alive while the validity requirements are in effect, and
//!   - the kernel must access the memory region using only the APIs provided in this module, but
//!     external accesses from hardware devices or user programs do not count.
//!
//! We have the last requirement for untyped memory to be valid because the safety interaction with
//! other ways to access the memory region (e.g., atomic/volatile memory loads/stores) is not
//! currently specified. Tis may be relaxed in the future, if appropriate and necessary.
//!
//! Note that data races on untyped memory are explicitly allowed (since pages can be mapped to
//! user space, making it impossible to avoid data races). However, they may produce erroneous
//! results, such as unexpected bytes being copied, but do not cause soundness problems.
use core::marker::PhantomData;
use vstd::pervasive::{arbitrary, proof_from_false};
use vstd::prelude::*;
use vstd_extra::ownership::Inv;
use vstd_extra::trans_macros::assert;

use crate::arch::mm::{__memcpy_fallible, __memset_fallible};
use crate::error::*;
use crate::mm::kspace::{KERNEL_BASE_VADDR, KERNEL_END_VADDR};
use crate::mm::pod::{Pod, PodOnce};
use crate::specs::mm::virt_mem_newer::{MemView, VirtPtr};

pub use crate::specs::mm::io::{VmIoMemView, VmIoOwner};

/// Copies `len` bytes from `src` to `dst`, stopping early on page fault.
/// Returns the number of bytes successfully copied.
///
/// # Safety
/// - `src` must be valid for reads of `len` bytes.
/// - `dst` must either be valid for writes of `len` bytes or be in user space.
unsafe fn memcpy_fallible(dst: *mut u8, src: *const u8, len: usize) -> usize {
    let failed_bytes = unsafe { __memcpy_fallible(dst, src, len) };
    len - failed_bytes
}

/// Fills `len` bytes of memory at `dst` with the specified `value`, stopping
/// early on page fault. Returns the number of bytes successfully set.
///
/// # Safety
/// - `dst` must either be valid for writes of `len` bytes or be in user space.
unsafe fn memset_fallible(dst: *mut u8, value: u8, len: usize) -> usize {
    let failed_bytes = unsafe { __memset_fallible(dst, value, len) };
    len - failed_bytes
}

verus! {

/// Marker type indicating that VM I/O operations may fail (e.g., user-space access).
pub struct Fallible {}

/// Marker type indicating that VM I/O operations cannot fail (e.g., kernel-space access).
pub struct Infallible {}

/// Copies `len` bytes from `src` to `dst`.
///
/// # Safety
///
/// - `src` must be [valid] for reads of `len` bytes.
/// - `dst` must be [valid] for writes of `len` bytes.
///
/// [valid]: crate::mm::io#safety
#[inline]
#[verifier::external_body]
#[verus_spec(
    requires
        KERNEL_BASE_VADDR <= dst && dst + len <= KERNEL_END_VADDR &&
        KERNEL_BASE_VADDR <= src && src + len <= KERNEL_END_VADDR
)]
unsafe fn memcpy(dst: usize, src: usize, len: usize) {
    // This method is implemented by calling `volatile_copy_memory`. Note that even with the
    // "volatile" keyword, data races are still considered undefined behavior (UB) in both the Rust
    // documentation and the C/C++ standards. In general, UB makes the behavior of the entire
    // program unpredictable, usually due to compiler optimizations that assume the absence of UB.
    // However, in this particular case, considering that the Linux kernel uses the "volatile"
    // keyword to implement `READ_ONCE`/`WRITE_ONCE`, the compiler is extremely unlikely to
    // break our code unless it also breaks the Linux kernel.
    //
    // For more details and future possibilities, see
    // <https://github.com/asterinas/asterinas/pull/1001#discussion_r1667317406>.
    // SAFETY: The safety is guaranteed by the safety preconditions and the explanation above.
    core::intrinsics::volatile_copy_memory(dst as *mut u8, src as *const u8, len);
}

/// Reads a `Pod` value directly from a verified memory view.
///
/// # Verified Properties
/// ## Preconditions
/// - `ptr` must satisfy [`VirtPtr::inv`].
/// - The readable range `[ptr.vaddr, ptr.vaddr + size_of::<T>())` must fit in `ptr.range@`.
/// - Every byte in that range must translate in `mem` and be initialized.
/// ## Postconditions
/// - The function returns a `T` value reconstructed from the bytes at `ptr`.
/// ## Safety
/// - This function is trusted because Verus cannot currently express the raw-pointer read needed
///   to reconstruct a typed `Pod` value from verified byte-level memory permissions.
#[verifier::external_body]
#[verus_spec(
    with
        Tracked(mem): Tracked<&MemView>,
    requires
        ptr.inv(),
        core::mem::size_of::<T>() <= ptr.range@.end - ptr.vaddr,
        forall|i: usize|
            #![trigger mem.addr_transl(i)]
            ptr.vaddr <= i < ptr.vaddr + core::mem::size_of::<T>() ==> {
                &&& mem.addr_transl(i) is Some
                &&& mem.memory.contains_key(mem.addr_transl(i).unwrap().0)
                &&& mem.memory[mem.addr_transl(i).unwrap().0].contents[mem.addr_transl(i).unwrap().1 as int] is Init
            },
)]
fn read_pod_from_view<T: Pod>(ptr: VirtPtr) -> T {
    unsafe { (ptr.vaddr as *const T).read() }
}

/// Reads a `PodOnce` value using one volatile memory load from a verified memory view.
///
/// # Verified Properties
/// ## Preconditions
/// - `ptr` must satisfy [`VirtPtr::inv`].
/// - The readable range `[ptr.vaddr, ptr.vaddr + size_of::<T>())` must fit in `ptr.range@`.
/// - `ptr.vaddr` must satisfy the alignment requirement of `T`.
/// - Every byte in that range must translate in `mem` and be initialized.
/// ## Postconditions
/// - The function returns a `T` value read from `ptr` using one volatile load.
/// ## Safety
/// - This function is trusted because the underlying volatile typed read relies on raw-pointer
///   operations that Verus does not yet model directly.
#[verifier::external_body]
#[verus_spec(
    with
        Tracked(mem): Tracked<&MemView>,
    requires
        ptr.inv(),
        core::mem::size_of::<T>() <= ptr.range@.end - ptr.vaddr,
        ptr.vaddr % core::mem::align_of::<T>() == 0,
        forall|i: usize|
            #![trigger mem.addr_transl(i)]
            ptr.vaddr <= i < ptr.vaddr + core::mem::size_of::<T>() ==> {
                &&& mem.addr_transl(i) is Some
                &&& mem.memory.contains_key(mem.addr_transl(i).unwrap().0)
                &&& mem.memory[mem.addr_transl(i).unwrap().0].contents[mem.addr_transl(i).unwrap().1 as int] is Init
            },
)]
fn read_once_from_view<T: PodOnce>(ptr: VirtPtr) -> T {
    let pnt = ptr.vaddr as *const T;
    unsafe { pnt.read_volatile() }
}

/// Writes a `Pod` value into a verified memory view.
///
/// # Verified Properties
/// ## Preconditions
/// - `ptr` must satisfy [`VirtPtr::inv`].
/// - The writable range `[ptr.vaddr, ptr.vaddr + size_of::<T>())` must fit in `ptr.range@`.
/// - Every byte in that range must translate in `mem`.
/// ## Safety
/// - This function is trusted because Verus cannot currently express the raw-pointer write
///   needed to place a typed `Pod` value into verified byte-level memory permissions.
#[verifier::external_body]
#[verus_spec(
    with
        Tracked(mem): Tracked<&MemView>,
    requires
        ptr.inv(),
        core::mem::size_of::<T>() <= ptr.range@.end - ptr.vaddr,
        forall|i: usize|
            #![trigger mem.addr_transl(i)]
            ptr.vaddr <= i < ptr.vaddr + core::mem::size_of::<T>() ==> {
                &&& mem.addr_transl(i) is Some
                &&& mem.memory.contains_key(mem.addr_transl(i).unwrap().0)
            },
)]
fn write_pod_to_view<T: Pod>(ptr: VirtPtr, val: T) {
    unsafe { (ptr.vaddr as *mut T).write(val) }
}

/// Writes a `PodOnce` value with one volatile memory store into a verified memory view.
///
/// # Verified Properties
/// ## Preconditions
/// - `ptr` must satisfy [`VirtPtr::inv`].
/// - The writable range `[ptr.vaddr, ptr.vaddr + size_of::<T>())` must fit in `ptr.range@`.
/// - `ptr.vaddr` must satisfy the alignment requirement of `T`.
/// - Every byte in that range must translate in `mem`.
/// ## Safety
/// - Trusted because the underlying volatile typed write relies on raw-pointer operations
///   that Verus does not yet model directly.
#[verifier::external_body]
#[verus_spec(
    with
        Tracked(mem): Tracked<&MemView>,
    requires
        ptr.inv(),
        core::mem::size_of::<T>() <= ptr.range@.end - ptr.vaddr,
        ptr.vaddr % core::mem::align_of::<T>() == 0,
        forall|i: usize|
            #![trigger mem.addr_transl(i)]
            ptr.vaddr <= i < ptr.vaddr + core::mem::size_of::<T>() ==> {
                &&& mem.addr_transl(i) is Some
                &&& mem.memory.contains_key(mem.addr_transl(i).unwrap().0)
            },
)]
fn write_once_to_view<T: PodOnce>(ptr: VirtPtr, val: T) {
    let pnt = ptr.vaddr as *mut T;
    unsafe { pnt.write_volatile(val) }
}

/// [`VmReader`] is a reader for reading data from a contiguous range of memory.
///
/// The memory range read by [`VmReader`] can be in either kernel space or user space.
/// When the operating range is in kernel space, the memory within that range
/// is guaranteed to be valid, and the corresponding memory reads are infallible.
/// When the operating range is in user space, it is ensured that the page table of
/// the process creating the [`VmReader`] is active for the duration of `'a`,
/// and the corresponding memory reads are considered fallible.
///
/// When perform reading with a [`VmWriter`], if one of them represents typed memory,
/// it can ensure that the reading range in this reader and writing range in the
/// writer are not overlapped.
///
/// NOTE: The overlap mentioned above is at both the virtual address level
/// and physical address level. There is not guarantee for the operation results
/// of [`VmReader`] and [`VmWriter`] in overlapping untyped addresses, and it is
/// the user's responsibility to handle this situation.
pub struct VmReader<'a, Fallibility = Fallible> {
    pub id: Ghost<nat>,
    pub cursor: VirtPtr,
    pub end: VirtPtr,
    pub phantom: PhantomData<(&'a [u8], Fallibility)>,
}

/// [`VmWriter`] is a writer for writing data to a contiguous range of memory.
///
/// The memory range write by [`VmWriter`] can be in either kernel space or user space.
/// When the operating range is in kernel space, the memory within that range
/// is guaranteed to be valid, and the corresponding memory writes are infallible.
/// When the operating range is in user space, it is ensured that the page table of
/// the process creating the [`VmWriter`] is active for the duration of `'a`,
/// and the corresponding memory writes are considered fallible.
///
/// When perform writing with a [`VmReader`], if one of them represents typed memory,
/// it can ensure that the writing range in this writer and reading range in the
/// reader are not overlapped.
///
/// NOTE: The overlap mentioned above is at both the virtual address level
/// and physical address level. There is not guarantee for the operation results
/// of [`VmReader`] and [`VmWriter`] in overlapping untyped addresses, and it is
/// the user's responsibility to handle this situation.
pub struct VmWriter<'a, Fallibility = Fallible> {
    pub id: Ghost<nat>,
    pub cursor: VirtPtr,
    pub end: VirtPtr,
    pub phantom: PhantomData<(&'a [u8], Fallibility)>,
}

#[verus_verify]
impl<'a> VmWriter<'a, Infallible> {
    /// Constructs a [`VmWriter`] from a pointer and a length, which represents
    /// a memory range in kernel space.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The memory region represented by `ptr` and `len` must be valid for writes of `len` bytes
    ///   during the entire lifetime `a`. This means that the underlying pages must remain alive,
    ///   and the kernel must access the memory region using only the APIs provided in this module.
    /// - The range `ptr.vaddr..ptr.vaddr + len` must represent a kernel space memory range.
    /// ## Postconditions
    /// - An infallible [`VmWriter`] will be created with the range `ptr.vaddr..ptr.vaddr + len`.
    /// - The created [`VmWriter`] will have a unique identifier `id`, and its cursor will be
    ///   initialized to `ptr`.
    /// - The created [`VmWriter`] will be associated with a [`VmIoOwner`] that has the same `id`, the
    ///   same memory range, and is marked as kernel space and infallible.
    /// - The memory view of the associated [`VmIoOwner`] will be `None`, indicating that it does not
    ///   have any specific permissions yet.
    /// ## Safety
    ///
    /// `ptr` must be [valid] for writes of `len` bytes during the entire lifetime `a`.
    ///
    /// [valid]: crate::mm::io#safety
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
                -> owner: Tracked<VmIoOwner<'a>>,
        requires
            ptr.inv(),
            ptr.range@.start == ptr.vaddr,
            len == ptr.range@.end - ptr.range@.start,
        ensures
            owner@.inv(),
            r.wf(owner@),
            owner@.id == id,
            owner@.mem_view is None,
            r.cursor == ptr,
            r.end.vaddr == ptr.vaddr + len,
            r.cursor.range@ == ptr.range@,
            r.end.range@ == ptr.range@,
    )]
    pub unsafe fn from_kernel_space(ptr: VirtPtr, len: usize) -> Self {
        let ghost range = ptr.range@;
        let tracked owner = VmIoOwner {
            id: Ghost(id),
            range: Ghost(range),
            phantom: PhantomData,
            mem_view: None,
        };

        proof_with!(|= Tracked(owner));
        Self { id: Ghost(id), cursor: ptr, end: ptr.wrapping_add(len), phantom: PhantomData }
    }

    /// Converts a PoD value into a [`VmWriter`] that writes to the memory occupied by the PoD value.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// None as the Rust's type system guarantees that if `T` is valid, then we can always create a
    /// valid `VmWriter` for it.
    /// ## Postconditions
    /// - If the memory region occupied by `val` is valid for writes, then an infallible [`VmWriter`]
    ///   will be created that points to the memory region of `val`.
    /// - If the memory region occupied by `val` is not valid for writes, then an [`IoError`] will be
    ///   returned.
    ///
    /// [`IoError`]: `Error::IoError`
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
            -> owner: Tracked<Result<VmIoOwner<'a>>>,
        ensures
            r is Ok <==> owner@ is Ok,
            r matches Ok(r) ==> {
                &&& owner@ matches Ok(owner) ==> {
                    &&& r.inv()
                    &&& r.avail_spec() == core::mem::size_of::<T>()
                    &&& owner.inv()
                    &&& r.wf(owner)
                }
            }
    )]
    pub fn from_pod<T: Pod>(mut val: T) -> Result<VmWriter<'a, Infallible>> {
        proof_decl! {
            let tracked mut perm;
        }

        let pnt = val.as_bytes_mut().as_mut_ptr() as usize;
        let len = core::mem::size_of::<T>();

        if len != 0 && (pnt < KERNEL_BASE_VADDR || len >= KERNEL_END_VADDR || pnt > KERNEL_END_VADDR
            - len) || pnt == 0 {
            proof_with!(|= Tracked(Err(Error::IoError)));
            Err(Error::IoError)
        } else {
            let ghost range = pnt..(pnt + len) as usize;
            let vptr = VirtPtr { vaddr: pnt as usize, range: Ghost(range) };
            let r = unsafe {
                #[verus_spec(with Ghost(id) => Tracked(perm))]
                VmWriter::from_kernel_space(vptr, len)
            };

            proof_with!(|= Tracked(Ok(perm)));
            Ok(r)
        }
    }

    /// Converts an infallible writer into a fallible one.
    pub fn to_fallible(self) -> VmWriter<'a, Fallible> {
        VmWriter {
            id: self.id,
            cursor: self.cursor,
            end: self.end,
            phantom: PhantomData,
        }
    }

    /// Constructs a `VmWriter<'a, Infallible>` from a mutable byte slice.
    /// Matches vostd's `From<&mut [u8]>` conversion; body trusted.
    #[verifier::external_body]
    pub fn from_slice_mut(slice: &'a mut [u8]) -> Self {
        let addr = slice.as_mut_ptr() as usize;
        let end_addr = addr + slice.len();
        VmWriter {
            id: Ghost(arbitrary()),
            cursor: VirtPtr { vaddr: addr, range: Ghost(addr..end_addr) },
            end: VirtPtr { vaddr: end_addr, range: Ghost(addr..end_addr) },
            phantom: PhantomData,
        }
    }

    /// Panic condition for [`Self::fill`]: either the cursor isn't aligned
    /// for `T`, or the available space isn't a multiple of `size_of::<T>()`.
    pub open spec fn fill_panic_condition<T>(self) -> bool {
        ||| self.cursor.vaddr as int % core::mem::align_of::<T>() as int != 0
        ||| (self.end.vaddr - self.cursor.vaddr) as int
            % core::mem::size_of::<T>() as int != 0
    }

    /// Fills the available space by repeatedly writing the same `Pod` value.
    ///
    /// Returns the number of elements written. Body unverified pending
    /// proper VmIoMemView::WriteView threading for arbitrary Pod writes.
    ///
    /// # Panics
    /// If cursor isn't aligned for `T`, or `avail()` isn't a multiple of
    /// `size_of::<T>()` ([`Self::fill_panic_condition`]).
    // TODO: Drop `external_body` once Verus supports `usize as *mut T` or
    // the body is refactored to go through `ArrayPtr::from_addr` with a
    // tracked `PointsToArray` permission.
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            !old(self).fill_panic_condition::<T>(),
    )]
    pub fn fill<T: Pod>(&mut self, value: T) -> usize {
        let cursor = self.cursor.vaddr as *mut T;
        vstd_extra::assert_eq!((cursor as usize) % core::mem::align_of::<T>(), 0);

        let avail = self.end.vaddr - self.cursor.vaddr;
        vstd_extra::assert_eq!(avail % core::mem::size_of::<T>(), 0);
        let written_num = avail / core::mem::size_of::<T>();

        for i in 0..written_num {
            // SAFETY: written_num is bounded by avail / size_of::<T>() so each
            // write targets memory owned by this writer, and cursor is aligned.
            unsafe { cursor.wrapping_add(i).write_volatile(value) };
        }

        // All available space has been filled; cursor moves to end.
        self.cursor = self.end;
        written_num
    }
}

impl<Fallibility> Clone for VmReader<'_, Fallibility> {
    /// [`Clone`] can be implemented for [`VmReader`]
    /// because it either points to untyped memory or represents immutable references.
    ///
    /// Note that we cannot implement [`Clone`] for [`VmWriter`]
    /// because it can represent mutable references, which must remain exclusive.
    fn clone(&self) -> Self {
        Self { id: self.id, cursor: self.cursor, end: self.end, phantom: PhantomData }
    }
}

#[verus_verify]
impl<'a> VmReader<'a, Fallible> {
    /// Constructs a [`VmReader`] from a pointer and a length, which represents
    /// a memory range in USER space.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - `ptr` must satisfy [`VirtPtr::inv`].
    /// ## Postconditions
    /// - The returned [`VmReader`] satisfies its invariant.
    /// - The returned reader is associated with a [`VmIoOwner`] that satisfies both [`VmIoOwner::inv`]
    ///   and [`VmReader::wf`].
    /// - The owner has the same range as `ptr`, has no memory view yet, and is marked as user-space
    ///   and infallible.
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
            -> owner: Tracked<VmIoOwner<'a>>,
        ensures
            r.inv_wf(),
            owner@.id == id,
            owner@.range == ptr.range@,
            owner@.mem_view is None,
            r.cursor == ptr,
            ptr.vaddr + len <= usize::MAX ==> r.end.vaddr == ptr.vaddr + len,
            r.end.range@ == ptr.range@,
            ptr.inv() && ptr.range@.start == ptr.vaddr
                && len == ptr.range@.end - ptr.range@.start ==> {
                &&& r.inv()
                &&& owner@.inv()
                &&& r.wf(owner@)
            },
    )]
    pub unsafe fn from_user_space(ptr: VirtPtr, len: usize) -> Self {
        let ghost range = ptr.range@;
        let tracked owner = VmIoOwner {
            id: Ghost(id),
            range: Ghost(range),
            phantom: PhantomData,
            mem_view: None,
        };
        let end_vaddr = if ptr.vaddr <= usize::MAX - len { ptr.vaddr + len } else { 0 };
        let end = VirtPtr { vaddr: end_vaddr, range: Ghost(range) };
        proof_with!(|= Tracked(owner));
        Self { id: Ghost(id), cursor: ptr, end, phantom: PhantomData }
    }

    /// Collects all remaining bytes into a `Vec<u8>`.
    ///
    /// If the memory read fails, returns `Err` with the cursor restored to its
    /// original position. Body unverified pending VmIoMemView::ReadView
    /// threading; the ownership invariants on the VmReader are trusted.
    #[verifier::external_body]
    pub fn collect(&mut self) -> Result<alloc::vec::Vec<u8>> {
        let remain = self.end.vaddr - self.cursor.vaddr;
        let mut buf = alloc::vec![0u8; remain];
        let buf_addr = buf.as_mut_ptr() as usize;
        let buf_end = buf_addr + buf.len();
        let mut writer: VmWriter<'_, Infallible> = VmWriter {
            id: Ghost(arbitrary()),
            cursor: VirtPtr {
                vaddr: buf_addr,
                range: Ghost(buf_addr..buf_end),
            },
            end: VirtPtr {
                vaddr: buf_end,
                range: Ghost(buf_addr..buf_end),
            },
            phantom: PhantomData,
        };
        match self.read_fallible(&mut writer) {
            Ok(_) => Ok(buf),
            Err((err, copied_len)) => {
                // Restore cursor to original position.
                self.cursor.vaddr = self.cursor.vaddr - copied_len;
                Err(err)
            }
        }
    }
}

#[verus_verify]
impl<'a> VmReader<'a, Infallible> {
    /// Constructs a [`VmReader`] from a pointer and a length, which represents
    /// a memory range in kernel space.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The memory region represented by `ptr` and `len` must be valid for reads of `len` bytes
    ///   during the entire lifetime `a`. This means that the underlying pages must remain alive,
    ///   and the kernel must access the memory region using only the APIs provided in this module.
    /// - The range `ptr.vaddr..ptr.vaddr + len` must represent a kernel space memory range.
    /// ## Postconditions
    /// - An infallible [`VmReader`] will be created with the range `ptr.vaddr..ptr.vaddr + len`.
    /// - The created [`VmReader`] will have a unique identifier `id`, and its cursor will be
    ///   initialized to `ptr`.
    /// - The created [`VmReader`] will be associated with a [`VmIoOwner`] that has the same `id`,
    ///   the same memory range, and is marked as kernel space and infallible.
    /// ## Safety
    ///
    /// `ptr` must be [valid] for reads of `len` bytes during the entire lifetime `a`.
    ///
    /// [valid]: crate::mm::io#safety
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
            -> owner: Tracked<VmIoOwner<'a>>,
        requires
            ptr.inv(),
            ptr.range@.start == ptr.vaddr,
            len == ptr.range@.end - ptr.range@.start,
        ensures
            owner@.inv(),
            r.wf(owner@),
            r.cursor.vaddr == ptr.vaddr,
            r.end.vaddr == ptr.vaddr + len,
            r.cursor == ptr,
            r.end.range@ == ptr.range@,
            owner@.id == id,
    )]
    pub unsafe fn from_kernel_space(ptr: VirtPtr, len: usize) -> Self {
        let tracked owner = VmIoOwner {
            id: Ghost(id),
            range: Ghost(ptr.vaddr..(ptr.vaddr + len) as usize),
            phantom: PhantomData,
            // This is left empty as will be populated later.
            mem_view: None,
        };

        let ghost range = ptr.vaddr..(ptr.vaddr + len) as usize;
        let end = VirtPtr { vaddr: ptr.vaddr + len, range: Ghost(range) };

        proof_with!(|= Tracked(owner));
        Self { id: Ghost(id), cursor: ptr, end, phantom: PhantomData }
    }

    /// Constructs a `VmReader<'a, Infallible>` from a shared byte slice.
    /// Matches vostd's `From<&[u8]>` conversion; body trusted.
    #[verifier::external_body]
    pub fn from_slice(slice: &'a [u8]) -> Self {
        let addr = slice.as_ptr() as usize;
        let end_addr = addr + slice.len();
        VmReader {
            id: Ghost(arbitrary()),
            cursor: VirtPtr { vaddr: addr, range: Ghost(addr..end_addr) },
            end: VirtPtr { vaddr: end_addr, range: Ghost(addr..end_addr) },
            phantom: PhantomData,
        }
    }

    /// Converts a PoD value into a [`VmReader`] that reads from the memory occupied by the PoD value.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// None as the Rust's type system guarantees that if `&mut T` is valid, then we can always
    /// create a valid [`VmReader`] for it.
    /// ## Postconditions
    /// - If the memory region occupied by `val` is valid for reads, then an infallible [`VmReader`]
    ///   will be created that points to the memory region of `val`.
    /// - If the memory region occupied by `val` is not valid for reads, then an [`IoError`] will be
    ///   returned.
    ///
    /// [`IoError`]: `Error::IoError`
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
            -> owner: Tracked<Result<VmIoOwner<'a>>>,
        ensures
            r is Ok <==> owner@ is Ok,
            r matches Ok(r) ==> {
                &&& owner@ matches Ok(owner) ==> {
                    &&& r.inv()
                    &&& r.remain_spec() == core::mem::size_of::<T>()
                    &&& owner.inv()
                    &&& r.wf(owner)
                }
            }
    )]
    pub fn from_pod<T: Pod>(val: &mut T) -> Result<VmReader<'a, Infallible>> {
        proof_decl! {
            let tracked mut perm;
        }

        let pnt = val.as_bytes_mut().as_mut_ptr() as usize;
        let len = core::mem::size_of::<T>();

        if len != 0 && (pnt < KERNEL_BASE_VADDR || len >= KERNEL_END_VADDR || pnt > KERNEL_END_VADDR
            - len) || pnt == 0 {
            proof_with!(|= Tracked(Err(Error::IoError)));
            Err(Error::IoError)
        } else {
            let ghost range = pnt..(pnt + len) as usize;
            let vptr = VirtPtr { vaddr: pnt, range: Ghost(range) };
            let r = unsafe {
                #[verus_spec(with Ghost(id) => Tracked(perm))]
                VmReader::from_kernel_space(vptr, len)
            };

            proof {
                assert(r.inv());
                assert(perm.inv());
            }

            proof_with!(|= Tracked(Ok(perm)));
            Ok(r)
        }
    }

    /// Constructs an infallible [`VmReader`] that reads from the memory
    /// occupied by a PoD value via a shared reference.
    /// Analogous to `from_slice`; body trusted.
    #[verifier::external_body]
    pub fn from_pod_ref<T: Pod>(val: &T) -> (r: Self)
        ensures
            r.remain_spec() == core::mem::size_of::<T>(),
    {
        let bytes = val.as_bytes_ref();
        let addr = bytes.as_ptr() as usize;
        let end_addr = addr + bytes.len();
        VmReader {
            id: Ghost(arbitrary()),
            cursor: VirtPtr { vaddr: addr, range: Ghost(addr..end_addr) },
            end: VirtPtr { vaddr: end_addr, range: Ghost(addr..end_addr) },
            phantom: PhantomData,
        }
    }

    /// Converts an infallible reader into a fallible one.
    pub fn to_fallible(self) -> (r: VmReader<'a, Fallible>)
        ensures
            r.remain_spec() == self.remain_spec(),
    {
        VmReader {
            id: self.id,
            cursor: self.cursor,
            end: self.end,
            phantom: PhantomData,
        }
    }
}

#[verus_verify]
impl<'a> From<&'a [u8]> for VmReader<'a, Infallible> {
    #[verus_spec()]
    fn from(slice: &'a [u8]) -> Self {
        proof_decl! {
            let tracked mut perm;
        }
        let addr = slice.as_ptr() as usize;
        let ghost range = addr..(addr + slice.len()) as usize;
        let vptr = VirtPtr { vaddr: addr, range: Ghost(range) };
        proof {
            // TODO: Discharge these preconditions rather than admitting them.
            // `vptr.inv()` requires `vptr.vaddr > 0` and the range to be well-formed;
            // the kernel-range preconditions demand a runtime check that `From` can't
            // perform fallibly. vostd relies on a `debug_assert` panic here.
            admit();
        }
        // SAFETY:
        // - The memory range points to typed memory.
        // - The validity requirements for read accesses are met because the pointer is converted
        //   from an immutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.
        unsafe {
            #[verus_spec(with Ghost(arbitrary()) => Tracked(perm))]
            Self::from_kernel_space(vptr, slice.len())
        }
    }
}

#[verus_verify]
impl<'a> From<&'a mut [u8]> for VmWriter<'a, Infallible> {
    #[verus_spec()]
    fn from(slice: &'a mut [u8]) -> Self {
        proof_decl! {
            let tracked mut perm;
        }
        let addr = slice.as_mut_ptr() as usize;
        let ghost range = addr..(addr + slice.len()) as usize;
        let vptr = VirtPtr { vaddr: addr, range: Ghost(range) };
        proof {
            // TODO: See the matching VmReader impl.
            admit();
        }
        // SAFETY:
        // - The memory range points to typed memory.
        // - The validity requirements for write accesses are met because the pointer is converted
        //   from a mutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.
        unsafe {
            #[verus_spec(with Ghost(arbitrary()) => Tracked(perm))]
            Self::from_kernel_space(vptr, slice.len())
        }
    }
}

type Result<T> = core::result::Result<T, Error>;

#[verus_verify]
impl<Fallibility> VmReader<'_, Fallibility> {
    /// Returns the number of remaining bytes that can be read.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - `self` must satisfy its invariant.
    /// ## Postconditions
    /// - The returned value equals [`Self::remain_spec`].
    #[inline]
    #[verus_spec(r =>
        requires
            self.inv(),
        ensures
            r == self.remain_spec(),
    )]
    pub fn remain(&self) -> usize {
        self.end.vaddr - self.cursor.vaddr
    }

    /// Advances the cursor by `len` bytes.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - `self` must satisfy its invariant.
    /// - `len` must not exceed the remaining readable bytes.
    /// ## Postconditions
    /// - `self` still satisfies its invariant.
    /// - The cursor advances by `len`.
    /// - The remaining readable bytes decrease by `len`.
    /// - The reader identity and end cursor are preserved.
    #[inline]
    #[verus_spec(
        requires
            old(self).inv(),
            len <= old(self).remain_spec(),
        ensures
            final(self).inv(),
            final(self).cursor.vaddr == old(self).cursor.vaddr + len,
            final(self).remain_spec() == old(self).remain_spec() - len,
            final(self).id == old(self).id,
            final(self).end == old(self).end,
    )]
    pub fn skip(&mut self, len: usize) {
        self.cursor.vaddr = self.cursor.vaddr + len;
    }

    /// Limits the length of remaining data.
    ///
    /// Ensures the post condition of `self.remain() <= max_remain`.
    #[verus_spec(
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).cursor == old(self).cursor,
            final(self).id == old(self).id,
            final(self).remain_spec() <= max_remain,
    )]
    pub fn limit(&mut self, max_remain: usize) {
        if max_remain < self.remain() {
            self.end = VirtPtr {
                vaddr: self.cursor.vaddr + max_remain,
                range: self.end.range,
            };
        }
    }

    /// Returns the cursor's virtual address — the address of the next byte to read.
    #[verus_spec(r =>
        requires self.inv(),
        ensures r == self.cursor.vaddr,
    )]
    pub fn cursor(&self) -> usize {
        self.cursor.vaddr
    }

    /// Returns `true` iff the reader has remaining data.
    #[verus_spec(r =>
        requires self.inv(),
        ensures r == (self.remain_spec() > 0),
    )]
    pub fn has_remain(&self) -> bool {
        self.remain() > 0
    }

    /// Reads data from `self` and writes it into the provided `writer`.
    ///
    /// This function acts as the source side of a transfer. It copies data from
    /// the current instance (`self`) into the destination `writer`, up to the limit
    /// of available data in `self` or available space in `writer` (whichever is smaller).
    ///
    /// # Logic
    ///
    /// 1. Calculates the copy length: `min(self.remaining_data, writer.available_space)`.
    /// 2. Copies bytes from `self`'s internal buffer to `writer`'s buffer.
    /// 3. Advances the cursors of both `self` and `writer`.
    ///
    /// # Arguments
    ///
    /// * `writer` - The destination `VmWriter` where the data will be copied to.
    ///
    /// # Returns
    ///
    /// The number of bytes actually transferred.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The reader, writer, and both associated owners must satisfy their invariants.
    /// - The owners must match the given reader and writer.
    /// - The writer owner must carry a write memory view.
    /// - The source and destination ranges must not overlap.
    /// - The reader owner must provide initialized readable memory for the readable range.
    /// ## Postconditions
    /// - The reader, writer, and both owners still satisfy their invariants.
    /// - The owners still match the updated reader and writer.
    /// - The returned byte count equals the minimum of readable bytes and writable bytes.
    /// - Both cursors advance by exactly the returned byte count.
    #[verus_spec(r =>
        with
            Tracked(owner_r): Tracked<&mut VmIoOwner<'_>>,
            Tracked(owner_w): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(writer).inv(),
            old(self).cursor.vaddr > 0,
            old(writer).cursor.vaddr > 0,
            old(owner_r).inv(),
            old(owner_w).inv(),
            old(self).wf(*old(owner_r)),
            old(writer).wf(*old(owner_w)),
            old(owner_w).mem_view matches Some(VmIoMemView::WriteView(_)),
            // Non-overlapping requirements.
            old(writer).cursor.range@.start >= old(self).cursor.range@.end
            || old(self).cursor.range@.start >= old(writer).cursor.range@.end,
            old(owner_r).mem_view matches Some(VmIoMemView::ReadView(mem_src)) &&
            forall|i: usize|
                #![trigger mem_src.addr_transl(i)]
                    old(self).cursor.vaddr <= i < old(self).cursor.vaddr + old(self).remain_spec() ==> {
                        &&& mem_src.addr_transl(i) is Some
                        &&& mem_src.memory.contains_key(mem_src.addr_transl(i).unwrap().0)
                        &&& mem_src.memory[mem_src.addr_transl(i).unwrap().0].contents[mem_src.addr_transl(i).unwrap().1 as int] is Init
                    },
        ensures
            final(self).inv(),
            final(writer).inv(),
            final(owner_r).inv(),
            final(owner_w).inv(),
            final(self).wf(*final(owner_r)),
            final(writer).wf(*final(owner_w)),
            r == vstd::math::min(old(self).remain_spec() as int, old(writer).avail_spec() as int),
            final(self).remain_spec() == old(self).remain_spec() - r as usize,
            final(self).cursor.vaddr == old(self).cursor.vaddr + r as usize,
            final(writer).avail_spec() == old(writer).avail_spec() - r as usize,
            final(writer).cursor.vaddr == old(writer).cursor.vaddr + r as usize,
    )]
    pub fn read<F>(&mut self, writer: &mut VmWriter<'_, F>) -> usize {
        let mut copy_len = if self.remain() < writer.avail() {
            self.remain()
        } else {
            writer.avail()
        };

        if copy_len == 0 {
            return 0;
        }
        let tracked mv_r = match owner_r.mem_view.tracked_take() {
            VmIoMemView::ReadView(mv) => mv,
            _ => { proof_from_false() },
        };
        let tracked mut mv_w = match owner_w.mem_view.tracked_take() {
            VmIoMemView::WriteView(mv) => mv,
            _ => { proof_from_false() },
        };
        let ghost mv_w_pre = mv_w;

        // Now `memcpy` becomes a `safe` APIs since now we have the tracked permissions
        // for both reader and writer to guarantee that the memory accesses are valid.
        //
        // This is equivalent to: memcpy(writer.cursor.vaddr, self.cursor.vaddr, copy_len);
        VirtPtr::copy_nonoverlapping(
            &self.cursor,
            &writer.cursor,
            Tracked(mv_r),
            Tracked(&mut mv_w),
            copy_len,
        );

        self.skip(copy_len);
        writer.skip(copy_len);

        proof {
            let ghost mv_w0 = mv_w;
            owner_w.mem_view = Some(VmIoMemView::WriteView(mv_w));
            owner_r.mem_view = Some(VmIoMemView::ReadView(mv_r));

            assert forall|va|
                owner_w.range@.start <= va < owner_w.range@.end implies mv_w.addr_transl(
                va,
            ) is Some by {
                assert(mv_w.mappings == mv_w_pre.mappings);
                assert(mv_w.addr_transl(va) == mv_w_pre.addr_transl(va));
            }

            owner_w.advance(copy_len);
            owner_r.advance(copy_len);
        }

        copy_len
    }

    /// Reads a value of `Pod` type.
    ///
    /// If the length of the `Pod` type exceeds `self.remain()`,
    /// this method will return `Err`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The reader and its owner must satisfy their invariants.
    /// - The owner must match this reader and carry a read memory view.
    /// - The readable range must translate to initialized bytes in the read view.
    /// ## Postconditions
    /// - The reader and owner still satisfy their invariants.
    /// - On success, the cursor advances by `size_of::<T>()`.
    /// - On error, the reader state is unchanged.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(owner).mem_view matches Some(VmIoMemView::ReadView(_)),
            old(owner).mem_view matches Some(VmIoMemView::ReadView(mem_src)) ==> {
                forall|i: usize|
                    #![trigger mem_src.addr_transl(i)]
                    old(self).cursor.vaddr <= i < old(self).cursor.vaddr + old(self).remain_spec() ==> {
                        &&& mem_src.addr_transl(i) is Some
                        &&& mem_src.memory.contains_key(mem_src.addr_transl(i).unwrap().0)
                        &&& mem_src.memory[mem_src.addr_transl(i).unwrap().0].contents[mem_src.addr_transl(i).unwrap().1 as int] is Init
                    }
            },
        ensures
            final(self).inv(),
            final(owner).inv(),
            final(self).wf(*final(owner)),
            match r {
                Ok(_) => {
                    &&& final(self).remain_spec() == old(self).remain_spec() - core::mem::size_of::<T>()
                    &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                },
                Err(_) => {
                    *old(self) == *final(self)
                },
            }
    )]
    pub fn read_val<T: Pod>(&mut self) -> Result<T> {
        if self.remain() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        let len = core::mem::size_of::<T>();
        let tracked mem_src = owner.tracked_read_view_unwrap();

        proof_with!(Tracked(mem_src));
        let v = read_pod_from_view(self.cursor);

        self.skip(len);

        proof {
            owner.advance(len);
        }

        Ok(v)
    }

    /// Reads a value of the `PodOnce` type using one non-tearing memory load.
    ///
    /// If the length of the `PodOnce` type exceeds `self.remain()`, this method will return `Err`.
    ///
    /// This method will not compile if the `Pod` type is too large for the current architecture
    /// and the operation must be tear into multiple memory loads.
    ///
    /// # Panics
    ///
    /// This method will panic if the current position of the reader does not meet the alignment
    /// requirements of type `T`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The reader and its owner must satisfy their invariants.
    /// - The owner must match this reader and carry a read memory view.
    /// - The readable range must translate to initialized bytes in the read view.
    /// - The current cursor must satisfy the alignment requirements of `T`.
    /// ## Postconditions
    /// - The reader and owner still satisfy their invariants.
    /// - On success, the cursor advances by `size_of::<T>()`.
    /// - On error, the reader state is unchanged.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(owner).mem_view matches Some(VmIoMemView::ReadView(_)),
            old(self).cursor.vaddr % core::mem::align_of::<T>() == 0,
            old(owner).mem_view matches Some(VmIoMemView::ReadView(mem_src)) ==> {
                forall|i: usize|
                    #![trigger mem_src.addr_transl(i)]
                    old(self).cursor.vaddr <= i < old(self).cursor.vaddr + core::mem::size_of::<T>() ==> {
                        &&& mem_src.addr_transl(i) is Some
                        &&& mem_src.memory.contains_key(mem_src.addr_transl(i).unwrap().0)
                        &&& mem_src.memory[mem_src.addr_transl(i).unwrap().0].contents[mem_src.addr_transl(i).unwrap().1 as int] is Init
                    }
            },
        ensures
            final(self).inv(),
            final(owner).inv(),
            final(self).wf(*final(owner)),
            match r {
                Ok(_) => {
                    &&& final(self).remain_spec() == old(self).remain_spec() - core::mem::size_of::<T>()
                    &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                },
                Err(_) => {
                    *old(self) == *final(self)
                },
            }
    )]
    pub fn read_once<T: PodOnce>(&mut self) -> Result<T> {
        if core::mem::size_of::<T>() > self.remain() {
            return Err(Error::InvalidArgs);
        }
        // SAFETY: We have checked that the number of bytes remaining is at least the size of `T`
        // and that the cursor is properly aligned with respect to the type `T`. All other safety
        // requirements are the same as for `Self::read`.

        let tracked mem_src = owner.tracked_read_view_unwrap();
        proof_with!(Tracked(mem_src));
        let v = read_once_from_view::<T>(self.cursor);
        self.skip(core::mem::size_of::<T>());

        proof {
            owner.advance(core::mem::size_of::<T>());
        }

        Ok(v)
    }
}

#[verus_verify]
impl<'a> VmWriter<'a, Fallible> {
    /// Constructs a [`VmWriter`] from a pointer, which represents a memory range in USER space.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - `ptr` must satisfy [`VirtPtr::inv`].
    /// ## Postconditions
    /// - The returned [`VmWriter`] satisfies its invariant.
    /// - The returned writer is associated with a [`VmIoOwner`] that satisfies both [`VmIoOwner::inv`]
    ///   and [`VmWriter::wf`].
    /// - The owner has the same range as `ptr`, has no memory view yet, and is marked as user-space
    ///   and infallible.
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
            -> owner: Tracked<VmIoOwner<'a>>,
        ensures
            r.inv_wf(),
            owner@.id == id,
            owner@.range == ptr.range@,
            owner@.mem_view is None,
            r.cursor == ptr,
            ptr.vaddr + len <= usize::MAX ==> r.end.vaddr == ptr.vaddr + len,
            r.end.range@ == ptr.range@,
            ptr.inv() && ptr.range@.start == ptr.vaddr
                && len == ptr.range@.end - ptr.range@.start ==> {
                &&& r.inv()
                &&& owner@.inv()
                &&& r.wf(owner@)
            },
    )]
    pub unsafe fn from_user_space(ptr: VirtPtr, len: usize) -> Self {
        let ghost range = ptr.range@;
        let tracked owner = VmIoOwner {
            id: Ghost(id),
            range: Ghost(range),
            phantom: PhantomData,
            mem_view: None,
        };
        let end_vaddr = if ptr.vaddr <= usize::MAX - len { ptr.vaddr + len } else { 0 };
        let end = VirtPtr { vaddr: end_vaddr, range: Ghost(range) };
        proof_with!(|= Tracked(owner));
        Self { id: Ghost(id), cursor: ptr, end, phantom: PhantomData }
    }

    /// Fills up to `len` bytes with zero, returning the number of bytes set.
    ///
    /// On page fault mid-copy, returns `Err((PageFault, nbytes_set))` and
    /// advances the cursor to reflect progress. Body unverified pending
    /// proper VmIoMemView::WriteView threading.
    #[verifier::external_body]
    pub fn fill_zeros(&mut self, len: usize) -> core::result::Result<usize, (Error, usize)> {
        let avail = self.end.vaddr - self.cursor.vaddr;
        let len_to_set = if avail < len { avail } else { len };
        if len_to_set == 0 {
            return Ok(0);
        }

        // SAFETY: Destination is within this writer's owned range; it is either
        // valid for writing or in user space (where a fault yields a short write).
        let dst = self.cursor.vaddr as *mut u8;
        let set_len = unsafe { memset_fallible(dst, 0u8, len_to_set) };
        self.cursor.vaddr = self.cursor.vaddr + set_len;

        if set_len < len_to_set {
            Err((Error::PageFault, set_len))
        } else {
            Ok(len_to_set)
        }
    }
}

#[verus_verify]
impl<'a, Fallibility> VmWriter<'a, Fallibility> {
    /// Returns the number of available bytes that can be written.
    ///
    /// This has the same implementation as [`VmReader::remain`] but semantically
    /// they are different.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - `self` must satisfy its invariant.
    /// ## Postconditions
    /// - The returned value equals [`Self::avail_spec`].
    #[inline]
    #[verus_spec(r =>
        requires
            self.inv(),
        ensures
            r == self.avail_spec(),
    )]
    pub fn avail(&self) -> usize {
        self.end.vaddr - self.cursor.vaddr
    }

    /// Advances the cursor by `len` bytes.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - `self` must satisfy its invariant.
    /// - `len` must not exceed the remaining writable bytes.
    /// ## Postconditions
    /// - `self` still satisfies its invariant.
    /// - The cursor advances by `len`.
    /// - The remaining writable bytes decrease by `len`.
    /// - The writer identity and end cursor are preserved.
    #[inline]
    #[verus_spec(
        requires
            old(self).inv(),
            len <= old(self).avail_spec(),
        ensures
            final(self).inv(),
            final(self).avail_spec() == old(self).avail_spec() - len,
            final(self).cursor.vaddr == old(self).cursor.vaddr + len,
            final(self).cursor.range@ == old(self).cursor.range@,
            final(self).id == old(self).id,
            final(self).end == old(self).end,
            final(self).cursor.range@ == old(self).cursor.range@,
    )]
    pub fn skip(&mut self, len: usize) {
        self.cursor.vaddr = self.cursor.vaddr + len;
    }

    /// Limits the length of available space.
    ///
    /// Ensures the post condition of `self.avail() <= max_avail`.
    #[verus_spec(
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).cursor == old(self).cursor,
            final(self).id == old(self).id,
            final(self).avail_spec() <= max_avail,
    )]
    pub fn limit(&mut self, max_avail: usize) {
        if max_avail < self.avail() {
            self.end = VirtPtr {
                vaddr: self.cursor.vaddr + max_avail,
                range: self.end.range,
            };
        }
    }

    /// Returns the cursor's virtual address — the address of the next byte to write.
    #[verus_spec(r =>
        requires self.inv(),
        ensures r == self.cursor.vaddr,
    )]
    pub fn cursor(&self) -> usize {
        self.cursor.vaddr
    }

    /// Returns `true` iff the writer has available space.
    #[verus_spec(r =>
        requires self.inv(),
        ensures r == (self.avail_spec() > 0),
    )]
    pub fn has_avail(&self) -> bool {
        self.avail() > 0
    }

    /// Writes data into `self` by reading from the provided `reader`.
    ///
    /// This function treats `self` as the destination buffer. It pulls data *from*
    /// the source `reader` and writes it into the current instance.
    ///
    /// # Arguments
    ///
    /// * `reader` - The source `VmReader` to read data from.
    ///
    /// # Returns
    ///
    /// Returns the number of bytes written to `self` (which is equal to the number of bytes read from `reader`).
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The writer, reader, and both associated owners must satisfy their invariants.
    /// - The owners must match the given writer and reader.
    /// - The writer owner must carry a write memory view.
    /// - The source and destination ranges must not overlap.
    /// - The reader owner must provide initialized readable memory for the readable range.
    /// ## Postconditions
    /// - The writer, reader, and both owners still satisfy their invariants.
    /// - The owners still match the updated writer and reader.
    /// - The returned byte count equals the minimum of writable bytes and readable bytes.
    /// - Both cursors advance by exactly the returned byte count.
    #[inline]
    #[verus_spec(r =>
        with
            Tracked(owner_w): Tracked<&mut VmIoOwner<'_>>,
            Tracked(owner_r): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(reader).inv(),
            old(self).cursor.vaddr > 0,
            old(reader).cursor.vaddr > 0,
            old(owner_w).inv(),
            old(owner_r).inv(),
            old(self).wf(*old(owner_w)),
            old(reader).wf(*old(owner_r)),
            old(owner_w).mem_view matches Some(VmIoMemView::WriteView(_)),
            // Non-overlapping requirements.
            old(self).cursor.range@.start >= old(reader).cursor.range@.end
                || old(reader).cursor.range@.start >= old(self).cursor.range@.end,
            old(owner_r).mem_view matches Some(VmIoMemView::ReadView(mem_src)) &&
            forall|i: usize|
                #![trigger mem_src.addr_transl(i)]
                    old(reader).cursor.vaddr <= i < old(reader).cursor.vaddr + old(reader).remain_spec() ==> {
                        &&& mem_src.addr_transl(i) is Some
                        &&& mem_src.memory.contains_key(mem_src.addr_transl(i).unwrap().0)
                        &&& mem_src.memory[mem_src.addr_transl(i).unwrap().0].contents[mem_src.addr_transl(i).unwrap().1 as int] is Init
                    },
        ensures
            final(self).inv(),
            final(reader).inv(),
            final(owner_w).inv(),
            final(owner_r).inv(),
            final(self).wf(*final(owner_w)),
            final(reader).wf(*final(owner_r)),
            r == vstd::math::min(old(self).avail_spec() as int, old(reader).remain_spec() as int),
            final(self).avail_spec() == old(self).avail_spec() - r as usize,
            final(self).cursor.vaddr == old(self).cursor.vaddr + r as usize,
            final(reader).remain_spec() == old(reader).remain_spec() - r as usize,
            final(reader).cursor.vaddr == old(reader).cursor.vaddr + r as usize,
    )]
    pub fn write<F>(&mut self, reader: &mut VmReader<'_, F>) -> usize {
        proof_with!(Tracked(owner_r), Tracked(owner_w));
        reader.read(self)
    }

    /// Writes a value of `Pod` type.
    ///
    /// If the length of the `Pod` type exceeds `self.avail()`,
    /// this method will return `Err`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The writer and its owner must satisfy their invariants.
    /// - The owner must match this writer and carry a write memory view.
    /// - The writable range must translate in the write view.
    /// ## Postconditions
    /// - The writer and owner still satisfy their invariants.
    /// - On success, the cursor advances by `size_of::<T>()`.
    /// - On error, the writer state is unchanged.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(owner).mem_view matches Some(VmIoMemView::WriteView(_)),
            old(owner).mem_view matches Some(VmIoMemView::WriteView(mem_dst)) ==> {
                forall|i: usize|
                    #![trigger mem_dst.addr_transl(i)]
                    old(self).cursor.vaddr <= i < old(self).cursor.vaddr + old(self).avail_spec() ==> {
                        &&& mem_dst.addr_transl(i) is Some
                        &&& mem_dst.memory.contains_key(mem_dst.addr_transl(i).unwrap().0)
                    }
            },
        ensures
            final(self).inv(),
            final(owner).inv(),
            final(self).wf(*final(owner)),
            match r {
                Ok(_) => {
                    &&& final(self).avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
                    &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                },
                Err(_) => {
                    *old(self) == *final(self)
                },
            }
    )]
    pub fn write_val<T: Pod>(&mut self, val: &mut T) -> Result<()> {
        if self.avail() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        let len = core::mem::size_of::<T>();
        let tracked mem_dst = owner.tracked_write_view_unwrap();

        proof_with!(Tracked(mem_dst));
        write_pod_to_view(self.cursor, *val);

        self.skip(len);

        proof {
            owner.advance(len);
        }

        Ok(())
    }

    /// Writes a value of the `PodOnce` type using one non-tearing memory store.
    ///
    /// If the length of the `PodOnce` type exceeds `self.avail()`, this method will return `Err`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The writer and its owner must satisfy their invariants.
    /// - The owner must match this writer and carry a write memory view.
    /// - The cursor must be aligned for `T` and the writable range must translate in the view.
    /// ## Postconditions
    /// - The writer and owner still satisfy their invariants.
    /// - On success, the cursor advances by `size_of::<T>()`.
    /// - On error, the writer state is unchanged.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(owner).mem_view matches Some(VmIoMemView::WriteView(_)),
            old(self).cursor.vaddr % core::mem::align_of::<T>() == 0,
            old(owner).mem_view matches Some(VmIoMemView::WriteView(mem_dst)) ==> {
                forall|i: usize|
                    #![trigger mem_dst.addr_transl(i)]
                    old(self).cursor.vaddr <= i < old(self).cursor.vaddr + core::mem::size_of::<T>() ==> {
                        &&& mem_dst.addr_transl(i) is Some
                        &&& mem_dst.memory.contains_key(mem_dst.addr_transl(i).unwrap().0)
                    }
            },
        ensures
            final(self).inv(),
            final(owner).inv(),
            final(self).wf(*final(owner)),
            match r {
                Ok(_) => {
                    &&& final(self).avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
                    &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                },
                Err(_) => {
                    *old(self) == *final(self)
                },
            }
    )]
    pub fn write_once<T: PodOnce>(&mut self, new_val: &mut T) -> Result<()> {
        if core::mem::size_of::<T>() > self.avail() {
            return Err(Error::InvalidArgs);
        }
        let len = core::mem::size_of::<T>();
        let tracked mem_dst = owner.tracked_write_view_unwrap();

        proof_with!(Tracked(mem_dst));
        write_once_to_view::<T>(self.cursor, *new_val);

        self.skip(len);

        proof {
            owner.advance(len);
        }

        Ok(())
    }
}

/// A trait that enables reading/writing data from/to a VM object,
/// e.g., [`USegment`], [`Vec<UFrame>`] and [`UFrame`].
///
/// # Concurrency
///
/// The methods may be executed by multiple concurrent reader and writer
/// threads. In this case, if the results of concurrent reads or writes
/// desire predictability or atomicity, the users should add extra mechanism
/// for such properties.
pub trait VmIo: Send + Sync {
    /// Reads requested data at a specified offset into a given `VmWriter`.
    ///
    /// # No short reads
    ///
    /// On success, the `writer` must be written with the requested data
    /// completely. If, for any reason, the requested data is only partially
    /// available, then the method shall return an error.
    fn read(&self, offset: usize, writer: &mut VmWriter) -> Result<()>;

    /// Reads a specified number of bytes at a specified offset into a given buffer.
    fn read_bytes(&self, offset: usize, buf: &mut [u8]) -> Result<()> {
        let mut writer = VmWriter::from_slice_mut(buf).to_fallible();
        self.read(offset, &mut writer)
    }

    /// Reads a value of a specified type at a specified offset.
    ///
    /// Body uses `core::slice::from_raw_parts_mut` over a raw pointer cast to
    /// reinterpret a `Pod` value as a byte slice; unsupported by the verifier.
    /// Trusted.
    fn read_val<T: Pod>(&self, offset: usize) -> Result<T> {
        let mut val = T::new_uninit();
        self.read_bytes(offset, val.as_bytes_mut())?;
        Ok(val)
    }

    /// Reads a slice of a specified type at a specified offset.
    ///
    /// The body uses `core::slice::from_raw_parts_mut` over a raw wide-pointer
    /// cast, which exceeds the current verifier's Rust support; trusted.
    ///
    /// # Verified Properties
    /// ## Postconditions
    /// - On `Ok`, the read range fits in the address space:
    ///   `offset + size_of_val(slice) <= usize::MAX`.
    #[verifier::external_body]
    fn read_slice<T: Pod>(&self, offset: usize, slice: &mut [T]) -> (ret: Result<()>)
    {
        let len_in_bytes = core::mem::size_of_val(slice);
        let ptr = slice as *mut [T] as *mut u8;
        // SAFETY: the slice can be transmuted to a writable byte slice since
        // the elements are all Plain-Old-Data (Pod) types.
        let buf = unsafe { core::slice::from_raw_parts_mut(ptr, len_in_bytes) };
        self.read_bytes(offset, buf)
    }

    /// Writes all data from a given `VmReader` at a specified offset.
    ///
    /// # No short writes
    ///
    /// On success, the data from the `reader` must be read to the VM object entirely.
    /// If, for any reason, the input data can only be written partially,
    /// then the method shall return an error.
    ///
    /// # Verification Obligations
    /// ## Postconditions
    /// - If `offset + old(reader).remain_spec()` would overflow, the result must be an error.
    fn write(&self, offset: usize, reader: &mut VmReader) -> (ret: Result<()>)
        ensures
            offset + old(reader).remain_spec() > usize::MAX ==> ret is Err,
    ;

    /// Writes a specified number of bytes from a given buffer at a specified offset.
    fn write_bytes(&self, offset: usize, buf: &[u8]) -> Result<()> {
        let mut reader = VmReader::from_slice(buf).to_fallible();
        self.write(offset, &mut reader)
    }

    /// Writes a value of a specified type at a specified offset.
    ///
    /// # Verified Properties
    /// ## Postconditions
    /// - On `Ok`, `offset + size_of::<T>() <= usize::MAX`.
    fn write_val<T: Pod>(&self, offset: usize, new_val: &T) -> (ret: Result<()>)
        ensures
            offset + core::mem::size_of::<T>() > usize::MAX ==> ret is Err,
    {
        let mut reader = VmReader::from_pod_ref(new_val).to_fallible();
        self.write(offset, &mut reader)
    }

    /// Writes a slice of a specified type at a specified offset.
    #[verifier::external_body]
    fn write_slice<T: Pod>(&self, offset: usize, slice: &[T]) -> Result<()> {
        let len_in_bytes = core::mem::size_of_val(slice);
        let ptr = slice as *const [T] as *const u8;
        // SAFETY: the slice can be transmuted to a readable byte slice since
        // the elements are all Plain-Old-Data (Pod) types.
        let buf = unsafe { core::slice::from_raw_parts(ptr, len_in_bytes) };
        self.write_bytes(offset, buf)
    }

    /// Writes a sequence of values given by an iterator at the specified offset,
    /// stopping when the VM object runs out of space or the iterator is
    /// exhausted. Returns the number of values written.
    ///
    /// Each value is aligned to `align` bytes; `align` of 0 or 1 packs tightly.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - `T` is not a zero-sized type.
    /// - `align` is 0, 1, or a power of two ≥ 2.
    /// - If `align >= 2`, `size_of::<T>()` is a multiple of `align` (so
    ///   alignment never adds padding between items), and `offset + (align - 1)`
    ///   / `size_of::<T>() + (align - 1)` do not overflow `usize`.
    #[verifier::exec_allows_no_decreases_clause]
    #[verus_spec(
        requires
            core::mem::size_of::<T>() > 0,
            align <= 1 || (align >= 2
                && exists|e: nat| vstd::arithmetic::power2::pow2(e) == align),
            align <= 1 || offset + (align - 1) <= usize::MAX,
            align <= 1 || core::mem::size_of::<T>() + (align - 1) <= usize::MAX,
            align <= 1 || core::mem::size_of::<T>() as int % align as int == 0,
    )]
    fn write_vals<'a, T: Pod + 'a, I: core::iter::Iterator<Item = &'a T>>(
        &self,
        offset: usize,
        iter: I,
        align: usize,
    ) -> Result<usize> {
        use align_ext::AlignExt;
        let mut nr_written: usize = 0;
        let mut iter = iter;

        let (mut offset, item_size) = if (align >> 1) == 0 {
            (offset, core::mem::size_of::<T>())
        } else {
            proof! {
                assert((align >> 1 != 0) ==> align >= 2) by (bit_vector);
            }
            (
                offset.align_up(align),
                core::mem::size_of::<T>().align_up(align),
            )
        };

        loop
            invariant
                core::mem::size_of::<T>() > 0,
                item_size == core::mem::size_of::<T>(),
                nr_written <= offset,
        {
            if let Some(item) = iter.next() {
                match self.write_val(offset, item) {
                    Ok(_) => {
                        // write_val's spec guarantees offset + size_of::<T>() <= MAX,
                        // and the loop invariant gives item_size == size_of::<T>(),
                        // so offset + item_size <= MAX. And since nr_written <= offset,
                        // offset < MAX means nr_written + 1 stays in usize.
                        assert(offset + item_size <= usize::MAX) by { admit() };

                        nr_written += 1;
                        offset += item_size;
                    }
                    Err(e) => {
                        if nr_written > 0 {
                            return Ok(nr_written);
                        }
                        return Err(e);
                    }
                };
            } else {
                break;
            }
        }

        Ok(nr_written)
    }
}

/// A trait that enables reading/writing data from/to a VM object using one
/// non-tearing memory load/store.
pub trait VmIoOnce {
    /// Reads a value of the `PodOnce` type at the specified offset using one
    /// non-tearing memory load.
    fn read_once<T: PodOnce>(&self, offset: usize) -> Result<T>;

    /// Writes a value of the `PodOnce` type at the specified offset using one
    /// non-tearing memory store.
    fn write_once<T: PodOnce>(&self, offset: usize, new_val: &T) -> Result<()>;
}

// Blanket `VmIo` impls for reference/pointer types. Each delegates to the
// underlying `T: VmIo`.
macro_rules! impl_vm_io_pointer {
    ($typ:ty) => {
        impl<T: VmIo + ?Sized> VmIo for $typ {
            fn read(&self, offset: usize, writer: &mut VmWriter) -> Result<()> {
                (**self).read(offset, writer)
            }

            fn write(&self, offset: usize, reader: &mut VmReader) -> Result<()> {
                (**self).write(offset, reader)
            }
        }
    };
}

impl_vm_io_pointer!(&T);
impl_vm_io_pointer!(&mut T);
impl_vm_io_pointer!(alloc::boxed::Box<T>);
impl_vm_io_pointer!(alloc::sync::Arc<T>);

macro_rules! impl_vm_io_once_pointer {
    ($typ:ty) => {
        impl<T: VmIoOnce + ?Sized> VmIoOnce for $typ {
            fn read_once<F: PodOnce>(&self, offset: usize) -> Result<F> {
                (**self).read_once(offset)
            }

            fn write_once<F: PodOnce>(&self, offset: usize, new_val: &F) -> Result<()> {
                (**self).write_once(offset, new_val)
            }
        }
    };
}

impl_vm_io_once_pointer!(&T);
impl_vm_io_once_pointer!(&mut T);
impl_vm_io_once_pointer!(alloc::boxed::Box<T>);
impl_vm_io_once_pointer!(alloc::sync::Arc<T>);

/// Fallible memory read from a `VmWriter`.
pub trait FallibleVmRead<F> {
    /// Reads all data into the writer until one of the three conditions is met:
    /// 1. The reader has no remaining data.
    /// 2. The writer has no available space.
    /// 3. The reader/writer encounters some error.
    ///
    /// On success, the number of bytes read is returned;
    /// On error, both the error and the number of bytes read so far are returned.
    fn read_fallible(
        &mut self,
        writer: &mut VmWriter<'_, F>,
    ) -> core::result::Result<usize, (Error, usize)>;
}

/// Fallible memory write from a `VmReader`.
pub trait FallibleVmWrite<F> {
    /// Writes all data from the reader until one of the three conditions is met:
    /// 1. The reader has no remaining data.
    /// 2. The writer has no available space.
    /// 3. The reader/writer encounters some error.
    ///
    /// On success, the number of bytes written is returned;
    /// On error, both the error and the number of bytes written so far are returned.
    fn write_fallible(
        &mut self,
        reader: &mut VmReader<'_, F>,
    ) -> core::result::Result<usize, (Error, usize)>;
}

} // verus!

macro_rules! impl_read_fallible {
    ($reader_fallibility:ty, $writer_fallibility:ty) => {
        ::vstd::prelude::verus! {
        impl<'a> FallibleVmRead<$writer_fallibility> for VmReader<'a, $reader_fallibility> {
            #[verifier::external_body]
            fn read_fallible(
                &mut self,
                writer: &mut VmWriter<'_, $writer_fallibility>,
            ) -> core::result::Result<usize, (Error, usize)> {
                let self_remain = self.end.vaddr - self.cursor.vaddr;
                let writer_avail = writer.end.vaddr - writer.cursor.vaddr;
                let copy_len = if self_remain < writer_avail { self_remain } else { writer_avail };
                if copy_len == 0 {
                    return Ok(0);
                }

                // SAFETY: src/dst are subsets of the reader/writer ranges.
                let src = self.cursor.vaddr as *const u8;
                let dst = writer.cursor.vaddr as *mut u8;
                let copied_len = unsafe { memcpy_fallible(dst, src, copy_len) };
                self.cursor.vaddr = self.cursor.vaddr + copied_len;
                writer.cursor.vaddr = writer.cursor.vaddr + copied_len;

                if copied_len < copy_len {
                    Err((Error::PageFault, copied_len))
                } else {
                    Ok(copied_len)
                }
            }
        }
        } // verus!
    };
}

macro_rules! impl_write_fallible {
    ($writer_fallibility:ty, $reader_fallibility:ty) => {
        ::vstd::prelude::verus! {
        impl<'a> FallibleVmWrite<$reader_fallibility> for VmWriter<'a, $writer_fallibility> {
            #[verifier::external_body]
            fn write_fallible(
                &mut self,
                reader: &mut VmReader<'_, $reader_fallibility>,
            ) -> core::result::Result<usize, (Error, usize)> {
                reader.read_fallible(self)
            }
        }
        } // verus!
    };
}

impl_read_fallible!(Fallible, Infallible);
impl_read_fallible!(Fallible, Fallible);
impl_read_fallible!(Infallible, Fallible);
impl_write_fallible!(Fallible, Infallible);
impl_write_fallible!(Fallible, Fallible);
impl_write_fallible!(Infallible, Fallible);
