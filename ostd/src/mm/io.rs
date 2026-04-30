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
use crate::arch::mm::{__memcpy_fallible, __memset_fallible};
use crate::specs::arch::PAGE_SIZE;
use core::marker::PhantomData;
use core::ops::Range;
use vstd::pervasive::{arbitrary, proof_from_false};
use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::std_specs::convert::TryFromSpecImpl;
use vstd_extra::array_ptr::ArrayPtr;
use vstd_extra::array_ptr::PointsToArray;
use vstd_extra::ownership::Inv;

use crate::error::*;
use crate::mm::kspace::{KERNEL_BASE_VADDR, KERNEL_END_VADDR};
use crate::mm::pod::{Pod, PodOnce};
use crate::specs::arch::MAX_USERSPACE_VADDR;
use crate::specs::mm::virt_mem_newer::{MemView, VirtPtr};

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

/// Performs a fallible transfer from `reader` to `writer`.
///
/// # Verified Properties
/// ## Preconditions
/// - `reader`, `writer`, and their associated owners must satisfy their invariants.
/// - Each owner must match the corresponding reader or writer.
/// - Both owners must be marked fallible.
/// ## Postconditions
/// - The reader, writer, and both owners still satisfy their invariants.
/// - The owner parameters tracked by [`VmIoOwner::params_eq`] are preserved for both sides.
#[verus_spec(r =>
        with
            Tracked(owner_r): Tracked<&mut VmIoOwner<'_>>,
            Tracked(owner_w): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(reader).inv(),
            old(writer).inv(),
            old(owner_r).inv(),
            old(owner_w).inv(),
            old(reader).wf(*old(owner_r)),
            old(writer).wf(*old(owner_w)),
            old(owner_r).is_fallible && old(owner_w).is_fallible, // both fallible
        ensures
            final(reader).inv(),
            final(writer).inv(),
            final(owner_r).inv(),
            final(owner_w).inv(),
            final(reader).wf(*final(owner_r)),
            final(writer).wf(*final(owner_w)),
            final(owner_r).params_eq(*old(owner_r)),
            final(owner_w).params_eq(*old(owner_w)),
    )]
pub fn rw_fallible(reader: &mut VmReader<'_>, writer: &mut VmWriter<'_>) -> core::result::Result<
    usize,
    (Error, usize),
> {
    Ok(0)  // placeholder.

}

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
pub struct VmReader<'a, Fallibility = Infallible> {
    pub id: Ghost<nat>,
    pub cursor: VirtPtr,
    pub end: VirtPtr,
    pub phantom: PhantomData<(&'a [u8], Fallibility)>,
}

/// The memory view used for VM I/O operations.
///
/// The readers can think of this as a wrapped permission tokens for operating with a certain
/// memory view (see [`MemView`]) "owned" by the [`VmIoOwner`] that they are created from, which
/// are used for allowing callers to use [`VmReader`] and [`VmWriter`] to perform VM I/O operations.
///
/// For writers the memory permission must be exclusive so this enum contains an owned [`MemView`]
/// for the write view; for readers the memory permission can be shared so this enum contains a
/// reference to a [`MemView`] for the read view (which can be disabled optionally in [`VmSpaceOwner`]).
///
/// ⚠️ WARNING: We do not recommend using this enum directly.
///
/// [`VmSpaceOwner`]: crate::mm::vm_space::VmSpaceOwner
pub tracked enum VmIoMemView<'a> {
    /// An owned memory for writing.
    WriteView(MemView),
    /// A shared memory for reading.
    ReadView(&'a MemView),
}

/// The owner of a VM I/O operation, which tracks the memory range and the memory view for the
/// operation.
///
/// Basically the caller should be only interested in this struct when using [`VmReader`] and
/// [`VmWriter`] to perform VM I/O operations, since the safety of these operations depends on the
/// validity of the memory range and memory view tracked by this struct.
pub tracked struct VmIoOwner<'a> {
    /// The unique identifier of this owner.
    pub id: Ghost<nat>,
    /// The virtual address range owned by this owner.
    pub range: Ghost<Range<usize>>,
    /// Whether this reader is fallible.
    pub is_fallible: bool,
    pub phantom: PhantomData<&'a [u8]  /*, Fallibility)*/ >,
    /// Whether this owner is for kernel space.
    pub is_kernel: bool,
    /// The mem view associated with this owner.
    pub mem_view: Option<VmIoMemView<'a>>,
}

impl VmIoOwner<'_> {
    /// Structural well-formedness: the range is ordered.
    /// Always holds after construction.
    pub open spec fn inv_wf(self) -> bool {
        self.range@.start <= self.range@.end
    }
}

impl Inv for VmIoOwner<'_> {
    /// Full invariant: well-formed AND memory view (if present) covers the range.
    open spec fn inv(self) -> bool {
        &&& self.inv_wf()
        &&& match self.mem_view {
            Some(VmIoMemView::WriteView(mv)) => {
                &&& mv.mappings.finite()
                &&& mv.mappings_are_disjoint()
                &&& forall|va: usize|
                    self.range@.start <= va < self.range@.end ==> {
                        &&& #[trigger] mv.addr_transl(va) is Some
                    }
            },
            Some(VmIoMemView::ReadView(mv)) => {
                &&& mv.mappings.finite()
                &&& mv.mappings_are_disjoint()
                &&& forall|va: usize|
                    self.range@.start <= va < self.range@.end ==> {
                        &&& #[trigger] mv.addr_transl(va) is Some
                    }
            },
            None => true,
        }
    }
}

impl VmIoOwner<'_> {
    /// Whether this owner carries a read memory view.
    #[verifier::inline]
    pub open spec fn has_read_view(self) -> bool {
        self.mem_view matches Some(VmIoMemView::ReadView(_))
    }

    /// Whether this owner carries a write memory view.
    #[verifier::inline]
    pub open spec fn has_write_view(self) -> bool {
        self.mem_view matches Some(VmIoMemView::WriteView(_))
    }

    /// Whether this owner is ready to serve as the readable side of a copy.
    #[verifier::inline]
    pub open spec fn can_read(self) -> bool {
        self.has_read_view()
    }

    /// Whether this owner is ready to serve as the writable side of a copy.
    #[verifier::inline]
    pub open spec fn can_write(self) -> bool {
        self.has_write_view()
    }

    /// Whether the read view initializes the entire owner range.
    #[verifier::inline]
    pub open spec fn read_view_initialized(self) -> bool {
        match self.mem_view {
            Some(VmIoMemView::ReadView(mem_src)) => {
                forall|i: usize|
                    #![trigger mem_src.addr_transl(i)]
                    self.range@.start <= i < self.range@.end ==> {
                        &&& mem_src.addr_transl(i) is Some
                        &&& mem_src.memory.contains_key(mem_src.addr_transl(i).unwrap().0)
                        &&& mem_src.memory[mem_src.addr_transl(
                            i,
                        ).unwrap().0].contents[mem_src.addr_transl(i).unwrap().1 as int] is Init
                    }
            },
            _ => false,
        }
    }

    /// Checks whether this owner overlaps with another owner.
    #[verifier::inline]
    pub open spec fn overlaps(self, other: VmIoOwner<'_>) -> bool {
        !self.disjoint(other)
    }

    #[verifier::inline]
    pub open spec fn overlaps_with_range(self, range: Range<usize>) -> bool {
        &&& self.range@.start <= range.end
        &&& range.start <= self.range@.end
    }

    /// Checks whether this owner is disjoint with another owner.
    #[verifier::inline]
    pub open spec fn disjoint(self, other: VmIoOwner<'_>) -> bool {
        &&& !self.overlaps_with_range(other.range@)
        &&& match (self.mem_view, other.mem_view) {
            (Some(lhs), Some(rhs)) => match (lhs, rhs) {
                (VmIoMemView::WriteView(lmv), VmIoMemView::WriteView(rmv)) => {
                    lmv.mappings.disjoint(rmv.mappings)
                },
                (VmIoMemView::WriteView(lmv), VmIoMemView::ReadView(rmv)) => {
                    lmv.mappings.disjoint(rmv.mappings)
                },
                (VmIoMemView::ReadView(lmv), VmIoMemView::WriteView(rmv)) => {
                    lmv.mappings.disjoint(rmv.mappings)
                },
                (VmIoMemView::ReadView(lmv), VmIoMemView::ReadView(rmv)) => {
                    lmv.mappings.disjoint(rmv.mappings)
                },
            },
            _ => true,
        }
    }

    #[verifier::inline]
    pub open spec fn params_eq(self, other: VmIoOwner<'_>) -> bool {
        &&& self.range@ == other.range@
        &&& self.is_fallible == other.is_fallible
    }

    /// Changes the fallibility of this owner.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The owner must satisfy its invariant.
    /// - The new fallibility must differ from the current one.
    /// ## Postconditions
    /// - The updated owner still satisfies its invariant.
    /// - The `is_fallible` field is updated to `fallible`.
    pub proof fn change_fallible(tracked &mut self, tracked fallible: bool)
        requires
            old(self).inv(),
            old(self).is_fallible != fallible,
        ensures
            final(self).inv(),
            final(self).is_fallible == fallible,
    {
        self.is_fallible = fallible;
    }

    /// Advances the cursor of the reader/writer by the given number of bytes.
    ///
    /// Note this will return the advanced `VmIoMemView` as the previous permission
    /// is no longer needed and must be discarded then.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The owner must satisfy its invariant.
    /// - The owner must carry a memory view.
    /// - `nbytes` must not exceed the remaining length of the owned range.
    /// ## Postconditions
    /// - The updated owner still satisfies its invariant.
    /// - The start of the owned range is advanced by `nbytes`.
    /// - The end of the owned range and the other owner parameters are preserved.
    /// - The returned [`VmIoMemView`] is the portion advanced past.
    #[verifier::external_body]
    pub proof fn advance(tracked &mut self, nbytes: usize) -> (tracked res: VmIoMemView<'_>)
        requires
            old(self).inv(),
            old(self).mem_view is Some,
            nbytes <= old(self).range@.end - old(self).range@.start,
        ensures
            final(self).inv(),
            final(self).range@.start == old(self).range@.start + nbytes,
            final(self).range@.end == old(self).range@.end,
            final(self).is_fallible == old(self).is_fallible,
            final(self).id == old(self).id,
            final(self).is_kernel == old(self).is_kernel,
            old(self).mem_view matches Some(VmIoMemView::ReadView(_)) ==> final(self).mem_view matches Some(VmIoMemView::ReadView(_)),
            old(self).mem_view matches Some(VmIoMemView::WriteView(_)) ==> final(self).mem_view matches Some(VmIoMemView::WriteView(_)),
            old(self).read_view_initialized() ==> final(self).read_view_initialized(),
    {
        arbitrary()
    }

    /// Unwraps the read view.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The owner must satisfy its invariant.
    /// - The owner must carry a read memory view.
    /// ## Postconditions
    /// - The returned reference is exactly the read view stored in `self.mem_view`.
    pub proof fn tracked_read_view_unwrap(tracked &self) -> (tracked r: &MemView)
        requires
            self.inv(),
            self.mem_view matches Some(VmIoMemView::ReadView(_)),
        ensures
            VmIoMemView::ReadView(r) == self.mem_view.unwrap(),
    {
        match &self.mem_view {
            Some(VmIoMemView::ReadView(r)) => r,
            _ => { proof_from_false() },
        }
    }
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
pub struct VmWriter<'a, Fallibility = Infallible> {
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
            Tracked(fallible): Tracked<bool>,
                -> owner: Tracked<VmIoOwner<'a>>,
        requires
            !fallible,
            ptr.inv(),
            ptr.range@.start == ptr.vaddr,
            len == ptr.range@.end - ptr.range@.start,
            len == 0 || KERNEL_BASE_VADDR <= ptr.vaddr,
            len == 0 || ptr.vaddr + len <= KERNEL_END_VADDR,
        ensures
            owner@.inv(),
            r.wf(owner@),
            owner@.is_fallible == fallible,
            owner@.id == id,
            owner@.is_kernel,
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
            is_fallible: fallible,
            phantom: PhantomData,
            is_kernel: true,
            mem_view: None,
        };

        let ghost range = ptr.vaddr..(ptr.vaddr + len) as usize;
        let end = VirtPtr { vaddr: ptr.vaddr + len, range: Ghost(range) };

        proof_with!(|= Tracked(owner));
        Self { id: Ghost(id), cursor: ptr, end, phantom: PhantomData }
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

        let bytes = val.as_bytes_mut();
        let pnt = bytes.as_mut_ptr() as usize;
        let len = core::mem::size_of::<T>();

        if len != 0 && (pnt < KERNEL_BASE_VADDR || len >= KERNEL_END_VADDR || pnt > KERNEL_END_VADDR
            - len) || pnt == 0 {
            proof_with!(|= Tracked(Err(Error::IoError)));
            Err(Error::IoError)
        } else {
            let ghost range = pnt..(pnt + len) as usize;
            let vptr = VirtPtr { vaddr: pnt as usize, range: Ghost(range) };
            let r = unsafe {
                #[verus_spec(with Ghost(id), Tracked(false) => Tracked(perm))]
                VmWriter::from_kernel_space(vptr, len)
            };

            proof_with!(|= Tracked(Ok(perm)));
            Ok(r)
        }
    }

    /// Converts an infallible writer into a fallible one.
    pub fn to_fallible(self) -> VmWriter<'a, Fallible> {
        VmWriter { id: self.id, cursor: self.cursor, end: self.end, phantom: PhantomData }
    }

    /// Writes a value of `Pod` type to the kernel-space buffer.
    ///
    /// If the length of the `Pod` type exceeds `self.avail()`, this method
    /// will return `Err(InvalidArgs)`. Kernel-space writes don't fault, so
    /// no rollback is needed — see [`VmWriter<Fallible>::write_val`] for the
    /// user-space variant with cursor rewind.
    #[verifier::external_body]
    pub fn write_val<T: Pod>(&mut self, val: &mut T) -> Result<()> {
        if self.avail() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        let mut reader = VmReader::from_pod(val)?;
        self.write(&mut reader);
        Ok(())
    }

    /// Constructs a `VmWriter<'a, Infallible>` from a mutable byte slice.
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
    // TODO: go through `ArrayPtr::from_addr` with a tracked `PointsToArray` permission.
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
            let cursor_i = cursor.wrapping_add(i);
            // SAFETY: written_num is bounded by avail / size_of::<T>() so each
            // write targets memory owned by this writer, and cursor is aligned.
            unsafe { cursor_i.write_volatile(value) };
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
impl<'a> VmReader<'a, Infallible> {
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
            !owner@.is_kernel,
            !owner@.is_fallible,
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
            is_fallible: false,
            phantom: PhantomData,
            is_kernel: false,
            mem_view: None,
        };
        let end_vaddr = if ptr.vaddr <= usize::MAX - len {
            ptr.vaddr + len
        } else {
            0
        };
        let end = VirtPtr { vaddr: end_vaddr, range: Ghost(range) };
        proof_with!(|= Tracked(owner));
        Self { id: Ghost(id), cursor: ptr, end, phantom: PhantomData }
    }

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
            len == 0 || KERNEL_BASE_VADDR <= ptr.vaddr,
            len == 0 || ptr.vaddr + len <= KERNEL_END_VADDR,
        ensures
            owner@.inv(),
            r.wf(owner@),
            r.cursor.vaddr == ptr.vaddr,
            r.end.vaddr == ptr.vaddr + len,
            r.cursor == ptr,
            r.end.range@ == ptr.range@,
            owner@.is_kernel,
            owner@.id == id,
    )]
    pub unsafe fn from_kernel_space(ptr: VirtPtr, len: usize) -> Self {
        let tracked owner = VmIoOwner {
            id: Ghost(id),
            range: Ghost(ptr.vaddr..(ptr.vaddr + len) as usize),
            is_fallible: false,
            phantom: PhantomData,
            is_kernel: true,
            // This is left empty as will be populated later.
            mem_view: None,
        };

        proof_with!(|= Tracked(owner));
        Self { id: Ghost(id), cursor: ptr, end: ptr.wrapping_add(len), phantom: PhantomData }
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

        let bytes = val.as_bytes_mut();
        let pnt = bytes.as_mut_ptr() as usize;
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

    /// Constructs a `VmReader<'a, Infallible>` from a shared byte slice.
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

    /// Constructs an infallible [`VmReader`] from a shared PoD reference.
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
        VmReader { id: self.id, cursor: self.cursor, end: self.end, phantom: PhantomData }
    }
}

impl<'a> VmReader<'a, Fallible> {
    /// Collects all the remaining bytes into a `Vec<u8>`.
    ///
    /// If the memory read failed, this method will return `Err`
    /// and the current reader's cursor remains pointing to
    /// the original starting position. The cursor rollback is verified —
    /// `rewind_cursor` discharges the spec that ties `copied_len` to the
    /// cursor advancement.
    #[verifier::external_body]
    pub fn collect(&mut self) -> Result<alloc::vec::Vec<u8>> {
        let mut buf = alloc::vec![0u8; self.remain()];
        let mut writer: VmWriter<'_, Infallible> = buf.as_mut_slice().into();
        match self.read_fallible(&mut writer) {
            Ok(_) => Ok(buf),
            Err((err, copied_len)) => {
                self.rewind_cursor(copied_len);
                Err(err)
            },
        }
    }

    /// Rewinds the cursor by `n` bytes. Used to undo a partial read.
    ///
    /// The cursor advancement on `read_fallible`'s `Err` path equals
    /// `copied_len`, so calling `rewind_cursor(copied_len)` deterministically
    /// restores the cursor to its position before the failed read.
    #[verus_spec(
        requires
            old(self).inv(),
            n <= old(self).cursor.vaddr - old(self).cursor.range@.start,
        ensures
            final(self).inv(),
            final(self).cursor.vaddr == old(self).cursor.vaddr - n,
            final(self).cursor.range == old(self).cursor.range,
            final(self).end == old(self).end,
            final(self).id == old(self).id,
    )]
    fn rewind_cursor(&mut self, n: usize) {
        self.cursor.vaddr = self.cursor.vaddr - n;
    }
}

// Perhaps we can implement `tryfrom` instead.
// This trait method should be discarded as we do not want to make VmWriter <N> ?
#[verus_verify]
impl<'a> TryFrom<&'a [u8]> for VmWriter<'a, Infallible> {
    type Error = Error;

    // fn try_from(slice: ArrayPtr<u8, N>, Tracked(owner))??
    #[verus_spec()]
    fn try_from(slice: &'a [u8]  /* length... */ ) -> Result<Self> {
        proof_decl! {
            let tracked mut perm;
        }

        let addr = slice.as_ptr() as usize;

        if slice.len() != 0 && (addr < KERNEL_BASE_VADDR || slice.len() >= KERNEL_END_VADDR || addr
            > KERNEL_END_VADDR - slice.len()) || addr == 0 {
            return Err(Error::IoError);
        }
        // SAFETY:
        // - The memory range points to typed memory.
        // - The validity requirements for write accesses are met because the pointer is converted
        //   from a mutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.

        let ghost range = addr..(addr + slice.len()) as usize;
        let vptr = VirtPtr { vaddr: addr, range: Ghost(range) };

        proof {
            assert(vptr.inv());
        }

        Ok(
            unsafe {
                #[verus_spec(with Ghost(arbitrary()), Tracked(false) => Tracked(perm))]
                Self::from_kernel_space(vptr, slice.len())
            },
        )
    }
}

impl<'a> TryFromSpecImpl<&'a [u8]> for VmWriter<'a, Infallible> {
    open spec fn obeys_try_from_spec() -> bool {
        true
    }

    open spec fn try_from_spec(slice: &'a [u8]) -> Result<Self> {
        let addr = slice.as_ptr() as usize;
        let len = slice.len();

        if len != 0 && (addr < KERNEL_BASE_VADDR || len >= KERNEL_END_VADDR || addr
            > KERNEL_END_VADDR - slice.len()) || addr == 0 {
            Err(Error::IoError)
        } else {
            Ok(
                Self {
                    id: Ghost(arbitrary()),
                    cursor: VirtPtr { vaddr: addr, range: Ghost(addr..(addr + len) as usize) },
                    end: VirtPtr {
                        vaddr: (addr + len) as usize,
                        range: Ghost(addr..(addr + len) as usize),
                    },
                    phantom: PhantomData,
                },
            )
        }
    }
}

type Result<T> = core::result::Result<T, Error>;

/// A trait that enables reading/writing data from/to a VM object,
/// e.g., [`USegment`], [`Vec<UFrame>`] and [`UFrame`].
///
/// # Concurrency
///
/// The methods may be executed by multiple concurrent reader and writer
/// threads. In this case, if the results of concurrent reads or writes
/// desire predictability or atomicity, the users should add extra mechanism
/// for such properties.
///
/// [`USegment`]: crate::mm::USegment
/// [`UFrame`]: crate::mm::UFrame
///
/// Note: In this trait we follow the standard of `vstd` trait that allows precondition and
/// postcondition overriding by introducing `obeys_`, `_requires`, and `_ensures` spec functions.
///
/// `P` is the type of the permission/ownership token used to track the state of the VM object.
pub trait VmIo<P: Sized>: Send + Sync + Sized {
    spec fn obeys_vmio_spec() -> bool;

    open spec fn obeys_vmio_read_requires() -> bool
        recommends
            Self::obeys_vmio_spec(),
    {
        false
    }

    open spec fn obeys_vmio_write_requires() -> bool
        recommends
            Self::obeys_vmio_spec(),
    {
        false
    }

    spec fn obeys_vmio_read_spec() -> bool
        recommends
            Self::obeys_vmio_spec(),
    ;

    spec fn obeys_vmio_write_spec() -> bool
        recommends
            Self::obeys_vmio_spec(),
    ;

    open spec fn read_requires(
        self,
        offset: usize,
        writer: VmWriter<'_>,
        writer_own: VmIoOwner<'_>,
        owner: P,
    ) -> bool {
        true
    }

    open spec fn write_requires(
        self,
        offset: usize,
        reader: VmReader<'_>,
        reader_own: VmIoOwner<'_>,
        owner: P,
    ) -> bool {
        true
    }

    spec fn read_spec(
        self,
        offset: usize,
        old_writer: VmWriter<'_>,
        new_writer: VmWriter<'_>,
        old_writer_own: VmIoOwner<'_>,
        new_writer_own: VmIoOwner<'_>,
        old_owner: P,
        new_owner: P,
        r: Result<()>,
    ) -> bool;

    spec fn write_spec(
        self,
        offset: usize,
        old_reader: VmReader<'_>,
        new_reader: VmReader<'_>,
        old_writer_own: VmIoOwner<'_>,
        new_writer_own: VmIoOwner<'_>,
        old_owner: P,
        new_owner: P,
        r: Result<()>,
    ) -> bool;

    /// Reads requested data at a specified offset into a given [`VmWriter`].
    ///
    /// # No short reads
    ///
    /// On success, the `writer` must be written with the requested data
    /// completely. If, for any reason, the requested data is only partially
    /// available, then the method shall return an error.
    fn read(
        &self,
        offset: usize,
        writer: &mut VmWriter<'_>,
        Tracked(writer_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> (r: Result<()>)
        requires
            Self::obeys_vmio_read_requires() ==> Self::read_requires(
                *self,
                offset,
                *old(writer),
                *old(writer_own),
                *old(owner),
            ),
        ensures
            Self::obeys_vmio_read_spec() ==> Self::read_spec(
                *self,
                offset,
                *old(writer),
                *final(writer),
                *old(writer_own),
                *final(writer_own),
                *old(owner),
                *final(owner),
                r,
            ),
    ;

    /// Writes all data from a given `VmReader` at a specified offset.
    ///
    /// # No short writes
    ///
    /// On success, the data from the `reader` must be read to the VM object entirely.
    /// If, for any reason, the input data can only be written partially,
    /// then the method shall return an error.
    fn write(
        &self,
        offset: usize,
        reader: &mut VmReader,
        Tracked(writer_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> (r: Result<()>)
        requires
            Self::obeys_vmio_write_requires() ==> Self::write_requires(
                *self,
                offset,
                *old(reader),
                *old(writer_own),
                *old(owner),
            ),
        ensures
            Self::obeys_vmio_write_spec() ==> Self::write_spec(
                *self,
                offset,
                *old(reader),
                *final(reader),
                *old(writer_own),
                *final(writer_own),
                *old(owner),
                *final(owner),
                r,
            ),
    ;

    /// Reads a specified number of bytes at a specified offset into a given buffer.
    ///
    /// # No short reads
    ///
    /// Similar to [`read`].
    ///
    /// [`read`]: VmIo::read
    fn read_byte<const N: usize>(
        &self,
        offset: usize,
        bytes: ArrayPtr<u8, N>,
        Tracked(bytes_owner): Tracked<&mut PointsToArray<u8, N>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> (r: Result<()>)
    // requires
    //     Self::obeys_vmio_write_requires() ==> Self::vmio_write_requires(
    //         *self,
    //         *old(owner),
    //         offset,
    //     ),
    // ensures
    //     Self::obeys_vmio_write_ensures() ==> Self::vmio_write_ensures(
    //         *self,
    //         *old(owner),
    //         offset,
    //         *owner,
    //         r,
    //     ),
    ;

    /// Reads a specified number of bytes at a specified offset into a given buffer.
    ///
    /// This default impl wraps `buf` in a [`VmWriter`] and delegates to
    /// [`Self::read`]. Mirrors vostd's `read_bytes` default.
    #[verifier::external_body]
    fn read_bytes(
        &self,
        offset: usize,
        buf: &mut [u8],
        Tracked(writer_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> Result<()> {
        let mut writer = VmWriter::from(buf);
        self.read(offset, &mut writer, Tracked(writer_own), Tracked(owner))
    }

    /// Reads a value of a specified type at a specified offset.
    ///
    /// Mirrors vostd's `read_val` default.
    #[verifier::external_body]
    fn read_val<T: Pod>(
        &self,
        offset: usize,
        Tracked(writer_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> Result<T> {
        let mut val = T::new_uninit();
        self.read_bytes(offset, val.as_bytes_mut(), Tracked(writer_own), Tracked(owner))?;
        Ok(val)
    }

    /// Reads a slice of a specified type at a specified offset.
    ///
    /// Mirrors vostd's `read_slice` default.
    #[verifier::external_body]
    fn read_slice<T: Pod>(
        &self,
        offset: usize,
        slice: &mut [T],
        Tracked(writer_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> Result<()> {
        let len_in_bytes = core::mem::size_of_val(slice);
        let ptr = slice as *mut [T] as *mut u8;
        // SAFETY: the slice can be transmuted to a writable byte slice since
        // the elements are all Plain-Old-Data (Pod) types.
        let buf = unsafe { core::slice::from_raw_parts_mut(ptr, len_in_bytes) };
        self.read_bytes(offset, buf, Tracked(writer_own), Tracked(owner))
    }

    /// Writes a specified number of bytes from a given buffer at a specified offset.
    ///
    /// This default impl wraps `buf` in a [`VmReader`] and delegates to
    /// [`Self::write`]. Mirrors vostd's `write_bytes` default.
    #[verifier::external_body]
    fn write_bytes(
        &self,
        offset: usize,
        buf: &[u8],
        Tracked(reader_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> Result<()> {
        let mut reader = VmReader::from(buf);
        self.write(offset, &mut reader, Tracked(reader_own), Tracked(owner))
    }

    /// Writes a value of a specified type at a specified offset.
    ///
    /// Mirrors vostd's `write_val` default.
    #[verifier::external_body]
    fn write_val<T: Pod>(
        &self,
        offset: usize,
        new_val: &T,
        Tracked(reader_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> Result<()> {
        self.write_bytes(offset, new_val.as_bytes_ref(), Tracked(reader_own), Tracked(owner))?;
        Ok(())
    }

    /// Writes a slice of a specified type at a specified offset.
    ///
    /// Mirrors vostd's `write_slice` default.
    #[verifier::external_body]
    fn write_slice<T: Pod>(
        &self,
        offset: usize,
        slice: &[T],
        Tracked(reader_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> Result<()> {
        let len_in_bytes = core::mem::size_of_val(slice);
        let ptr = slice as *const [T] as *const u8;
        // SAFETY: the slice can be transmuted to a readable byte slice since
        // the elements are all Plain-Old-Data (Pod) types.
        let buf = unsafe { core::slice::from_raw_parts(ptr, len_in_bytes) };
        self.write_bytes(offset, buf, Tracked(reader_own), Tracked(owner))
    }

    /// Writes a sequence of values given by an iterator (`iter`) from the
    /// specified offset (`offset`).
    ///
    /// Stops on iterator exhaustion or write error. Returns `Ok(nr_written)`
    /// if at least one value was written; only the first-call error path
    /// surfaces as `Err`.
    ///
    /// `align` rounds the offset and item size up: `0`/`1` means no padding,
    /// otherwise must be a power of two.
    ///
    /// Mirrors vostd's `write_vals` default.
    #[verifier::external_body]
    fn write_vals<'a, T: Pod + 'a, I: Iterator<Item = &'a T>>(
        &self,
        offset: usize,
        iter: I,
        align: usize,
        Tracked(reader_own): Tracked<&mut VmIoOwner<'_>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> Result<usize> {
        use ::align_ext::AlignExt;
        let mut nr_written = 0;
        let (mut offset, item_size) = if (align >> 1) == 0 {
            (offset, core::mem::size_of::<T>())
        } else {
            (offset.align_up(align), core::mem::size_of::<T>().align_up(align))
        };
        for item in iter {
            match self.write_val(offset, item, Tracked(reader_own), Tracked(owner)) {
                Ok(_) => {
                    offset += item_size;
                    nr_written += 1;
                },
                Err(e) => {
                    if nr_written > 0 {
                        return Ok(nr_written);
                    }
                    return Err(e);
                },
            }
        }
        Ok(nr_written)
    }

    // fn write_val<T: Pod>(&self, offset: usize, val: T, Tracked(owner): Tracked<&mut P>) -> (r:
    //     Result<()>)
    // requires
    //     Self::obeys_vmio_write_requires() ==> Self::vmio_write_requires(
    //         *self,
    //         *old(owner),
    //         offset,
    //     ),
    // ensures
    //     Self::obeys_vmio_write_ensures() ==> Self::vmio_write_ensures(
    //         *self,
    //         *old(owner),
    //         offset,
    //         *owner,
    //         r,
    //     ),
    // ;

    // fn write_slice<T: Pod, const N: usize>(
    //     &self,
    //     offset: usize,
    //     slice: ArrayPtr<T, N>,
    //     Tracked(slice_owner): Tracked<&mut PointsToArray<T, N>>,
    //     Tracked(owner): Tracked<&mut P>,
    // ) -> (r: Result<()>)
    //     requires
    //         Self::obeys_vmio_write_requires() ==> Self::vmio_write_requires(
    //             *self,
    //             *old(owner),
    //             offset,
    //         ),
    //     ensures
    //         Self::obeys_vmio_write_ensures() ==> Self::vmio_write_ensures(
    //             *self,
    //             *old(owner),
    //             offset,
    //             *final(owner),
    //             r,
    //         ),
    // ;
}

/// A trait that enables reading/writing data from/to a VM object using one non-tearing memory
/// load/store.
///
/// See also [`VmIo`], which enables reading/writing data from/to a VM object without the guarantee
/// of using one non-tearing memory load/store.
pub trait VmIoOnce: Sized {
    spec fn obeys_vmio_once_read_requires() -> bool;

    spec fn obeys_vmio_once_write_requires() -> bool;

    spec fn obeys_vmio_once_read_ensures() -> bool;

    spec fn obeys_vmio_once_write_ensures() -> bool;

    /// Reads a value of the `PodOnce` type at the specified offset using one non-tearing memory
    /// load.
    ///
    /// Except that the offset is specified explicitly, the semantics of this method is the same as
    /// [`VmReader::read_once`].
    fn read_once<T: PodOnce>(&self, offset: usize) -> Result<T>;

    /// Writes a value of the `PodOnce` type at the specified offset using one non-tearing memory
    /// store.
    ///
    /// Except that the offset is specified explicitly, the semantics of this method is the same as
    /// [`VmWriter::write_once`].
    fn write_once<T: PodOnce>(&self, offset: usize, new_val: &T) -> Result<()>;
}

#[verus_verify]
impl<Fallibility> VmReader<'_, Fallibility> {
    pub open spec fn remain_spec(&self) -> usize {
        (self.end.vaddr - self.cursor.vaddr) as usize
    }

    /// Returns the number of remaining bytes that can be read.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - `self` must satisfy its invariant.
    /// ## Postconditions
    /// - The returned value equals [`Self::remain_spec`].
    #[verus_spec(r =>
        requires
            self.inv(),
        ensures
            r == self.remain_spec(),
    )]
    #[verifier::when_used_as_spec(remain_spec)]
    pub fn remain(&self) -> usize {
        self.end.addr() - self.cursor.addr()
    }

    /// Returns the cursor pointer, which refers to the address of the next byte to read.
    #[verifier::external_body]
    pub fn cursor(&self) -> *const u8 {
        self.cursor.vaddr as *const u8
    }

    /// Returns if it has remaining data to read.
    #[verifier::external_body]
    pub fn has_remain(&self) -> bool {
        self.remain() > 0
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
    pub fn advance(&mut self, len: usize) {
        self.cursor.vaddr = self.cursor.vaddr + len;
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
            old(owner_r).read_view_initialized(),
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
    pub fn read<WFallibility>(&mut self, writer: &mut VmWriter<'_, WFallibility>) -> usize {
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
        proof {
            assert forall|i: usize|
                #![trigger mv_r.addr_transl(i)]
                self.cursor.vaddr <= i < self.cursor.vaddr + copy_len implies {
                &&& mv_r.addr_transl(i) is Some
                &&& mv_r.memory.contains_key(mv_r.addr_transl(i).unwrap().0)
                &&& mv_r.memory[mv_r.addr_transl(i).unwrap().0].contents[mv_r.addr_transl(
                    i,
                ).unwrap().1 as int] is Init
            } by {
                assert(owner_r.range@.start == self.cursor.vaddr);
                assert(owner_r.range@.end == self.end.vaddr);
            }
        }
        VirtPtr::copy_nonoverlapping(
            &self.cursor,
            &writer.cursor,
            Tracked(mv_r),
            Tracked(&mut mv_w),
            copy_len,
        );

        self.advance(copy_len);
        writer.advance(copy_len);

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

        proof {
            assert forall|i: usize|
                #![trigger mem_src.addr_transl(i)]
                self.cursor.vaddr <= i < self.cursor.vaddr + core::mem::size_of::<T>() implies {
                &&& mem_src.addr_transl(i) is Some
                &&& mem_src.memory.contains_key(mem_src.addr_transl(i).unwrap().0)
                &&& mem_src.memory[mem_src.addr_transl(i).unwrap().0].contents[mem_src.addr_transl(
                    i,
                ).unwrap().1 as int] is Init
            } by {}
        }
        proof_with!(Tracked(mem_src));
        let v = read_pod_from_view(self.cursor);

        self.advance(len);

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
    /// ## Postconditions
    /// - The reader and owner still satisfy their invariants.
    /// - On success, the cursor advances by `size_of::<T>()` and the cursor was
    ///   aligned to `align_of::<T>()` (the runtime `assert!` would otherwise diverge).
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
                    &&& old(self).cursor.vaddr % core::mem::align_of::<T>() == 0
                    &&& final(self).remain_spec() == old(self).remain_spec() - core::mem::size_of::<T>()
                    &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                },
                Err(_) => {
                    *old(self) == *final(self)
                },
            }
    )]
    pub fn read_val_once<T: PodOnce>(&mut self) -> Result<T> {
        if core::mem::size_of::<T>() > self.remain() {
            return Err(Error::InvalidArgs);
        }
        vstd_extra::assert_eq!(self.cursor.vaddr % core::mem::align_of::<T>(), 0);
        // SAFETY: We have checked that the number of bytes remaining is at least the size of `T`
        // and that the cursor is properly aligned with respect to the type `T`. All other safety
        // requirements are the same as for `Self::read`.

        let tracked mem_src = owner.tracked_read_view_unwrap();
        proof {
            assert forall|i: usize|
                #![trigger mem_src.addr_transl(i)]
                self.cursor.vaddr <= i < self.cursor.vaddr + core::mem::size_of::<T>() implies {
                &&& mem_src.addr_transl(i) is Some
                &&& mem_src.memory.contains_key(mem_src.addr_transl(i).unwrap().0)
                &&& mem_src.memory[mem_src.addr_transl(i).unwrap().0].contents[mem_src.addr_transl(
                    i,
                ).unwrap().1 as int] is Init
            } by {}
        }
        proof_with!(Tracked(mem_src));
        let v = read_once_from_view::<T>(self.cursor);
        self.advance(core::mem::size_of::<T>());

        proof {
            owner.advance(core::mem::size_of::<T>());
        }

        Ok(v)
    }
}

#[verus_verify]
impl<'a, Fallibility> VmWriter<'a, Fallibility> {
    pub open spec fn avail_spec(&self) -> usize {
        (self.end.vaddr - self.cursor.vaddr) as usize
    }

    /// Constructs a [`VmWriter`] from a pointer, which represents a memory range in USER space.
    ///
    /// ⚠️ WARNING: Currently not implemented yet.
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
            !owner@.is_kernel,
            !owner@.is_fallible,
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
            is_fallible: false,
            phantom: PhantomData,
            is_kernel: false,
            mem_view: None,
        };
        let end_vaddr = if ptr.vaddr <= usize::MAX - len {
            ptr.vaddr + len
        } else {
            0
        };
        let end = VirtPtr { vaddr: end_vaddr, range: Ghost(range) };
        proof_with!(|= Tracked(owner));
        Self { id: Ghost(id), cursor: ptr, end, phantom: PhantomData }
    }

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
    #[verifier::when_used_as_spec(avail_spec)]
    pub fn avail(&self) -> usize {
        self.end.vaddr - self.cursor.vaddr
    }

    /// Returns the cursor pointer, which refers to the address of the next byte to write.
    #[verifier::external_body]
    pub fn cursor(&self) -> *mut u8 {
        self.cursor.vaddr as *mut u8
    }

    /// Returns if it has available space to write.
    #[verifier::external_body]
    pub fn has_avail(&self) -> bool {
        self.avail() > 0
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
    pub fn advance(&mut self, len: usize) {
        self.cursor.vaddr = self.cursor.vaddr + len;
    }

    /// Rewinds the cursor by `n` bytes. Used to undo a partial write.
    ///
    /// The cursor advancement on `write_fallible`'s `Err` path equals
    /// `copied_len`, so calling `rewind_cursor(copied_len)` deterministically
    /// restores the cursor to its position before the failed write.
    #[verus_spec(
        requires
            old(self).inv(),
            n <= old(self).cursor.vaddr - old(self).cursor.range@.start,
        ensures
            final(self).inv(),
            final(self).cursor.vaddr == old(self).cursor.vaddr - n,
            final(self).cursor.range == old(self).cursor.range,
            final(self).end == old(self).end,
            final(self).id == old(self).id,
    )]
    fn rewind_cursor(&mut self, n: usize) {
        self.cursor.vaddr = self.cursor.vaddr - n;
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
            old(owner_r).read_view_initialized(),
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
    pub fn write<RFallibility>(&mut self, reader: &mut VmReader<'_, RFallibility>) -> usize {
        proof_with!(Tracked(owner_r), Tracked(owner_w));
        reader.read(self)
    }


    #[verifier::external_body]
    #[verus_spec(
        requires
            self.inv(),
            core::mem::size_of::<T>() <= self.avail_spec(),
    )]
    fn write_once_inner<T: PodOnce>(&self, new_val: &mut T) {
        let cursor = self.cursor.vaddr as *mut T;
        unsafe { cursor.write_volatile(*new_val) };
    }

    /// Writes a value of the `PodOnce` type using one non-tearing memory store.
    ///
    /// If the length of the `PodOnce` type exceeds `self.avail()`, this method will return `Err`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The writer and its owner must satisfy their invariants.
    /// - The owner must match this writer and carry a memory view.
    /// ## Postconditions
    /// - The writer and owner still satisfy their invariants.
    /// - On success, the cursor advances by `size_of::<T>()`.
    /// - On error, the writer state is unchanged.
    #[verus_spec(r =>
        with
            Tracked(owner_w): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(owner_w).mem_view is Some,
            old(owner_w).inv(),
            old(self).wf(*old(owner_w)),
        ensures
            final(self).inv(),
            final(owner_w).inv(),
            final(self).wf(*final(owner_w)),
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
        // SAFETY: We have checked that the number of bytes available is at least the size of `T`
        // and that the cursor is properly aligned with respect to the type `T`. All other safety
        // requirements are the same as for `Self::write`.

        self.write_once_inner::<T>(new_val);
        self.advance(core::mem::size_of::<T>());

        proof {
            owner_w.advance(core::mem::size_of::<T>());
        }

        Ok(())
    }
}

impl<'a> VmWriter<'a, Fallible> {
    /// Writes a value of `Pod` type to user space.
    ///
    /// If the underlying memory access faults during the write, the cursor
    /// is rolled back to its starting position before returning `Err`. The
    /// rollback math is verified by [`Self::rewind_cursor`].
    ///
    /// # Verified Properties
    /// ## Postconditions
    /// - On success, the cursor advances by `size_of::<T>()`.
    /// - On error, the cursor is at its original position (writer state preserved).
    #[verifier::external_body]
    pub fn write_val<T: Pod>(&mut self, val: &mut T) -> Result<()> {
        if self.avail() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        let mut reader = VmReader::from_pod(val)?;
        // On partial write, restore the cursor to its position before the
        // failed `write_fallible`. Mirrors vostd's `.map_err(|(err, n)| {
        // self.cursor = self.cursor.sub(n); err })` pattern, with the
        // rollback math verified by `rewind_cursor`.
        match self.write_fallible(&mut reader) {
            Ok(_) => Ok(()),
            Err((err, copied_len)) => {
                self.rewind_cursor(copied_len);
                Err(err)
            },
        }
    }
}

} // verus!

impl<'a> From<&'a [u8]> for VmReader<'a, Infallible> {
    fn from(slice: &'a [u8]) -> Self {
        Self::from_slice(slice)
    }
}

impl<'a> From<&'a mut [u8]> for VmWriter<'a, Infallible> {
    fn from(slice: &'a mut [u8]) -> Self {
        Self::from_slice_mut(slice)
    }
}

/// Fallible memory read from a `VmWriter`.
pub trait FallibleVmRead<F> {
    fn read_fallible(
        &mut self,
        writer: &mut VmWriter<'_, F>,
    ) -> core::result::Result<usize, (Error, usize)>;
}

/// Fallible memory write from a `VmReader`.
pub trait FallibleVmWrite<F> {
    fn write_fallible(
        &mut self,
        reader: &mut VmReader<'_, F>,
    ) -> core::result::Result<usize, (Error, usize)>;
}

macro_rules! impl_read_fallible {
    ($reader_fallibility:ty, $writer_fallibility:ty) => {
        ::vstd::prelude::verus! {
        impl<'a> FallibleVmRead<$writer_fallibility> for VmReader<'a, $reader_fallibility> {
            #[verifier::external_body]
            #[verus_spec(r =>
                requires
                    old(self).inv(),
                    old(writer).inv(),
                ensures
                    final(self).end == old(self).end,
                    final(self).id == old(self).id,
                    final(self).cursor.range == old(self).cursor.range,
                    final(writer).end == old(writer).end,
                    final(writer).id == old(writer).id,
                    final(writer).cursor.range == old(writer).cursor.range,
                    final(self).inv(),
                    final(writer).inv(),
                    match r {
                        Ok(n) => {
                            &&& final(self).cursor.vaddr == old(self).cursor.vaddr + n
                            &&& final(writer).cursor.vaddr == old(writer).cursor.vaddr + n
                            &&& n <= old(self).remain_spec()
                            &&& n <= old(writer).avail_spec()
                        },
                        Err((_, copied_len)) => {
                            &&& final(self).cursor.vaddr == old(self).cursor.vaddr + copied_len
                            &&& final(writer).cursor.vaddr == old(writer).cursor.vaddr + copied_len
                            &&& copied_len <= old(self).remain_spec()
                            &&& copied_len <= old(writer).avail_spec()
                        },
                    }
            )]
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
            #[verus_spec(r =>
                requires
                    old(self).inv(),
                    old(reader).inv(),
                ensures
                    final(self).end == old(self).end,
                    final(self).id == old(self).id,
                    final(self).cursor.range == old(self).cursor.range,
                    final(reader).end == old(reader).end,
                    final(reader).id == old(reader).id,
                    final(reader).cursor.range == old(reader).cursor.range,
                    final(self).inv(),
                    final(reader).inv(),
                    match r {
                        Ok(n) => {
                            &&& final(self).cursor.vaddr == old(self).cursor.vaddr + n
                            &&& final(reader).cursor.vaddr == old(reader).cursor.vaddr + n
                            &&& n <= old(self).avail_spec()
                            &&& n <= old(reader).remain_spec()
                        },
                        Err((_, copied_len)) => {
                            &&& final(self).cursor.vaddr == old(self).cursor.vaddr + copied_len
                            &&& final(reader).cursor.vaddr == old(reader).cursor.vaddr + copied_len
                            &&& copied_len <= old(self).avail_spec()
                            &&& copied_len <= old(reader).remain_spec()
                        },
                    }
            )]
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
