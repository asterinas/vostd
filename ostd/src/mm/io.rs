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
use vstd_extra::assert;
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
    // SAFETY: The safety is upheld by the caller.
    let failed_bytes = unsafe { __memcpy_fallible(dst, src, len) };
    len - failed_bytes
}

/// Fills `len` bytes of memory at `dst` with the specified `value`, stopping
/// early on page fault. Returns the number of bytes successfully set.
///
/// # Safety
/// - `dst` must either be valid for writes of `len` bytes or be in user space.
unsafe fn memset_fallible(dst: *mut u8, value: u8, len: usize) -> usize {
    // SAFETY: The safety is upheld by the caller.
    let failed_bytes = unsafe { __memset_fallible(dst, value, len) };
    len - failed_bytes
}

verus! {

/// Verus spec stub for [`<*mut T>::is_aligned`]: returns whether the pointer's address is a
/// multiple of `align_of::<T>()`.
pub assume_specification<T>[ <*mut T>::is_aligned ](_0: *mut T) -> (res: bool)
    ensures
        res <==> (_0 as usize) % core::mem::align_of::<T>() == 0,
;

/// Marker type indicating that VM I/O operations may fail (e.g., user-space access).
pub struct Fallible {}

/// Marker type indicating that VM I/O operations cannot fail (e.g., kernel-space access).
pub struct Infallible {}


/// Copies `len` bytes from `src` to `dst`.
///
/// This is the escape hatch into the abstract [`VirtPtr`] memory model: it is
/// the only place in the executable code that performs a multi-byte copy, and
/// it discharges the obligation by delegating to [`VirtPtr::copy_nonoverlapping`].
///
/// # Safety
///
/// - `src` must be [valid] for reads of `len` bytes.
/// - `dst` must be [valid] for writes of `len` bytes.
///
/// [valid]: crate::mm::io#safety
#[inline]
#[verus_spec(
    with
        Tracked(mem_src): Tracked<&MemView>,
        Tracked(mem_dst): Tracked<&mut MemView>,
    requires
        src.inv(),
        dst.inv(),
        src.vaddr + len <= dst.vaddr || dst.vaddr + len <= src.vaddr,
        src.range@.start <= src.vaddr,
        src.vaddr + len <= src.range@.end,
        forall|i: usize|
            #![trigger mem_src.addr_transl(i)]
            src.vaddr <= i < src.vaddr + len ==> {
                &&& mem_src.addr_transl(i) is Some
                &&& mem_src.memory.contains_key(mem_src.addr_transl(i).unwrap().0)
                &&& mem_src.memory[mem_src.addr_transl(i).unwrap().0].contents[mem_src.addr_transl(i).unwrap().1 as int] is Init
            },
        dst.range@.start <= dst.vaddr,
        dst.vaddr + len <= dst.range@.end,
        forall|i: usize|
            dst.vaddr <= i < dst.vaddr + len ==> {
                &&& old(mem_dst).addr_transl(i) is Some
            },
    ensures
        *final(mem_dst) == VirtPtr::memcpy_spec(src, dst, *mem_src, *old(mem_dst), len),
        final(mem_dst).mappings == old(mem_dst).mappings,
        old(mem_dst).memory.dom().subset_of(final(mem_dst).memory.dom()),
        forall|i: usize|
            #![trigger final(mem_dst).addr_transl(i)]
            dst.vaddr <= i < dst.vaddr + len ==> {
                &&& final(mem_dst).addr_transl(i) is Some
            },
)]
unsafe fn memcpy(dst: VirtPtr, src: VirtPtr, len: usize) {
    VirtPtr::copy_nonoverlapping(&src, &dst, Tracked(mem_src), Tracked(mem_dst), len);
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
pub tracked enum VmIoMemView {
    /// An owned memory for writing.
    WriteView(MemView),
    /// An owned snapshot of memory for reading.
    ReadView(MemView),
}

/// The owner of a VM I/O operation, which tracks the memory range and the memory view for the
/// operation.
///
/// Basically the caller should be only interested in this struct when using [`VmReader`] and
/// [`VmWriter`] to perform VM I/O operations, since the safety of these operations depends on the
/// validity of the memory range and memory view tracked by this struct.
pub tracked struct VmIoOwner {
    /// The unique identifier of this owner.
    pub id: Ghost<nat>,
    /// The virtual address range owned by this owner.
    pub range: Ghost<Range<usize>>,
    /// Whether this reader is fallible.
    pub is_fallible: bool,
    /// Whether this owner is for kernel space.
    pub is_kernel: bool,
    /// The mem view associated with this owner.
    pub mem_view: Option<VmIoMemView>,
}

impl VmIoOwner {
    /// Structural well-formedness: the range is ordered.
    /// Always holds after construction.
    pub open spec fn inv_wf(self) -> bool {
        self.range@.start <= self.range@.end
    }
}

impl Inv for VmIoOwner {
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

impl VmIoOwner {
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
    pub open spec fn overlaps(self, other: VmIoOwner) -> bool {
        !self.disjoint(other)
    }

    #[verifier::inline]
    pub open spec fn overlaps_with_range(self, range: Range<usize>) -> bool {
        &&& self.range@.start <= range.end
        &&& range.start <= self.range@.end
    }

    /// Checks whether this owner is disjoint with another owner.
    #[verifier::inline]
    pub open spec fn disjoint(self, other: VmIoOwner) -> bool {
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
    pub open spec fn params_eq(self, other: VmIoOwner) -> bool {
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
    pub proof fn advance(tracked &mut self, nbytes: usize) -> (tracked res: VmIoMemView)
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

    /// Splits this owner at `nbytes`, returning the front portion as a new owner and shrinking
    /// `self` to cover the back portion.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The owner must satisfy its invariant.
    /// - The owner must carry a memory view.
    /// - `nbytes` must not exceed the remaining length of the owned range.
    /// ## Postconditions
    /// - Both the returned front owner and the updated `self` satisfy their invariants and
    ///   carry the same kind of memory view as the original.
    /// - The front owner covers `[old.start, old.start + nbytes)`.
    /// - `self`'s range becomes `[old.start + nbytes, old.end)`.
    /// - `is_fallible`, `is_kernel` are preserved on both sides.
    /// - If the original was an initialized read view, both sides remain initialized.
    #[verifier::external_body]
    pub proof fn split(tracked &mut self, nbytes: usize) -> (tracked r: VmIoOwner)
        requires
            old(self).inv(),
            old(self).mem_view is Some,
            nbytes <= old(self).range@.end - old(self).range@.start,
        ensures
            r.inv(),
            r.range@.start == old(self).range@.start,
            r.range@.end == old(self).range@.start + nbytes,
            r.is_fallible == old(self).is_fallible,
            r.is_kernel == old(self).is_kernel,
            r.mem_view is Some,
            final(self).inv(),
            final(self).range@.start == old(self).range@.start + nbytes,
            final(self).range@.end == old(self).range@.end,
            final(self).is_fallible == old(self).is_fallible,
            final(self).id == old(self).id,
            final(self).is_kernel == old(self).is_kernel,
            final(self).mem_view is Some,
            old(self).mem_view matches Some(VmIoMemView::ReadView(_)) ==> {
                &&& r.mem_view matches Some(VmIoMemView::ReadView(_))
                &&& final(self).mem_view matches Some(VmIoMemView::ReadView(_))
            },
            old(self).mem_view matches Some(VmIoMemView::WriteView(_)) ==> {
                &&& r.mem_view matches Some(VmIoMemView::WriteView(_))
                &&& final(self).mem_view matches Some(VmIoMemView::WriteView(_))
            },
            old(self).read_view_initialized() ==> {
                &&& r.read_view_initialized()
                &&& final(self).read_view_initialized()
            },
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
            VmIoMemView::ReadView(*r) == self.mem_view.unwrap(),
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
            Tracked(fallible): Tracked<bool>,
                -> owner: Tracked<VmIoOwner>,
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
        let tracked owner = VmIoOwner {
            id: Ghost(id),
            range: Ghost(ptr.vaddr..(ptr.vaddr + len) as usize),
            is_fallible: fallible,
            is_kernel: true,
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
            -> owner: Tracked<Result<VmIoOwner>>,
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
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The writer and its owner must satisfy their invariants.
    /// - The owner must match this writer and carry a write memory view.
    /// - Every byte in the writable range must translate in the write view.
    /// - The caller supplies a tracked reader owner whose front `size_of::<T>()` bytes
    ///   provide the source bytes; the borrowed `reader_owner` shrinks by `size_of::<T>()`.
    /// - The reader's source range and the writer's destination range do not overlap.
    /// ## Postconditions
    /// - The writer and owner still satisfy their invariants.
    /// - On success, the cursor advances by `size_of::<T>()`.
    /// - On error, the writer state is unchanged.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmIoOwner>,
            Tracked(reader_owner): Tracked<&mut VmIoOwner>,
        requires
            old(self).inv(),
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(owner).has_write_view(),
            old(owner).mem_view matches Some(VmIoMemView::WriteView(mem_dst)) ==> {
                forall|i: usize|
                    #![trigger mem_dst.addr_transl(i)]
                    old(self).cursor.vaddr <= i < old(self).cursor.vaddr + old(self).avail_spec() ==> {
                        &&& mem_dst.addr_transl(i) is Some
                    }
            },
            old(reader_owner).inv(),
            old(reader_owner).range@.end - old(reader_owner).range@.start >= core::mem::size_of::<T>(),
            old(reader_owner).read_view_initialized(),
            old(self).end.vaddr <= old(reader_owner).range@.start
                || old(reader_owner).range@.end <= old(self).cursor.vaddr,
        ensures
            final(self).inv(),
            final(owner).inv(),
            final(self).wf(*final(owner)),
            final(reader_owner).range@.start == old(reader_owner).range@.start + core::mem::size_of::<T>(),
            final(reader_owner).range@.end == old(reader_owner).range@.end,
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
    pub fn write_val<T: Pod>(&mut self, new_val: &T) -> Result<()> {
        let len = core::mem::size_of::<T>();
        proof_decl! {
            let tracked mut temp_r_owner;
        }
        proof {
            temp_r_owner = reader_owner.split(len);
        }
        if self.avail() < len {
            return Err(Error::InvalidArgs);
        }

        #[verus_spec(with Tracked(&temp_r_owner))]
        let mut reader = VmReader::from(new_val.as_bytes());
        #[verus_spec(with Tracked(owner), Tracked(&mut temp_r_owner))]
        let _ = self.write(&mut reader);
        Ok(())
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
        let cursor = self.cursor.cast::<T>();
        assert!(cursor.is_aligned());

        let avail = self.avail();
        assert!(avail % core::mem::size_of::<T>() == 0);
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
            Tracked(owner_w): Tracked<&mut VmIoOwner>,
            Tracked(owner_r): Tracked<&mut VmIoOwner>,
        requires
            old(self).inv(),
            old(reader).inv(),
            old(self).wf(*old(owner_w)),
            old(reader).wf(*old(owner_r)),
            old(owner_w).has_write_view(),
            old(owner_r).read_view_initialized(),
            // Non-overlapping active ranges.
            old(self).end.vaddr <= old(reader).cursor.vaddr
            || old(reader).end.vaddr <= old(self).cursor.vaddr,
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
    pub fn write(&mut self, reader: &mut VmReader<'_, Infallible>) -> usize {
        proof_decl! {
            let tracked mut _discarded_consumed_w: VmIoOwner;
        }
        #[verus_spec(with Tracked(owner_r), Tracked(owner_w) => Tracked(_discarded_consumed_w))]
        reader.read(self)
    }


    /// Writes a value of the `PodOnce` type using one non-tearing memory store.
    ///
    /// If the length of the `PodOnce` type exceeds `self.avail()`, this method will return `Err`.
    ///
    /// # Panics
    ///
    /// This method will panic if the current position of the writer does not meet the alignment
    /// requirements of type `T`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The writer and its owner must satisfy their invariants.
    /// - The owner must match this writer and carry a write memory view.
    /// - Every byte in the writable range must translate in the write view.
    /// ## Postconditions
    /// - The writer and owner still satisfy their invariants.
    /// - On success, the cursor advances by `size_of::<T>()` and the cursor was
    ///   aligned to `align_of::<T>()` (the runtime `assert!` would otherwise diverge).
    /// - On error, the writer state is unchanged.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmIoOwner>,
        requires
            old(self).inv(),
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(owner).has_write_view(),
            old(owner).mem_view matches Some(VmIoMemView::WriteView(mem_dst)) ==> {
                forall|i: usize|
                    #![trigger mem_dst.addr_transl(i)]
                    old(self).cursor.vaddr <= i < old(self).cursor.vaddr + old(self).avail_spec() ==> {
                        &&& mem_dst.addr_transl(i) is Some
                    }
            },
        ensures
            final(self).inv(),
            final(owner).inv(),
            final(self).wf(*final(owner)),
            match r {
                Ok(_) => {
                    &&& old(self).cursor.vaddr % core::mem::align_of::<T>() == 0
                    &&& final(self).avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
                    &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                },
                Err(_) => {
                    *old(self) == *final(self)
                },
            }
    )]
    pub fn write_once<T: PodOnce>(&mut self, new_val: &T) -> Result<()> {
        if self.avail() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }

        let cursor = self.cursor.cast::<T>();
        assert!(cursor.is_aligned());

        // NOTE: vostd has `const { assert!(pod_once_impls::is_non_tearing::<T>()) };` here, but
        // verus doesn't yet support const block expressions. The non-tearing guarantee for our
        // `PodOnce` impls is restricted to types of size 1/2/4/8 by convention.

        // SAFETY: We have checked that the number of bytes available is at least the size of `T`
        // and that the cursor is properly aligned with respect to the type `T`. All other safety
        // requirements are the same as for `Self::write`.

        let len = core::mem::size_of::<T>();
        let tracked mut mem_dst = match owner.mem_view.tracked_take() {
            VmIoMemView::WriteView(mv) => mv,
            _ => { proof_from_false() },
        };
        let ghost mem_dst_pre = mem_dst;

        proof {
            assert forall|i: usize|
                #![trigger mem_dst.addr_transl(i)]
                self.cursor.vaddr <= i < self.cursor.vaddr + core::mem::size_of::<T>() implies {
                    mem_dst.addr_transl(i) is Some
                } by {
                    assert(owner.range@.start == self.cursor.vaddr);
                    assert(owner.range@.end == self.end.vaddr);
                }
        }
        self.cursor.write_volatile::<T>(Tracked(&mut mem_dst), *new_val);

        self.cursor = self.cursor.wrapping_add(len);

        proof {
            owner.mem_view = Some(VmIoMemView::WriteView(mem_dst));

            assert forall|va|
                owner.range@.start <= va < owner.range@.end implies mem_dst.addr_transl(
                va,
            ) is Some by {
                assert(mem_dst.mappings == mem_dst_pre.mappings);
                assert(mem_dst.addr_transl(va) == mem_dst_pre.addr_transl(va));
            }

            owner.advance(len);
        }

        Ok(())
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
            -> owner: Tracked<VmIoOwner>,
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
            -> owner: Tracked<Result<VmIoOwner>>,
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

    /// Constructs an infallible [`VmReader`] from a shared PoD reference.
    #[verifier::external_body]
    pub fn from_pod_ref<T: Pod>(val: &T) -> (r: Self)
        ensures
            r.remain_spec() == core::mem::size_of::<T>(),
    {
        let bytes = val.as_bytes();
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
    /// - `consumed_w` is the just-written portion of the writer's owner, covering
    ///   `[old(owner_w).range@.start, old(owner_w).range@.start + r)`.
    #[verus_spec(r =>
        with
            Tracked(owner_r): Tracked<&mut VmIoOwner>,
            Tracked(owner_w): Tracked<&mut VmIoOwner>,
                -> consumed_w: Tracked<VmIoOwner>,
        requires
            old(self).inv(),
            old(writer).inv(),
            old(self).wf(*old(owner_r)),
            old(writer).wf(*old(owner_w)),
            old(owner_w).has_write_view(),
            old(owner_r).read_view_initialized(),
            // Non-overlapping active ranges.
            // TODO: this needs to be in the invariants
            old(self).end.vaddr <= old(writer).cursor.vaddr
            || old(writer).end.vaddr <= old(self).cursor.vaddr,
        ensures
            final(self).inv(),
            final(writer).inv(),
            final(self).wf(*final(owner_r)),
            final(writer).wf(*final(owner_w)),
            r == vstd::math::min(old(self).remain_spec() as int, old(writer).avail_spec() as int),
            final(self).remain_spec() == old(self).remain_spec() - r as usize,
            final(self).cursor.vaddr == old(self).cursor.vaddr + r as usize,
            final(writer).avail_spec() == old(writer).avail_spec() - r as usize,
            final(writer).cursor.vaddr == old(writer).cursor.vaddr + r as usize,
            consumed_w@.inv(),
            consumed_w@.range@.start == old(owner_w).range@.start,
            consumed_w@.range@.end == old(owner_w).range@.start + r as usize,
            consumed_w@.has_write_view(),
    )]
    pub fn read(&mut self, writer: &mut VmWriter<'_, Infallible>) -> usize {
        let copy_len = self.remain().min(writer.avail());
        proof_decl! {
            let tracked mut consumed_w_owner_inner: VmIoOwner;
        }
        if copy_len == 0 {
            proof {
                consumed_w_owner_inner = owner_w.split(0);
            }
            proof_with!(|= Tracked(consumed_w_owner_inner));
            0
        } else {
            let tracked mv_r = match owner_r.mem_view.tracked_take() {
                VmIoMemView::ReadView(mv) => mv,
                _ => { proof_from_false() },
            };
            let tracked mut mv_w = match owner_w.mem_view.tracked_take() {
                VmIoMemView::WriteView(mv) => mv,
                _ => { proof_from_false() },
            };
            let ghost mv_w_pre = mv_w;

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
            // SAFETY: The source and destination are subsets of memory ranges specified by the
            // reader and writer, so they are valid for reading and writing.
            unsafe {
                #[verus_spec(with Tracked(&mv_r), Tracked(&mut mv_w))]
                memcpy(writer.cursor, self.cursor, copy_len)
            };

            self.cursor = self.cursor.wrapping_add(copy_len);
            writer.cursor = writer.cursor.wrapping_add(copy_len);

            proof {
                owner_w.mem_view = Some(VmIoMemView::WriteView(mv_w));
                owner_r.mem_view = Some(VmIoMemView::ReadView(mv_r));

                assert forall|va|
                    owner_w.range@.start <= va < owner_w.range@.end implies mv_w.addr_transl(
                    va,
                ) is Some by {
                    assert(mv_w.mappings == mv_w_pre.mappings);
                    assert(mv_w.addr_transl(va) == mv_w_pre.addr_transl(va));
                }

                consumed_w_owner_inner = owner_w.split(copy_len);
                owner_r.advance(copy_len);
            }
            proof_with!(|= Tracked(consumed_w_owner_inner));
            copy_len
        }
    }

    /// Reads a value of `Pod` type.
    ///
    /// If the length of the `Pod` type exceeds `self.remain()`,
    /// this method will return `Err`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The reader and its owner must satisfy their invariants.
    /// - The owner must match this reader and carry an initialized read memory view.
    /// - The caller supplies a tracked writer owner whose front `size_of::<T>()` bytes
    ///   will become the owner of the returned value. The borrowed `writer_owner` shrinks
    ///   to cover the remaining range.
    /// ## Postconditions
    /// - The reader and its owner still satisfy their invariants.
    /// - On success, the cursor advances by `size_of::<T>()` and the returned `val_owner`
    ///   owns the bytes backing `val`.
    /// - On error, the reader state is unchanged.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmIoOwner>,
            Tracked(writer_owner): Tracked<&mut VmIoOwner>,
                -> val_owner: Tracked<VmIoOwner>,
        requires
            old(self).inv(),
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(owner).read_view_initialized(),
            old(writer_owner).inv(),
            old(writer_owner).range@.end - old(writer_owner).range@.start >= core::mem::size_of::<T>(),
            old(writer_owner).has_write_view(),
            old(self).end.vaddr <= old(writer_owner).range@.start
                || old(writer_owner).range@.end <= old(self).cursor.vaddr,
        ensures
            final(self).inv(),
            final(owner).inv(),
            final(self).wf(*final(owner)),
            final(writer_owner).range@.start == old(writer_owner).range@.start + core::mem::size_of::<T>(),
            final(writer_owner).range@.end == old(writer_owner).range@.end,
            val_owner@.inv(),
            val_owner@.range@.start == old(writer_owner).range@.start,
            val_owner@.range@.end == old(writer_owner).range@.start + core::mem::size_of::<T>(),
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
        let len = core::mem::size_of::<T>();
        proof_decl! {
            let tracked mut temp_w_owner;
            let tracked mut val_owner_inner;
        }
        proof {
            temp_w_owner = writer_owner.split(len);
        }
        if self.remain() < len {
            proof {
                val_owner_inner = temp_w_owner;
            }
            proof_with!(|= Tracked(val_owner_inner));
            Err(Error::InvalidArgs)
        } else {
            let mut val = T::new_uninit();
            #[verus_spec(with Tracked(&temp_w_owner))]
            let mut writer = VmWriter::from(val.as_bytes_mut());
            #[verus_spec(with Tracked(owner), Tracked(&mut temp_w_owner) => Tracked(val_owner_inner))]
            let _ = self.read(&mut writer);
            proof_with!(|= Tracked(val_owner_inner));
            Ok(val)
        }
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
            Tracked(owner): Tracked<&mut VmIoOwner>,
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
    pub fn read_once<T: PodOnce>(&mut self) -> Result<T> {
        if self.remain() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }

        let cursor = self.cursor.cast::<T>();
        assert!(cursor.is_aligned());

        // NOTE: vostd has `const { assert!(pod_once_impls::is_non_tearing::<T>()) };` here, but
        // verus doesn't yet support const block expressions. The non-tearing guarantee for our
        // `PodOnce` impls is restricted to types of size 1/2/4/8 by convention.

        // SAFETY: We have checked that the number of bytes remaining is at least the size of `T`
        // and that the cursor is properly aligned with respect to the type `T`. All other safety
        // requirements are the same as for `Self::read`.

        let len = core::mem::size_of::<T>();
        let tracked mem_src = owner.tracked_read_view_unwrap();
        proof {
            assert forall|i: usize|
                #![trigger mem_src.addr_transl(i)]
                self.cursor.vaddr <= i < self.cursor.vaddr + len implies {
                &&& mem_src.addr_transl(i) is Some
                &&& mem_src.memory.contains_key(mem_src.addr_transl(i).unwrap().0)
                &&& mem_src.memory[mem_src.addr_transl(i).unwrap().0].contents[mem_src.addr_transl(
                    i,
                ).unwrap().1 as int] is Init
            } by {}
        }
        let v = self.cursor.read_volatile::<T>(Tracked(mem_src));

        self.cursor = self.cursor.wrapping_add(len);

        proof {
            owner.advance(len);
        }

        Ok(v)
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
    /// - The owner has the same range as `ptr`, has no memory view yet, and is marked as user-space.
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
            -> owner: Tracked<VmIoOwner>,
        ensures
            r.inv_wf(),
            owner@.id == id,
            owner@.range == ptr.range@,
            owner@.mem_view is None,
            !owner@.is_kernel,
            r.cursor == ptr,
            r.end == ptr.wrapping_add_spec(len),
            r.end.range@ == ptr.range@,
            ptr.inv() && ptr.range@.start == ptr.vaddr
                && len == ptr.range@.end - ptr.range@.start ==> {
                &&& r.inv()
                &&& owner@.inv()
                &&& r.wf(owner@)
            },
    )]
    pub unsafe fn from_user_space(ptr: VirtPtr, len: usize) -> Self {
        let tracked owner = VmIoOwner {
            id: Ghost(id),
            range: Ghost(ptr.range@),
            is_fallible: true,
            is_kernel: false,
            mem_view: None,
        };
        proof_with!(|= Tracked(owner));
        Self { id: Ghost(id), cursor: ptr, end: ptr.wrapping_add(len), phantom: PhantomData }
    }

    /// Reads a value of `Pod` type from a (potentially) user-space buffer.
    ///
    /// If the length of the `Pod` type exceeds `self.remain()`, or the value
    /// can not be read completely (e.g. due to a page fault), this method
    /// returns `Err` and the reader's cursor is rolled back to its original
    /// position.
    #[verus_spec(r =>
        with
            Tracked(writer_owner): Tracked<&mut VmIoOwner>,
                -> val_owner: Tracked<VmIoOwner>,
        requires
            old(self).inv(),
            old(writer_owner).inv(),
            old(writer_owner).range@.end - old(writer_owner).range@.start >= core::mem::size_of::<T>(),
            old(writer_owner).has_write_view(),
        ensures
            final(self).inv(),
            final(self).end == old(self).end,
            final(self).id == old(self).id,
            final(self).cursor.range == old(self).cursor.range,
            final(writer_owner).range@.start == old(writer_owner).range@.start + core::mem::size_of::<T>(),
            final(writer_owner).range@.end == old(writer_owner).range@.end,
            val_owner@.inv(),
            val_owner@.range@.start == old(writer_owner).range@.start,
            val_owner@.range@.end == old(writer_owner).range@.start + core::mem::size_of::<T>(),
            r is Err ==> final(self).cursor.vaddr == old(self).cursor.vaddr,
    )]
    pub fn read_val<T: Pod>(&mut self) -> Result<T> {
        let len = core::mem::size_of::<T>();
        proof_decl! {
            let tracked mut val_owner_inner;
        }
        proof {
            val_owner_inner = writer_owner.split(len);
        }
        let result = if self.remain() < len {
            Err(Error::InvalidArgs)
        } else {
            let mut val = T::new_uninit();
            #[verus_spec(with Tracked(&val_owner_inner))]
            let mut writer = VmWriter::from(val.as_bytes_mut());
            match self.read_fallible(&mut writer) {
                Ok(_) => Ok(val),
                Err((err, copied_len)) => {
                    self.cursor = self.cursor.sub(copied_len);
                    Err(err)
                },
            }
        };
        proof_with!(|= Tracked(val_owner_inner));
        result
    }

    /// Collects all the remaining bytes into a `Vec<u8>`.
    ///
    /// If the memory read failed, this method will return `Err`
    /// and the current reader's cursor remains pointing to
    /// the original starting position.
    #[verus_spec(r =>
        with
            Tracked(writer_owner): Tracked<&mut VmIoOwner>,
                -> val_owner: Tracked<VmIoOwner>,
        requires
            old(self).inv(),
            old(writer_owner).inv(),
            old(writer_owner).range@.end - old(writer_owner).range@.start >= old(self).remain_spec(),
            old(writer_owner).has_write_view(),
        ensures
            final(self).inv(),
            final(self).end == old(self).end,
            final(self).id == old(self).id,
            final(self).cursor.range == old(self).cursor.range,
            final(writer_owner).range@.start == old(writer_owner).range@.start + old(self).remain_spec(),
            final(writer_owner).range@.end == old(writer_owner).range@.end,
            val_owner@.inv(),
            val_owner@.range@.start == old(writer_owner).range@.start,
            val_owner@.range@.end == old(writer_owner).range@.start + old(self).remain_spec(),
            r is Err ==> final(self).cursor.vaddr == old(self).cursor.vaddr,
    )]
    pub fn collect(&mut self) -> Result<alloc::vec::Vec<u8>> {
        let len = self.remain();
        proof_decl! {
            let tracked mut val_owner_inner;
        }
        proof {
            val_owner_inner = writer_owner.split(len);
        }
        let mut buf = alloc::vec![0u8; len];
        #[verus_spec(with Tracked(&val_owner_inner))]
        let mut writer = VmWriter::from(buf.as_mut_slice());
        let result = match self.read_fallible(&mut writer) {
            Ok(_) => Ok(buf),
            Err((err, copied_len)) => {
                self.cursor = self.cursor.sub(copied_len);
                Err(err)
            },
        };
        proof_with!(|= Tracked(val_owner_inner));
        result
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
        writer_own: VmIoOwner,
        owner: P,
    ) -> bool {
        true
    }

    open spec fn write_requires(
        self,
        offset: usize,
        reader: VmReader<'_>,
        reader_own: VmIoOwner,
        owner: P,
    ) -> bool {
        true
    }

    spec fn read_spec(
        self,
        offset: usize,
        old_writer: VmWriter<'_>,
        new_writer: VmWriter<'_>,
        old_writer_own: VmIoOwner,
        new_writer_own: VmIoOwner,
        old_owner: P,
        new_owner: P,
        r: Result<()>,
    ) -> bool;

    spec fn write_spec(
        self,
        offset: usize,
        old_reader: VmReader<'_>,
        new_reader: VmReader<'_>,
        old_writer_own: VmIoOwner,
        new_writer_own: VmIoOwner,
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
        Tracked(writer_own): Tracked<&mut VmIoOwner>,
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
        Tracked(writer_own): Tracked<&mut VmIoOwner>,
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
        Tracked(writer_own): Tracked<&mut VmIoOwner>,
        Tracked(owner): Tracked<&mut P>,
    ) -> Result<()> {
        let mut writer = VmWriter::from(buf).to_fallible();
        self.read(offset, &mut writer, Tracked(writer_own), Tracked(owner))
    }

    /// Reads a value of a specified type at a specified offset.
    ///
    /// Mirrors vostd's `read_val` default.
    #[verifier::external_body]
    fn read_val<T: Pod>(
        &self,
        offset: usize,
        Tracked(writer_own): Tracked<&mut VmIoOwner>,
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
        Tracked(writer_own): Tracked<&mut VmIoOwner>,
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
        Tracked(reader_own): Tracked<&mut VmIoOwner>,
        Tracked(owner): Tracked<&mut P>,
    ) -> Result<()> {
        let mut reader = VmReader::from(buf).to_fallible();
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
        Tracked(reader_own): Tracked<&mut VmIoOwner>,
        Tracked(owner): Tracked<&mut P>,
    ) -> Result<()> {
        self.write_bytes(offset, new_val.as_bytes(), Tracked(reader_own), Tracked(owner))?;
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
        Tracked(reader_own): Tracked<&mut VmIoOwner>,
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
        Tracked(reader_own): Tracked<&mut VmIoOwner>,
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

    /// Returns the cursor pointer, which refers to the address of the next byte to read.
    pub fn cursor(&self) -> VirtPtr {
        self.cursor
    }

    /// Returns whether there is remaining data to read.
    #[verus_spec(
        requires
            self.inv(),
    )]
    pub fn has_remain(&self) -> bool {
        self.remain() > 0
    }

    /// Limits the length of remaining data.
    ///
    /// This method ensures the post-condition `self.remain() <= max_remain`.
    #[verus_spec(r =>
        requires
            old(self).inv(),
        ensures
            r.inv(),
            r.remain_spec() <= max_remain,
            r.remain_spec() <= old(self).remain_spec(),
            r.cursor == old(self).cursor,
            r.id == old(self).id,
    )]
    pub fn limit(&mut self, max_remain: usize) -> &mut Self {
        if max_remain < self.remain() {
            self.end = self.cursor.wrapping_add(max_remain);
        }
        self
    }

    /// Skips the first `nbytes` bytes of data.
    ///
    /// The length of remaining data is decreased accordingly.
    ///
    /// # Panics
    ///
    /// If `nbytes` is greater than `self.remain()`, then the method panics.
    #[verus_spec(r =>
        requires
            old(self).inv(),
            nbytes <= old(self).remain_spec(),
        ensures
            r.inv(),
            r.cursor.vaddr == old(self).cursor.vaddr + nbytes,
            r.remain_spec() == old(self).remain_spec() - nbytes,
            r.end == old(self).end,
            r.id == old(self).id,
    )]
    pub fn skip(&mut self, nbytes: usize) -> &mut Self {
        assert!(nbytes <= self.remain());
        self.cursor = self.cursor.wrapping_add(nbytes);
        self
    }
}

#[verus_verify]
impl<'a, Fallibility> VmWriter<'a, Fallibility> {
    pub open spec fn avail_spec(&self) -> usize {
        (self.end.vaddr - self.cursor.vaddr) as usize
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
    pub fn cursor(&self) -> VirtPtr {
        self.cursor
    }

    /// Returns if it has available space to write.
    #[verus_spec(
        requires
            self.inv(),
    )]
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

    /// Limits the length of available space.
    ///
    /// This method ensures the post-condition `self.avail() <= max_avail`.
    #[verus_spec(r =>
        requires
            old(self).inv(),
        ensures
            r.inv(),
            r.avail_spec() <= max_avail,
            r.avail_spec() <= old(self).avail_spec(),
            r.cursor == old(self).cursor,
            r.id == old(self).id,
    )]
    pub fn limit(&mut self, max_avail: usize) -> &mut Self {
        if max_avail < self.avail() {
            self.end = self.cursor.wrapping_add(max_avail);
        }
        self
    }

    /// Skips the first `nbytes` of available space.
    ///
    /// The length of available space is decreased accordingly.
    ///
    /// # Panics
    ///
    /// If `nbytes` is greater than `self.avail()`, then the method panics.
    #[verus_spec(r =>
        requires
            old(self).inv(),
            nbytes <= old(self).avail_spec(),
        ensures
            r.inv(),
            r.cursor.vaddr == old(self).cursor.vaddr + nbytes,
            r.avail_spec() == old(self).avail_spec() - nbytes,
            r.end == old(self).end,
            r.id == old(self).id,
    )]
    pub fn skip(&mut self, nbytes: usize) -> &mut Self {
        assert!(nbytes <= self.avail());
        self.cursor = self.cursor.wrapping_add(nbytes);
        self
    }
}

#[verus_verify]
impl<'a> VmWriter<'a, Fallible> {
    /// Constructs a [`VmWriter`] from a pointer and a length, which represents
    /// a memory range in USER space.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - `ptr` must satisfy [`VirtPtr::inv`].
    /// ## Postconditions
    /// - The returned [`VmWriter`] satisfies its invariant.
    /// - The returned writer is associated with a [`VmIoOwner`] that satisfies both [`VmIoOwner::inv`]
    ///   and [`VmWriter::wf`].
    /// - The owner has the same range as `ptr`, has no memory view yet, and is marked as user-space.
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
            -> owner: Tracked<VmIoOwner>,
        ensures
            r.inv_wf(),
            owner@.id == id,
            owner@.range == ptr.range@,
            owner@.mem_view is None,
            !owner@.is_kernel,
            r.cursor == ptr,
            r.end == ptr.wrapping_add_spec(len),
            r.end.range@ == ptr.range@,
            ptr.inv() && ptr.range@.start == ptr.vaddr
                && len == ptr.range@.end - ptr.range@.start ==> {
                &&& r.inv()
                &&& owner@.inv()
                &&& r.wf(owner@)
            },
    )]
    pub unsafe fn from_user_space(ptr: VirtPtr, len: usize) -> Self {
        let tracked owner = VmIoOwner {
            id: Ghost(id),
            range: Ghost(ptr.range@),
            is_fallible: true,
            is_kernel: false,
            mem_view: None,
        };
        proof_with!(|= Tracked(owner));
        Self { id: Ghost(id), cursor: ptr, end: ptr.wrapping_add(len), phantom: PhantomData }
    }

    /// Writes a value of `Pod` type to user space.
    ///
    /// If the underlying memory access faults during the write, the cursor
    /// is rolled back to its starting position before returning `Err`.
    ///
    /// # Verified Properties
    /// ## Postconditions
    /// - On success, the cursor advances by `size_of::<T>()`.
    /// - On error, the cursor is at its original position (writer state preserved).
    #[verus_spec(r =>
        with
            Tracked(reader_owner): Tracked<&mut VmIoOwner>,
        requires
            old(self).inv(),
            old(reader_owner).inv(),
            old(reader_owner).range@.end - old(reader_owner).range@.start >= core::mem::size_of::<T>(),
            old(reader_owner).read_view_initialized(),
        ensures
            final(self).inv(),
            final(self).end == old(self).end,
            final(self).id == old(self).id,
            final(self).cursor.range == old(self).cursor.range,
            final(reader_owner).range@.start == old(reader_owner).range@.start + core::mem::size_of::<T>(),
            final(reader_owner).range@.end == old(reader_owner).range@.end,
            r is Err ==> final(self).cursor.vaddr == old(self).cursor.vaddr,
    )]
    pub fn write_val<T: Pod>(&mut self, new_val: &T) -> Result<()> {
        let len = core::mem::size_of::<T>();
        proof_decl! {
            let tracked mut _temp_r_owner;
        }
        proof {
            _temp_r_owner = reader_owner.split(len);
        }
        if self.avail() < len {
            return Err(Error::InvalidArgs);
        }
        #[verus_spec(with Tracked(&_temp_r_owner))]
        let mut reader = VmReader::from(new_val.as_bytes());
        match self.write_fallible(&mut reader) {
            Ok(_) => Ok(()),
            Err((err, copied_len)) => {
                self.cursor = self.cursor.sub(copied_len);
                Err(err)
            },
        }
    }

    /// Writes `len` zeros to the target memory.
    ///
    /// This method attempts to fill up to `len` bytes with zeros. If the
    /// available memory from the current cursor position is less than `len`,
    /// it will only fill the available space.
    ///
    /// If the memory write failed due to an unresolvable page fault, this
    /// method will return `Err` with the length set so far.
    #[verifier::external_body]
    pub fn fill_zeros(&mut self, len: usize) -> core::result::Result<usize, (Error, usize)> {
        let len_to_set = self.avail().min(len);
        if len_to_set == 0 {
            return Ok(0);
        }

        // SAFETY: The destination is a subset of the memory range specified by
        // the current writer, so it is either valid for writing or in user space.
        let set_len = unsafe { memset_fallible(self.cursor.vaddr as *mut u8, 0u8, len_to_set) };
        self.cursor = self.cursor.wrapping_add(set_len);

        if set_len < len_to_set {
            Err((Error::PageFault, set_len))
        } else {
            Ok(len_to_set)
        }
    }
}

/// Extension trait for byte slices that produces a [`VirtPtr`] covering the
/// slice's bytes. Mirrors the role of [`<[u8]>::as_ptr`] but in our verified
/// pointer model.
pub trait AsVirtPtr {
    fn as_virt_ptr(&self) -> VirtPtr;
}

#[verus_verify]
impl AsVirtPtr for [u8] {
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r.inv(),
            r.range@.start == r.vaddr,
            r.range@.end - r.range@.start == self.len(),
    )]
    fn as_virt_ptr(&self) -> VirtPtr {
        let addr = self.as_ptr() as usize;
        let len = self.len();
        VirtPtr { vaddr: addr, range: Ghost(addr..(addr + len) as usize) }
    }
}

#[verus_verify]
impl<'a> VmWriter<'a, Infallible> {
    /// Constructs a [`VmWriter<'a, Infallible>`] from a mutable byte slice.
    ///
    /// The caller passes a tracked [`VmIoOwner`] whose tracked memory view describes the
    /// slice's bytes — essentially what the `wf` condition would say if `&'a mut [u8]`
    /// implemented `OwnerOf`. The returned writer is then [`Self::wf`] with that owner.
    ///
    /// # Safety
    ///
    /// The slice's memory must be in kernel space and valid for writes during `'a`.
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&VmIoOwner>,
        requires
            owner.inv(),
            owner.range@.end - owner.range@.start == slice.len(),
            owner.has_write_view(),
        ensures
            r.inv(),
            r.wf(*owner),
            r.cursor.range@ == owner.range@,
    )]
    pub fn from(slice: &'a mut [u8]) -> Self {
        // SAFETY:
        // - The memory range points to typed memory.
        // - The validity requirements for write accesses are met because the pointer is converted
        //   from a mutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.
        unsafe { Self::from_kernel_space(slice.as_virt_ptr(), slice.len()) }
    }
}

#[verus_verify]
impl<'a> VmReader<'a, Infallible> {
    /// Constructs a [`VmReader<'a, Infallible>`] from a shared byte slice.
    ///
    /// The caller passes a tracked [`VmIoOwner`] whose tracked memory view describes the
    /// slice's bytes — essentially what the `wf` condition would say if `&'a [u8]`
    /// implemented `OwnerOf`. The returned reader is then [`Self::wf`] with that owner.
    ///
    /// # Safety
    ///
    /// The slice's memory must be in kernel space and valid for reads during `'a`.
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&VmIoOwner>,
        requires
            owner.inv(),
            owner.range@.end - owner.range@.start == slice.len(),
            owner.read_view_initialized(),
        ensures
            r.inv(),
            r.wf(*owner),
            r.cursor.range@ == owner.range@,
    )]
    pub fn from(slice: &'a [u8]) -> Self {
        // SAFETY:
        // - The memory range points to typed memory.
        // - The validity requirements for read accesses are met because the pointer is converted
        //   from a shared reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.
        unsafe { Self::from_kernel_space(slice.as_virt_ptr(), slice.len()) }
    }
}

} // verus!

mod pod_once_impls {
    use super::PodOnce;

    impl PodOnce for u8 {}
    impl PodOnce for u16 {}
    impl PodOnce for u32 {}
    impl PodOnce for u64 {}
    impl PodOnce for usize {}
    impl PodOnce for i8 {}
    impl PodOnce for i16 {}
    impl PodOnce for i32 {}
    impl PodOnce for i64 {}
    impl PodOnce for isize {}

    /// Checks whether the memory operation created by `ptr::read_volatile` and
    /// `ptr::write_volatile` doesn't tear.
    ///
    /// Note that the Rust documentation makes no such guarantee, and even the wording in the LLVM
    /// LangRef is ambiguous. But this is unlikely to break in practice because the Linux kernel
    /// also uses "volatile" semantics to implement `READ_ONCE`/`WRITE_ONCE`.
    pub(super) const fn is_non_tearing<T>() -> bool {
        let size = core::mem::size_of::<T>();

        size == 1 || size == 2 || size == 4 || size == 8
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
                let copy_len = self.remain().min(writer.avail());
                if copy_len == 0 {
                    return Ok(0);
                }

                // SAFETY: The source and destination are subsets of memory ranges specified by
                // the reader and writer, so they are either valid for reading and writing or in
                // user space.
                let copied_len = unsafe {
                    memcpy_fallible(writer.cursor.vaddr as *mut u8, self.cursor.vaddr as *const u8, copy_len)
                };
                self.cursor = self.cursor.wrapping_add(copied_len);
                writer.cursor = writer.cursor.wrapping_add(copied_len);

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
