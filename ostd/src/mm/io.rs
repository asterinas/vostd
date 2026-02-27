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
use crate::specs::arch::PAGE_SIZE;
use core::marker::PhantomData;
use core::ops::Range;
use vstd::pervasive::arbitrary;
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
use crate::specs::mm::page_table::Mapping;
use crate::specs::mm::virt_mem_newer::{MemView, VirtPtr};

verus! {

#[verus_spec(r =>
        with
            Tracked(owner_r): Tracked<&mut VmIoOwner<'_>>,
            Tracked(owner_w): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(reader).inv(),
            old(writer).inv(),
            old(owner_r).inv(),
            old(owner_w).inv(),
            old(owner_r).inv_with_reader(*old(reader)),
            old(owner_w).inv_with_writer(*old(writer)),
            old(owner_r).is_fallible && old(owner_w).is_fallible, // both fallible
        ensures
            reader.inv(),
            writer.inv(),
            owner_r.inv(),
            owner_w.inv(),
            owner_r.inv_with_reader(*reader),
            owner_w.inv_with_writer(*writer),
            owner_r.params_eq(*old(owner_r)),
            owner_w.params_eq(*old(owner_w)),
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
pub struct VmReader<'a  /*, Fallibility = Fallible*/ > {
    pub id: Ghost<nat>,
    pub cursor: VirtPtr,
    pub end: VirtPtr,
    pub phantom: PhantomData<&'a [u8]  /*, Fallibility)*/ >,
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
    /// The mem view associated with this owner.
    // pub mem_view: MemView,
    pub phantom: PhantomData<&'a [u8]  /*, Fallibility)*/ >,
    /// Whether this owner is for kernel space.
    pub is_kernel: bool,
    /// The mem view associated with this owner.
    pub mem_view: Option<VmIoMemView<'a>>,
}

impl Inv for VmIoOwner<'_> {
    open spec fn inv(self) -> bool {
        // We do allow ZSTs so that empty ranges are valid.
        &&& self.range@.start <= self.range@.end
        &&& match self.mem_view {
            // Case 1: Write (exclusive)
            Some(VmIoMemView::WriteView(mv)) => {
                &&& mv.mappings.finite()
                &&& mv.mappings_are_disjoint()
                &&& forall|va: usize|
                    self.range@.start <= va < self.range@.end ==> {
                        &&& #[trigger] mv.addr_transl(va) is Some
                    }
            },
            // Case 2: Read (shared)
            Some(VmIoMemView::ReadView(mv)) => {
                &&& mv.mappings.finite()
                &&& mv.mappings_are_disjoint()
                &&& forall|va: usize|
                    self.range@.start <= va < self.range@.end ==> {
                        &&& #[trigger] mv.addr_transl(va) is Some
                    }
            },
            // Case 3: Empty/Invalid; this means no memory is accessible,
            //         and we are just creating a placeholder.
            None => true,
        }
    }
}

impl VmIoOwner<'_> {
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
    pub proof fn change_fallible(tracked &mut self, tracked fallible: bool)
        requires
            old(self).inv(),
            old(self).is_fallible != fallible,
        ensures
            self.inv(),
            self.is_fallible == fallible,
    {
        self.is_fallible = fallible;
    }

    /// Advances the cursor of the reader/writer by the given number of bytes.
    ///
    /// Note this will return the advanced `VmIoMemView` as the previous permission
    /// is no longer needed and must be discarded then.
    pub proof fn advance(tracked &mut self, nbytes: usize) -> (tracked res: VmIoMemView<'_>)
        requires
            old(self).inv(),
            old(self).mem_view is Some,
            nbytes <= old(self).range@.end - old(self).range@.start,
        ensures
            self.inv(),
            self.range@.start == old(self).range@.start + nbytes,
            self.range@.end == old(self).range@.end,
            self.is_fallible == old(self).is_fallible,
            self.id == old(self).id,
            self.is_kernel == old(self).is_kernel,
    {
        let start = self.range@.start;
        let old_end = self.range@.end;
        self.range = Ghost((start + nbytes) as usize..self.range@.end);
        // Take this option and leaves the `None` in its place temporarily.
        let tracked inner = self.mem_view.tracked_take();
        let tracked ret_perm = match inner {
            VmIoMemView::WriteView(mv) => {
                let tracked (lhs, rhs) = mv.split(start, nbytes);

                assert(forall|va: usize|
                    start <= va < start + nbytes ==> mv.addr_transl(va) is Some);

                // Update the mem view to the remaining part.
                self.mem_view = Some(VmIoMemView::WriteView(rhs));

                assert(self.inv()) by {
                    assert forall|va: usize| start + nbytes <= va < old_end implies {
                        #[trigger] rhs.addr_transl(va) is Some
                    } by {
                        assert(mv.addr_transl(va) is Some) by {
                            assert(old(self).inv());
                        }

                        let old_mappings = mv.mappings.filter(
                            |m: Mapping| m.va_range.start <= va < m.va_range.end,
                        );
                        let new_mappings = rhs.mappings.filter(
                            |m: Mapping| m.va_range.start <= va < m.va_range.end,
                        );
                        assert(old_mappings.len() != 0);
                        assert(rhs.mappings =~= mv.mappings.filter(
                            |m: Mapping| m.va_range.end > start + nbytes,
                        ));
                        assert(new_mappings =~= mv.mappings.filter(
                            |m: Mapping|
                                m.va_range.start <= va < m.va_range.end && m.va_range.end > start
                                    + nbytes,
                        ));

                        assert(new_mappings.len() != 0) by {
                            broadcast use vstd::set::group_set_axioms;

                            let m = old_mappings.choose();
                            // m.start <= va < m.end
                            assert(start + nbytes <= va);
                            assert(m.va_range.end > va) by {
                                if (m.va_range.end <= va) {
                                    assert(!old_mappings.contains(m));
                                }
                            }
                            assert(m.va_range.end > start + nbytes);
                            assert(old_mappings.contains(m));
                            assert(old_mappings.subset_of(mv.mappings));
                            assert(rhs.mappings.contains(m));
                            assert(new_mappings.contains(m));
                            assert(new_mappings.len() >= 1);
                        }
                    }
                }

                VmIoMemView::WriteView(lhs)
            },
            VmIoMemView::ReadView(mv) => {
                let tracked sub_view = mv.borrow_at(start, nbytes);
                // Since reads are shared so we don't need to
                // modify the original view; here we just put
                // it back.
                self.mem_view = Some(VmIoMemView::ReadView(mv));
                VmIoMemView::ReadView(sub_view)
            },
        };

        ret_perm
    }

    /// Unwraps the read view.
    pub proof fn tracked_read_view_unwrap(tracked &self) -> (tracked r: &MemView)
        requires
            self.inv(),
            self.mem_view matches Some(VmIoMemView::ReadView(_)),
        ensures
            VmIoMemView::ReadView(r) == self.mem_view.unwrap(),
    {
        match self.mem_view {
            Some(VmIoMemView::ReadView(r)) => r,
            _ => { proof_from_false() },
        }
    }
}

impl Inv for VmWriter<'_> {
    open spec fn inv(self) -> bool {
        &&& self.cursor.inv()
        &&& self.end.inv()
        &&& self.cursor.vaddr
            <= self.end.vaddr
        // Ensure that they point to the same range as in VmIoOwner.
        &&& self.cursor.range@ == self.end.range@
    }
}

impl Inv for VmReader<'_> {
    open spec fn inv(self) -> bool {
        &&& self.cursor.inv()
        &&& self.end.inv()
        &&& self.cursor.vaddr
            <= self.end.vaddr
        // Ensure that they point to the same range as in VmIoOwner.
        &&& self.cursor.range@ == self.end.range@
    }
}

impl VmIoOwner<'_> {
    pub open spec fn inv_with_reader(
        self,
        reader: VmReader<'_  /* Fallibility */ >,
    ) -> bool {
        &&& self.inv()
        &&& self.range@.start == reader.cursor.vaddr
        &&& self.range@.end == reader.end.vaddr
        &&& self.id == reader.id
        &&& self.mem_view matches Some(VmIoMemView::ReadView(mv)) ==> {
            // Ensure that the mem view covers the entire range.
            forall|va: usize|
                self.range@.start <= va < self.range@.end ==> {
                    &&& #[trigger] mv.addr_transl(va) is Some
                }
        }
    }

    pub open spec fn inv_with_writer(
        self,
        writer: VmWriter<'_  /* Fallibility */ >,
    ) -> bool {
        &&& self.inv()
        &&& self.range@.start == writer.cursor.vaddr
        &&& self.range@.end == writer.end.vaddr
        &&& self.id == writer.id
        &&& self.mem_view matches Some(VmIoMemView::WriteView(mv)) ==> {
            // Ensure that the mem view covers the entire range.
            forall|va: usize|
                self.range@.start <= va < self.range@.end ==> {
                    &&& #[trigger] mv.addr_transl(va) is Some
                }
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
pub struct VmWriter<'a  /*, Fallibility = Fallible*/ > {
    pub id: Ghost<nat>,
    pub cursor: VirtPtr,
    pub end: VirtPtr,
    pub phantom: PhantomData<&'a [u8]  /*, Fallibility)*/ >,
}

#[verus_verify]
impl<'a> VmWriter<'a  /* Infallible */ > {
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
            owner@.inv_with_writer(r),
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
                    &&& owner.inv_with_writer(r)
                }
            }
    )]
    pub fn from_pod<T: Pod>(mut val: T) -> Result<VmWriter<'a  /* Infallible */ >> {
        proof_decl! {
            let tracked mut perm;
        }

        let (pnt, len) = val.as_bytes_mut();

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
}

impl Clone for VmReader<'_  /* Fallibility */ > {
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
impl<'a> VmReader<'a  /* Infallible */ > {
    /// Constructs a [`VmReader`] from a pointer and a length, which represents
    /// a memory range in USER space.
    ///
    /// ⚠️ WARNING: Currently not implemented yet.
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
            -> owner: Tracked<VmIoOwner<'a>>,
        requires
            ptr.inv(),
        ensures
            r.inv(),
            owner@.id == id,
            owner@.inv(),
            owner@.inv_with_reader(r),
            owner@.range == ptr.range@,
            owner@.mem_view is None,
            !owner@.is_kernel,
            !owner@.is_fallible,
    )]
    pub unsafe fn from_user_space(ptr: VirtPtr) -> Self {
        // SAFETY: The caller must ensure the safety requirements.
        unimplemented!()
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
            owner@.inv_with_reader(r),
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

        let ghost range = ptr.vaddr..(ptr.vaddr + len) as usize;
        let end = VirtPtr { vaddr: ptr.vaddr + len, range: Ghost(range) };

        proof_with!(|= Tracked(owner));
        Self { id: Ghost(id), cursor: ptr, end, phantom: PhantomData }
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
                    &&& owner.inv_with_reader(r)
                }
            }
    )]
    pub fn from_pod<T: Pod>(val: &mut T) -> Result<VmReader<'a  /* Infallible */ >> {
        proof_decl! {
            let tracked mut perm;
        }

        let (pnt, len) = val.as_bytes_mut();

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
}

#[verus_verify]
impl<'a> TryFrom<&'a [u8]> for VmReader<'a  /* Infallible */ > {
    type Error = Error;

    #[verus_spec()]
    fn try_from(slice: &'a [u8]) -> Result<Self> {
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
        // - The validity requirements for read accesses are met because the pointer is converted
        //   from an immutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.

        let ghost range = addr..(addr + slice.len()) as usize;
        let vptr = VirtPtr { vaddr: addr, range: Ghost(range) };

        Ok(
            unsafe {
                #[verus_spec(with Ghost(arbitrary()) => Tracked(perm))]
                Self::from_kernel_space(vptr, slice.len())
            },
        )
    }
}

impl<'a> TryFromSpecImpl<&'a [u8]> for VmReader<'a> {
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
                    // Id is not important here.
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

// Perhaps we can implement `tryfrom` instead.
// This trait method should be discarded as we do not want to make VmWriter <N> ?
#[verus_verify]
impl<'a> TryFrom<&'a [u8]> for VmWriter<'a  /* Infallible */ > {
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

impl<'a> TryFromSpecImpl<&'a [u8]> for VmWriter<'a> {
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
    // spec fn reader_inv_with_owner(self, owner: VmIoOwner<'_>) -> bool;
    /// If this returns true then the `requires` clause of `read` will be active.
    spec fn obeys_vmio_read_requires() -> bool;

    /// If this returns true then the `ensures` clause of `read` will be active.
    spec fn obeys_vmio_read_ensures() -> bool;

    /// If this returns true then the `requires` clause of `write` will be active.
    spec fn obeys_vmio_write_requires() -> bool;

    /// If this returns true then the `ensures` clause of `write` will be active.
    spec fn obeys_vmio_write_ensures() -> bool;

    /// Checks whether the preconditions for `read` are met.
    spec fn vmio_read_requires(self, owner: P, offset: usize) -> bool;

    /// Checks whether the postconditions for `read` are met.
    spec fn vmio_read_ensures(self, owner: P, offset: usize, new_owner: P, r: Result<()>) -> bool;

    /// Checks whether the preconditions for `write` are met.
    spec fn vmio_write_requires(self, owner: P, offset: usize) -> bool;

    /// Checks whether the postconditions for `write` are met.
    spec fn vmio_write_ensures(self, owner: P, offset: usize, new_owner: P, r: Result<()>) -> bool;

    fn read_slice<T: Pod, const N: usize>(
        &self,
        offset: usize,
        slice: ArrayPtr<T, N>,
        Tracked(slice_owner): Tracked<&mut PointsToArray<u8, N>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> (r: Result<()>);

    fn write_bytes<const N: usize>(
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

    fn write_val<T: Pod>(&self, offset: usize, val: T, Tracked(owner): Tracked<&mut P>) -> (r:
        Result<()>)
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

    fn write_slice<T: Pod, const N: usize>(
        &self,
        offset: usize,
        slice: ArrayPtr<T, N>,
        Tracked(slice_owner): Tracked<&mut PointsToArray<T, N>>,
        Tracked(owner): Tracked<&mut P>,
    ) -> (r: Result<()>)
        requires
            Self::obeys_vmio_write_requires() ==> Self::vmio_write_requires(
                *self,
                *old(owner),
                offset,
            ),
        ensures
            Self::obeys_vmio_write_ensures() ==> Self::vmio_write_ensures(
                *self,
                *old(owner),
                offset,
                *owner,
                r,
            ),
    ;
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
impl VmReader<'_> {
    pub open spec fn remain_spec(&self) -> usize {
        (self.end.vaddr - self.cursor.vaddr) as usize
    }

    /// Returns the number of remaining bytes that can be read.
    #[inline]
    #[verus_spec(r =>
        requires
            self.inv(),
        ensures
            r == self.remain_spec(),
    )]
    #[verifier::when_used_as_spec(remain_spec)]
    pub fn remain(&self) -> usize {
        self.end.vaddr - self.cursor.vaddr
    }

    /// Advances the cursor by `len` bytes. Requires that there are at least `len` bytes remaining.
    #[inline]
    #[verus_spec(
        requires
            old(self).inv(),
            len <= old(self).remain_spec(),
        ensures
            self.inv(),
            self.cursor.vaddr == old(self).cursor.vaddr + len,
            self.remain_spec() == old(self).remain_spec() - len,
            self.id == old(self).id,
            self.end == old(self).end,
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
    #[verus_spec(r =>
        with
            Tracked(owner_r): Tracked<&mut VmIoOwner<'_>>,
            Tracked(owner_w): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(writer).inv(),
            old(owner_r).inv(),
            old(owner_w).inv(),
            old(owner_r).inv_with_reader(*old(self)),
            old(owner_w).inv_with_writer(*old(writer)),
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
            self.inv(),
            writer.inv(),
            owner_r.inv(),
            owner_w.inv(),
            owner_r.inv_with_reader(*self),
            owner_w.inv_with_writer(*writer),
            r == vstd::math::min(old(self).remain_spec() as int, old(writer).avail_spec() as int),
            self.remain_spec() == old(self).remain_spec() - r as usize,
            self.cursor.vaddr == old(self).cursor.vaddr + r as usize,
            writer.avail_spec() == old(writer).avail_spec() - r as usize,
            writer.cursor.vaddr == old(writer).cursor.vaddr + r as usize,
    )]
    pub fn read(&mut self, writer: &mut VmWriter) -> usize {
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
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
            Tracked(owner): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(owner).inv(),
            old(owner).inv_with_reader(*old(self)),
            old(owner).mem_view is Some,
        ensures
            self.inv(),
            owner.inv(),
            owner.inv_with_reader(*self),
            owner.params_eq(*old(owner)),
            match r {
                Ok(_) => {
                    &&& self.remain_spec() == old(self).remain_spec() - core::mem::size_of::<T>()
                    &&& self.cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                },
                Err(_) => {
                    *old(self) == *self
                },
            }
    )]
    pub fn read_val<T: Pod>(&mut self) -> Result<T> {
        if self.remain() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        let mut v = T::new_uninit();
        proof_with!(Ghost(id) => Tracked(owner_w));
        let mut writer = VmWriter::from_pod(v)?;

        let tracked mut owner_w = owner_w.tracked_unwrap();

        proof_with!(Tracked(owner), Tracked(&mut owner_w));
        self.read(&mut writer);

        Ok(v)
    }

    #[verifier::external_body]
    #[verus_spec(
        requires
            self.inv(),
            core::mem::size_of::<T>() <= self.remain_spec(),
    )]
    fn read_once_inner<T: PodOnce>(&self) -> T {
        let pnt = self.cursor.vaddr as *const T;
        unsafe { pnt.read_volatile() }
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
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(owner).mem_view is Some,
            old(owner).inv(),
            old(owner).inv_with_reader(*old(self)),
        ensures
            self.inv(),
            owner.inv(),
            owner.inv_with_reader(*self),
            match r {
                Ok(_) => {
                    &&& self.remain_spec() == old(self).remain_spec() - core::mem::size_of::<T>()
                    &&& self.cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                },
                Err(_) => {
                    *old(self) == *self
                },
            }
    )]
    pub fn read_val_once<T: PodOnce>(&mut self) -> Result<T> {
        if core::mem::size_of::<T>() > self.remain() {
            return Err(Error::InvalidArgs);
        }
        // SAFETY: We have checked that the number of bytes remaining is at least the size of `T`
        // and that the cursor is properly aligned with respect to the type `T`. All other safety
        // requirements are the same as for `Self::read`.

        let v = self.read_once_inner::<T>();
        self.advance(core::mem::size_of::<T>());

        proof {
            owner.advance(core::mem::size_of::<T>());
        }

        Ok(v)
    }
}

#[verus_verify]
impl<'a> VmWriter<'a> {
    pub open spec fn avail_spec(&self) -> usize {
        (self.end.vaddr - self.cursor.vaddr) as usize
    }

    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
            -> owner: Tracked<VmIoOwner<'a>>,
        requires
            ptr.inv(),
        ensures
            r.inv(),
            owner@.id == id,
            owner@.inv(),
            owner@.inv_with_writer(r),
            owner@.range == ptr.range@,
            owner@.mem_view is None,
            !owner@.is_kernel,
            !owner@.is_fallible,
    )]
    pub unsafe fn from_user_space(ptr: VirtPtr) -> Self {
        // SAFETY: The caller must ensure the safety requirements.
        unimplemented!()
    }

    /// Returns the number of available bytes that can be written.
    ///
    /// This has the same implementation as [`VmReader::remain`] but semantically
    /// they are different.
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

    /// Advances the cursor by `len` bytes. Requires that there are at least `len` bytes available.
    #[inline]
    #[verus_spec(
        requires
            old(self).inv(),
            len <= old(self).avail_spec(),
        ensures
            self.inv(),
            self.avail_spec() == old(self).avail_spec() - len,
            self.cursor.vaddr == old(self).cursor.vaddr + len,
            self.cursor.range@ == old(self).cursor.range@,
            self.id == old(self).id,
            self.end == old(self).end,
            self.cursor.range@ == old(self).cursor.range@,
    )]
    pub fn advance(&mut self, len: usize) {
        self.cursor.vaddr = self.cursor.vaddr + len;
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
    #[inline]
    #[verus_spec(r =>
        with
            Tracked(owner_w): Tracked<&mut VmIoOwner<'_>>,
            Tracked(owner_r): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(reader).inv(),
            old(owner_w).inv(),
            old(owner_r).inv(),
            old(owner_w).inv_with_writer(*old(self)),
            old(owner_r).inv_with_reader(*old(reader)),
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
            self.inv(),
            reader.inv(),
            owner_w.inv(),
            owner_r.inv(),
            owner_w.inv_with_writer(*self),
            owner_r.inv_with_reader(*reader),
            r == vstd::math::min(old(self).avail_spec() as int, old(reader).remain_spec() as int),
            self.avail_spec() == old(self).avail_spec() - r as usize,
            self.cursor.vaddr == old(self).cursor.vaddr + r as usize,
            reader.remain_spec() == old(reader).remain_spec() - r as usize,
            reader.cursor.vaddr == old(reader).cursor.vaddr + r as usize,
    )]
    pub fn write(&mut self, reader: &mut VmReader) -> usize {
        proof_with!(Tracked(owner_r), Tracked(owner_w));
        reader.read(self)
    }

    /// Writes a value of `Pod` type.
    ///
    /// If the length of the `Pod` type exceeds `self.avail()`,
    /// this method will return `Err`.
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Ghost(id): Ghost<nat>,
            Tracked(owner_w): Tracked<&mut VmIoOwner<'_>>,
            Tracked(memview_r): Tracked<&MemView>,
        requires
            old(self).inv(),
            old(owner_w).inv(),
            old(owner_w).inv_with_writer(*old(self)),
            old(owner_w).mem_view is Some,
        ensures
            self.inv(),
            owner_w.inv(),
            owner_w.inv_with_writer(*self),
            owner_w.params_eq(*old(owner_w)),
            match r {
                Ok(_) => {
                    &&& self.avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
                    &&& self.cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                },
                Err(_) => {
                    *old(self) == *self
                },
            }
    )]
    pub fn write_val<T: Pod>(&mut self, val: &mut T) -> Result<()> {
        if self.avail() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        proof_with!(Ghost(id) => Tracked(owner_r));
        let mut reader = VmReader::from_pod(val)?;

        let tracked mut owner_r = owner_r.tracked_unwrap();

        proof_with!(Tracked(owner_w), Tracked(&mut owner_r));
        self.write(&mut reader);

        Ok(())
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

    #[verus_spec(r =>
        with
            Tracked(owner_w): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(owner_w).mem_view is Some,
            old(owner_w).inv(),
            old(owner_w).inv_with_writer(*old(self)),
        ensures
            self.inv(),
            owner_w.inv(),
            owner_w.inv_with_writer(*self),
            match r {
                Ok(_) => {
                    &&& self.avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
                    &&& self.cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                },
                Err(_) => {
                    *old(self) == *self
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

} // verus!
