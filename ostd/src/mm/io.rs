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
use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::std_specs::convert::TryFromSpecImpl;
use vstd_extra::array_ptr::ArrayPtr;
use vstd_extra::array_ptr::PointsToArray;
use vstd_extra::ownership::Inv;

use core::marker::PhantomData;
use core::ops::Range;

use crate::mm::pod::{Pod, PodOnce};
use crate::aster_common::{KERNEL_BASE_VADDR, KERNEL_END_VADDR};

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
pub fn rw_fallible(reader: &mut VmReader<'_>, writer: &mut VmWriter<'_>) ->
    core::result::Result<usize, (crate::mm::Error, usize)> {
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
        KERNEL_BASE_VADDR <= dst && dst + len <= KERNEL_END_VADDR,
        KERNEL_BASE_VADDR <= src && src + len <= KERNEL_END_VADDR,
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

/// `VmReader` is a reader for reading data from a contiguous range of memory.
///
/// The memory range read by `VmReader` can be in either kernel space or user space.
/// When the operating range is in kernel space, the memory within that range
/// is guaranteed to be valid, and the corresponding memory reads are infallible.
/// When the operating range is in user space, it is ensured that the page table of
/// the process creating the `VmReader` is active for the duration of `'a`,
/// and the corresponding memory reads are considered fallible.
///
/// When perform reading with a `VmWriter`, if one of them represents typed memory,
/// it can ensure that the reading range in this reader and writing range in the
/// writer are not overlapped.
///
/// NOTE: The overlap mentioned above is at both the virtual address level
/// and physical address level. There is not guarantee for the operation results
/// of `VmReader` and `VmWriter` in overlapping untyped addresses, and it is
/// the user's responsibility to handle this situation.
#[rustc_has_incoherent_inherent_impls]
pub struct VmReader<'a  /*, Fallibility = Fallible*/ > {
    pub cursor: PPtr<u8>,
    pub end: PPtr<u8>,
    pub phantom: PhantomData<&'a [u8]  /*, Fallibility)*/>,
    // if so, we must also make it
    // phantom <ArrayPtr<u8, N>>???
    // phantaom: PhantomData<PointsToArray<u8, N>>, ? // what should be here?
}

/// This looks like we can implement a single struct with a type parameter
#[rustc_has_incoherent_inherent_impls]
pub tracked struct VmIoOwner<'a> {
    pub range: Ghost<Range<int>>,
    /// Whether this reader is fallible.
    pub is_fallible: bool,
    pub phantom: PhantomData<&'a [u8]  /*, Fallibility)*/ >,
}

impl Inv for VmIoOwner<'_> {
    open spec fn inv(self) -> bool {
        // We do allow ZSTs so that empty ranges are valid.
        &&& self.range@.start != self.range@.end ==> KERNEL_BASE_VADDR as int <= self.range@.start
            <= self.range@.end <= KERNEL_END_VADDR as int
    }
}

impl VmIoOwner<'_> {
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
}

impl Inv for VmWriter<'_> {
    open spec fn inv(self) -> bool {
        &&& self.cursor.addr() <= self.end.addr()
    }
}

impl Inv for VmReader<'_> {
    open spec fn inv(self) -> bool {
        &&& self.cursor.addr() <= self.end.addr()
    }
}

impl VmIoOwner<'_> {
    pub open spec fn inv_with_reader(
        self,
        reader: VmReader<'_  /* Fallibility */ >,
    ) -> bool {
        &&& self.inv()
        &&& self.range@.start as usize <= reader.cursor.addr()
        &&& reader.end.addr() <= self.range@.end as usize
    }

    pub open spec fn inv_with_writer(
        self,
        writer: VmWriter<'_  /* Fallibility */ >,
    ) -> bool {
        &&& self.inv()
        &&& self.range@.start as usize <= writer.cursor.addr()
        &&& writer.end.addr() <= self.range@.end as usize
    }
}

/// `VmWriter` is a writer for writing data to a contiguous range of memory.
///
/// The memory range write by `VmWriter` can be in either kernel space or user space.
/// When the operating range is in kernel space, the memory within that range
/// is guaranteed to be valid, and the corresponding memory writes are infallible.
/// When the operating range is in user space, it is ensured that the page table of
/// the process creating the `VmWriter` is active for the duration of `'a`,
/// and the corresponding memory writes are considered fallible.
///
/// When perform writing with a `VmReader`, if one of them represents typed memory,
/// it can ensure that the writing range in this writer and reading range in the
/// reader are not overlapped.
///
/// NOTE: The overlap mentioned above is at both the virtual address level
/// and physical address level. There is not guarantee for the operation results
/// of `VmReader` and `VmWriter` in overlapping untyped addresses, and it is
/// the user's responsibility to handle this situation.
#[rustc_has_incoherent_inherent_impls]
pub struct VmWriter<'a  /*, Fallibility = Fallible*/ > {
    pub cursor: PPtr<u8>,
    pub end: PPtr<u8>,
    pub phantom: PhantomData<&'a [u8]  /*, Fallibility)*/ >,
}

#[verus_verify]
impl<'a> VmWriter<'a  /* Infallible */ > {
    /// Constructs a `VmWriter` from a pointer and a length, which represents
    /// a memory range in kernel space.
    ///
    /// # Safety
    ///
    /// `ptr` must be [valid] for writes of `len` bytes during the entire lifetime `a`.
    ///
    /// [valid]: crate::mm::io#safety
    #[rustc_allow_incoherent_impl]
    #[verus_spec(r =>
        with
            Tracked(fallible): Tracked<bool>,
                -> owner: Tracked<VmIoOwner<'a>>,
        requires
            !fallible,
            len == 0 || KERNEL_BASE_VADDR <= ptr.addr(),
            len == 0 || ptr.addr() + len <= KERNEL_END_VADDR,
        ensures
            owner@.inv(),
            owner@.inv_with_writer(r),
            owner@.is_fallible == fallible,
            r.cursor.addr() == ptr.addr(),
            r.end.addr() == ptr.addr() + len,
    )]
    pub unsafe fn from_kernel_space(ptr: PPtr<u8>, len: usize) -> Self {
        let tracked owner = VmIoOwner {
            range: Ghost((ptr.addr() as int)..((ptr.addr() + len) as int)),
            is_fallible: fallible,
            phantom: PhantomData,
        };

        proof_with!(|= Tracked(owner));
        Self {
            cursor: ptr,
            end: PPtr(ptr.addr().checked_add(len).unwrap(), PhantomData),
            phantom: PhantomData,
        }
    }

    #[verus_spec(r =>
        with
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

        let (pnt, len) = val.as_bytes_mut();  // do not return a slice but a iteratorptr

        if len != 0 && (pnt.addr() < KERNEL_BASE_VADDR || len >= KERNEL_END_VADDR || pnt.addr()
            > KERNEL_END_VADDR - len) {
            proof_with!(|= Tracked(Err(crate::mm::Error::IoError)));
            Err(crate::mm::Error::IoError)
        } else {
            let r = unsafe {
                #[verus_spec(with Tracked(false) => Tracked(perm))]
                VmWriter::from_kernel_space(PPtr(pnt.addr(), PhantomData), len)
            };

            proof_with!(|= Tracked(Ok(perm)));
            Ok(r)
        }
    }
}

// `Clone` can be implemented for `VmReader`
// because it either points to untyped memory or represents immutable references.
// Note that we cannot implement `Clone` for `VmWriter`
// because it can represent mutable references, which must remain exclusive.
impl Clone for VmReader<'_  /* Fallibility */ > {
    fn clone(&self) -> Self {
        Self { cursor: self.cursor, end: self.end, phantom: PhantomData }
    }
}

#[verus_verify]
impl<'a> VmReader<'a  /* Infallible */ > {
    /// Constructs a `VmReader` from a pointer and a length, which represents
    /// a memory range in kernel space.
    ///
    /// # Safety
    ///
    /// `ptr` must be [valid] for reads of `len` bytes during the entire lifetime `a`.
    ///
    /// [valid]: crate::mm::io#safety
    #[rustc_allow_incoherent_impl]
    #[verus_spec(r =>
        with
            -> owner: Tracked<VmIoOwner<'a>>,
        requires
            len == 0 || KERNEL_BASE_VADDR <= ptr.addr(),
            len == 0 || ptr.addr() + len <= KERNEL_END_VADDR,
        ensures
            owner@.inv(),
            owner@.inv_with_reader(r),
            r.cursor.addr() == ptr.addr(),
            r.end.addr() == ptr.addr() + len,
    )]
    pub unsafe fn from_kernel_space(ptr: PPtr<u8>, len: usize) -> Self {
        let tracked owner = VmIoOwner {
            range: Ghost((ptr.addr() as int)..((ptr.addr() + len) as int)),
            is_fallible: false,
            phantom: PhantomData,
        };

        proof_with!(|= Tracked(owner));
        Self {
            cursor: ptr,
            end: PPtr(ptr.addr().checked_add(len).unwrap(), PhantomData),
            phantom: PhantomData,
        }
    }

    #[verus_spec(r =>
        with
            -> owner: Tracked<Result<VmIoOwner<'a>>>,
        ensures
            r is Ok <==> owner@ is Ok,
            r matches Ok(r) ==> {
                &&& owner@ matches Ok(owner) ==> {
                    &&& r.inv()
                    &&& r.remain_spec() == core::mem::size_of::<T>()
                    &&& owner.inv()
                    &&& owner.inv_with_reader(r)
                    // &&& r.cursor.addr() == ptr.addr(),
                    // &&& r.end.addr() == ptr.addr() + len,
                }
            }
    )]
    pub fn from_pod<T: Pod>(val: &mut T) -> Result<VmReader<'a  /* Infallible */ >> {
        proof_decl! {
            let tracked mut perm;
        }

        let (pnt, len) = val.as_bytes_mut();

        if len != 0 && (pnt.addr() < KERNEL_BASE_VADDR || len >= KERNEL_END_VADDR || pnt.addr()
            > KERNEL_END_VADDR - len) {
            proof_with!(|= Tracked(Err(crate::mm::Error::IoError)));
            Err(crate::mm::Error::IoError)
        } else {
            let r = unsafe {
                #[verus_spec(with => Tracked(perm))]
                VmReader::from_kernel_space(PPtr(pnt.addr(), PhantomData), len)
            };

            proof_with!(|= Tracked(Ok(perm)));
            Ok(r)
        }
    }
}

#[verus_verify]
impl<'a> TryFrom<&'a [u8]> for VmReader<'a  /* Infallible */ > {
    type Error = crate::mm::Error;

    #[verus_spec()]
    fn try_from(slice: &'a [u8]) -> Result<Self> {
        proof_decl! {
            let tracked mut perm;
        }

        let addr = slice.as_ptr() as usize;

        if slice.len() != 0 && (addr < KERNEL_BASE_VADDR || slice.len() >= KERNEL_END_VADDR
            || addr > KERNEL_END_VADDR - slice.len()) {
            return Err(crate::mm::Error::IoError);
        }
        // SAFETY:
        // - The memory range points to typed memory.
        // - The validity requirements for read accesses are met because the pointer is converted
        //   from an immutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.

        Ok(
            unsafe {
                #[verus_spec(with => Tracked(perm))]
                Self::from_kernel_space(PPtr(addr, PhantomData), slice.len())
            },
        )
    }
}

impl<'a> TryFromSpecImpl<&'a [u8]> for VmReader<'a> {
    open spec fn obeys_try_from_spec() -> bool {
        true
    }

    open spec fn try_from_spec(slice: &'a [u8]  /* length.. */ ) -> Result<Self> {
        let addr = slice.as_ptr() as usize;
        let len = slice.len();

        if len != 0 && (addr < KERNEL_BASE_VADDR || len >= KERNEL_END_VADDR || addr
            > KERNEL_END_VADDR - slice.len()) {
            Err(crate::mm::Error::IoError)
        } else {
            Ok(
                Self {
                    cursor: PPtr(addr, PhantomData),
                    end: PPtr((addr + len) as usize, PhantomData),
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
    type Error = crate::mm::Error;

    // fn try_from(slice: ArrayPtr<u8, N>, Tracked(owner))??
    #[verus_spec()]
    fn try_from(slice: &'a [u8]  /* length... */ ) -> Result<Self> {
        proof_decl! {
            let tracked mut perm;
        }

        let addr = slice.as_ptr() as usize;

        if slice.len() != 0 && (addr < KERNEL_BASE_VADDR || slice.len() >= KERNEL_END_VADDR
            || addr > KERNEL_END_VADDR - slice.len()) {
            return Err(crate::mm::Error::IoError);
        }
        // SAFETY:
        // - The memory range points to typed memory.
        // - The validity requirements for write accesses are met because the pointer is converted
        //   from a mutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.

        Ok(
            unsafe {
                #[verus_spec(with Tracked(false) => Tracked(perm))]
                Self::from_kernel_space(PPtr(addr, PhantomData), slice.len())
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
            > KERNEL_END_VADDR - slice.len()) {
            Err(crate::mm::Error::IoError)
        } else {
            Ok(
                Self {
                    cursor: PPtr(addr, PhantomData),
                    end: PPtr((addr + len) as usize, PhantomData),
                    phantom: PhantomData,
                },
            )
        }

    }
}

type Result<T> = core::result::Result<T, crate::mm::Error>;

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
        (self.end.addr() - self.cursor.addr()) as usize
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
        self.end.addr() - self.cursor.addr()
    }

    /// Advances the cursor by `len` bytes. Requires that there are at least `len` bytes remaining.
    #[inline]
    #[verus_spec(
        requires
            old(self).inv(),
            len <= old(self).remain_spec(),
        ensures
            self.inv(),
            self.cursor.addr() == old(self).cursor.addr() + len,
            self.remain_spec() == old(self).remain_spec() - len,
    )]
    pub fn advance(&mut self, len: usize) {
        self.cursor = PPtr(self.cursor.addr() + len, PhantomData);
    }

    /// Reads all data into the writer until one of the two conditions is met:
    /// 1. The reader has no remaining data.
    /// 2. The writer has no available space.
    ///
    /// Returns the number of bytes read.
    #[rustc_allow_incoherent_impl]
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
        ensures
            self.inv(),
            writer.inv(),
            owner_r.inv(),
            owner_w.inv(),
            owner_r.inv_with_reader(*self),
            owner_w.inv_with_writer(*writer),
            owner_r.params_eq(*old(owner_r)),
            owner_w.params_eq(*old(owner_w)),
            r == vstd::math::min(old(self).remain_spec() as int, old(writer).avail_spec() as int),
            self.remain_spec() == old(self).remain_spec() - r as usize,
            self.cursor.addr() == old(self).cursor.addr() + r as usize,
            writer.avail_spec() == old(writer).avail_spec() - r as usize,
            writer.cursor.addr() == old(writer).cursor.addr() + r as usize,
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
        // SAFETY: The source and destination are subsets of memory ranges specified by the reader
        // and writer (owners), so they are valid for reading and writing.

        unsafe {
            memcpy(writer.cursor.addr(), self.cursor.addr(), copy_len);
        }

        self.advance(copy_len);
        writer.advance(copy_len);

        copy_len
    }

    /// Reads a value of `Pod` type.
    ///
    /// If the length of the `Pod` type exceeds `self.remain()`,
    /// this method will return `Err`.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(owner).inv(),
            old(owner).inv_with_reader(*old(self)),
        ensures
            self.inv(),
            owner.inv(),
            owner.inv_with_reader(*self),
            owner.params_eq(*old(owner)),
            match r {
                Ok(_) => {
                    &&& self.remain_spec() == old(self).remain_spec() - core::mem::size_of::<T>()
                    &&& self.cursor.addr() == old(self).cursor.addr() + core::mem::size_of::<T>()
                },
                Err(_) => {
                    old(self) == self
                },
            }
    )]
    pub fn read_val<T: Pod>(&mut self) -> Result<T> {
        if self.remain() < core::mem::size_of::<T>() {
            return Err(crate::mm::Error::InvalidArgs);
        }
        let mut v = T::new_uninit();
        proof_with!(=> Tracked(owner_w));
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
        let pnt = self.cursor.addr() as *const T;
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
            old(owner).inv(),
            old(owner).inv_with_reader(*old(self)),
        ensures
            self.inv(),
            owner.inv(),
            owner.inv_with_reader(*self),
            owner.params_eq(*old(owner)),
            match r {
                Ok(_) => {
                    &&& self.remain_spec() == old(self).remain_spec() - core::mem::size_of::<T>()
                    &&& self.cursor.addr() == old(self).cursor.addr() + core::mem::size_of::<T>()
                },
                Err(_) => {
                    old(self) == self
                },
            }
    )]
    pub fn read_val_once<T: PodOnce>(&mut self) -> Result<T> {
        if core::mem::size_of::<T>() > self.remain() {
            return Err(crate::mm::Error::InvalidArgs);
        }
        // SAFETY: We have checked that the number of bytes remaining is at least the size of `T`
        // and that the cursor is properly aligned with respect to the type `T`. All other safety
        // requirements are the same as for `Self::read`.

        let v = self.read_once_inner::<T>();
        self.advance(core::mem::size_of::<T>());

        Ok(v)
    }
}

impl VmWriter<'_> {
    pub open spec fn avail_spec(&self) -> usize {
        (self.end.addr() - self.cursor.addr()) as usize
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
        self.end.addr() - self.cursor.addr()
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
            self.cursor.addr() == old(self).cursor.addr() + len,
    )]
    pub fn advance(&mut self, len: usize) {
        self.cursor = PPtr(self.cursor.addr() + len, PhantomData);
    }

    /// Writes all data from the reader until one of the two conditions is met:
    /// 1. The reader has no remaining data.
    /// 2. The writer has no available space.
    ///
    /// Returns the number of bytes written.
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
        ensures
            self.inv(),
            reader.inv(),
            owner_w.inv(),
            owner_r.inv(),
            owner_w.inv_with_writer(*self),
            owner_r.inv_with_reader(*reader),
            owner_w.params_eq(*old(owner_w)),
            owner_r.params_eq(*old(owner_r)),
            r == vstd::math::min(old(self).avail_spec() as int, old(reader).remain_spec() as int),
            self.avail_spec() == old(self).avail_spec() - r as usize,
            self.cursor.addr() == old(self).cursor.addr() + r as usize,
            reader.remain_spec() == old(reader).remain_spec() - r as usize,
            reader.cursor.addr() == old(reader).cursor.addr() + r as usize,
    )]
    pub fn write(&mut self, reader: &mut VmReader) -> usize {
        proof_with!(Tracked(owner_r), Tracked(owner_w));
        reader.read(self)
    }

    /// Writes a value of `Pod` type.
    ///
    /// If the length of the `Pod` type exceeds `self.avail()`,
    /// this method will return `Err`.
    #[verus_spec(r =>
        with
            Tracked(owner_w): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(owner_w).inv(),
            old(owner_w).inv_with_writer(*old(self)),
        ensures
            self.inv(),
            owner_w.inv(),
            owner_w.inv_with_writer(*self),
            owner_w.params_eq(*old(owner_w)),
            match r {
                Ok(_) => {
                    &&& self.avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
                    &&& self.cursor.addr() == old(self).cursor.addr() + core::mem::size_of::<T>()
                },
                Err(_) => {
                    old(self) == self
                },
            }
    )]
    pub fn write_val<T: Pod>(&mut self, val: &mut T) -> Result<()> {
        if self.avail() < core::mem::size_of::<T>() {
            return Err(crate::mm::Error::InvalidArgs);
        }
        proof_with!(=> Tracked(owner_r));
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
        let cursor = self.cursor.addr() as *mut T;
        unsafe { cursor.write_volatile(*new_val) };
    }

    #[verus_spec(r =>
        with
            Tracked(owner_w): Tracked<&mut VmIoOwner<'_>>,
        requires
            old(self).inv(),
            old(owner_w).inv(),
            old(owner_w).inv_with_writer(*old(self)),
        ensures
            self.inv(),
            owner_w.inv(),
            owner_w.inv_with_writer(*self),
            owner_w.params_eq(*old(owner_w)),
            match r {
                Ok(_) => {
                    &&& self.avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
                    &&& self.cursor.addr() == old(self).cursor.addr() + core::mem::size_of::<T>()
                },
                Err(_) => {
                    old(self) == self
                },
            }
    )]
    pub fn write_once<T: PodOnce>(&mut self, new_val: &mut T) -> Result<()> {
        if core::mem::size_of::<T>() > self.avail() {
            return Err(crate::mm::Error::InvalidArgs);
        }
        // SAFETY: We have checked that the number of bytes available is at least the size of `T`
        // and that the cursor is properly aligned with respect to the type `T`. All other safety
        // requirements are the same as for `Self::write`.

        self.write_once_inner::<T>(new_val);
        self.advance(core::mem::size_of::<T>());

        Ok(())
    }
}

} // verus!
// pub trait VmIo: Send + Sync {
//     /// Reads a slice of a specified type at a specified offset.
//     ///
//     /// # No short reads
//     ///
//     /// Similar to [`read`].
//     ///
//     /// [`read`]: VmIo::read
//     fn read_slice<T>(&self, offset: usize, slice: &mut [T]) -> Result<()> {
//         let len_in_bytes = core::mem::size_of_val(slice);
//         let ptr = slice as *mut [T] as *mut u8;
//         // SAFETY: the slice can be transmuted to a writable byte slice since the elements
//         // are all Plain-Old-Data (Pod) types.
//         let buf = unsafe { core::slice::from_raw_parts_mut(ptr, len_in_bytes) };
//         self.read_bytes(offset, buf)
//     }
//     /// Writes a specified number of bytes from a given buffer at a specified offset.
//     ///
//     /// # No short writes
//     ///
//     /// Similar to [`write`].
//     ///
//     /// [`write`]: VmIo::write
//     fn write_bytes(&self, offset: usize, buf: &[u8]) -> Result<()> {
//         let mut reader = VmReader::from(buf).to_fallible();
//         self.write(offset, &mut reader)
//     }
//     /// Writes a value of a specified type at a specified offset.
//     fn write_val<T>(&self, offset: usize, new_val: &T) -> Result<()> {
//         self.write_bytes(offset, new_val.as_bytes())?;
//         Ok(())
//     }
//     /// Writes a slice of a specified type at a specified offset.
//     ///
//     /// # No short write
//     ///
//     /// Similar to [`write`].
//     ///
//     /// [`write`]: VmIo::write
//     fn write_slice<T>(&self, offset: usize, slice: &[T]) -> Result<()> {
//         let len_in_bytes = core::mem::size_of_val(slice);
//         let ptr = slice as *const [T] as *const u8;
//         // SAFETY: the slice can be transmuted to a readable byte slice since the elements
//         // are all Plain-Old-Data (Pod) types.
//         let buf = unsafe { core::slice::from_raw_parts(ptr, len_in_bytes) };
//         self.write_bytes(offset, buf)
//     }
//     /// Writes a sequence of values given by an iterator (`iter`) from the specified offset (`offset`).
//     ///
//     /// The write process stops until the VM object does not have enough remaining space
//     /// or the iterator returns `None`. If any value is written, the function returns `Ok(nr_written)`,
//     /// where `nr_written` is the number of the written values.
//     ///
//     /// The offset of every value written by this method is aligned to the `align`-byte boundary.
//     /// Naturally, when `align` equals to `0` or `1`, then the argument takes no effect:
//     /// the values will be written in the most compact way.
//     ///
//     /// # Example
//     ///
//     /// Initializes an VM object with the same value can be done easily with `write_values`.
//     ///
//     /// ```
//     /// use core::iter::self;
//     ///
//     /// let _nr_values = vm_obj.write_vals(0, iter::repeat(0_u32), 0).unwrap();
//     /// ```
//     ///
//     /// # Panics
//     ///
//     /// This method panics if `align` is greater than two,
//     /// but not a power of two, in release mode.
//     fn write_vals<'a, T: 'a, I: Iterator<Item = &'a T>>(
//         &self,
//         offset: usize,
//         iter: I,
//         align: usize,
//     ) -> Result<usize> {
//         let mut nr_written = 0;
//         let (mut offset, item_size) = if (align >> 1) == 0 {
//             // align is 0 or 1
//             (offset, core::mem::size_of::<T>())
//         } else {
//             // align is more than 2
//             (
//                 offset.align_up(align),
//                 core::mem::size_of::<T>().align_up(align),
//             )
//         };
//         for item in iter {
//             match self.write_val(offset, item) {
//                 Ok(_) => {
//                     offset += item_size;
//                     nr_written += 1;
//                 }
//                 Err(e) => {
//                     if nr_written > 0 {
//                         return Ok(nr_written);
//                     }
//                     return Err(e);
//                 }
//             }
//         }
//         Ok(nr_written)
//     }
// }
// #[allow(unused_macros)]
// macro_rules! impl_vm_io_pointer {
//     ($typ:ty,$from:tt) => {
//         // #[inherit_methods(from = $from)]
//         impl<T: VmIo> VmIo for $typ {
//             fn read(&self, offset: usize, writer: &mut VmWriter) -> Result<()>;
//             fn read_bytes(&self, offset: usize, buf: &mut [u8]) -> Result<()>;
//             fn read_val<F>(&self, offset: usize) -> Result<F>;
//             fn read_slice<F>(&self, offset: usize, slice: &mut [F]) -> Result<()>;
//             fn write(&self, offset: usize, reader: &mut VmReader) -> Result<()>;
//             fn write_bytes(&self, offset: usize, buf: &[u8]) -> Result<()>;
//             fn write_val<F>(&self, offset: usize, new_val: &F) -> Result<()>;
//             fn write_slice<F>(&self, offset: usize, slice: &[F]) -> Result<()>;
//         }
//     };
// }
// // impl_vm_io_pointer!(&T, "(**self)");
// // impl_vm_io_pointer!(&mut T, "(**self)");
// // impl_vm_io_pointer!(Box<T>, "(**self)");
// // impl_vm_io_pointer!(Arc<T>, "(**self)");
// #[allow(unused_macros)]
// macro_rules! impl_vm_io_once_pointer {
//     ($typ:ty,$from:tt) => {
//         // #[inherit_methods(from = $from)]
//         impl<T: VmIoOnce> VmIoOnce for $typ {
//             fn read_once<F>(&self, offset: usize) -> Result<F>;
//             fn write_once<F>(&self, offset: usize, new_val: &F) -> Result<()>;
//         }
//     };
// }
// // impl_vm_io_once_pointer!(&T, "(**self)");
// // impl_vm_io_once_pointer!(&mut T, "(**self)");
// // impl_vm_io_once_pointer!(Box<T>, "(**self)");
// // impl_vm_io_once_pointer!(Arc<T>, "(**self)");
// /// A marker type used for [`VmReader`] and [`VmWriter`],
// /// representing whether reads or writes on the underlying memory region are fallible.
// pub enum Fallible {}
// /// A marker type used for [`VmReader`] and [`VmWriter`],
// /// representing whether reads or writes on the underlying memory region are infallible.
// pub enum Infallible {}
// /// Copies `len` bytes from `src` to `dst`.
// /// This function will early stop copying if encountering an unresolvable page fault.
// ///
// /// Returns the number of successfully copied bytes.
// ///
// /// In the following cases, this method may cause unexpected bytes to be copied, but will not cause
// /// safety problems as long as the safety requirements are met:
// /// - The source and destination overlap.
// /// - The current context is not associated with valid user space (e.g., in the kernel thread).
// ///
// /// # Safety
// ///
// /// - `src` must either be [valid] for reads of `len` bytes or be in user space for `len` bytes.
// /// - `dst` must either be [valid] for writes of `len` bytes or be in user space for `len` bytes.
// ///
// /// [valid]: crate::mm::io#safety
// #[verifier::external_body]
// unsafe fn memcpy_fallible(dst: *mut u8, src: *const u8, len: usize) -> usize {
//     // SAFETY: The safety is upheld by the caller.
//     let failed_bytes = unsafe { __memcpy_fallible(dst, src, len) };
//     len - failed_bytes
// }
// /// Fills `len` bytes of memory at `dst` with the specified `value`.
// /// This function will early stop filling if encountering an unresolvable page fault.
// ///
// /// Returns the number of successfully set bytes.
// ///
// /// # Safety
// ///
// /// - `dst` must either be [valid] for writes of `len` bytes or be in user space for `len` bytes.
// ///
// /// [valid]: crate::mm::io#safety
// unsafe fn memset_fallible(dst: *mut u8, value: u8, len: usize) -> usize {
//     // SAFETY: The safety is upheld by the caller.
//     let failed_bytes = unsafe { __memset_fallible(dst, value, len) };
//     len - failed_bytes
// }
// /// Fallible memory read from a `VmWriter`.
// pub trait FallibleVmRead {
//     /// Reads all data into the writer until one of the three conditions is met:
//     /// 1. The reader has no remaining data.
//     /// 2. The writer has no available space.
//     /// 3. The reader/writer encounters some error.
//     ///
//     /// On success, the number of bytes read is returned;
//     /// On error, both the error and the number of bytes read so far are returned.
//     fn read_fallible(
//         &mut self,
//         writer: &mut VmWriter<'_>,
//     ) -> core::result::Result<usize, (Error, usize)>;
// }
// /// Fallible memory write from a `VmReader`.
// pub trait FallibleVmWrite {
//     /// Writes all data from the reader until one of the three conditions is met:
//     /// 1. The reader has no remaining data.
//     /// 2. The writer has no available space.
//     /// 3. The reader/writer encounters some error.
//     ///
//     /// On success, the number of bytes written is returned;
//     /// On error, both the error and the number of bytes written so far are returned.
//     fn write_fallible(
//         &mut self,
//         reader: &mut VmReader<'_>,
//     ) -> core::result::Result<usize, (Error, usize)>;
// }
// macro_rules! impl_read_fallible {
//     ($reader_fallibility:ty, $writer_fallibility:ty) => {
//         impl<'a> FallibleVmRead for VmReader<'a /* $reader_fallibility */> {
//             fn read_fallible(
//                 &mut self,
//                 writer: &mut VmWriter<'_ /* $writer_fallibility */>,
//             ) -> core::result::Result<usize, (Error, usize)> {
//                 let copy_len = self.remain().min(writer.avail());
//                 if copy_len == 0 {
//                     return Ok(0);
//                 }
//                 // SAFETY: The source and destination are subsets of memory ranges specified by
//                 // the reader and writer, so they are either valid for reading and writing or in
//                 // user space.
//                 let copied_len = unsafe { memcpy_fallible(writer.cursor, self.cursor, copy_len) };
//                 self.cursor = self.cursor.wrapping_add(copied_len);
//                 writer.cursor = writer.cursor.wrapping_add(copied_len);
//                 if copied_len < copy_len {
//                     Err((Error::PageFault, copied_len))
//                 } else {
//                     Ok(copied_len)
//                 }
//             }
//         }
//     };
// }
// macro_rules! impl_write_fallible {
//     ($writer_fallibility:ty, $reader_fallibility:ty) => {
//         impl<'a> FallibleVmWrite for VmWriter<'a /* $writer_fallibility */> {
//             fn write_fallible(
//                 &mut self,
//                 reader: &mut VmReader<'_ /* $reader_fallibility */>,
//             ) -> core::result::Result<usize, (Error, usize)> {
//                 reader.read_fallible(self)
//             }
//         }
//     };
// }
// // impl_read_fallible!(Fallible, Infallible);
// // impl_read_fallible!(Fallible, Fallible);
// // impl_read_fallible!(Infallible, Fallible);
// // impl_write_fallible!(Fallible, Infallible);
// // impl_write_fallible!(Fallible, Fallible);
// // impl_write_fallible!(Infallible, Fallible);
// impl<'a> VmReader<'a /* Infallible */> {
//     #[rustc_allow_incoherent_impl]
//     pub fn read(&mut self, writer: &mut VmWriter<'_ /* Infallible */>) -> usize {
//         let copy_len = self.remain().min(writer.avail());
//         if copy_len == 0 {
//             return 0;
//         }
//         // SAFETY: The source and destination are subsets of memory ranges specified by the reader
//         // and writer, so they are valid for reading and writing.
//         unsafe { memcpy(writer.cursor, self.cursor, copy_len) };
//         self.cursor = self.cursor.wrapping_add(copy_len);
//         writer.cursor = writer.cursor.wrapping_add(copy_len);
//         copy_len
//     }
//     /// Reads a value of `Pod` type.
//     ///
//     /// If the length of the `Pod` type exceeds `self.remain()`,
//     /// this method will return `Err`.
//     #[rustc_allow_incoherent_impl]
//     pub fn read_val<T>(&mut self) -> Result<T> {
//         if self.remain() < core::mem::size_of::<T>() {
//             return Err(Error::InvalidArgs);
//         }
//         let mut val = T::new_uninit();
//         let mut writer = VmWriter::from(val.as_bytes_mut());
//         self.read(&mut writer);
//         Ok(val)
//     }
//     /// Reads a value of the `PodOnce` type using one non-tearing memory load.
//     ///
//     /// If the length of the `PodOnce` type exceeds `self.remain()`, this method will return `Err`.
//     ///
//     /// This method will not compile if the `Pod` type is too large for the current architecture
//     /// and the operation must be tear into multiple memory loads.
//     ///
//     /// # Panics
//     ///
//     /// This method will panic if the current position of the reader does not meet the alignment
//     /// requirements of type `T`.
//     #[rustc_allow_incoherent_impl]
//     pub fn read_once<T>(&mut self) -> Result<T> {
//         if self.remain() < core::mem::size_of::<T>() {
//             return Err(Error::InvalidArgs);
//         }
//         let cursor = self.cursor.cast::<T>();
//         assert!(cursor.is_aligned());
//         const { assert!(pod_once_impls::is_non_tearing::<T>()) };
//         // SAFETY: We have checked that the number of bytes remaining is at least the size of `T`
//         // and that the cursor is properly aligned with respect to the type `T`. All other safety
//         // requirements are the same as for `Self::read`.
//         let val = unsafe { cursor.read_volatile() };
//         self.cursor = self.cursor.wrapping_add(core::mem::size_of::<T>());
//         Ok(val)
//     }
//     /// Converts to a fallible reader.
//     #[rustc_allow_incoherent_impl]
//     pub fn to_fallible(self) -> VmReader<'a /* Fallible */> {
//         // It is safe to construct a fallible reader since an infallible reader covers the
//         // capabilities of a fallible reader.
//         VmReader {
//             cursor: self.cursor,
//             end: self.end,
//             phantom: PhantomData,
//         }
//     }
// }
// impl VmReader<'_ /* Fallible */> {
//     /// Constructs a `VmReader` from a pointer and a length, which represents
//     /// a memory range in user space.
//     ///
//     /// # Safety
//     ///
//     /// The virtual address range `ptr..ptr + len` must be in user space.
//     #[rustc_allow_incoherent_impl]
//     pub unsafe fn from_user_space(ptr: *const u8, len: usize) -> Self {
//         debug_assert!(ptr.addr().checked_add(len).unwrap() <= MAX_USERSPACE_VADDR);
//         Self {
//             cursor: ptr,
//             end: ptr.wrapping_add(len),
//             phantom: PhantomData,
//         }
//     }
//     /// Reads a value of `Pod` type.
//     ///
//     /// If the length of the `Pod` type exceeds `self.remain()`,
//     /// or the value can not be read completely,
//     /// this method will return `Err`.
//     ///
//     /// If the memory read failed, this method will return `Err`
//     /// and the current reader's cursor remains pointing to
//     /// the original starting position.
//     #[rustc_allow_incoherent_impl]
//     pub fn read_val<T>(&mut self) -> Result<T> {
//         if self.remain() < core::mem::size_of::<T>() {
//             return Err(Error::InvalidArgs);
//         }
//         let mut val = T::new_uninit();
//         let mut writer = VmWriter::from(val.as_bytes_mut());
//         self.read_fallible(&mut writer)
//             .map_err(|(err, copied_len)| {
//                 // SAFETY: The `copied_len` is the number of bytes read so far.
//                 // So the `cursor` can be moved back to the original position.
//                 unsafe {
//                     self.cursor = self.cursor.sub(copied_len);
//                 }
//                 err
//             })?;
//         Ok(val)
//     }
//     /// Collects all the remaining bytes into a `Vec<u8>`.
//     ///
//     /// If the memory read failed, this method will return `Err`
//     /// and the current reader's cursor remains pointing to
//     /// the original starting position.
//     #[rustc_allow_incoherent_impl]
//     pub fn collect(&mut self) -> Result<Vec<u8>> {
//         let mut buf = vec![0u8; self.remain()];
//         self.read_fallible(&mut buf.as_mut_slice().into())
//             .map_err(|(err, copied_len)| {
//                 // SAFETY: The `copied_len` is the number of bytes read so far.
//                 // So the `cursor` can be moved back to the original position.
//                 unsafe {
//                     self.cursor = self.cursor.sub(copied_len);
//                 }
//                 err
//             })?;
//         Ok(buf)
//     }
// }
// impl<'a> VmReader<'a /* Fallibility */> {
//     /// Returns the number of bytes for the remaining data.
//     #[rustc_allow_incoherent_impl]
//     pub fn remain(&self) -> usize {
//         self.end.addr() - self.cursor.addr()
//     }
//     /// Returns the cursor pointer, which refers to the address of the next byte to read.
//     #[rustc_allow_incoherent_impl]
//     pub fn cursor(&self) -> *const u8 {
//         self.cursor
//     }
//     /// Returns if it has remaining data to read.
//     #[rustc_allow_incoherent_impl]
//     pub fn has_remain(&self) -> bool {
//         self.remain() > 0
//     }
//     // /// Limits the length of remaining data.
//     // ///
//     // /// This method ensures the post condition of `self.remain() <= max_remain`.
//     // #[rustc_allow_incoherent_impl]
//     // pub fn limit(&mut self, max_remain: usize) -> &mut Self {
//     //     if max_remain < self.remain() {
//     //         self.end = self.cursor.wrapping_add(max_remain);
//     //     }
//     //     self
//     // }
//     // /// Skips the first `nbytes` bytes of data.
//     // /// The length of remaining data is decreased accordingly.
//     // ///
//     // /// # Panics
//     // ///
//     // /// If `nbytes` is greater than `self.remain()`, then the method panics.
//     // #[rustc_allow_incoherent_impl]
//     // pub fn skip(&mut self, nbytes: usize) -> &mut Self {
//     //     assert!(nbytes <= self.remain());
//     //     self.cursor = self.cursor.wrapping_add(nbytes);
//     //     self
//     // }
// }
// impl<'a> VmWriter<'a /* Infallible */> {
//     /// Writes all data from the reader until one of the two conditions is met:
//     /// 1. The reader has no remaining data.
//     /// 2. The writer has no available space.
//     ///
//     /// Returns the number of bytes written.
//     #[rustc_allow_incoherent_impl]
//     pub fn write(&mut self, reader: &mut VmReader<'_ /* Infallible */>) -> usize {
//         reader.read(self)
//     }
//     /// Writes a value of `Pod` type.
//     ///
//     /// If the length of the `Pod` type exceeds `self.avail()`,
//     /// this method will return `Err`.
//     #[rustc_allow_incoherent_impl]
//     pub fn write_val<T>(&mut self, new_val: &T) -> Result<()> {
//         if self.avail() < core::mem::size_of::<T>() {
//             return Err(Error::InvalidArgs);
//         }
//         let mut reader = VmReader::from(new_val.as_bytes());
//         self.write(&mut reader);
//         Ok(())
//     }
//     /// Writes a value of the `PodOnce` type using one non-tearing memory store.
//     ///
//     /// If the length of the `PodOnce` type exceeds `self.remain()`, this method will return `Err`.
//     ///
//     /// # Panics
//     ///
//     /// This method will panic if the current position of the writer does not meet the alignment
//     /// requirements of type `T`.
//     #[rustc_allow_incoherent_impl]
//     pub fn write_once<T>(&mut self, new_val: &T) -> Result<()> {
//         if self.avail() < core::mem::size_of::<T>() {
//             return Err(Error::InvalidArgs);
//         }
//         let cursor = self.cursor.cast::<T>();
//         assert!(cursor.is_aligned());
//         const { assert!(pod_once_impls::is_non_tearing::<T>()) };
//         // SAFETY: We have checked that the number of bytes remaining is at least the size of `T`
//         // and that the cursor is properly aligned with respect to the type `T`. All other safety
//         // requirements are the same as for `Self::write`.
//         unsafe { cursor.write_volatile(*new_val) };
//         self.cursor = self.cursor.wrapping_add(core::mem::size_of::<T>());
//         Ok(())
//     }
//     /// Fills the available space by repeating `value`.
//     ///
//     /// Returns the number of values written.
//     ///
//     /// # Panics
//     ///
//     /// The size of the available space must be a multiple of the size of `value`.
//     /// Otherwise, the method would panic.
//     #[rustc_allow_incoherent_impl]
//     pub fn fill<T>(&mut self, value: T) -> usize {
//         let cursor = self.cursor.cast::<T>();
//         assert!(cursor.is_aligned());
//         let avail = self.avail();
//         assert!(avail % core::mem::size_of::<T>() == 0);
//         let written_num = avail / core::mem::size_of::<T>();
//         for i in 0..written_num {
//             let cursor_i = cursor.wrapping_add(i);
//             // SAFETY: `written_num` is calculated by the avail size and the size of the type `T`,
//             // so the `write` operation will only manipulate the memory managed by this writer.
//             // We've checked that the cursor is properly aligned with respect to the type `T`. All
//             // other safety requirements are the same as for `Self::write`.
//             unsafe { cursor_i.write_volatile(value) };
//         }
//         // The available space has been filled so this cursor can be moved to the end.
//         self.cursor = self.end;
//         written_num
//     }
//     /// Converts to a fallible writer.
//     #[rustc_allow_incoherent_impl]
//     pub fn to_fallible(self) -> VmWriter<'a /* Fallible */> {
//         // It is safe to construct a fallible reader since an infallible reader covers the
//         // capabilities of a fallible reader.
//         VmWriter {
//             cursor: self.cursor,
//             end: self.end,
//             phantom: PhantomData,
//         }
//     }
// }
// impl VmWriter<'_ /* Fallible */> {
//     /// Constructs a `VmWriter` from a pointer and a length, which represents
//     /// a memory range in user space.
//     ///
//     /// The current context should be consistently associated with valid user space during the
//     /// entire lifetime `'a`. This is for correct semantics and is not a safety requirement.
//     ///
//     /// # Safety
//     ///
//     /// The virtual address range `ptr..ptr + len` must be in user space.
//     #[rustc_allow_incoherent_impl]
//     pub unsafe fn from_user_space(ptr: *mut u8, len: usize) -> Self {
//         debug_assert!(ptr.addr().checked_add(len).unwrap() <= MAX_USERSPACE_VADDR);
//         Self {
//             cursor: ptr,
//             end: ptr.wrapping_add(len),
//             phantom: PhantomData,
//         }
//     }
//     /// Writes a value of `Pod` type.
//     ///
//     /// If the length of the `Pod` type exceeds `self.avail()`,
//     /// or the value can not be write completely,
//     /// this method will return `Err`.
//     ///
//     /// If the memory write failed, this method will return `Err`
//     /// and the current writer's cursor remains pointing to
//     /// the original starting position.
//     #[rustc_allow_incoherent_impl]
//     pub fn write_val<T>(&mut self, new_val: &T) -> Result<()> {
//         if self.avail() < core::mem::size_of::<T>() {
//             return Err(Error::InvalidArgs);
//         }
//         let mut reader = VmReader::from(new_val.as_bytes());
//         self.write_fallible(&mut reader)
//             .map_err(|(err, copied_len)| {
//                 // SAFETY: The `copied_len` is the number of bytes written so far.
//                 // So the `cursor` can be moved back to the original position.
//                 unsafe {
//                     self.cursor = self.cursor.sub(copied_len);
//                 }
//                 err
//             })?;
//         Ok(())
//     }
//     /// Writes `len` zeros to the target memory.
//     ///
//     /// This method attempts to fill up to `len` bytes with zeros. If the available
//     /// memory from the current cursor position is less than `len`, it will only fill
//     /// the available space.
//     ///
//     /// If the memory write failed due to an unresolvable page fault, this method
//     /// will return `Err` with the length set so far.
//     #[rustc_allow_incoherent_impl]
//     pub fn fill_zeros(&mut self, len: usize) -> core::result::Result<usize, (Error, usize)> {
//         let len_to_set = self.avail().min(len);
//         if len_to_set == 0 {
//             return Ok(0);
//         }
//         // SAFETY: The destination is a subset of the memory range specified by
//         // the current writer, so it is either valid for writing or in user space.
//         let set_len = unsafe { memset_fallible(self.cursor, 0u8, len_to_set) };
//         self.cursor = self.cursor.wrapping_add(set_len);
//         if set_len < len_to_set {
//             Err((Error::PageFault, set_len))
//         } else {
//             Ok(len_to_set)
//         }
//     }
// }
// impl<'a> VmWriter<'a /* Fallibility */> {
//     /// Returns the number of bytes for the available space.
//     #[rustc_allow_incoherent_impl]
//     pub fn avail(&self) -> usize {
//         self.end.addr() - self.cursor.addr()
//     }
//     /// Returns the cursor pointer, which refers to the address of the next byte to write.
//     #[rustc_allow_incoherent_impl]
//     pub fn cursor(&self) -> *mut u8 {
//         self.cursor
//     }
//     /// Returns if it has available space to write.
//     #[rustc_allow_incoherent_impl]
//     pub fn has_avail(&self) -> bool {
//         self.avail() > 0
//     }
//     /// Limits the length of available space.
//     ///
//     /// This method ensures the post condition of `self.avail() <= max_avail`.
//     #[rustc_allow_incoherent_impl]
//     pub fn limit(&mut self, max_avail: usize) -> &mut Self {
//         if max_avail < self.avail() {
//             self.end = self.cursor.wrapping_add(max_avail);
//         }
//         self
//     }
//     // /// Skips the first `nbytes` bytes of data.
//     // /// The length of available space is decreased accordingly.
//     // ///
//     // /// # Panics
//     // ///
//     // /// If `nbytes` is greater than `self.avail()`, then the method panics.
//     // pub fn skip(&mut self, nbytes: usize) -> &mut Self {
//     //     assert!(nbytes <= self.avail());
//     //     self.cursor = self.cursor.wrapping_add(nbytes);
//     //     self
//     // }
// }
// /// A marker trait for POD types that can be read or written with one instruction.
// ///
// /// This trait is mostly a hint, since it's safe and can be implemented for _any_ POD type. If it
// /// is implemented for a type that cannot be read or written with a single instruction, calling
// /// `read_once`/`write_once` will lead to a failed compile-time assertion.
// pub trait PodOnce /* Pod */ {}
// #[cfg(any(
//     target_arch = "x86_64",
//     target_arch = "riscv64",
//     target_arch = "loongarch64"
// ))]
// mod pod_once_impls {
//     use super::PodOnce;
//     impl PodOnce for u8 {}
//     impl PodOnce for u16 {}
//     impl PodOnce for u32 {}
//     impl PodOnce for u64 {}
//     impl PodOnce for usize {}
//     impl PodOnce for i8 {}
//     impl PodOnce for i16 {}
//     impl PodOnce for i32 {}
//     impl PodOnce for i64 {}
//     impl PodOnce for isize {}
//     /// Checks whether the memory operation created by `ptr::read_volatile` and
//     /// `ptr::write_volatile` doesn't tear.
//     ///
//     /// Note that the Rust documentation makes no such guarantee, and even the wording in the LLVM
//     /// LangRef is ambiguous. But this is unlikely to break in practice because the Linux kernel
//     /// also uses "volatile" semantics to implement `READ_ONCE`/`WRITE_ONCE`.
//     pub(super) const fn is_non_tearing<T>() -> bool {
//         let size = core::mem::size_of::<T>();
//         size == 1 || size == 2 || size == 4 || size == 8
//     }
// }
