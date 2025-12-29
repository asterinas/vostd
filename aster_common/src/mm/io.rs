use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::std_specs::convert::TryFromSpecImpl;
use vstd_extra::array_ptr::ArrayPtr;
use vstd_extra::array_ptr::PointsToArray;
use vstd_extra::ownership::Inv;

use core::marker::PhantomData;
use core::ops::Range;

use crate::pod::Pod;
use crate::pod::PodOnce;
use crate::KERNEL_BASE_VADDR;
use crate::KERNEL_END_VADDR;

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
    (crate::mm::Error, usize),
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
        KERNEL_BASE_VADDR() <= dst && dst + len <= KERNEL_END_VADDR(),
        KERNEL_BASE_VADDR() <= src && src + len <= KERNEL_END_VADDR(),
)]
unsafe fn memcpy(dst: usize, src: usize, len: usize) {
    // This method is implemented by calling `volatile_copy_memory`. Note that even with the
    // "volatile" keyword, data races are still considered undefined behavior (UB) in both the Rust
    // documentation and the C/C++ standards. In general, UB makes the behavior of the entire
    // program unpredictable, usually due to compiler optimizations that assume the absence of UB.
    // However, in this particular case, considering that the Linux kernel uses the "volatile"
    // keyword to implement `READ_ONCE` and `WRITE_ONCE`, the compiler is extremely unlikely to
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
    pub phantom: PhantomData<&'a [u8]  /*, Fallibility)*/
    >,
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
        &&& self.range@.start != self.range@.end ==> KERNEL_BASE_VADDR() as int <= self.range@.start
            <= self.range@.end <= KERNEL_END_VADDR() as int
    }
}

impl VmIoOwner<'_> {
    /// Checks whether this owner overlaps with another owner.
    #[verifier::inline]
    pub open spec fn overlaps(self, other: VmIoOwner<'_>) -> bool {
        &&& self.range@.start < other.range@.end
        &&& other.range@.start < self.range@.end
    }

    /// Checks whether this owner is disjoint with another owner.
    #[verifier::inline]
    pub open spec fn disjoint(self, other: VmIoOwner<'_>) -> bool {
        !self.overlaps(other)
    }

    /// Checks whether this owner has the same parameters as another owner.
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
            len == 0 || KERNEL_BASE_VADDR() <= ptr.addr(),
            len == 0 || ptr.addr() + len <= KERNEL_END_VADDR(),
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

        if len != 0 && (pnt.addr() < KERNEL_BASE_VADDR() || len >= KERNEL_END_VADDR() || pnt.addr()
            > KERNEL_END_VADDR() - len) {
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
            len == 0 || KERNEL_BASE_VADDR() <= ptr.addr(),
            len == 0 || ptr.addr() + len <= KERNEL_END_VADDR(),
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

        if len != 0 && (pnt.addr() < KERNEL_BASE_VADDR() || len >= KERNEL_END_VADDR() || pnt.addr()
            > KERNEL_END_VADDR() - len) {
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

        if slice.len() != 0 && (addr < KERNEL_BASE_VADDR() || slice.len() >= KERNEL_END_VADDR()
            || addr > KERNEL_END_VADDR() - slice.len()) {
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

        if len != 0 && (addr < KERNEL_BASE_VADDR() || len >= KERNEL_END_VADDR() || addr
            > KERNEL_END_VADDR() - slice.len()) {
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

        if slice.len() != 0 && (addr < KERNEL_BASE_VADDR() || slice.len() >= KERNEL_END_VADDR()
            || addr > KERNEL_END_VADDR() - slice.len()) {
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

        if len != 0 && (addr < KERNEL_BASE_VADDR() || len >= KERNEL_END_VADDR() || addr
            > KERNEL_END_VADDR() - slice.len()) {
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
