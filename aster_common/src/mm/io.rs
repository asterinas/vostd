use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::std_specs::convert::TryFromSpecImpl;
use vstd_extra::ownership::Inv;

use core::marker::PhantomData;
use core::ops::Range;

use crate::pod::Pod;
use crate::pod::PodOnce;
use crate::KERNEL_BASE_VADDR;
use crate::KERNEL_END_VADDR;

verus! {

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
    pub phantom: PhantomData<&'a [u8]  /*, Fallibility)*/ >,
}

/// This looks like we can implement a single struct with a type parameter
#[rustc_has_incoherent_inherent_impls]
pub tracked struct VmIoOwner<'a> {
    pub range: Ghost<Range<int>>,
    // Whether this reader is fallible.
    pub is_fallible: bool,
    pub phantom: PhantomData<&'a [u8]  /*, Fallibility)*/ >,
}

impl<'a> Inv for VmIoOwner<'a> {
    open spec fn inv(self) -> bool {
        // We do allow ZSTs so that empty ranges are valid.
        &&& self.range@.start != self.range@.end ==> KERNEL_BASE_VADDR() as int <= self.range@.start
            <= self.range@.end <= KERNEL_END_VADDR() as int
    }
}

impl<'a> VmIoOwner<'a> {
    pub open spec fn inv_with_reader(
        self,
        reader: VmReader<'a  /* Fallibility */ >,
    ) -> bool {
        &&& self.inv()
        &&& self.range@.start as usize <= reader.cursor.addr()
        &&& reader.end.addr() <= self.range@.end as usize
    }

    pub open spec fn inv_with_writer(
        self,
        writer: VmWriter<'a  /* Fallibility */ >,
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
            -> owner: Tracked<VmIoOwner<'a>>,
        requires
            len == 0 || KERNEL_BASE_VADDR() <= ptr.addr(),
            len == 0 || ptr.addr() + len <= KERNEL_END_VADDR(),
        ensures
            owner@.inv(),
            owner@.inv_with_writer(r),
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
                    &&& owner.inv()
                    &&& owner.inv_with_writer(r)
                    // &&& r.cursor.addr() == ptr.addr(),
                    // &&& r.end.addr() == ptr.addr() + len,
                }
            }
    )]
    pub fn from_pod<T: Pod>(mut val: T) -> Result<
        VmWriter<'a  /* Infallible */ >,
    > {
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
                    &&& owner.inv()
                    &&& owner.inv_with_reader(r)
                    // &&& r.cursor.addr() == ptr.addr(),
                    // &&& r.end.addr() == ptr.addr() + len,
                }
            }
    )]
    pub fn from_pod<T: Pod>(mut val: T) -> Result<
        VmReader<'a  /* Infallible */ >,
    > {
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

// Perhaps we can implement `tryfrom` instead.
#[verus_verify]
impl<'a> TryFrom<&'a [u8]> for VmWriter<'a  /* Infallible */ > {
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
        // - The validity requirements for write accesses are met because the pointer is converted
        //   from a mutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.

        Ok(
            unsafe {
                #[verus_spec(with => Tracked(perm))]
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

pub type Result<T> = core::result::Result<T, crate::mm::Error>;

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
/// Unfortunately `verus_spec` does not support traits so we have to keep the style for the
/// time being but hopefully we can make the code more concise in the future.
pub trait VmIo: Send + Sync + Sized {
    // /// Checks whether the given `VmReader` is valid with respect to this VM object.
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
    spec fn vmio_read_requires(self, owner: VmIoOwner<'_>, offset: usize) -> bool;

    // {
    //     &&& owner.inv()
    //     // &&& self.reader_inv_with_owner(owner)
    //     &&& offset + owner.range@.start as usize <= owner.range@.end as usize
    // }
    spec fn vmio_read_ensures(
        self,
        owner: VmIoOwner<'_>,
        offset: usize,
        new_owner: VmIoOwner<'_>,
        r: Result<()>,
    ) -> bool;

    // {
    //     &&& r is Ok ==> {
    //         &&& new_owner.inv()
    //         // &&& self.reader_inv_with_owner(new_owner)
    //     }
    //     &&& r is Err ==> { true  /* what happened? */  }
    // }
    spec fn vmio_write_requires(self, owner: VmIoOwner<'_>, offset: usize) -> bool;

    // {
    //     &&& owner.inv()
    //     // &&& self.reader_inv_with_owner(owner)
    //     &&& offset + owner.range@.start as usize <= owner.range@.end as usize
    // }
    spec fn vmio_write_ensures(
        self,
        owner: VmIoOwner<'_>,
        offset: usize,
        new_owner: VmIoOwner<'_>,
        r: Result<()>,
    ) -> bool;

    // {
    //     &&& r is Ok ==> {
    //         &&& new_owner.inv()
    //         // &&& self.reader_inv_with_owner(new_owner)
    //     }
    //     &&& r is Err ==> { true  /* what happened? */  }
    // }
    /// Reads requested data at a specified offset into a given `VmWriter`.
    ///
    /// # No short reads
    ///
    /// On success, the `writer` must be written with the requested data
    /// completely. If, for any reason, the requested data is only partially
    /// available, then the method shall return an error.
    fn read(
        &self,
        offset: usize,
        writer: &mut VmWriter,
        Tracked(owner): Tracked<&mut VmIoOwner<'_>>,
    ) -> (r: Result<()>)
        requires
            Self::obeys_vmio_read_requires() ==> Self::vmio_read_requires(
                *self,
                *old(owner),
                offset,
            ),
        ensures
            Self::obeys_vmio_read_ensures() ==> Self::vmio_read_ensures(
                *self,
                *old(owner),
                offset,
                *owner,
                r,
            ),
    ;

    /// Reads a value of a specified type at a specified offset.
    fn read_val<T: Pod>(&self, offset: usize) -> Result<T>;

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
        Tracked(owner): Tracked<&mut VmIoOwner<'_>>,
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

    fn write_val<T: Pod>(&self, offset: usize, val: T) -> Result<()>;
}

/// A trait that enables reading/writing data from/to a VM object using one non-tearing memory
/// load/store.
///
/// See also [`VmIo`], which enables reading/writing data from/to a VM object without the guarantee
/// of using one non-tearing memory load/store.
pub trait VmIoOnce: Sized {
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

impl<'a> VmIo for VmReader<'a> {
    closed spec fn obeys_vmio_read_requires() -> bool {
        true
    }

    open spec fn vmio_read_requires(self, owner: VmIoOwner<'_>, offset: usize) -> bool {
        &&& owner.inv()
        // &&& self.reader_inv_with_owner(owner)
        &&& offset + owner.range@.start as usize <= owner.range@.end as usize
    }

    closed spec fn obeys_vmio_read_ensures() -> bool {
        true
    }

    open spec fn vmio_read_ensures(
        self,
        owner: VmIoOwner<'_>,
        offset: usize,
        new_owner: VmIoOwner<'_>,
        r: Result<()>,
    ) -> bool {
        &&& r is Ok ==> {
            &&& new_owner.inv()
            // &&& self.reader_inv_with_owner(new_owner)

        }&&& r is Err ==> { true  /* what happened? */  }
    }

    closed spec fn obeys_vmio_write_requires() -> bool {
        true
    }

    open spec fn vmio_write_requires(self, owner: VmIoOwner<'_>, offset: usize) -> bool {
        &&& owner.inv()
        // &&& self.reader_inv_with_owner(owner)
        &&& offset + owner.range@.start as usize <= owner.range@.end as usize
    }

    closed spec fn obeys_vmio_write_ensures() -> bool {
        true
    }

    open spec fn vmio_write_ensures(
        self,
        owner: VmIoOwner<'_>,
        offset: usize,
        new_owner: VmIoOwner<'_>,
        r: Result<()>,
    ) -> bool {
        &&& r is Ok ==> {
            &&& new_owner.inv()
            // &&& self.reader_inv_with_owner(new_owner)

        }&&& r is Err ==> { true  /* what happened? */  }
    }

    fn read(
        &self,
        offset: usize,
        writer: &mut VmWriter,
        Tracked(owner): Tracked<&mut VmIoOwner<'_>>,
    ) -> (r: Result<()>)
        ensures
            Self::obeys_vmio_read_ensures() ==> Self::vmio_read_ensures(
                *self,
                *old(owner),
                offset,
                *owner,
                r,
            ),
    {
        vstd::vpanic!("stub");
    }

    fn write(
        &self,
        offset: usize,
        reader: &mut VmReader,
        Tracked(owner): Tracked<&mut VmIoOwner<'_>>,
    ) -> (r: Result<()>)
        ensures
            Self::obeys_vmio_write_ensures() ==> Self::vmio_write_ensures(
                *self,
                *old(owner),
                offset,
                *owner,
                r,
            ),
    {
        vstd::vpanic!("stub");
    }

    fn read_val<T: Pod>(&self, offset: usize) -> Result<T> {
        vstd::vpanic!("stub");
    }

    fn write_val<T: Pod>(&self, offset: usize, val: T) -> Result<()> {
        vstd::vpanic!("stub");
    }
}

} // verus!
