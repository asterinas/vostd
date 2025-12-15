use vstd::prelude::*;

use vstd::simple_pptr::*;
use vstd_extra::ownership::Inv;

use core::marker::PhantomData;
use core::ops::Range;

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
}

impl<'a> From<&'a [u8]> for VmReader<'a  /* Infallible */ > {
    #[verifier::external_body]
    fn from(slice: &'a [u8]) -> Self {
        // SAFETY:
        // - The memory range points to typed memory.
        // - The validity requirements for read accesses are met because the pointer is converted
        //   from an immutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.
        unsafe { Self::from_kernel_space(PPtr(slice.as_ptr() as usize, PhantomData), slice.len()) }
    }
}

impl<'a> From<&'a [u8]> for VmWriter<'a  /* Infallible */ > {
    #[verifier::external_body]
    fn from(slice: &'a [u8]) -> Self {
        // SAFETY:
        // - The memory range points to typed memory.
        // - The validity requirements for write accesses are met because the pointer is converted
        //   from a mutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.
        unsafe { Self::from_kernel_space(PPtr(slice.as_ptr() as usize, PhantomData), slice.len()) }
    }
}

} // verus!
