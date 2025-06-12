use vstd::prelude::*;
use vstd::raw_ptr::*;
use core::marker::PhantomData;

use crate::{common::*, io::model::VmIoModel, io::fallible::*, io::specs::*};

verus! {

pub struct VmReader<'a, Fallibility> {
    pub cursor: *const u8,
    pub end: *const u8,
    pub phantom: PhantomData<(&'a [u8], Fallibility)>,
    pub state: Tracked<VmIoModel>,
}

impl<'a, Fallibility> VmReader<'a, Fallibility> {
    pub open spec fn invariants(&self) -> bool {
        self.end as usize == self.state@.end && self.state@.range_valid()
            && self.state@.cursor_within_range(self.cursor as usize)
    }

    pub open spec fn cursor_monotonic(&self, new_reader: &Self) -> bool {
        self.cursor as usize <= new_reader.cursor as usize
    }

    pub open spec fn invariants_mut(&self, new_reader: &Self) -> bool {
        self.cursor_monotonic(new_reader) && self.state@.state_eq(&new_reader.state@)
    }

    pub fn cursor_add(&mut self, len: usize)
        requires
            old(self).invariants(),
            len <= old(self).remain_spec(),
        ensures
            self.invariants(),
            self.cursor as usize == old(self).cursor as usize + len,
            self.state@.state_eq(&old(self).state@),
    {
        self.cursor = pnt_add(self.cursor, len);
    }

    pub fn cursor_sub(&mut self, len: usize)
        requires
            old(self).invariants(),
            old(self).state@.cursor_within_range(
                pnt_sub_spec(old(self).cursor as usize, len) as usize,
            ),
        ensures
            self.invariants(),
            self.cursor as usize == old(self).cursor as usize - len,
            self.state@.state_eq(&old(self).state@),
    {
        self.cursor = pnt_sub(self.cursor, len);
    }
}

impl<'a> VmReader<'a, Infallible> {
    /// Constructs a `VmReader` from a pointer and a length, which represents
    /// a memory range in kernel space.
    ///
    /// # Safety
    ///
    /// `ptr` must be [valid] for reads of `len` bytes during the entire lifetime `a`.
    ///
    /// [valid]: crate::mm::io#safety
    pub unsafe fn from_kernel_space(ptr: *const u8, len: usize) -> (reader: Self)
        requires
            len == 0 || range_within_kspace_spec(ptr as usize, len),
        ensures
            reader.invariants(),
    {
        Self {
            cursor: ptr,
            end: pnt_add(ptr, len),
            phantom: PhantomData,
            state: Tracked(
                VmIoModel { start: ptr as usize as int, end: pnt_add_spec(ptr as usize, len) },
            ),
        }
    }

    /// Reads all data into the writer until one of the two conditions is met:
    /// 1. The reader has no remaining data.
    /// 2. The writer has no available space.
    ///
    /// Returns the number of bytes read.
    pub fn read(&mut self, writer: &mut VmWriter<'_, Infallible>) -> (copy_len: usize)
        requires
            old(self).invariants(),
            old(writer).invariants(),
        ensures
            self.invariants(),
            old(self).invariants_mut(self),
            writer.invariants(),
            old(writer).invariants_mut(writer),
            self.remain_spec() == 0 || writer.avail_spec() == 0,
            old(self).remain_spec() == self.remain_spec() + copy_len,
            old(writer).avail_spec() == writer.avail_spec() + copy_len,
    {
        let mut copy_len = if self.remain() < writer.avail() {
            self.remain()
        } else {
            writer.avail()
        };

        if copy_len == 0 {
            return 0;
        }
        // SAFETY: The source and destination are subsets of memory ranges specified by the reader
        // and writer, so they are valid for reading and writing.

        unsafe {
            memcpy(writer.cursor, self.cursor, copy_len);
            self.cursor_add(copy_len);
            writer.cursor_add(copy_len);
        }

        copy_len
    }

    /// Reads a value of `Pod` type.
    ///
    /// If the length of the `Pod` type exceeds `self.remain()`,
    /// this method will return `Err`.
    pub fn read_val<T: Pod>(&mut self) -> (res: Result<T>)
        requires
            old(self).invariants(),
        ensures
            self.invariants(),
            old(self).invariants_mut(self),
            (res.is_err() && old(self).cursor as usize == self.cursor as usize) || (res.is_ok()
                && old(self).cursor as usize == self.cursor as usize - pod_size_spec::<T>()),
    {
        if self.remain() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        let mut val = T::new_uninit();
        let mut writer = from_pod(val);

        self.read(&mut writer);

        Ok(val)
    }

    #[verifier::external_body]
    fn read_once_inner<T: PodOnce>(&self) -> T {
        let pnt = self.cursor.cast::<T>();
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
    pub fn read_once<T: PodOnce>(&mut self) -> (res: Result<T>)
        requires
            old(self).invariants(),
            pod_pnt_is_aligned::<T>(old(self).cursor),
        ensures
            self.invariants(),
            old(self).invariants_mut(self),
            (res.is_err() && old(self).cursor as usize == self.cursor as usize) || (res.is_ok()
                && old(self).cursor as usize == self.cursor as usize - pod_size_spec::<T>()),
    {
        if self.remain() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        // SAFETY: We have checked that the number of bytes remaining is at least the size of `T`
        // and that the cursor is properly aligned with respect to the type `T`. All other safety
        // requirements are the same as for `Self::read`.

        let val = self.read_once_inner();

        unsafe { self.cursor_add(core::mem::size_of::<T>()) };

        Ok(val)
    }

    /// Converts to a fallible reader.
    #[verifier::external_body]
    pub fn to_fallible(self) -> (new_reader: VmReader<'a, Fallible>)
        requires
            self.invariants(),
        ensures
            new_reader.invariants(),
            new_reader.cursor as usize == self.cursor as usize,
            new_reader.state@.state_eq(&self.state@),
    {
        // SAFETY: It is safe to transmute to a fallible reader since
        // 1. the fallibility is a zero-sized marker type,
        // 2. an infallible reader covers the capabilities of a fallible reader.
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a> VmReader<'a, Fallible> {
    /// Constructs a `VmReader` from a pointer and a length, which represents
    /// a memory range in user space.
    ///
    /// # Safety
    ///
    /// The virtual address range `ptr..ptr + len` must be in user space.
    pub unsafe fn from_user_space(ptr: *const u8, len: usize) -> (reader: Self)
        requires
            range_within_uspace_spec(ptr as usize, len),
        ensures
            reader.invariants(),
    {
        Self {
            cursor: ptr,
            end: pnt_add(ptr, len),
            phantom: PhantomData,
            state: Tracked(
                VmIoModel { start: ptr as usize as int, end: pnt_add_spec(ptr as usize, len) },
            ),
        }
    }

    /// Reads a value of `Pod` type.
    ///
    /// If the length of the `Pod` type exceeds `self.remain()`,
    /// or the value can not be read completely,
    /// this method will return `Err`.
    ///
    /// If the memory read failed, this method will return `Err`
    /// and the current reader's cursor remains pointing to
    /// the original starting position.
    pub fn read_val<T: Pod>(&mut self) -> (res: Result<T>)
        requires
            old(self).invariants(),
        ensures
            self.invariants(),
            old(self).invariants_mut(self),
            (res.is_err() && old(self).cursor as usize == self.cursor as usize) || (res.is_ok()
                && old(self).cursor as usize == self.cursor as usize - pod_size_spec::<T>()),
    {
        if self.remain() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        let mut val = T::new_uninit();
        let mut writer = from_pod(val);

        let res = rw_fallible(self, &mut writer);
        if let Err((err, copied_len)) = res {
            // SAFETY: The `copied_len` is the number of bytes read so far.
            // So the `cursor` can be moved back to the original position.
            unsafe {
                self.cursor_sub(copied_len);
            }
            return Err(err);
        }
        Ok(val)
    }

    /// Collects all the remaining bytes into a `Vec<u8>`.
    ///
    /// If the memory read failed, this method will return `Err`
    /// and the current reader's cursor remains pointing to
    /// the original starting position.
    pub fn collect(&mut self) -> (res: Result<Vec<u8>>)
        requires
            old(self).invariants(),
        ensures
            self.invariants(),
            old(self).invariants_mut(self),
            (collect_spec_success(res, old(self).remain_spec() as usize) && self.remain_spec() == 0)
                || (collect_spec_failure(res, old(self).cursor as usize, self.cursor as usize)
                && old(self).remain_spec() == self.remain_spec()),
    {
        let mut buf = allocate_vec_zero(self.remain());
        let mut writer = from_vec(&mut buf);

        let res = rw_fallible(self, &mut writer);
        if let Err((err, copied_len)) = res {
            // SAFETY: The `copied_len` is the number of bytes read so far.
            // So the `cursor` can be moved back to the original position.
            unsafe {
                self.cursor_sub(copied_len);
            }

            return Err(err);
        }
        Ok(buf)
    }
}

impl<'a, Fallibility> VmReader<'a, Fallibility> {
    pub open spec fn remain_spec(&self) -> int {
        self.end as usize - self.cursor as usize
    }

    /// Returns the number of bytes for the remaining data.
    pub fn remain(&self) -> (rem_size: usize)
        requires
            self.invariants(),
        ensures
            rem_size == self.remain_spec(),
    {
        // SAFETY: the end is equal to or greater than the cursor.
        unsafe { self.end as usize - self.cursor as usize }
    }

    pub open spec fn cursor_spec(&self) -> *const u8 {
        self.cursor
    }

    /// Returns the cursor pointer, which refers to the address of the next byte to read.
    pub const fn cursor(&self) -> (cursor: *const u8)
        requires
            self.invariants(),
        ensures
            cursor == self.cursor_spec(),
    {
        self.cursor
    }

    pub open spec fn has_remain_spec(&self) -> bool {
        self.remain_spec() > 0
    }

    /// Returns if it has remaining data to read.
    pub fn has_remain(&self) -> (has_rm: bool)
        requires
            self.invariants(),
        ensures
            has_rm == self.has_remain_spec(),
    {
        self.remain() > 0
    }

    /// Limits the length of remaining data.
    ///
    /// This method ensures the post condition of `self.remain() <= max_remain`.
    pub fn limit(self, max_remain: usize) -> (new_reader: Self)
        requires
            self.invariants(),
        ensures
            new_reader.invariants(),
            new_reader.cursor as usize == self.cursor as usize,
            new_reader.remain_spec() == vstd::math::min(self.remain_spec(), max_remain as int),
    {
        if max_remain < self.remain() {
            // SAFETY: the new end is less than the old end.
            let new_reader = unsafe {
                Self {
                    cursor: self.cursor,
                    end: pnt_add(self.cursor, max_remain),
                    phantom: PhantomData,
                    state: Tracked(
                        VmIoModel {
                            start: self.state@.start,
                            end: pnt_add_spec(self.cursor as usize, max_remain),
                        },
                    ),
                }
            };

            return new_reader;
        }
        self
    }

    /// Skips the first `nbytes` bytes of data.
    /// The length of remaining data is decreased accordingly.
    ///
    /// # Panics
    ///
    /// If `nbytes` is greater than `self.remain()`, then the method panics.
    pub fn skip(self, nbytes: usize) -> (new_reader: Self)
        requires
            self.invariants(),
            nbytes <= self.remain_spec(),
        ensures
            new_reader.invariants(),
            self.invariants_mut(&mut new_reader),
            new_reader.remain_spec() == self.remain_spec() - nbytes,
    {
        // SAFETY: the new cursor is less than or equal to the end.
        let new_reader = unsafe {
            Self {
                cursor: pnt_add(self.cursor, nbytes),
                end: self.end,
                phantom: PhantomData,
                state: self.state,
            }
        };
        new_reader
    }
}

impl<'a> From<&'a [u8]> for VmReader<'a, Infallible> {
    #[verifier::external_body]
    fn from(slice: &'a [u8]) -> (reader: Self)
        ensures
            reader.invariants(),
            reader.remain_spec() == slice.len(),
    {
        // SAFETY:
        // - The memory range points to typed memory.
        // - The validity requirements for read accesses are met because the pointer is converted
        //   from an immutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.
        unsafe { Self::from_kernel_space(slice.as_ptr(), slice.len()) }
    }
}

} // verus!
verus! {

pub struct VmWriter<'a, Fallibility> {
    pub cursor: *mut u8,
    pub end: *mut u8,
    pub phantom: PhantomData<(&'a [u8], Fallibility)>,
    pub state: Tracked<VmIoModel>,
}

impl<'a, Fallibility> VmWriter<'a, Fallibility> {
    pub open spec fn invariants(&self) -> bool {
        self.end as usize == self.state@.end && self.state@.range_valid()
            && self.state@.cursor_within_range(self.cursor as usize)
    }

    pub open spec fn cursor_monotonic(&self, new_writer: &Self) -> bool {
        self.cursor as usize <= new_writer.cursor as usize
    }

    pub open spec fn invariants_mut(&self, new_writer: &Self) -> bool {
        self.cursor_monotonic(new_writer) && self.state@.state_eq(&new_writer.state@)
    }

    pub fn cursor_add(&mut self, len: usize)
        requires
            old(self).invariants(),
            len <= old(self).avail_spec(),
        ensures
            self.invariants(),
            self.cursor as usize == old(self).cursor as usize + len,
            self.state@.state_eq(&old(self).state@),
    {
        self.cursor = mut_pnt_add(self.cursor, len);
    }

    pub fn cursor_sub(&mut self, len: usize)
        requires
            old(self).invariants(),
            old(self).state@.cursor_within_range(
                mut_pnt_sub_spec(old(self).cursor as usize, len) as usize,
            ),
        ensures
            self.invariants(),
            self.cursor as usize == old(self).cursor as usize - len,
            self.state@.state_eq(&old(self).state@),
    {
        self.cursor = mut_pnt_sub(self.cursor, len);
    }
}

impl<'a> VmWriter<'a, Infallible> {
    /// Constructs a `VmWriter` from a pointer and a length, which represents
    /// a memory range in kernel space.
    ///
    /// # Safety
    ///
    /// `ptr` must be [valid] for writes of `len` bytes during the entire lifetime `a`.
    ///
    /// [valid]: crate::mm::io#safety
    pub unsafe fn from_kernel_space(ptr: *mut u8, len: usize) -> (writer: Self)
        requires
            range_within_kspace_spec(ptr as usize, len),
        ensures
            writer.invariants(),
    {
        Self {
            cursor: ptr,
            end: mut_pnt_add(ptr, len),
            phantom: PhantomData,
            state: Tracked(
                VmIoModel { start: ptr as usize as int, end: mut_pnt_add_spec(ptr as usize, len) },
            ),
        }
    }

    /// Writes all data from the reader until one of the two conditions is met:
    /// 1. The reader has no remaining data.
    /// 2. The writer has no available space.
    ///
    /// Returns the number of bytes written.
    pub fn write(&mut self, reader: &mut VmReader<'_, Infallible>) -> (copy_len: usize)
        requires
            old(self).invariants(),
            old(reader).invariants(),
        ensures
            self.invariants(),
            old(self).invariants_mut(self),
            reader.invariants(),
            old(reader).invariants_mut(reader),
            self.avail_spec() == 0 || reader.remain_spec() == 0,
            old(self).avail_spec() == self.avail_spec() + copy_len,
            old(reader).remain_spec() == reader.remain_spec() + copy_len,
    {
        reader.read(self)
    }

    /// Writes a value of `Pod` type.
    ///
    /// If the length of the `Pod` type exceeds `self.avail()`,
    /// this method will return `Err`.
    pub fn write_val<T: Pod>(&mut self, new_val: &T) -> (res: Result<()>)
        requires
            old(self).invariants(),
        ensures
            self.invariants(),
            old(self).invariants_mut(self),
            (res.is_err() && old(self).cursor as usize == self.cursor as usize) || (res.is_ok()
                && old(self).cursor as usize == self.cursor as usize - pod_size_spec::<T>()),
    {
        if self.avail() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        let mut reader = VmReader::from(new_val.as_bytes());
        self.write(&mut reader);
        Ok(())
    }

    #[verifier::external_body]
    fn write_once_inner<T: PodOnce>(&self, new_val: &T) {
        let cursor = self.cursor.cast::<T>();
        unsafe { cursor.cast::<T>().write_volatile(*new_val) };
    }

    /// Writes a value of the `PodOnce` type using one non-tearing memory store.
    ///
    /// If the length of the `PodOnce` type exceeds `self.remain()`, this method will return `Err`.
    ///
    /// # Panics
    ///
    /// This method will panic if the current position of the writer does not meet the alignment
    /// requirements of type `T`.
    pub fn write_once<T: PodOnce>(&mut self, new_val: &T) -> (res: Result<()>)
        requires
            old(self).invariants(),
            pod_pnt_is_aligned::<T>(old(self).cursor),
        ensures
            self.invariants(),
            old(self).invariants_mut(self),
            (res.is_err() && old(self).cursor as usize == self.cursor as usize) || (res.is_ok()
                && old(self).cursor as usize == self.cursor as usize - pod_size_spec::<T>()),
    {
        if self.avail() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        // SAFETY: We have checked that the number of bytes remaining is at least the size of `T`
        // and that the cursor is properly aligned with respect to the type `T`. All other safety
        // requirements are the same as for `Self::writer`.

        self.write_once_inner(new_val);

        unsafe { self.cursor_add(core::mem::size_of::<T>()) };

        Ok(())
    }

    #[verifier::external_body]
    fn fill_inner<T: Pod>(&self, value: T, idx: usize) {
        unsafe {
            (self.cursor as *mut T).add(idx).write_volatile(value);
        }
    }

    /// Fills the available space by repeating `value`.
    ///
    /// Returns the number of values written.
    ///
    /// # Panics
    ///
    /// The size of the available space must be a multiple of the size of `value`.
    /// Otherwise, the method would panic.
    pub fn fill<T: Pod>(&mut self, value: T) -> (written_val_num: usize)
        requires
            old(self).invariants(),
            pod_size_spec::<T>() != 0,
            pod_pnt_is_aligned::<T>(old(self).cursor),
            pod_mem_space_is_aligned::<T>(old(self).avail_spec()),
        ensures
            self.invariants(),
            old(self).invariants_mut(self),
            self.avail_spec() == 0,
    {
        let avail = self.avail();

        let written_num = avail / core::mem::size_of::<T>();

        for i in 0..written_num {
            // SAFETY: `written_num` is calculated by the avail size and the size of the type `T`,
            // hence the `add` operation and `write` operation are valid and will only manipulate
            // the memory managed by this writer.
            self.fill_inner(value, i);
        }

        // The available space has been filled so this cursor can be moved to the end.
        self.cursor = self.end;
        written_num
    }

    /// Converts to a fallible writer.
    #[verifier::external_body]
    pub fn to_fallible(self) -> (new_writer: VmWriter<'a, Fallible>)
        requires
            self.invariants(),
        ensures
            new_writer.invariants(),
            new_writer.cursor as usize == self.cursor as usize,
            new_writer.state@.state_eq(&self.state@),
    {
        // SAFETY: It is safe to transmute to a fallible writer since
        // 1. the fallibility is a zero-sized marker type,
        // 2. an infallible reader covers the capabilities of a fallible reader.
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a> VmWriter<'a, Fallible> {
    /// Constructs a `VmWriter` from a pointer and a length, which represents
    /// a memory range in user space.
    ///
    /// The current context should be consistently associated with valid user space during the
    /// entire lifetime `'a`. This is for correct semantics and is not a safety requirement.
    ///
    /// # Safety
    ///
    /// `ptr` must be in user space for `len` bytes.
    pub unsafe fn from_user_space(ptr: *mut u8, len: usize) -> (writer: Self)
        requires
            range_within_uspace_spec(ptr as usize, len),
        ensures
            writer.invariants(),
    {
        Self {
            cursor: ptr,
            end: mut_pnt_add(ptr, len),
            phantom: PhantomData,
            state: Tracked(
                VmIoModel { start: ptr as usize as int, end: mut_pnt_add_spec(ptr as usize, len) },
            ),
        }
    }

    /// Writes a value of `Pod` type.
    ///
    /// If the length of the `Pod` type exceeds `self.avail()`,
    /// or the value can not be write completely,
    /// this method will return `Err`.
    ///
    /// If the memory write failed, this method will return `Err`
    /// and the current writer's cursor remains pointing to
    /// the original starting position.
    pub fn write_val<T: Pod>(&mut self, new_val: &T) -> (res: Result<()>)
        requires
            old(self).invariants(),
        ensures
            self.invariants(),
            old(self).invariants_mut(self),
    {
        if self.avail() < core::mem::size_of::<T>() {
            return Err(Error::InvalidArgs);
        }
        let mut reader = VmReader::from(new_val.as_bytes());

        let res = rw_fallible(&mut reader, self);
        if let Err((err, copied_len)) = res {
            // SAFETY: The `copied_len` is the number of bytes written so far.
            // So the `cursor` can be moved back to the original position.
            unsafe {
                self.cursor_sub(copied_len);
            }
            return Err(err);
        };

        Ok(())
    }

    /// Writes `len` zeros to the target memory.
    ///
    /// This method attempts to fill up to `len` bytes with zeros. If the available
    /// memory from the current cursor position is less than `len`, it will only fill
    /// the available space.
    ///
    /// If the memory write failed due to an unresolvable page fault, this method
    /// will return `Err` with the length set so far.
    pub fn fill_zeros(&mut self, len: usize) -> (res: core::result::Result<usize, (Error, usize)>)
        requires
            old(self).invariants(),
        ensures
            self.invariants(),
            old(self).invariants_mut(self),
            fill_zeros_success(res, old(self).avail_spec() as usize, self.avail_spec() as usize)
                || fill_zeros_failure(
                res,
                old(self).avail_spec() as usize,
                self.avail_spec() as usize,
            ),
    {
        let len_to_set = if self.avail() < len {
            self.avail()
        } else {
            len
        };
        if len_to_set == 0 {
            return Ok(0);
        }
        // SAFETY: The destination is a subset of the memory range specified by
        // the current writer, so it is either valid for writing or in user space.

        let set_len = unsafe {
            let set_len = memset_fallible(self.cursor, 0u8, len_to_set);
            self.cursor_add(set_len);
            set_len
        };
        if set_len < len_to_set {
            Err((Error::PageFault, set_len))
        } else {
            assert(set_len == len_to_set);
            Ok(len_to_set)
        }
    }
}

impl<'a, Fallibility> VmWriter<'a, Fallibility> {
    pub open spec fn avail_spec(&self) -> int {
        self.end as usize - self.cursor as usize
    }

    /// Returns the number of bytes for the available space.
    pub fn avail(&self) -> (avail_size: usize)
        requires
            self.invariants(),
        ensures
            avail_size == self.avail_spec(),
    {
        // SAFETY: the end is equal to or greater than the cursor.
        unsafe { self.end as usize - self.cursor as usize }
    }

    pub open spec fn cursor_spec(&self) -> *mut u8 {
        self.cursor
    }

    /// Returns the cursor pointer, which refers to the address of the next byte to write.
    pub const fn cursor(&self) -> (cursor: *mut u8)
        requires
            self.invariants(),
        ensures
            cursor == self.cursor_spec(),
    {
        self.cursor
    }

    pub open spec fn has_avail_spec(&self) -> bool {
        self.avail_spec() > 0
    }

    /// Returns if it has available space to write.
    pub fn has_avail(&self) -> (has_avail: bool)
        requires
            self.invariants(),
        ensures
            has_avail == self.has_avail_spec(),
    {
        self.avail() > 0
    }

    /// Limits the length of available space.
    ///
    /// This method ensures the post condition of `self.avail() <= max_avail`.
    pub fn limit(self, max_avail: usize) -> (new_writer: Self)
        requires
            self.invariants(),
        ensures
            new_writer.invariants(),
            new_writer.cursor as usize == self.cursor as usize,
            new_writer.avail_spec() == vstd::math::min(self.avail_spec(), max_avail as int),
    {
        if max_avail < self.avail() {
            // SAFETY: the new end is less than the old end.
            let new_writer = unsafe {
                Self {
                    cursor: self.cursor,
                    end: mut_pnt_add(self.cursor, max_avail),
                    phantom: PhantomData,
                    state: Tracked(
                        VmIoModel {
                            start: self.state@.start,
                            end: mut_pnt_add_spec(self.cursor as usize, max_avail),
                        },
                    ),
                }
            };

            return new_writer;
        }
        self
    }

    /// Skips the first `nbytes` bytes of data.
    /// The length of available space is decreased accordingly.
    ///
    /// # Panics
    ///
    /// If `nbytes` is greater than `self.avail()`, then the method panics.
    pub fn skip(self, nbytes: usize) -> (new_writer: Self)
        requires
            self.invariants(),
            nbytes <= self.avail_spec(),
        ensures
            new_writer.invariants(),
            self.invariants_mut(&mut new_writer),
            new_writer.avail_spec() == self.avail_spec() - nbytes,
    {
        // SAFETY: the new cursor is less than or equal to the end.
        let new_writer = unsafe {
            Self {
                cursor: mut_pnt_add(self.cursor, nbytes),
                end: self.end,
                phantom: PhantomData,
                state: self.state,
            }
        };
        new_writer
    }
}

#[verifier::external]
impl<'a> From<&'a mut [u8]> for VmWriter<'a, Infallible> {
    fn from(slice: &'a mut [u8]) -> (writer: Self)
        ensures
            writer.invariants(),
    {
        // SAFETY:
        // - The memory range points to typed memory.
        // - The validity requirements for write accesses are met because the pointer is converted
        //   from a mutable reference that outlives the lifetime `'a`.
        // - The type, i.e., the `u8` slice, is plain-old-data.
        unsafe { Self::from_kernel_space(slice.as_mut_ptr(), slice.len()) }
    }
}

#[verifier::external_body]
pub fn from_vec<'a>(vec: &mut Vec<u8>) -> (writer: VmWriter<'a, Infallible>)
    ensures
        writer.invariants(),
        writer.avail_spec() == old(vec).len(),
        vec.len() == old(vec).len(),
{
    let pnt: *mut u8 = vec_to_ptr(vec);
    unsafe { VmWriter::from_kernel_space(pnt, vec.len()) }
}

#[verifier::external_body]
pub fn from_pod<'a, T: Pod>(mut val: T) -> (writer: VmWriter<'a, Infallible>)
    ensures
        writer.invariants(),
        writer.avail_spec() == pod_size_spec::<T>(),
{
    let (pnt, len) = val.as_bytes_mut();
    unsafe { VmWriter::from_kernel_space(pnt, len) }
}

} // verus!
