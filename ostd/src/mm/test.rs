// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;

use alloc::vec;
use core::mem::size_of;

use ostd_pod::Pod;

use crate::{
    /* Error, */
    mm::{
        /* CachePolicy, */ FallibleVmRead, FallibleVmWrite, /* FrameAllocOptions, PageFlags, PageProperty,
        UFrame, VmSpace, */
        io::{/* VmIo, */ VmReader, VmWriter},
        /* tlb::TlbFlushOp,
        vm_space::get_activated_vm_space, */
    },
    /* prelude::*,
    task::disable_preempt, */
};

mod io {
    use vstd_extra::{assert_eq, ownership::Inv};

    use crate::specs::mm::io::VmIoOwner;

    use super::*;

    verus! {

    /// A dummy Pod struct for testing complex types.
    #[repr(C)]
    #[derive(Clone, Copy, PartialEq, Debug, Pod)]
    pub struct TestPodStruct {
        pub a: u32,
        pub b: u64,
    }

    global layout TestPodStruct is size == 16, align == 8;

    /// Establishes the layout of the local test type.
    pub(crate) proof fn lemma_test_pod_struct_layout()
        ensures
            core::mem::size_of::<TestPodStruct>() == 16,
            core::mem::align_of::<TestPodStruct>() == 8,
    {
        broadcast use VERUS_layout_of_TestPodStruct;
    }

    } // verus!

    /// Tests reading and writing u32 values in Infallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn read_write_u32_infallible() {
        let mut buffer = [0u8; 8];
        proof! {
            vstd_extra::layout::lemma_primitive_layout();
        }
        proof_decl! {
            let tracked mut scratch_owner: VmIoOwner;
            let tracked mut writer_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(scratch_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_infallible = unsafe {
            #[verus_spec(with Ghost(0nat), Tracked(false) => Tracked(writer_owner))]
            VmWriter::from_kernel_space(writer.cursor(), buffer.len())
        };

        // Write two u32 values
        let val1: u32 = 0xDEADBEEF;
        let val2: u32 = 0xFEEDC0DE;
        // Origin: writer_infallible.write_val(&val1).unwrap();
        let res1 = #[verus_spec(with Tracked(&mut writer_owner))]
        writer_infallible.write_val(&val1);
        assert!(res1.is_ok());
        // Origin: writer_infallible.write_val(&val2).unwrap();
        let res2 = #[verus_spec(with Tracked(&mut writer_owner))]
        writer_infallible.write_val(&val2);
        assert!(res2.is_ok());
        // assert_eq!(&buffer[..4], &val1.to_le_bytes()[..]);
        // assert_eq!(&buffer[4..], &val2.to_le_bytes()[..]);

        // Read back the values
        proof_decl! {
            let tracked mut scratch_reader_owner: VmIoOwner;
            let tracked mut reader_owner: VmIoOwner;
        }
        let reader = #[verus_spec(with => Tracked(scratch_reader_owner))]
        VmReader::from(&buffer[..]);
        let mut reader_infallible = unsafe {
            #[verus_spec(with Ghost(0nat) => Tracked(reader_owner))]
            VmReader::from_kernel_space(reader.cursor(), buffer.len())
        };
        // Origin: let read_val1: u32 = reader_infallible.read_val().unwrap();
        let r1: crate::prelude::Result<u32> = #[verus_spec(with Tracked(&mut reader_owner))]
        reader_infallible.read_val();
        assert!(r1.is_ok());
        // Origin: let read_val2: u32 = reader_infallible.read_val().unwrap();
        let r2: crate::prelude::Result<u32> = #[verus_spec(with Tracked(&mut reader_owner))]
        reader_infallible.read_val();
        assert!(r2.is_ok());
        // assert_eq!(val1, read_val1);
        // assert_eq!(val2, read_val2);
    }

    /// Tests reading and writing slices in Infallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn read_write_slice_infallible() {
        let data = [1u8, 2, 3, 4, 5];
        // Origin: let mut buffer = vec![0u8; data.len()];
        let mut buffer = [0u8; 5];
        proof_decl! {
            let tracked mut scratch_owner: VmIoOwner;
            let tracked mut writer_owner: VmIoOwner;
            let tracked mut data_owner: VmIoOwner;
            let tracked mut read_scratch_owner: VmIoOwner;
            let tracked mut read_owner: VmIoOwner;
            let tracked mut read_buffer_owner: VmIoOwner;
            let tracked mut consumed_w: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(scratch_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_infallible = unsafe {
            #[verus_spec(with Ghost(0nat), Tracked(false) => Tracked(writer_owner))]
            VmWriter::from_kernel_space(writer.cursor(), buffer.len())
        };

        // Origin: writer_infallible.write(&mut VmReader::from(&data[..]));
        let mut reader = #[verus_spec(with => Tracked(data_owner))]
        VmReader::from(&data[..]);
        let _ = #[verus_spec(with Tracked(&mut writer_owner), Tracked(&mut data_owner))]
        writer_infallible.write(&mut reader);

        // assert_eq!(buffer, data);

        // Read back the bytes
        let reader = #[verus_spec(with => Tracked(read_scratch_owner))]
        VmReader::from(&buffer[..]);
        let mut reader_infallible = unsafe {
            #[verus_spec(with Ghost(0nat) => Tracked(read_owner))]
            VmReader::from_kernel_space(reader.cursor(), buffer.len())
        };
        let mut read_buffer = [0u8; 5];
        // Origin: reader_infallible.read(&mut VmWriter::from(&mut read_buffer[..]));
        let mut writer = #[verus_spec(with => Tracked(read_buffer_owner))]
        VmWriter::from(&mut read_buffer[..]);
        let _ = #[verus_spec(
            with Tracked(&mut read_owner), Tracked(&mut read_buffer_owner) => Tracked(consumed_w)
        )]
        reader_infallible.read(&mut writer);

        // assert_eq!(read_buffer, data);
    }

    /// Tests writing and reading a struct in Infallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn read_write_struct_infallible() {
        let mut buffer = [0u8; size_of::<TestPodStruct>()];
        proof! {
            vstd_extra::layout::lemma_primitive_layout();
            lemma_test_pod_struct_layout();
        }
        proof_decl! {
            let tracked mut scratch_owner: VmIoOwner;
            let tracked mut writer_owner: VmIoOwner;
            let tracked mut scratch_reader_owner: VmIoOwner;
            let tracked mut reader_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(scratch_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_infallible = unsafe {
            #[verus_spec(with Ghost(0nat), Tracked(false) => Tracked(writer_owner))]
            VmWriter::from_kernel_space(writer.cursor(), buffer.len())
        };

        let test_struct = TestPodStruct {
            a: 0x12345678,
            b: 0xABCDEF0123456789,
        };
        // Origin: writer_infallible.write_val(&test_struct).unwrap();
        let res = #[verus_spec(with Tracked(&mut writer_owner))]
        writer_infallible.write_val(&test_struct);
        res.unwrap();

        // Read back the struct
        let reader = #[verus_spec(with => Tracked(scratch_reader_owner))]
        VmReader::from(&buffer[..]);
        let mut reader_infallible = unsafe {
            #[verus_spec(with Ghost(0nat) => Tracked(reader_owner))]
            VmReader::from_kernel_space(reader.cursor(), buffer.len())
        };
        // Origin: let read_struct: TestPodStruct = reader_infallible.read_val().unwrap();
        let res = #[verus_spec(with Tracked(&mut reader_owner))]
        reader_infallible.read_val::<TestPodStruct>();
        res.unwrap();
        // assert_eq!(test_struct, read_struct);
    }

    /// Ensures reading beyond the buffer panics in Infallible mode.
    /* #[ktest] */
    /* #[should_panic] */
    #[verus_spec]
    fn read_beyond_buffer_infallible() {
        let buffer = [1u8, 2, 3];
        proof! {
            vstd_extra::layout::lemma_primitive_layout();
        }
        proof_decl! {
            let tracked mut scratch_owner: VmIoOwner;
            let tracked mut reader_owner: VmIoOwner;
        }
        let reader = #[verus_spec(with => Tracked(scratch_owner))]
        VmReader::from(&buffer[..]);
        let mut reader_infallible = unsafe {
            #[verus_spec(with Ghost(0nat) => Tracked(reader_owner))]
            VmReader::from_kernel_space(reader.cursor(), buffer.len())
        };

        // Attempt to read a u32 which requires 4 bytes, but buffer has only 3
        // Origin: let _val: u32 = reader_infallible.read_val().unwrap();
        let result = #[verus_spec(with Tracked(&mut reader_owner))]
        reader_infallible.read_val::<u32>();
        proof! {
            assert(result == Err(crate::Error::InvalidArgs));
        }
    }

    /// Ensures writing beyond the buffer panics in Infallible mode.
    /* #[ktest] */
    /* #[should_panic] */
    #[verus_spec]
    fn write_beyond_buffer_infallible() {
        let mut buffer = [0u8; 3];
        proof! {
            vstd_extra::layout::lemma_primitive_layout();
        }
        proof_decl! {
            let tracked mut scratch_owner: VmIoOwner;
            let tracked mut writer_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(scratch_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_infallible = unsafe {
            #[verus_spec(with Ghost(0nat), Tracked(false) => Tracked(writer_owner))]
            VmWriter::from_kernel_space(writer.cursor(), buffer.len())
        };

        // Attempt to write a u32 which requires 4 bytes, but buffer has only 3
        let val: u32 = 0xDEADBEEF;
        // Origin: writer_infallible.write_val(&val).unwrap();
        let result = #[verus_spec(with Tracked(&mut writer_owner))]
        writer_infallible.write_val(&val);
        proof! {
            assert(result == Err(crate::Error::InvalidArgs));
        }
    }

    /// Tests the `fill` method in Infallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn fill_infallible() {
        // Origin: let mut buffer = vec![0u8; 8];
        let mut buffer = [0u8; 8];
        proof! {
            vstd_extra::layout::lemma_primitive_layout();
        }
        proof_decl! {
            let tracked mut scratch_owner: VmIoOwner;
            let tracked mut owner: VmIoOwner;
            let tracked mut reader_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(scratch_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_infallible = unsafe {
            #[verus_spec(with Ghost(0nat), Tracked(false) => Tracked(owner))]
            VmWriter::from_kernel_space(writer.cursor(), buffer.len())
        };

        // Fill with 0xFF
        let filled = #[verus_spec(with Tracked(&mut owner) => Tracked(reader_owner))]
        writer_infallible.fill(0xFFu8);
        assert_eq!(filled, 8);
        // assert_eq!(buffer, vec![0xFF; 8]);

        // Ensure the cursor is at the end
        assert_eq!(writer_infallible.avail(), 0);
    }

    /// Tests the `skip` method for reading in Infallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn skip_read_infallible() {
        let data = [10u8, 20, 30, 40, 50];
        proof_decl! {
            let tracked mut scratch_owner: VmIoOwner;
            let tracked mut reader_owner: VmIoOwner;
        }
        let reader = #[verus_spec(with => Tracked(scratch_owner))]
        VmReader::from(&data[..]);
        let mut reader_infallible = unsafe {
            #[verus_spec(with Ghost(0nat) => Tracked(reader_owner))]
            VmReader::from_kernel_space(reader.cursor(), reader.remain())
        };

        // Skip first two bytes
        // Origin: reader_infallible.skip(2);
        let reader_infallible = reader_infallible.skip(2);
        proof! {
            let tracked front = reader_owner.advance(2);
        }

        // Read the remaining bytes
        let mut read_buffer = [0u8; 3];
        proof_decl! {
            let tracked mut dest_owner: VmIoOwner;
            let tracked mut consumed_dest: VmIoOwner;
        }
        // Origin: reader_infallible.read(&mut VmWriter::from(&mut read_buffer[..]));
        let mut dest_writer = #[verus_spec(with => Tracked(dest_owner))]
        VmWriter::from(&mut read_buffer[..]);
        let copied = #[verus_spec(with Tracked(&mut reader_owner), Tracked(&mut dest_owner) => Tracked(consumed_dest))]
        reader_infallible.read(&mut dest_writer);
        assert_eq!(copied, 3);
        // assert_eq!(read_buffer, [30, 40, 50]);
    }

    /// Tests the `skip` method for writing in Infallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn skip_write_infallible() {
        let mut buffer = [0u8; 5];
        proof_decl! {
            let tracked mut scratch_owner: VmIoOwner;
            let tracked mut writer_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(scratch_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_infallible = unsafe {
            #[verus_spec(with Ghost(0nat), Tracked(false) => Tracked(writer_owner))]
            VmWriter::from_kernel_space(writer.cursor(), writer.avail())
        };

        // Skip first two bytes
        // Origin: writer_infallible.skip(2);
        let writer_infallible = writer_infallible.skip(2);
        assert_eq!(writer_infallible.avail(), 3);
        proof! {
            let tracked front = writer_owner.advance(2);
        }

        // Write [100, 101, 102]
        let data = [100u8, 101, 102];
        proof_decl! {
            let tracked mut reader_owner: VmIoOwner;
        }
        // Origin: writer_infallible.write(&mut VmReader::from(&data[..]));
        let mut reader = #[verus_spec(with => Tracked(reader_owner))]
        VmReader::from(&data[..]);
        let copied = #[verus_spec(with Tracked(&mut writer_owner), Tracked(&mut reader_owner))]
        writer_infallible.write(&mut reader);
        assert_eq!(copied, 3);
        // assert_eq!(buffer, [0, 0, 100, 101, 102]);
    }

    /// Tests the `limit` method for VmReader in Infallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn limit_read_infallible() {
        let data = [1u8, 2, 3, 4, 5];
        proof_decl! {
            let tracked mut reader_owner: VmIoOwner;
        }
        let mut reader = #[verus_spec(with => Tracked(reader_owner))]
        VmReader::from(&data[..]);

        let limited_reader = reader.limit(3);
        // Origin keeps the receiver; the proof helper below only shrinks the ghost window.
        assert_eq!(limited_reader.remain(), 3);
        /* Shrink the owner to the limited window to keep `wf` for the copies. */
        proof! {
            reader_owner.tracked_shrink_range_front(3);
        }

        let mut read_buffer = [0u8; 3];
        proof_decl! {
            let tracked mut dest_owner: VmIoOwner;
            let tracked mut consumed_dest: VmIoOwner;
        }
        // Origin: limited_reader.read(&mut VmWriter::from(&mut read_buffer[..]));
        let mut dest_writer = #[verus_spec(with => Tracked(dest_owner))]
        VmWriter::from(&mut read_buffer[..]);
        let copied = #[verus_spec(with Tracked(&mut reader_owner), Tracked(&mut dest_owner) => Tracked(consumed_dest))]
        limited_reader.read(&mut dest_writer);
        assert_eq!(copied, 3);
        // assert_eq!(read_buffer, [1, 2, 3]);

        // Ensures no more data can be read
        let mut extra_buffer = [0u8; 1];
        proof_decl! {
            let tracked mut extra_owner: VmIoOwner;
            let tracked mut extra_consumed: VmIoOwner;
        }
        // Origin: let extra_read = limited_reader.read(&mut VmWriter::from(&mut extra_buffer[..]));
        let mut extra_writer = #[verus_spec(with => Tracked(extra_owner))]
        VmWriter::from(&mut extra_buffer[..]);
        let extra_read = #[verus_spec(with Tracked(&mut reader_owner), Tracked(&mut extra_owner) => Tracked(extra_consumed))]
        limited_reader.read(&mut extra_writer);
        assert_eq!(extra_read, 0);
    }

    /// Tests the `limit` method for VmWriter in Infallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn limit_write_infallible() {
        let mut buffer = [0u8; 5];
        proof_decl! {
            let tracked mut writer_owner: VmIoOwner;
        }
        let mut writer = #[verus_spec(with => Tracked(writer_owner))]
        VmWriter::from(&mut buffer[..]);

        let limited_writer = writer.limit(3);
        assert_eq!(limited_writer.avail(), 3);
        /* Shrink the owner to the limited window to keep `wf` for the writes. */
        proof! {
            writer_owner.tracked_shrink_range_front(3);
        }

        // Writes [10, 20, 30, 40] but only first three should be written
        let data = [10u8, 20, 30, 40];
        #[verus_spec(it =>
            invariant
                limited_writer.inv(),
                limited_writer.wf(writer_owner),
                writer_owner.has_write_view(),
        )]
        for val in data.iter() {
            #[verus_spec(with Tracked(&mut writer_owner))]
            let _ = limited_writer.write_val(val);
        }
        // assert_eq!(buffer, [10, 20, 30, 0, 0]);
    }

    /// Tests the `read_slice` and `write_slice` methods in Infallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn read_write_slice_vmio_infallible() {
        let data = [100u8, 101, 102, 103, 104];
        let mut buffer = [0u8; 5];
        proof_decl! {
            let tracked mut scratch_owner: VmIoOwner;
            let tracked mut writer_owner: VmIoOwner;
            let tracked mut data_owner: VmIoOwner;
            let tracked mut read_scratch_owner: VmIoOwner;
            let tracked mut read_owner: VmIoOwner;
            let tracked mut read_data_owner: VmIoOwner;
            let tracked mut consumed_w: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(scratch_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_infallible = unsafe {
            #[verus_spec(with Ghost(0nat), Tracked(false) => Tracked(writer_owner))]
            VmWriter::from_kernel_space(writer.cursor(), buffer.len())
        };

        // Origin: writer_infallible.write(&mut VmReader::from(&data[..]));
        let mut reader = #[verus_spec(with => Tracked(data_owner))]
        VmReader::from(&data[..]);
        let _ = #[verus_spec(with Tracked(&mut writer_owner), Tracked(&mut data_owner))]
        writer_infallible.write(&mut reader);

        // assert_eq!(buffer, data);

        let reader = #[verus_spec(with => Tracked(read_scratch_owner))]
        VmReader::from(&buffer[..]);
        let mut reader_infallible = unsafe {
            #[verus_spec(with Ghost(0nat) => Tracked(read_owner))]
            VmReader::from_kernel_space(reader.cursor(), buffer.len())
        };
        let mut read_data = [0u8; 5];
        // Origin: reader_infallible.read(&mut VmWriter::from(&mut read_data[..]));
        let mut writer = #[verus_spec(with => Tracked(read_data_owner))]
        VmWriter::from(&mut read_data[..]);
        let _ = #[verus_spec(
            with Tracked(&mut read_owner), Tracked(&mut read_data_owner) => Tracked(consumed_w)
        )]
        reader_infallible.read(&mut writer);

        // assert_eq!(read_data, data);
    }

    /* /// Tests the `read_once` and `write_once` methods in Infallible mode.
    #[ktest]
    fn read_write_once_infallible() {
        let mut buffer = [0u8; 8];
        let writer = VmWriter::from(&mut buffer[..]);
        let mut writer_infallible =
            unsafe { VmWriter::from_kernel_space(writer.cursor(), buffer.len()) };

        let val: u64 = 0x1122334455667788;
        writer_infallible.write_once(&val).unwrap();

        // Reads back the value
        let reader = VmReader::from(&buffer[..]);
        let mut reader_infallible =
            unsafe { VmReader::from_kernel_space(reader.cursor(), buffer.len()) };

        let read_val: u64 = reader_infallible.read_once().unwrap();
        assert_eq!(val, read_val);
    } */

    /// Tests the `write_val` method in Infallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn write_val_infallible() {
        let mut buffer = [0u8; 12];
        proof! {
            vstd_extra::layout::lemma_primitive_layout();
        }
        proof_decl! {
            let tracked mut scratch_owner: VmIoOwner;
            let tracked mut writer_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(scratch_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_infallible = unsafe {
            #[verus_spec(with Ghost(0nat), Tracked(false) => Tracked(writer_owner))]
            VmWriter::from_kernel_space(writer.cursor(), buffer.len())
        };

        let values = [1u32, 2, 3];
        #[verus_spec(it =>
            invariant
                writer_infallible.inv(),
                writer_infallible.wf(writer_owner),
                writer_owner.has_write_view(),
                writer_infallible.avail_spec() == 12 - 4 * it.index(),
                it.index() <= 3,
        )]
        for val in values.iter() {
            // Origin: writer_infallible.write_val(val).unwrap();
            let res = #[verus_spec(with Tracked(&mut writer_owner))]
            writer_infallible.write_val(val);
            res.unwrap();
        }
        // assert_eq!(buffer, [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0]);
    }

    /// Tests the `FallbackVmRead` and `FallbackVmWrite` traits (using Fallible mode).
    /// Note: Since simulating page faults is non-trivial in a test environment,
    /// we'll focus on successful read and write operations.
    /* #[ktest] */
    #[verus_spec]
    fn fallible_read_write() {
        let mut buffer = [0u8; 8];
        proof_decl! {
            let tracked mut writer_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(writer_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_fallible = writer.to_fallible();

        let val: u64 = 0xAABBCCDDEEFF0011;
        assert!(writer_fallible.has_avail());
        // Origin: writer_fallible.write_val(&val).unwrap();
        let write_result = writer_fallible.write_val(&val);

        // Reads back the value
        proof_decl! {
            let tracked mut reader_owner: VmIoOwner;
        }
        let reader = #[verus_spec(with => Tracked(reader_owner))]
        VmReader::from(&buffer[..]);
        let mut reader_fallible = reader.to_fallible();

        assert!(reader_fallible.has_remain());
        // Origin: let read_val: u64 = reader_fallible.read_val().unwrap();
        let read_result: crate::prelude::Result<u64> = reader_fallible.read_val();
        // assert_eq!(val, read_val);
    }

    /// Mimics partial reads in Fallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn partial_read_fallible() {
        let data = [10u8, 20, 30, 40, 50];
        proof_decl! {
            let tracked mut reader_scratch_owner: VmIoOwner;
        }
        let reader = #[verus_spec(with => Tracked(reader_scratch_owner))]
        VmReader::from(&data[..]);
        let mut reader_fallible = reader.to_fallible();

        // Limits the reader to 3 bytes
        let limited_reader = reader_fallible.limit(3);

        let mut writer_buffer = [0u8; 5];
        proof_decl! {
            let tracked mut writer_scratch_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(writer_scratch_owner))]
        VmWriter::from(&mut writer_buffer[..]);
        let mut writer_fallible = writer.to_fallible();

        // Attempts to read 5 bytes into a writer limited to 3 bytes
        let result = limited_reader.read_fallible(&mut writer_fallible);
        // assert!(result.is_ok());
        // assert_eq!(result.unwrap(), 3);
        // assert_eq!(&writer_buffer[..3], &[10, 20, 30]);
    }

    /// Mimics partial writes in Fallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn partial_write_fallible() {
        let mut buffer = [0u8; 5];
        proof_decl! {
            let tracked mut writer_scratch_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(writer_scratch_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_fallible = writer.to_fallible();

        // Limits the writer to 3 bytes
        let limited_writer = writer_fallible.limit(3);

        let data = [10u8, 20, 30, 40, 50];
        proof_decl! {
            let tracked mut reader_scratch_owner: VmIoOwner;
        }
        let mut reader = #[verus_spec(with => Tracked(reader_scratch_owner))]
        VmReader::from(&data[..]);

        // Attempts to write 5 bytes into a writer limited to 3 bytes
        let result = limited_writer.write_fallible(&mut reader);
        // assert!(result.is_ok());
        // assert_eq!(result.unwrap(), 3);
        // assert_eq!(&buffer[..3], &[10, 20, 30]);
    }

    /// Tests `write_val` and `read_val` methods in Fallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn read_write_val_fallible() {
        let mut buffer = [0u8; 8];
        proof_decl! {
            let tracked mut writer_owner: VmIoOwner;
            let tracked mut reader_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(writer_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_fallible = writer.to_fallible();

        let val: u64 = 0xAABBCCDDEEFF0011;
        // Origin: writer_fallible.write_val(&val).unwrap();
        let write_result = writer_fallible.write_val(&val);

        // Reads back the value
        let reader = #[verus_spec(with => Tracked(reader_owner))]
        VmReader::from(&buffer[..]);
        let mut reader_fallible = reader.to_fallible();

        // Origin: let read_val: u64 = reader_fallible.read_val().unwrap();
        let read_result: crate::prelude::Result<u64> = reader_fallible.read_val();
        // assert_eq!(val, read_val);
    }

    /// Tests the `collect` method in Fallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn collect_fallible() {
        let data = [5u8, 6, 7, 8, 9];
        proof_decl! {
            let tracked mut reader_scratch_owner: VmIoOwner;
        }
        let reader = #[verus_spec(with => Tracked(reader_scratch_owner))]
        VmReader::from(&data[..]);
        let mut reader_fallible = reader.to_fallible();

        // Origin: let collected = reader_fallible.collect().unwrap();
        let collected = reader_fallible.collect();
        // assert_eq!(collected, data);
    }

    /// Tests partial collection in Fallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn collect_partial_fallible() {
        let data = [1u8, 2, 3, 4, 5];
        proof_decl! {
            let tracked mut reader_scratch_owner: VmIoOwner;
        }
        let reader = #[verus_spec(with => Tracked(reader_scratch_owner))]
        VmReader::from(&data[..]);
        let mut reader_fallible = reader.to_fallible();

        // Limits the reader to 3 bytes
        let limited_reader = reader_fallible.limit(3);

        let result = limited_reader.collect();
        // assert!(result.is_ok());
        // assert_eq!(result.unwrap(), vec![1, 2, 3]);
    }

    /// Tests the `fill_zeros` method in Fallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn fill_zeros_fallible() {
        let mut buffer = vec![1u8; 8];
        proof_decl! {
            let tracked mut writer_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(writer_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_fallible = writer.to_fallible();

        // Origin: writer_fallible.fill_zeros(8).unwrap();
        let result = writer_fallible.fill_zeros(8);
        // assert_eq!(buffer, [0u8; 8]);
    }

    /// Tests handling invalid arguments in Fallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn invalid_args_read_write_fallible() {
        let mut buffer = [0u8; 3];
        proof! {
            vstd_extra::layout::lemma_primitive_layout();
        }
        proof_decl! {
            let tracked mut writer_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(writer_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_fallible = writer.to_fallible();

        // Attempts to write a u32 which requires 4 bytes, but buffer has only 3
        let val: u32 = 0xDEADBEEF;
        let result = writer_fallible.write_val(&val);
        proof! {
            assert(result == Err(crate::Error::InvalidArgs));
        }

        // Attempts to read a u32 which requires 4 bytes, but buffer has only 3
        proof_decl! {
            let tracked mut reader_owner: VmIoOwner;
        }
        let reader = #[verus_spec(with => Tracked(reader_owner))]
        VmReader::from(&buffer[..]);
        let mut reader_fallible = reader.to_fallible();
        let result = reader_fallible.read_val::<u32>();
        proof! {
            assert(result == Err(crate::Error::InvalidArgs));
        }
    }

    /// Tests handling invalid read/write in Infallible mode.
    /* #[ktest] */
    #[verus_spec]
    fn invalid_read_write_infallible() {
        let mut buffer = [0u8; 3];
        proof! {
            vstd_extra::layout::lemma_primitive_layout();
        }
        proof_decl! {
            let tracked mut scratch_owner: VmIoOwner;
            let tracked mut writer_owner: VmIoOwner;
        }
        let writer = #[verus_spec(with => Tracked(scratch_owner))]
        VmWriter::from(&mut buffer[..]);
        let mut writer_infallible = unsafe {
            #[verus_spec(with Ghost(0nat), Tracked(false) => Tracked(writer_owner))]
            VmWriter::from_kernel_space(writer.cursor(), buffer.len())
        };

        // Attempts to write a u32 which requires 4 bytes, but buffer has only 3
        let val: u32 = 0xDEADBEEF;
        let result = #[verus_spec(with Tracked(&mut writer_owner))]
        writer_infallible.write_val(&val);
        // Origin: assert_eq!(result, Err(Error::InvalidArgs));
        proof! {
            assert(result == Err(crate::Error::InvalidArgs));
        }

        // Attempts to read a u32 which requires 4 bytes, but buffer has only 3
        proof_decl! {
            let tracked mut scratch_reader_owner: VmIoOwner;
            let tracked mut reader_owner: VmIoOwner;
        }
        let reader = #[verus_spec(with => Tracked(scratch_reader_owner))]
        VmReader::from(&buffer[..]);
        let mut reader_infallible = unsafe {
            #[verus_spec(with Ghost(0nat) => Tracked(reader_owner))]
            VmReader::from_kernel_space(reader.cursor(), buffer.len())
        };
        let result = #[verus_spec(with Tracked(&mut reader_owner))]
        reader_infallible.read_val::<u32>();
        // Origin: assert_eq!(result, Err(Error::InvalidArgs));
        proof! {
            assert(result == Err(crate::Error::InvalidArgs));
        }
    }

    /* /// Tests the `write_vals` method in VmIO.
    #[ktest]
    fn write_vals_segment() {
        let mut buffer = [0u8; 12];
        let segment = FrameAllocOptions::new().alloc_segment(1).unwrap();
        let values = [1u32, 2, 3];
        let nr_written = segment.write_vals(0, values.iter(), 4).unwrap();
        assert_eq!(nr_written, 3);
        segment.read_bytes(0, &mut buffer[..]).unwrap();
        assert_eq!(buffer, [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0]);
        // Writes with error offset
        let result = segment.write_vals(8192, values.iter(), 4);
        assert_eq!(result, Err(Error::InvalidArgs));
    }

    /// Tests the `write_slice` method in VmIO.
    #[ktest]
    fn write_slice_segment() {
        let mut buffer = [0u8; 12];
        let segment = FrameAllocOptions::new().alloc_segment(1).unwrap();
        let data = [1u8, 2, 3, 4, 5];
        segment.write_slice(0, &data[..]).unwrap();
        segment.read_bytes(0, &mut buffer[..]).unwrap();
        assert_eq!(buffer[..5], data);
    }

    /// Tests the `read_val` method in VmIO.
    #[ktest]
    fn read_val_segment() {
        let segment = FrameAllocOptions::new().alloc_segment(1).unwrap();
        let values = [1u32, 2, 3];
        segment.write_vals(0, values.iter(), 4).unwrap();
        let val: u32 = segment.read_val(0).unwrap();
        assert_eq!(val, 1);
    }

    /// Tests the `read_slice` method in VmIO.
    #[ktest]
    fn read_slice_segment() {
        let segment = FrameAllocOptions::new().alloc_segment(1).unwrap();
        let values = [1u32, 2, 3];
        segment.write_vals(0, values.iter(), 4).unwrap();
        let mut read_buffer = [0u8; 12];
        segment.read_slice(0, &mut read_buffer[..]).unwrap();
        assert_eq!(read_buffer, [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0]);
    } */
}

/* The vm-space tests exercise real page tables, activation and TLB flushes
 * that are outside the current verification scope; kept verbatim for the
 * migration.

mod vmspace {
    use super::*;

    /// Helper function to create a dummy `UFrame`.
    fn create_dummy_frame() -> UFrame {
        let frame = FrameAllocOptions::new().alloc_frame().unwrap();
        let uframe: UFrame = frame.into();
        uframe
    }

    /// Creates a new `VmSpace` and verifies its initial state.
    #[ktest]
    fn vmspace_creation() {
        let vmspace = VmSpace::new();
        let range = 0x0..0x1000;
        let preempt_guard = disable_preempt();
        let mut cursor = vmspace
            .cursor(&preempt_guard, &range)
            .expect("Failed to create cursor");
        assert_eq!(cursor.next(), Some((0..0x1000, None)));
    }

    /// Maps and unmaps a single page using `CursorMut`.
    #[ktest]
    fn vmspace_map_unmap() {
        let vmspace = VmSpace::default();
        let range = 0x1000..0x2000;
        let frame = create_dummy_frame();
        let prop = PageProperty::new_user(PageFlags::R, CachePolicy::Writeback);
        let preempt_guard = disable_preempt();

        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            // Initially, the page should not be mapped.
            assert_eq!(cursor_mut.query().unwrap(), (range.clone(), None));
            // Maps a frame.
            cursor_mut.map(frame.clone(), prop);
        }

        // Queries the mapping.
        {
            let mut cursor = vmspace
                .cursor(&preempt_guard, &range)
                .expect("Failed to create cursor");
            assert_eq!(cursor.virt_addr(), range.start);
            assert_eq!(
                cursor.query().unwrap(),
                (range.clone(), Some((frame.clone(), prop)))
            );
        }

        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            // Unmaps the frame.
            cursor_mut.unmap(range.start);
        }

        // Queries to ensure it's unmapped.
        let mut cursor = vmspace
            .cursor(&preempt_guard, &range)
            .expect("Failed to create cursor");
        assert_eq!(cursor.query().unwrap(), (range, None));
    }

    /// Maps a page twice and unmaps twice using `CursorMut`.
    #[ktest]
    fn vmspace_map_twice() {
        let vmspace = VmSpace::default();
        let range = 0x1000..0x2000;
        let frame = create_dummy_frame();
        let prop = PageProperty::new_user(PageFlags::R, CachePolicy::Writeback);
        let preempt_guard = disable_preempt();

        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            cursor_mut.map(frame.clone(), prop);
        }

        {
            let mut cursor = vmspace
                .cursor(&preempt_guard, &range)
                .expect("Failed to create cursor");
            assert_eq!(
                cursor.query().unwrap(),
                (range.clone(), Some((frame.clone(), prop)))
            );
        }

        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            cursor_mut.map(frame.clone(), prop);
        }

        {
            let mut cursor = vmspace
                .cursor(&preempt_guard, &range)
                .expect("Failed to create cursor");
            assert_eq!(
                cursor.query().unwrap(),
                (range.clone(), Some((frame.clone(), prop)))
            );
        }

        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            cursor_mut.unmap(range.start);
        }

        let mut cursor = vmspace
            .cursor(&preempt_guard, &range)
            .expect("Failed to create cursor");
        assert_eq!(cursor.query().unwrap(), (range, None));
    }

    /// Unmaps twice using `CursorMut`.
    #[ktest]
    fn vmspace_unmap_twice() {
        let vmspace = VmSpace::default();
        let range = 0x1000..0x2000;
        let frame = create_dummy_frame();
        let prop = PageProperty::new_user(PageFlags::R, CachePolicy::Writeback);
        let preempt_guard = disable_preempt();

        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            cursor_mut.map(frame.clone(), prop);
        }

        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            cursor_mut.unmap(range.start);
        }

        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            cursor_mut.unmap(range.start);
        }

        let mut cursor = vmspace
            .cursor(&preempt_guard, &range)
            .expect("Failed to create cursor");
        assert_eq!(cursor.query().unwrap(), (range, None));
    }

    /// Activates and deactivates the `VmSpace` in single-CPU scenarios.
    #[ktest]
    fn vmspace_activate() {
        let vmspace = Arc::new(VmSpace::new());

        // Activates the VmSpace.
        vmspace.activate();
        assert_eq!(get_activated_vm_space(), Arc::as_ptr(&vmspace));

        // Deactivates the VmSpace.
        let vmspace2 = Arc::new(VmSpace::new());
        vmspace2.activate();
        assert_eq!(get_activated_vm_space(), Arc::as_ptr(&vmspace2));
    }

    /// Tests the `flusher` method of `CursorMut`.
    #[ktest]
    fn cursor_mut_flusher() {
        let vmspace = VmSpace::new();
        let range = 0x4000..0x5000;
        let frame = create_dummy_frame();
        let prop = PageProperty::new_user(PageFlags::R, CachePolicy::Writeback);
        let preempt_guard = disable_preempt();

        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            cursor_mut.map(frame.clone(), prop);
        }

        {
            // Verifies that the mapping exists.
            let mut cursor = vmspace
                .cursor(&preempt_guard, &range)
                .expect("Failed to create cursor");
            assert_eq!(
                cursor.next().unwrap(),
                (range.clone(), Some((frame.clone(), prop)))
            );
        }

        {
            // Flushes the TLB using a mutable cursor.
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            cursor_mut.flusher().issue_tlb_flush(TlbFlushOp::All);
            cursor_mut.flusher().dispatch_tlb_flush();
        }

        {
            // Verifies that the mapping still exists.
            let mut cursor = vmspace
                .cursor(&preempt_guard, &range)
                .expect("Failed to create cursor");
            assert_eq!(
                cursor.next().unwrap(),
                (
                    range.clone(),
                    Some((
                        frame.clone(),
                        PageProperty::new_user(PageFlags::R, CachePolicy::Writeback)
                    ))
                )
            );
        }
    }

    /// Verifies the `VmReader` and `VmWriter` interfaces.
    #[ktest]
    fn vmspace_reader_writer() {
        let vmspace = Arc::new(VmSpace::new());
        let range = 0x4000..0x5000;
        let preempt_guard = disable_preempt();
        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            let frame = create_dummy_frame();
            let prop = PageProperty::new_user(PageFlags::R, CachePolicy::Writeback);
            cursor_mut.map(frame, prop);
        }

        // Mocks the current page table paddr to match the VmSpace's root paddr.
        // Fails if the VmSpace is not the current task's user space.

        // Attempts to create a reader.
        let reader_result = vmspace.reader(0x4000, 0x1000);
        // Expects failure in a test environment.
        assert!(reader_result.is_err());

        // Attempts to create a writer.
        let writer_result = vmspace.writer(0x4000, 0x1000);
        assert!(writer_result.is_err());

        // Activates the VmSpace.
        vmspace.activate();

        // Attempts to create a reader.
        let reader_result = vmspace.reader(0x4000, 0x1000);
        assert!(reader_result.is_ok());
        // Attempts to create a writer.
        let writer_result = vmspace.writer(0x4000, 0x1000);
        assert!(writer_result.is_ok());

        // Attempts to create a reader with an out-of-range address.
        let reader_result = vmspace.reader(0x4000, usize::MAX);
        assert!(reader_result.is_err());
        // Attempts to create a writer with an out-of-range address.
        let writer_result = vmspace.writer(0x4000, usize::MAX);
        assert!(writer_result.is_err());
    }

    /// Creates overlapping cursors and verifies handling.
    #[ktest]
    fn overlapping_cursors() {
        let vmspace = VmSpace::new();
        let range1 = 0x5000..0x6000;
        let range2 = 0x5800..0x6800; // Overlaps with range1.
        let preempt_guard = disable_preempt();

        // Creates the first cursor.
        let _cursor1 = vmspace
            .cursor(&preempt_guard, &range1)
            .expect("Failed to create first cursor");

        // Attempts to create the second overlapping cursor.
        let cursor2_result = vmspace.cursor(&preempt_guard, &range2);
        assert!(cursor2_result.is_err());
    }

    /// Iterates over the `Cursor` using the `Iterator` trait.
    #[ktest]
    fn cursor_iterator() {
        let vmspace = VmSpace::new();
        let range = 0x6000..0x7000;
        let frame = create_dummy_frame();
        let preempt_guard = disable_preempt();
        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            let prop = PageProperty::new_user(PageFlags::R, CachePolicy::Writeback);
            cursor_mut.map(frame.clone(), prop);
        }

        let mut cursor = vmspace
            .cursor(&preempt_guard, &range)
            .expect("Failed to create cursor");
        assert!(cursor.jump(range.start).is_ok());
        let item = cursor.next();
        assert_eq!(
            item.unwrap(),
            (
                range.clone(),
                Some((
                    frame.clone(),
                    PageProperty::new_user(PageFlags::R, CachePolicy::Writeback)
                ))
            )
        );

        // Confirms no additional items.
        assert!(cursor.next().is_none());
    }

    /// Protects a range of pages.
    #[ktest]
    fn protect_next() {
        let vmspace = VmSpace::new();
        let range = 0x7000..0x8000;
        let frame = create_dummy_frame();
        let preempt_guard = disable_preempt();
        {
            let mut cursor_mut = vmspace
                .cursor_mut(&preempt_guard, &range)
                .expect("Failed to create mutable cursor");
            let prop = PageProperty::new_user(PageFlags::RW, CachePolicy::Writeback);
            cursor_mut.map(frame.clone(), prop);
            cursor_mut.jump(range.start).expect("Failed to jump cursor");
            let protected_range = cursor_mut.protect_next(0x1000, |prop| {
                prop.flags = PageFlags::R;
            });

            assert_eq!(protected_range, Some(0x7000..0x8000));
        }
        // Confirms that the property was updated.
        let mut cursor = vmspace
            .cursor(&preempt_guard, &range)
            .expect("Failed to create cursor");
        assert_eq!(
            cursor.next().unwrap(),
            (
                range.clone(),
                Some((
                    frame.clone(),
                    PageProperty::new_user(PageFlags::R, CachePolicy::Writeback)
                ))
            )
        );
    }

    /// Attempts to map unaligned lengths and expects a panic.
    #[ktest]
    #[should_panic]
    fn unaligned_unmap_panics() {
        let vmspace = VmSpace::new();
        let range = 0xA000..0xB000;
        let preempt_guard = disable_preempt();
        let mut cursor_mut = vmspace
            .cursor_mut(&preempt_guard, &range)
            .expect("Failed to create mutable cursor");
        cursor_mut.unmap(0x800); // Not page-aligned.
    }

    /// Attempts to protect a partial page and expects a panic.
    #[ktest]
    #[should_panic]
    fn protect_out_range_page() {
        let vmspace = VmSpace::new();
        let range = 0xB000..0xC000;
        let preempt_guard = disable_preempt();
        let mut cursor_mut = vmspace
            .cursor_mut(&preempt_guard, &range)
            .expect("Failed to create mutable cursor");
        cursor_mut.protect_next(0x2000, |_| {}); // Not page-aligned.
    }
} */
