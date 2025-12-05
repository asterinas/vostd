// SPDX-License-Identifier: MPL-2.0
//! Untyped physical memory management.
//!
//! As detailed in [`crate::mm::frame`], untyped memory can be accessed with
//! relaxed rules but we cannot create references to them. This module provides
//! the declaration of untyped frames and segments, and the implementation of
//! extra functionalities (such as [`VmIo`]) for them.
use super::{Frame /*, Segment*/};
use crate::{
    mm::{
        //        io::{FallibleVmRead, FallibleVmWrite, VmIo, VmReader, VmWriter},
        paddr_to_vaddr, //Infallible,
    },
    //    Error, Result,
};

use aster_common::prelude::frame::AnyFrameMeta;

/*
/// Makes a structure usable as untyped frame metadata.
///
/// If this macro is used for built-in typed frame metadata, it won't compile.
#[macro_export]
macro_rules! impl_untyped_frame_meta_for {
    // Implement without specifying the drop behavior.
    ($t:ty) => {
        // SAFETY: Untyped frames can be safely read.
        unsafe impl $crate::mm::frame::meta::AnyFrameMeta for $t {
            fn is_untyped(&self) -> bool {
                true
            }
        }
        impl $crate::mm::frame::untyped::AnyUFrameMeta for $t {}
    };
    // Implement with a customized drop function.
    ($t:ty, $body:expr) => {
        // SAFETY: Untyped frames can be safely read.
        unsafe impl $crate::mm::frame::meta::AnyFrameMeta for $t {
            fn on_drop(&mut self, reader: &mut $crate::mm::VmReader<$crate::mm::Infallible>) {
                $body
            }

            fn is_untyped(&self) -> bool {
                true
            }
        }
        impl $crate::mm::frame::untyped::AnyUFrameMeta for $t {}
    };
}*/

// A special case of untyped metadata is the unit type.
//impl_untyped_frame_meta_for!(());

/*macro_rules! impl_untyped_for {
    ($t:ident) => {
        impl<UM: AnyUFrameMeta + ?Sized> UntypedMem for $t<UM> {
            fn reader(&self) -> VmReader<'_, Infallible> {
                let ptr = paddr_to_vaddr(self.start_paddr()) as *const u8;
                // SAFETY: Only untyped frames are allowed to be read.
                unsafe { VmReader::from_kernel_space(ptr, self.size()) }
            }

            fn writer(&self) -> VmWriter<'_, Infallible> {
                let ptr = paddr_to_vaddr(self.start_paddr()) as *mut u8;
                // SAFETY: Only untyped frames are allowed to be written.
                unsafe { VmWriter::from_kernel_space(ptr, self.size()) }
            }
        }

        impl<UM: AnyUFrameMeta + ?Sized> VmIo for $t<UM> {
            fn read(&self, offset: usize, writer: &mut VmWriter) -> Result<()> {
                let read_len = writer.avail().min(self.size().saturating_sub(offset));
                // Do bound check with potential integer overflow in mind
                let max_offset = offset.checked_add(read_len).ok_or(Error::Overflow)?;
                if max_offset > self.size() {
                    return Err(Error::InvalidArgs);
                }
                let len = self
                    .reader()
                    .skip(offset)
                    .read_fallible(writer)
                    .map_err(|(e, _)| e)?;
                debug_assert!(len == read_len);
                Ok(())
            }

            fn write(&self, offset: usize, reader: &mut VmReader) -> Result<()> {
                let write_len = reader.remain().min(self.size().saturating_sub(offset));
                // Do bound check with potential integer overflow in mind
                let max_offset = offset.checked_add(write_len).ok_or(Error::Overflow)?;
                if max_offset > self.size() {
                    return Err(Error::InvalidArgs);
                }
                let len = self
                    .writer()
                    .skip(offset)
                    .write_fallible(reader)
                    .map_err(|(e, _)| e)?;
                debug_assert!(len == write_len);
                Ok(())
            }
        }
    };
}

impl_untyped_for!(Frame);
impl_untyped_for!(Segment);
*/
