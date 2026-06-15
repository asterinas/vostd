// SPDX-License-Identifier: MPL-2.0
//! Untyped physical memory management.
//!
//! As detailed in [`crate::mm::frame`], untyped memory can be accessed with
//! relaxed rules but we cannot create references to them. This module provides
//! the declaration of untyped frames and segments, and the implementation of
//! extra functionalities (such as [`VmIo`]) for them.
use vstd::prelude::*;
use vstd_extra::ownership::OwnerOf;

use super::*;
use crate::mm::{
    io::{Infallible, VmReader, VmWriter},
    kspace::{
        KERNEL_BASE_VADDR, KERNEL_END_VADDR, LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR,
        paddr_to_vaddr_spec,
    },
    paddr_to_vaddr,
};
use crate::specs::arch::{lemma_max_paddr_range, lemma_paddr_to_vaddr_properties};
use crate::specs::mm::frame::meta_owners::MetaSlotStorage;
use crate::specs::mm::io::VmIoOwner;
use crate::specs::mm::virt_mem::VirtPtr;

verus! {

/// The metadata of untyped frame.
///
/// If a structure `M` implements [`AnyUFrameMeta`], it can be used as the
/// metadata of a type of untyped frames [`Frame<M>`]. All frames of such type
/// will be accessible as untyped memory.
///
/// `Repr<MetaSlotStorage>` is required so that `Frame<M>` is well-formed (it
/// is no longer an `AnyFrameMeta` supertrait). This makes `AnyUFrameMeta`
/// itself dyn-incompatible — `Segment<dyn AnyUFrameMeta>` (the `USegment`
/// alias below) was already in an unsatisfiable state under the old
/// supertrait chain, so this doesn't lose anything in practice.
pub trait AnyUFrameMeta: AnyFrameMeta + vstd_extra::cast_ptr::Repr<MetaSlotStorage> {

}

/// A smart pointer to an untyped frame with any metadata.
///
/// The metadata of the frame is not known at compile time but the frame must
/// be an untyped one. An [`UFrame`] as a parameter accepts any type of
/// untyped frame metadata.
///
/// The usage of this frame will not be changed while this object is alive.
/// Verus doesn't let us do very much with `dyn` traits, so instead of a `dyn AnyFrameMeta`
/// we use `MetaSlotStorage`, a type that is a tagged union of the metadata types we've worked with so far.
pub type UFrame = Frame<MetaSlotStorage>;

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
}

// A special case of untyped metadata is the unit type.
impl_untyped_frame_meta_for!(()); */

/// A physical memory range that is untyped.
///
/// Untyped frames or segments can be safely read and written by the kernel or
/// the user.
///
/// TODO: Perhaps we also need to define this?
pub trait UntypedMem {
    /// Borrows a reader that can read the untyped memory.
    fn reader(&self) -> VmReader<'_, Infallible>;

    /// Borrows a writer that can write the untyped memory.
    fn writer(&self) -> VmWriter<'_, Infallible>;
}

#[verus_verify]
impl<M: AnyUFrameMeta + OwnerOf> Segment<M> {
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> owner: Tracked<VmIoOwner>,
        requires
            self.inv(),
        ensures
            r.inv(),
            owner@.inv(),
            r.wf(owner@),
            r.cursor.vaddr == paddr_to_vaddr_spec(self.start_paddr()),
            r.remain_spec() == self.size(),
            owner@.is_kernel,
    )]
    pub fn reader(&self) -> VmReader<'_, Infallible> {
        proof_decl! {
            let ghost id: nat;
            let tracked owner: VmIoOwner;
        }
        proof {
            lemma_max_paddr_range();
        }

        let vaddr = paddr_to_vaddr(self.start_paddr());
        let len = self.size();
        let ghost range = vaddr..(vaddr + len) as usize;
        let ptr = VirtPtr { vaddr, range: Ghost(range) };
        proof {
            lemma_paddr_to_vaddr_properties(self.start_paddr());
            assert(KERNEL_BASE_VADDR > 0) by (compute_only);
            assert(vaddr > 0);
            assert(VMALLOC_BASE_VADDR <= KERNEL_END_VADDR) by (compute_only);
            assert(ptr.inv());
        }

        let reader = unsafe {
            #[verus_spec(with Ghost(id) => Tracked(owner))]
            VmReader::from_kernel_space(ptr, len)
        };

        proof_with!(|= Tracked(owner));
        reader
    }

    #[inline(always)]
    #[verus_spec(r =>
        with
            -> owner: Tracked<VmIoOwner>,
        requires
            self.inv(),
        ensures
            r.inv(),
            owner@.inv(),
            r.wf(owner@),
            r.cursor.vaddr == paddr_to_vaddr_spec(self.start_paddr()),
            r.avail_spec() == self.size(),
            owner@.is_kernel,
            !owner@.is_fallible,
    )]
    pub fn writer(&self) -> VmWriter<'_, Infallible> {
        proof_decl! {
            let ghost id: nat;
            let tracked owner: VmIoOwner;
        }
        proof {
            lemma_max_paddr_range();
        }

        let vaddr = paddr_to_vaddr(self.start_paddr());
        let len = self.size();
        let ghost range = vaddr..(vaddr + len) as usize;
        let ptr = VirtPtr { vaddr, range: Ghost(range) };
        proof {
            lemma_paddr_to_vaddr_properties(self.start_paddr());
            assert(KERNEL_BASE_VADDR > 0) by (compute_only);
            assert(vaddr > 0);
            assert(VMALLOC_BASE_VADDR <= KERNEL_END_VADDR) by (compute_only);
            assert(ptr.inv());
        }

        let writer = unsafe {
            #[verus_spec(with Ghost(id), Tracked(false) => Tracked(owner))]
            VmWriter::from_kernel_space(ptr, len)
        };

        proof_with!(|= Tracked(owner));
        writer
    }
}

/*
// Original impl_untyped_for! macro and its invocations (removed during Verus migration):
// This macro provided UntypedMem + VmIo implementations for both Frame<UM> and Segment<UM>.

macro_rules! impl_untyped_for {
    ($t:ident) => {
        impl<UM: AnyUFrameMeta + ?Sized> UntypedMem for $t<UM> {
            fn reader(&self) -> VmReader<'_, Infallible> {
                let ptr = paddr_to_vaddr(self.start_paddr()) as *const u8;
                unsafe { VmReader::from_kernel_space(ptr, self.size()) }
            }

            fn writer(&self) -> VmWriter<'_, Infallible> {
                let ptr = paddr_to_vaddr(self.start_paddr()) as *mut u8;
                unsafe { VmWriter::from_kernel_space(ptr, self.size()) }
            }
        }

        impl<UM: AnyUFrameMeta + ?Sized> VmIo for $t<UM> {
            fn read(&self, offset: usize, writer: &mut VmWriter) -> Result<()> {
                let read_len = writer.avail().min(self.size().saturating_sub(offset));
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
} // verus!
