// SPDX-License-Identifier: MPL-2.0
//! Untyped physical memory management.
//!
//! As detailed in [`crate::mm::frame`], untyped memory can be accessed with
//! relaxed rules but we cannot create references to them. This module provides
//! the declaration of untyped frames and segments, and the implementation of
//! extra functionalities (such as [`VmIo`]) for them.
use vstd::prelude::*;

use super::*;
use crate::mm::{
    io::{VmIoOwner, VmReader, VmWriter},
    kspace::{
        paddr_to_vaddr_spec, KERNEL_BASE_VADDR, KERNEL_END_VADDR, LINEAR_MAPPING_BASE_VADDR,
        VMALLOC_BASE_VADDR,
    },
    paddr_to_vaddr,
};
use crate::specs::arch::kspace::{lemma_max_paddr_range, lemma_paddr_to_vaddr_properties};
use crate::specs::mm::frame::meta_owners::MetaSlotStorage;
use crate::specs::mm::virt_mem_newer::VirtPtr;
use vstd_extra::ownership::OwnerOf;

verus! {

/// The metadata of untyped frame.
///
/// If a structure `M` implements [`AnyUFrameMeta`], it can be used as the
/// metadata of a type of untyped frames [`Frame<M>`]. All frames of such type
/// will be accessible as untyped memory.
pub trait AnyUFrameMeta: AnyFrameMeta {

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

/// A physical memory range that is untyped.
///
/// Untyped frames or segments can be safely read and written by the kernel or
/// the user.
///
/// TODO: Perhaps we also need to define this?
pub trait UntypedMem {
    /// Borrows a reader that can read the untyped memory.
    fn reader(&self) -> VmReader<'_>;

    /// Borrows a writer that can write the untyped memory.
    fn writer(&self) -> VmWriter<'_>;
}

#[verus_verify]
impl<M: AnyUFrameMeta + OwnerOf> Segment<M> {
    #[inline(always)]
    #[verus_spec(r =>
        with
            -> owner: Tracked<VmIoOwner<'_>>,
        requires
            self.inv(),
        ensures
            r.inv(),
            owner@.inv(),
            r.wf(owner@),
            r.cursor.vaddr == paddr_to_vaddr_spec(self.start_paddr_spec()),
            r.remain_spec() == self.size_spec(),
            owner@.is_kernel,
    )]
    pub fn reader(&self) -> VmReader<'_> {
        proof_decl! {
            let ghost id: nat;
            let tracked owner: VmIoOwner<'_>;
        }
        proof {
            lemma_max_paddr_range();
        }

        let vaddr = paddr_to_vaddr(self.start_paddr());
        let len = self.size();
        let ghost range = vaddr..(vaddr + len) as usize;
        let ptr = VirtPtr { vaddr, range: Ghost(range) };
        proof {
            lemma_paddr_to_vaddr_properties(self.start_paddr_spec());
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
            -> owner: Tracked<VmIoOwner<'_>>,
        requires
            self.inv(),
        ensures
            r.inv(),
            owner@.inv(),
            r.wf(owner@),
            r.cursor.vaddr == paddr_to_vaddr_spec(self.start_paddr_spec()),
            r.avail_spec() == self.size_spec(),
            owner@.is_kernel,
            !owner@.is_fallible,
    )]
    pub fn writer(&self) -> VmWriter<'_> {
        proof_decl! {
            let ghost id: nat;
            let tracked owner: VmIoOwner<'_>;
        }
        proof {
            lemma_max_paddr_range();
        }

        let vaddr = paddr_to_vaddr(self.start_paddr());
        let len = self.size();
        let ghost range = vaddr..(vaddr + len) as usize;
        let ptr = VirtPtr { vaddr, range: Ghost(range) };
        proof {
            lemma_paddr_to_vaddr_properties(self.start_paddr_spec());
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

} // verus!
