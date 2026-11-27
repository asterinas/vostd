// SPDX-License-Identifier: MPL-2.0
//! Spec/proof companion for [`crate::mm::frame::segment`].
use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::specs::{
    arch::PAGE_SIZE,
    mm::{
        frame::{
            mapping::{frame_to_index, index_to_meta},
            meta_region_owners::MetaRegionOwners,
        },
        virt_mem::MemView,
    },
};

use crate::mm::{
    Paddr, Vaddr,
    frame::{
        Segment,
        meta::{AnyFrameMeta, MetaSlot},
    },
    paddr_to_vaddr,
};
use core::ops::Range;

verus! {

impl<M: AnyFrameMeta + ?Sized> Segment<M> {
    /// The cross-object relation between a [`Segment`] and the global
    /// [`MetaRegionOwners`].
    pub open spec fn relate_regions(&self, regions: MetaRegionOwners) -> bool {
        &&& forall|i: int|
            #![trigger frame_to_index((self.range().start + i * PAGE_SIZE) as usize)]
            0 <= i < self.len() ==> {
                let idx = frame_to_index((self.range().start + i * PAGE_SIZE) as usize);
                &&& self.raw_perms()[i].slot_perm == regions.slots[idx]
                &&& self.raw_perms()[i].inv()
                &&& self.raw_perms()[i].metadata_perm.id()
                    == regions.slot_owners[idx].metadata_perm.id()
                &&& regions.contains(idx)
                &&& regions.slot_owners[idx].slot_vaddr == index_to_meta(idx)
                &&& 0 < regions.slot_owners[idx].ref_count()
                    <= crate::mm::frame::meta::REF_COUNT_MAX
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                &&& regions.slot_owners[idx].usage
                    == self.raw_perms()[i].metadata_perm.resource().usage()
            }
        &&& forall|i: int, j: int|
            #![trigger frame_to_index((self.range().start + i * PAGE_SIZE) as usize),
                frame_to_index((self.range().start + j * PAGE_SIZE) as usize)]
            0 <= i < j < self.len() ==> frame_to_index(
                (self.range().start + i * PAGE_SIZE) as usize,
            ) != frame_to_index((self.range().start + j * PAGE_SIZE) as usize)
    }
}

} // verus!
