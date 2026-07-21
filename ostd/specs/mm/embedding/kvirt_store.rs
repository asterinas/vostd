//! Kernel-side one-step-soundness store for the kernel virtual area API
//! ([`crate::mm::kspace::kvirt_area::KVirtArea`]) — the *kernel* analog of
//! [`super::VmStore`].
//!
//! # Why a separate, kernel store
//!
//! [`super::VmStore`] models a caller of the **user** `VmSpace` API: it
//! holds a `Map<VmSpaceId, VmSpaceOwner>`, each wrapping an
//! `OwnerSubtree<UserPtConfig>`, plus user-space cursors
//! (`CursorOwner<'rcu, UserPtConfig>`). `KVirtArea` instead maps frames
//! into the single, global **kernel** page table
//! ([`crate::mm::kspace::KERNEL_PAGE_TABLE`], a `KernelPtConfig` table),
//! so the kernel store differs in three ways:
//!
//!   - **one** page table, not a map: a single
//!     [`PageTableOwner<KernelPtConfig>`] (`kernel_pt`) rather than
//!     `Map<VmSpaceId, _>`;
//!   - it tracks the allocated **kernel virtual areas**
//!     (`kvirt_areas`) — each `KVirtArea` is just a `Range<Vaddr>`
//!     handle, since its `KVirtAreaOwner` is consumed into the page table
//!     at construction (`map_frames`/`map_untracked_frames` take it by
//!     value);
//!   - cursors and owners are over `KernelPtConfig`, not `UserPtConfig`
//!     (added when the mutating ops land).
//!
//! # Roadmap
//!
//! Landed: the store + invariant. Next: `step_query` (read-only) over
//! `kernel_pt`, then `map_frames` / `map_untracked_frames` (the
//! mapping-creating ops; their exec ensures may need strengthening
//! first). Accounting (the `rc == H + P + cover_count` equation
//! [`super::VmStore`] carries) is deferred — `KVirtArea` is
//! mapping-focused, not reference-count-focused.
use core::ops::Range;

use vstd::prelude::*;
use vstd_extra::prelude::Inv;

use crate::specs::{
    arch::PAGE_SIZE,
    mm::{
        frame::meta_region_owners::MetaRegionOwners,
        page_table::{node::Guards, *},
    },
};

use crate::mm::{
    Vaddr,
    kspace::{
        FRAME_METADATA_BASE_VADDR, KERNEL_BASE_VADDR, KernelPtConfig, MappedItem,
        kvirt_area::{KVirtArea, KVirtAreaOwner},
    },
    page_table::PageTableGuard,
};

verus! {

/// Logical identifier for an allocated [`KVirtArea`] in the store.
pub type KVirtId = int;

/// One-step-soundness store for the kernel virtual area API. Holds the
/// shared `regions`, the single global kernel page table `kernel_pt`,
/// and the set of allocated kernel virtual areas (each a `Range<Vaddr>`
/// handle — see the module docs).
///
/// The kernel analog of [`super::VmStore`]; see the module documentation
/// for how it differs (one global PT vs. a map of user `VmSpace`s).
pub tracked struct KVmStore {
    pub regions: MetaRegionOwners,
    pub kernel_pt: PageTableOwner<KernelPtConfig>,
    pub kvirt_areas: Map<KVirtId, Range<Vaddr>>,
}

impl KVmStore {
    /// The store's top-level invariant.
    ///
    /// Mirrors the page-table-soundness portion of
    /// [`super::VmStore::structural_inv`] (the kernel PT relates to the
    /// region map via [`PageTableOwner::metaregion_sound`]) and adds the
    /// per-area range well-formedness that [`KVirtArea::inv`] enforces at
    /// the handle level (within the kernel VMALLOC bounds, page-aligned,
    /// ordered).
    pub open spec fn inv(self) -> bool {
        &&& self.regions.inv()
        &&& self.kernel_pt.inv()
        // The global kernel page table relates to the shared region map —
        // every present page-table node sits at a sound region slot, just
        // as `VmStore::inv` requires of each cursor's owner.
        &&& self.kernel_pt.metaregion_sound(
            self.regions,
        )
        // Each allocated area is a well-formed kernel virtual range:
        // within `[KERNEL_BASE_VADDR, FRAME_METADATA_BASE_VADDR]` (the
        // VMALLOC region the real allocator draws from), page-aligned,
        // and ordered — exactly the handle-level facts `KVirtArea::inv`
        // guarantees at construction and every op preserves.
        &&& forall|id: KVirtId| #[trigger]
            self.kvirt_areas.dom().contains(id) ==> {
                let r = self.kvirt_areas[id];
                &&& KERNEL_BASE_VADDR <= r.start
                &&& r.end <= FRAME_METADATA_BASE_VADDR
                &&& r.start % PAGE_SIZE == 0
                &&& r.end % PAGE_SIZE == 0
                &&& r.start <= r.end
            }
    }
}

} // verus!
