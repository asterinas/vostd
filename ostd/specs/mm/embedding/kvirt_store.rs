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
use vstd::prelude::*;
use vstd_extra::prelude::Inv;

use core::ops::Range;

use crate::mm::Vaddr;
use crate::mm::kspace::kvirt_area::{KVirtArea, KVirtAreaOwner};
use crate::mm::kspace::{FRAME_METADATA_BASE_VADDR, KERNEL_BASE_VADDR, KernelPtConfig, MappedItem};
use crate::mm::page_table::PageTableGuard;
use crate::specs::arch::PAGE_SIZE;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::node::Guards;
use crate::specs::mm::page_table::*;

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

/// Trusted reflection of the (checkout/checkin-rewired, verified)
/// [`KVirtArea::query`]. Mirrors its `ensures` verbatim, but threads the
/// kernel page-table ownership by `&mut` (`kernel_pt`) instead of
/// consuming a `KVirtAreaOwner` and returning it — so a [`KVmStore`] can
/// keep `kernel_pt` across the call. The query clones the resolved leaf
/// (bumping its slot's refcount), then `unlock_range` hands the ownership
/// back sound (`inv()` + `metaregion_sound` over the bumped region map).
/// The `query_panic_condition` precondition is required *false* here: the
/// embedding models only the non-panicking query.
pub axiom fn query_embedded<'rcu>(
    range: Range<Vaddr>,
    addr: Vaddr,
    tracked regions: &mut MetaRegionOwners,
    tracked kernel_pt: &mut PageTableOwner<KernelPtConfig>,
    tracked guards: &mut Guards<'rcu>,
    root_guard: PageTableGuard<'rcu, KernelPtConfig>,
) -> (res: Option<MappedItem>)
    requires
        KERNEL_BASE_VADDR <= range.start,
        range.end <= FRAME_METADATA_BASE_VADDR,
        range.start % PAGE_SIZE == 0,
        range.end % PAGE_SIZE == 0,
        range.start <= range.end,
        range.start <= addr < range.end,
        old(regions).inv(),
        old(kernel_pt).inv(),
        old(kernel_pt).metaregion_sound(*old(regions)),
        !(KVirtArea { range }).query_panic_condition(
            KVirtAreaOwner { pt_owner: *old(kernel_pt) },
            addr,
            *old(regions),
        ),
    ensures
        final(regions).inv(),
        final(kernel_pt).inv(),
        final(kernel_pt).metaregion_sound(*final(regions)),
        ({
            let area = KVirtArea { range };
            let owner = KVirtAreaOwner { pt_owner: *old(kernel_pt) };
            &&& area.query_some_condition(owner, addr) ==> area.query_some_ensures(owner, addr, res)
            &&& !area.query_some_condition(owner, addr) ==> KVirtArea::query_none_ensures(res)
        }),
;

impl KVmStore {
    /// `KVirtArea::query`: read the mapped item at the page containing
    /// `addr` in area `id`. Checks the kernel PT out into a cursor,
    /// queries (cloning the resolved leaf — `regions` refcount bump), and
    /// checks it back in, so the store keeps a sound `kernel_pt`. The
    /// caller supplies the ambient lock state (`guards` / `root_guard`),
    /// as the exec does.
    pub proof fn step_query<'rcu>(
        tracked &mut self,
        id: KVirtId,
        addr: Vaddr,
        tracked guards: &mut Guards<'rcu>,
        root_guard: PageTableGuard<'rcu, KernelPtConfig>,
    ) -> (res: Option<MappedItem>)
        requires
            old(self).inv(),
            old(self).kvirt_areas.dom().contains(id),
            old(self).kvirt_areas[id].start <= addr < old(self).kvirt_areas[id].end,
            !(KVirtArea { range: old(self).kvirt_areas[id] }).query_panic_condition(
                KVirtAreaOwner { pt_owner: old(self).kernel_pt },
                addr,
                old(self).regions,
            ),
        ensures
            final(self).inv(),
            final(self).kvirt_areas == old(self).kvirt_areas,
            ({
                let area = KVirtArea { range: old(self).kvirt_areas[id] };
                let owner = KVirtAreaOwner { pt_owner: old(self).kernel_pt };
                &&& area.query_some_condition(owner, addr) ==> area.query_some_ensures(
                    owner,
                    addr,
                    res,
                )
                &&& !area.query_some_condition(owner, addr) ==> KVirtArea::query_none_ensures(res)
            }),
    {
        let ghost old_self = *self;
        let ghost range = self.kvirt_areas[id];
        let res = query_embedded(
            range,
            addr,
            &mut self.regions,
            &mut self.kernel_pt,
            guards,
            root_guard,
        );
        // `kvirt_areas` is untouched; `regions`/`kernel_pt` come back sound
        // (`inv` + `metaregion_sound`) from the axiom — so `inv()` holds.
        assert(self.kvirt_areas =~= old_self.kvirt_areas);
        res
    }
}

} // verus!
