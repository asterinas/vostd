use vstd::prelude::*;

use crate::mm::page_table::*;
use crate::mm::{PagingConstsTrait, Vaddr};
use crate::specs::arch::{NR_LEVELS, PAGE_SIZE};
use crate::specs::mm::frame::mapping::frame_to_index;
use crate::specs::mm::frame::meta_owners::{REF_COUNT_MAX, REF_COUNT_UNUSED, is_mmio_paddr};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::*;
use crate::specs::task::InAtomicMode;

use core::ops::Range;

verus! {

// ─── Cursor specs ─────────────────────────────────────────────────────────────
impl<'rcu, C: PageTableConfig, A: InAtomicMode> Cursor<'rcu, C, A> {
    pub open spec fn cursor_new_success_conditions(va: &Range<Vaddr>) -> bool {
        &&& va.start < va.end
        &&& va.start % C::BASE_PAGE_SIZE() == 0
        &&& va.end % C::BASE_PAGE_SIZE() == 0
        &&& crate::mm::page_table::is_valid_range_spec::<C>(va)
    }

    pub open spec fn invariants(
        self,
        owner: CursorOwner<'rcu, C>,
        regions: MetaRegionOwners,
        guards: Guards<'rcu>,
    ) -> bool {
        &&& owner.inv()
        &&& self.inv()
        &&& self.wf(owner)
        &&& regions.inv()
        &&& owner.children_not_locked(guards)
        &&& owner.nodes_locked(guards)
        &&& owner.metaregion_sound(regions)
        &&& !owner.popped_too_high
    }

    pub open spec fn query_some_condition(self, owner: CursorOwner<'rcu, C>) -> bool {
        self.model(owner).present()
    }

    /// Panic condition for [`Self::query`]. `query` diverges *only* via the
    /// Arc-style refcount-saturation abort when it clones the **specific**
    /// frame the cursor resolves to. That happens iff:
    ///  - the cursor is in range (out-of-range returns `Err` *before* any
    ///    clone — the early `self.va >= barrier_va.end` exit), and
    ///  - a mapping is present at the cursor (`owner@.present()`), and
    ///  - the resolved leaf frame is tracked (non-MMIO, so cloning it bumps
    ///    its slot's refcount — MMIO/untracked leaves never bump), and
    ///  - that slot's refcount is already at `REF_COUNT_MAX`, so the
    ///    `inc_ref_count` in `clone_item` would overflow and abort.
    /// `owner@.query_mapping().pa_range.start` is exactly the paddr the
    /// descent lands on (bridged by [`CursorOwner::cur_entry_frame_present`]).
    pub open spec fn query_panic_condition(
        self,
        owner: CursorOwner<'rcu, C>,
        regions: MetaRegionOwners,
    ) -> bool {
        let pa = owner@.query_mapping().pa_range.start;
        let idx = frame_to_index(pa);
        &&& self.barrier_va.start <= self.va < self.barrier_va.end
        &&& owner@.present()
        &&& !is_mmio_paddr(pa)
        &&& regions.slot_owners[idx].inner_perms.ref_count.value() >= REF_COUNT_MAX
    }

    pub open spec fn query_some_ensures(
        self,
        owner: CursorOwner<'rcu, C>,
        res: PagesState<C>,
    ) -> bool {
        &&& owner.cur_va_range().start.reflect(res.0.start)
        &&& owner.cur_va_range().end.reflect(res.0.end)
        &&& res.1 is Some
        &&& {
            let qr = owner@.query_range();
            owner@.query_item_spec(res.1->0) == Some(qr.start as Vaddr..qr.end as Vaddr)
        }
    }

    pub open spec fn query_none_ensures(
        self,
        owner: CursorOwner<'rcu, C>,
        res: PagesState<C>,
    ) -> bool {
        &&& res.1 is None
    }

    /// Whether the level-`lv` node around the cursor's own VA contains `va`
    /// — exactly the per-iteration test in `jump`'s loop
    /// (`node_start <= va && va - node_start < node_size`, with
    /// `node_start == nat_align_down(self.va, page_size(lv + 1))` and
    /// `node_size == page_size(lv + 1)`).
    pub open spec fn jump_node_holds(self, lv: PagingLevel, va: Vaddr) -> bool {
        let nstart = nat_align_down(self.va as nat, page_size((lv + 1) as PagingLevel) as nat);
        &&& nstart <= va as nat
        &&& (va as nat) - nstart < page_size((lv + 1) as PagingLevel) as nat
    }

    /// Structural (reachability) panic condition for `jump`: it diverges on a
    /// misaligned `va` (the `assert_eq!`), or when `va` is in the barrier
    /// range but **no** node on the ascending path within the guard levels
    /// `[level, guard_level]` contains it — exactly the case where the loop
    /// never finds `va`, pops above the guard, and hits `pop_level`'s
    /// `None`-slot unwrap. (An out-of-range `va` returns `Err`, no panic.)
    /// This mirrors the loop's own search, so it neither over- nor
    /// under-approximates: an out-of-locked-range cursor that *can* still
    /// reach `va` via a shared ancestor node does **not** satisfy it.
    pub open spec fn jump_panic_condition(self, va: Vaddr) -> bool {
        ||| va % PAGE_SIZE != 0
        ||| (self.barrier_va.start <= va < self.barrier_va.end && forall|lv: PagingLevel|
            #![trigger self.jump_node_holds(lv, va)]
            self.level <= lv <= self.guard_level ==> !self.jump_node_holds(lv, va))
    }

    pub open spec fn find_next_panic_condition(self, len: usize) -> bool {
        ||| len % PAGE_SIZE != 0
        ||| self.va + len > self.barrier_va.end
    }
}

// ─── CursorMut specs ──────────────────────────────────────────────────────────
impl<'rcu, C: PageTableConfig, A: InAtomicMode> CursorMut<'rcu, C, A> {
    // TODO: trace the `level >= guard_level` panic to its actual location in `pop_level`
    // (unwrap of None path entry). The lock treatment of the invariant has now been
    // fixed (`Cursor::wf` and `CursorOwner::nodes_locked` are gated on `guard_level`
    // rather than hardcoding `NR_LEVELS`, so `path[i]`/continuations above
    // `guard_level` are unlocked/`None`), which is the prerequisite for expressing
    // the `level >= guard_level` pop as a precondition violation. What remains is
    // routing that `path[level-1] is None` fact into `pop_level`'s panic precondition.
    pub open spec fn map_panic_conditions(self, item: C::Item) -> bool {
        ||| self.0.va >= self.0.barrier_va.end
        ||| C::item_into_raw(item).1 > C::HIGHEST_TRANSLATION_LEVEL()
        ||| C::item_into_raw(item).1 >= self.0.guard_level
        ||| (!C::TOP_LEVEL_CAN_UNMAP_spec() && C::item_into_raw(item).1 >= NR_LEVELS)
        ||| self.0.va % page_size(C::item_into_raw(item).1) != 0
        ||| self.0.va + page_size(C::item_into_raw(item).1) > self.0.barrier_va.end
    }

    // TODO: ideally this should be an `OwnerOf` impl for `C::Item`
    pub open spec fn item_wf(self, item: C::Item, entry_owner: EntryOwner<C>) -> bool {
        let (paddr, level, prop) = C::item_into_raw(item);
        &&& entry_owner.inv()
        &&& (entry_owner.is_absent() || Child::Frame(paddr, level, prop).wf(entry_owner))
    }

    pub open spec fn item_not_mapped(item: C::Item, regions: MetaRegionOwners) -> bool {
        let (pa, level, prop) = C::item_into_raw(item);
        let size = page_size(level);
        let range = pa..(pa + size) as usize;
        regions.paddr_range_not_mapped(range)
    }

    pub open spec fn item_slot_in_regions(item: C::Item, regions: MetaRegionOwners) -> bool {
        let (pa, level, prop) = C::item_into_raw(item);
        let idx = frame_to_index(pa);
        &&& regions.slots.contains_key(idx)
        &&& regions.slot_owners[idx].inner_perms.ref_count.value()
            != REF_COUNT_UNUSED
        // Tracked items hold a refcount; untracked (MMIO) don't.
        &&& C::tracked(item) ==> regions.slot_owners[idx].inner_perms.ref_count.value()
            > 0
        // A tracked (mapped) item is a SHARED frame, never the UNIQUE sentinel:
        // `rc <= MAX < REF_COUNT_UNIQUE`. Carries the bound into the mapped
        // slot's `metaregion_sound`, keeping the UNIQUE-branch `paths_in_pt`
        // inv clause vacuous.
        &&& C::tracked(item) ==> regions.slot_owners[idx].inner_perms.ref_count.value()
            <= REF_COUNT_MAX
        // Sub-page slot existence for huge frames (unconditional). Rc parts gated on tracked.
        &&& level > 1 ==> {
            forall|j: usize|
                #![trigger frame_to_index((pa + j * PAGE_SIZE) as usize)]
                0 < j < page_size(level) / PAGE_SIZE ==> {
                    let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                    &&& regions.slots.contains_key(sub_idx)
                    &&& C::tracked(item)
                        ==> regions.slot_owners[sub_idx].inner_perms.ref_count.value()
                        != REF_COUNT_UNUSED
                    &&& C::tracked(item)
                        ==> regions.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                    // SHARED upper bound for tracked sub-pages — carries `rc <= MAX`
                    // into the mapped huge frame's `frame_sub_pages_valid`.
                    &&& C::tracked(item)
                        ==> regions.slot_owners[sub_idx].inner_perms.ref_count.value()
                        <= REF_COUNT_MAX
                }
        }
    }

    pub open spec fn map_item_ensures(
        self,
        item: C::Item,
        old_view: CursorView<C>,
        new_view: CursorView<C>,
    ) -> bool {
        let (pa, level, prop) = C::item_into_raw(item);
        new_view == old_view.map_spec(pa, page_size(level), prop)
    }
}

} // verus!
