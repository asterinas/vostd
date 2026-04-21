use vstd::prelude::*;

use crate::mm::page_table::*;
use crate::mm::{PagingConstsTrait, Vaddr};
use crate::specs::arch::mm::{NR_LEVELS, PAGE_SIZE};
use crate::specs::mm::frame::mapping::frame_to_index;
use crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED;
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
        guards: Guards<'rcu, C>,
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

    pub open spec fn query_some_ensures(
        self,
        owner: CursorOwner<'rcu, C>,
        res: PagesState<C>,
    ) -> bool {
        &&& owner.cur_va_range().start.reflect(res.0.start)
        &&& owner.cur_va_range().end.reflect(res.0.end)
        &&& res.1 is Some
        &&& owner@.query_item_spec(res.1.unwrap()) == Some(owner@.query_range())
    }

    pub open spec fn query_none_ensures(
        self,
        owner: CursorOwner<'rcu, C>,
        res: PagesState<C>,
    ) -> bool {
        &&& res.1 is None
    }

    pub open spec fn jump_panic_condition(self, va: Vaddr) -> bool {
        va % PAGE_SIZE != 0
    }

    pub open spec fn find_next_panic_condition(self, len: usize) -> bool {
        ||| len % PAGE_SIZE != 0
        ||| self.va + len > self.barrier_va.end
    }
}

// ─── CursorMut specs ──────────────────────────────────────────────────────────

impl<'rcu, C: PageTableConfig, A: InAtomicMode> CursorMut<'rcu, C, A> {
    // TODO: trace the `level >= guard_level` panic to its actual location in `pop_level`
    // (unwrap of None path entry). Doing so requires tweaking the cursor invariant's
    // treatment of locks so that `pop_level` can express the panic as a precondition violation.
    pub open spec fn map_panic_conditions(self, item: C::Item) -> bool {
        ||| self.inner.va >= self.inner.barrier_va.end
        ||| C::item_into_raw(item).1 > C::HIGHEST_TRANSLATION_LEVEL()
        ||| C::item_into_raw(item).1 >= self.inner.guard_level
        ||| (!C::TOP_LEVEL_CAN_UNMAP && C::item_into_raw(item).1 >= NR_LEVELS)
        ||| self.inner.va % page_size(C::item_into_raw(item).1) != 0
        ||| self.inner.va + page_size(C::item_into_raw(item).1) > self.inner.barrier_va.end
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
        &&& regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
        // Allocator invariant for huge frames (level > 1): all 4KB sub-page slots are valid.
        // Established by huge-frame allocator postcondition.
        &&& level > 1 ==> {
            forall |j: usize| #![trigger frame_to_index((pa + j * PAGE_SIZE) as usize)]
                0 < j < page_size(level) / PAGE_SIZE ==> {
                let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                &&& regions.slots.contains_key(sub_idx)
                &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
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
