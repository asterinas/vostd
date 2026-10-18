use vstd::prelude::*;

use crate::specs::{
    arch::PAGE_SIZE,
    mm::{
        frame::{mapping::frame_to_index, meta_region_owners::MetaRegionOwners},
        page_table::{cursor::owners::*, is_valid_range_spec, *},
    },
    task::InAtomicMode,
};

use crate::arch::mm::PagingConsts;
use crate::mm::{
    PagingConstsTrait, Vaddr,
    frame::meta::{REF_COUNT_MAX, REF_COUNT_UNUSED},
    page_table::*,
};
use core::ops::Range;

verus! {

// ─── Cursor specs ─────────────────────────────────────────────────────────────
impl<'rcu, C: PageTableConfig, A: InAtomicMode> Cursor<'rcu, C, A> {
    pub open spec fn cursor_new_success_conditions(va: Range<Vaddr>) -> bool {
        &&& va.start < va.end
        &&& va.start % C::BASE_PAGE_SIZE() == 0
        &&& va.end % C::BASE_PAGE_SIZE() == 0
        &&& is_valid_range_spec::<C>(va)
    }

    pub open spec fn invariants(
        self,
        owner: CursorOwner<'rcu, C>,
        regions: MetaRegionOwners,
        guards: Guards,
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
        owner@.present()
    }

    /// Panic condition for [`Self::query`]. `query` diverges *only* via the
    /// Arc-style refcount-saturation abort when it clones the **specific**
    /// frame the cursor resolves to. That happens iff:
    ///  - the cursor is in range,
    ///  - the resolved leaf owner carries a permission, so cloning
    ///    it bumps its slot's refcount (raw RAM/MMIO mappings never bump),
    ///  - that slot's refcount is already at `REF_COUNT_MAX`, so the
    ///    `inc_ref_count` in `clone_item` would overflow and abort.
    pub open spec fn query_panic_condition(
        self,
        owner: CursorOwner<'rcu, C>,
        regions: MetaRegionOwners,
    ) -> bool {
        &&& self.barrier_va.start <= self.va < self.barrier_va.end
        &&& PageTableOwner(owner.cur_subtree()).query_leaf(self.va) matches Some(entry) && {
            &&& entry.is_frame()
            &&& entry.frame_is_tracked()
            &&& regions.ref_count(frame_to_index(entry.frame().mapped_pa)) >= REF_COUNT_MAX
        }
    }

    pub open spec fn query_some_ensures(
        self,
        owner: CursorOwner<'rcu, C>,
        res: PagesState<C>,
    ) -> bool {
        &&& owner.cur_va_range() == res.0
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
        let nstart = nat_align_down(
            self.va as nat,
            page_size::<PagingConsts>((lv + 1) as PagingLevel) as nat,
        );
        &&& nstart <= va as nat
        &&& (va as nat) - nstart < page_size::<PagingConsts>((lv + 1) as PagingLevel) as nat
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
    /// Runtime checks for mapping an item, matching the source's range and alignment checks.
    pub open spec fn map_panic_conditions(self, item: C::Item) -> bool {
        ||| self.0.va >= self.0.barrier_va.end
        ||| C::item_into_raw(item).1 > C::HIGHEST_TRANSLATION_LEVEL()
        ||| self.0.va % page_size::<PagingConsts>(C::item_into_raw(item).1) != 0
        ||| self.0.va + page_size::<PagingConsts>(C::item_into_raw(item).1) > self.0.barrier_va.end
    }

    // TODO: ideally this should be an `OwnerOf` impl for `C::Item`
    pub open spec fn item_wf(self, item: C::Item, entry_owner: EntryOwner<C>) -> bool {
        let (paddr, level, prop, _perm) = C::item_into_raw(item);
        &&& C::item_well_formed(item)
        &&& entry_owner.inv()
        &&& (entry_owner.is_absent() || Child::Frame(paddr, level, prop).wf(entry_owner))
    }

    pub open spec fn item_not_mapped(item: C::Item, regions: MetaRegionOwners) -> bool {
        let (pa, level, prop, perm) = C::item_into_raw(item);
        let size = page_size::<PagingConsts>(level);
        let range = pa..(pa + size) as usize;
        perm@ is Some ==> regions.paddr_range_not_mapped(range)
    }

    pub open spec fn item_slot_in_regions_except_perm(
        item: C::Item,
        regions: MetaRegionOwners,
    ) -> bool {
        let (pa, _level, _prop, perm) = C::item_into_raw(item);
        let idx = frame_to_index(pa);
        &&& regions.contains(idx)
        &&& perm@ is Some ==> {
            &&& regions.slot_owners[idx].usage !is PageTable
            &&& 0 < regions.ref_count(idx) <= REF_COUNT_MAX
        }
    }

    pub closed spec fn item_slot_in_regions(item: C::Item, regions: MetaRegionOwners) -> bool {
        let (pa, _level, _prop, perm) = C::item_into_raw(item);
        &&& Self::item_slot_in_regions_except_perm(item, regions)
        &&& C::perm_well_formed_with_region(pa, perm, regions)
    }

    pub proof fn lemma_item_slot_in_regions_facts(item: C::Item, regions: MetaRegionOwners)
        ensures
            Self::item_slot_in_regions(item, regions) <==> {
                &&& Self::item_slot_in_regions_except_perm(item, regions)
                &&& C::perm_well_formed_with_region(
                    C::item_into_raw(item).0,
                    C::item_into_raw(item).3,
                    regions,
                )
            },
    {
    }

    pub proof fn lemma_item_slot_in_regions_preserved(
        item: C::Item,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    )
        requires
            Self::item_slot_in_regions(item, regions0),
            Self::item_slot_in_regions_except_perm(item, regions1),
            C::item_into_raw(item).3@ is Some ==> {
                let idx = frame_to_index(C::item_into_raw(item).0);
                &&& regions0.slots[idx] == regions1.slots[idx]
                &&& regions0.slot_owners[idx].metadata_perm.id()
                    == regions1.slot_owners[idx].metadata_perm.id()
            },
        ensures
            Self::item_slot_in_regions(item, regions1),
    {
        if C::item_into_raw(item).3@ is Some {
            C::lemma_perm_well_formed_with_region_preserved(
                C::item_into_raw(item).0,
                C::item_into_raw(item).3,
                regions0,
                regions1,
            );
        } else {
            C::lemma_none_perm_well_formed(C::item_into_raw(item).0, regions1);
        }
    }

    pub proof fn lemma_all_item_slots_preserved(
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    )
        requires
            forall|idx: int| regions0.contains(idx) ==> #[trigger] regions1.contains(idx),
            forall|idx: int|
                regions0.contains(idx) && regions0.ref_count(idx) != REF_COUNT_UNUSED ==> {
                    &&& (#[trigger] regions1.slot_owners[idx]).same_permissions(
                        regions0.slot_owners[idx],
                    )
                    &&& regions1.slot_owners[idx].usage == regions0.slot_owners[idx].usage
                    &&& regions1.slot_owners[idx].slot_vaddr == regions0.slot_owners[idx].slot_vaddr
                    &&& regions1.slots[idx] == regions0.slots[idx]
                },
        ensures
            forall|item: C::Item|
                #![trigger Self::item_slot_in_regions(item, regions0)]
                Self::item_slot_in_regions(item, regions0) ==> Self::item_slot_in_regions(
                    item,
                    regions1,
                ),
    {
        assert forall|item: C::Item|
            Self::item_slot_in_regions(
                item,
                regions0,
            ) implies #[trigger] Self::item_slot_in_regions(item, regions1) by {
            let (pa, _level, _prop, _perm) = C::item_into_raw(item);
            if C::item_into_raw(item).3@ is Some {
                Self::lemma_item_slot_in_regions_preserved(item, regions0, regions1);
            } else {
                C::lemma_none_perm_well_formed(pa, regions1);
            }
        };
    }

    pub open spec fn map_item_ensures(
        self,
        item: C::Item,
        old_view: CursorView<C>,
        new_view: CursorView<C>,
    ) -> bool {
        let (pa, level, prop, _perm) = C::item_into_raw(item);
        new_view == old_view.map_spec(pa, page_size::<PagingConsts>(level), prop)
    }
}

} // verus!
