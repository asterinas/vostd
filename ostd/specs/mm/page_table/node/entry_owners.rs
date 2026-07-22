use core::marker::PhantomData;

use vstd::prelude::*;

use vstd::{modes::tracked_swap, simple_pptr::PointsTo};
use vstd_extra::{ghost_tree::*, ownership::*};

use crate::specs::{
    arch::*,
    mm::{
        frame::{
            mapping::{frame_to_index, index_to_meta},
            meta_owners::PageUsage,
            meta_region_owners::MetaRegionOwners,
        },
        page_table::{node::entry_view::*, *},
    },
};

use crate::arch::mm::PagingConsts;
use crate::mm::{
    Paddr, PagingConstsTrait, PagingLevel, Vaddr,
    frame::meta::{
        MetaSlot, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED, mapping::meta_to_frame,
    },
    page_prop::PageProperty,
    page_table::*,
};

verus! {

/// # Verification Design
/// The proof-side snapshot for a page table leaf: a frame mapped in a node. Asterinas
/// supports huge pages, so it is not necessarily at level 1.
/// - `mapped_pa` is the physical address of the mapped frame.
/// - `prop` is a bitfield tracking the properties of the page ([`PageProperty`])
pub ghost struct FrameEntryState {
    pub mapped_pa: usize,
    pub prop: PageProperty,
}

pub tracked enum EntryOwnerKind<C: PageTableConfig> {
    Node(NodeOwner<C>),
    Frame(ghost FrameEntryState),
    /// Translation-only / borrowed-sub-tree variant.
    ///
    /// Present when the slot's PTE references a sub-tree owned by *another*
    /// page-table configuration (e.g. a user PT's kernel-half slot
    /// pointing at a kernel-owned sub-table). The ghost `Set<Mapping>`
    /// records the mappings reachable through that sub-tree so the
    /// embedding can reason about what the borrowed translation provides
    /// without descending into a sub-tree it does not own. Mutually
    /// exclusive with `node`, `frame`, and `absent` by construction.
    Borrowed(ghost Set<Mapping>),
    Absent,
}

pub tracked struct EntryOwner<C: PageTableConfig> {
    pub kind: EntryOwnerKind<C>,
    pub ghost path: TreePath<NR_ENTRIES>,
    pub ghost parent_level: PagingLevel,
}

impl<C: PageTableConfig> EntryOwner<C> {
    #[verifier::inline]
    pub open spec fn is_node(self) -> bool {
        self.kind is Node
    }

    #[verifier::inline]
    pub open spec fn is_frame(self) -> bool {
        self.kind is Frame
    }

    #[verifier::inline]
    pub open spec fn is_absent(self) -> bool {
        self.kind is Absent
    }

    #[verifier::inline]
    pub open spec fn is_borrowed(self) -> bool {
        self.kind is Borrowed
    }

    pub open spec fn node(self) -> NodeOwner<C> {
        self.kind->Node_0
    }

    pub open spec fn frame(self) -> FrameEntryState {
        self.kind->Frame_0
    }

    pub open spec fn frame_is_tracked(self) -> bool
        recommends
            self.is_frame(),
    {
        C::tracked(
            C::item_from_raw_spec(self.frame().mapped_pa, self.parent_level, self.frame().prop),
        )
    }

    pub open spec fn borrowed(self) -> Set<Mapping> {
        self.kind->Borrowed_0
    }

    pub open spec fn new_absent(path: TreePath<NR_ENTRIES>, parent_level: PagingLevel) -> Self {
        EntryOwner { kind: EntryOwnerKind::Absent, path, parent_level }
    }

    pub open spec fn new_frame(
        paddr: Paddr,
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
        prop: PageProperty,
    ) -> Self {
        EntryOwner {
            kind: EntryOwnerKind::Frame(FrameEntryState { mapped_pa: paddr, prop }),
            path,
            parent_level,
        }
    }

    pub open spec fn new_node(node: NodeOwner<C>, path: TreePath<NR_ENTRIES>) -> Self {
        EntryOwner {
            kind: EntryOwnerKind::Node(node),
            path,
            parent_level: (node.level + 1) as PagingLevel,
        }
    }

    /// Constructor spec for a translation-only / borrowed entry. See
    /// [`EntryOwner`]'s `borrowed` field for semantics.
    pub open spec fn new_borrowed(
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
        mappings: Set<Mapping>,
    ) -> Self {
        EntryOwner { kind: EntryOwnerKind::Borrowed(mappings), path, parent_level }
    }

    pub proof fn tracked_new_borrowed(
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
        mappings: Set<Mapping>,
    ) -> tracked Self
        returns
            Self::new_borrowed(path, parent_level, mappings),
    {
        Self { kind: EntryOwnerKind::Borrowed(mappings), path, parent_level }
    }

    pub proof fn tracked_new_absent(
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
    ) -> tracked Self
        returns
            Self::new_absent(path, parent_level),
    {
        Self { kind: EntryOwnerKind::Absent, path, parent_level }
    }

    pub proof fn tracked_take_node(tracked &mut self) -> (tracked res: NodeOwner<C>)
        requires
            old(self).kind is Node,
        ensures
            res == old(self).node(),
            *final(self) == (EntryOwner { kind: EntryOwnerKind::Absent, ..*old(self) }),
    {
        let tracked mut tmp = EntryOwnerKind::Absent;
        tracked_swap(&mut self.kind, &mut tmp);
        match tmp {
            EntryOwnerKind::Node(node) => node,
            _ => { proof_from_false() },
        }
    }

    pub proof fn tracked_put_node(tracked &mut self, tracked node: NodeOwner<C>)
        ensures
            *final(self) == (EntryOwner { kind: EntryOwnerKind::Node(node), ..*old(self) }),
    {
        self.kind = EntryOwnerKind::Node(node);
    }

    pub proof fn tracked_borrow_node(tracked &self) -> (tracked res: &NodeOwner<C>)
        requires
            self.kind is Node,
        ensures
            *res == self.node(),
    {
        match self.kind {
            EntryOwnerKind::Node(ref node) => node,
            _ => { proof_from_false() },
        }
    }

    pub proof fn tracked_borrow_mut_node(tracked &mut self) -> (tracked res: &mut NodeOwner<C>)
        requires
            old(self).kind is Node,
        ensures
            *res == old(self).node(),
            *final(self) == (EntryOwner { kind: EntryOwnerKind::Node(*final(res)), ..*old(self) }),
    {
        match self.kind {
            EntryOwnerKind::Node(ref mut node) => node,
            _ => { proof_from_false() },
        }
    }

    pub proof fn tracked_set_frame_prop(tracked &mut self, prop: PageProperty)
        requires
            old(self).kind is Frame,
        ensures
            *final(self) == (EntryOwner {
                kind: EntryOwnerKind::Frame(FrameEntryState { prop, ..old(self).frame() }),
                ..*old(self)
            }),
    {
        let ghost old_frame = self.frame();
        self.kind = EntryOwnerKind::Frame(FrameEntryState { prop, ..old_frame });
    }

    pub proof fn tracked_new_frame(
        paddr: Paddr,
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
        prop: PageProperty,
    ) -> tracked Self
        returns
            Self::new_frame(paddr, path, parent_level, prop),
    {
        Self {
            kind: EntryOwnerKind::Frame(FrameEntryState { mapped_pa: paddr, prop }),
            path,
            parent_level,
        }
    }

    /// The frame's `is_tracked` flag is pinned to its paddr's range membership:
    /// tracked frames map regular RAM (non-MMIO paddrs); untracked frames map
    /// MMIO. Combined with `axiom_mmio_usage_iff_mmio_paddr`, this lets proofs
    /// translate between the derived frame trackedness and `usage == MMIO`
    /// on the corresponding meta slot.
    pub broadcast axiom fn axiom_frame_is_tracked_iff_not_mmio(entry: Self)
        requires
            entry.is_frame(),
            entry.inv_base(),
        ensures
            #[trigger] entry.frame_is_tracked()
                != crate::specs::mm::frame::meta_owners::is_mmio_paddr(entry.frame().mapped_pa),
    ;

    pub proof fn tracked_new_node(
        tracked node: NodeOwner<C>,
        path: TreePath<NR_ENTRIES>,
    ) -> tracked Self
        returns
            Self::new_node(node, path),
    {
        Self {
            parent_level: (node.level + 1) as PagingLevel,
            kind: EntryOwnerKind::Node(node),
            path,
        }
    }

    /// Creates a ghost entry owner for mapping an untracked (device memory) frame.
    /// Unlike `new_frame`, this does not consume a slot permission from the meta region,
    /// since device memory PAs are outside the tracked frame allocator.
    /// The actual mapping correctness is guaranteed by the caller's `unsafe` contract.
    ///
    /// The `requires` reflect properties established by `collect_largest_pages` and the page-table
    /// configuration model, allowing this checked constructor to build an invariant-safe,
    /// untracked entry owner.
    pub proof fn tracked_new_untracked_frame(
        paddr: Paddr,
        parent_level: PagingLevel,
        prop: PageProperty,
    ) -> (tracked res: Self)
        requires
            has_safe_slot(paddr),
            1 <= parent_level < NR_LEVELS,
            paddr % page_size(parent_level) == 0,
            paddr + page_size(parent_level) <= MAX_PADDR,
            C::raw_item_well_formed(paddr, parent_level, prop),
            C::E::new_page_req(paddr, parent_level, prop),
            !C::tracked(C::item_from_raw_spec(paddr, parent_level, prop)),
        ensures
            res.is_frame(),
            res.frame().mapped_pa == paddr,
            res.frame().prop == prop,
            !res.frame_is_tracked(),
            res.parent_level == parent_level,
            res.path.inv(),
            res.inv_base(),
            crate::mm::page_table::Child::<C>::Frame(paddr, parent_level, prop).wf(res),
    {
        Self {
            kind: EntryOwnerKind::Frame(FrameEntryState { mapped_pa: paddr, prop }),
            path: TreePath(Seq::empty()),
            parent_level,
        }
    }

    pub open spec fn match_pte(self, pte: C::E, parent_level: PagingLevel) -> bool {
        &&& has_safe_slot(pte.paddr())
        &&& !pte.is_present() ==> {
            &&& self.is_absent()
            &&& parent_level > 1 ==> !pte.is_last(parent_level)
        }
        &&& pte.is_present() && !pte.is_last(parent_level) ==> {
            &&& self.is_node()
            &&& meta_to_frame(self.node().meta_vaddr()) == pte.paddr()
        }
        &&& pte.is_present() && pte.is_last(parent_level) ==> {
            &&& self.is_frame()
            &&& self.frame().mapped_pa == pte.paddr()
            &&& self.frame().prop == pte.prop()
        }
    }

    /// PTE-shape constraint for a borrowed / translation-only entry. The
    /// PTE must be a node-PTE (present and non-leaf at `parent_level`),
    /// since the borrowed sub-table is accessed only via the MMU walk.
    /// Unlike [`match_pte`], we do *not* pin the PTE's target paddr to
    /// any owned `NodeOwner` — the sub-table is owned by a different
    /// page-table configuration and the embedding doesn't track its
    /// address here.
    pub open spec fn borrowed_match_pte(self, pte: C::E, parent_level: PagingLevel) -> bool {
        &&& self.is_borrowed()
        &&& has_safe_slot(pte.paddr())
        &&& pte.is_present()
        &&& !pte.is_last(parent_level)
    }

    /// When owner is absent and pte is the absent PTE with valid paddr, match_pte holds.
    pub proof fn absent_match_pte(owner: Self, pte: C::E, parent_level: PagingLevel)
        requires
            owner.is_absent(),
            pte == C::E::new_absent_spec(),
            has_safe_slot(pte.paddr()),
        ensures
            owner.match_pte(pte, parent_level),
    {
        C::E::lemma_page_table_entry_properties();
    }

    pub proof fn last_pte_implies_frame_match(self, pte: C::E, parent_level: PagingLevel)
        requires
            self.inv(),
            self.match_pte(pte, parent_level),
            1 < parent_level,
            pte.is_last(parent_level),
        ensures
            self.is_frame(),
            self.frame().mapped_pa == pte.paddr(),
            self.frame().prop == pte.prop(),
    {
    }

    pub proof fn huge_frame_split_child_at(self, regions: MetaRegionOwners, idx: usize)
        requires
            self.inv(),
            self.is_frame(),
            regions.inv(),
            1 < self.parent_level < NR_LEVELS,
            idx < NR_ENTRIES,
        ensures
            self.frame().mapped_pa + idx * page_size((self.parent_level - 1) as PagingLevel)
                < MAX_PADDR,
            ((self.frame().mapped_pa + idx * page_size(
                (self.parent_level - 1) as PagingLevel,
            )) as Paddr) % page_size((self.parent_level - 1) as PagingLevel) == 0,
            ((self.frame().mapped_pa + idx * page_size(
                (self.parent_level - 1) as PagingLevel,
            )) as Paddr) + page_size((self.parent_level - 1) as PagingLevel) <= MAX_PADDR,
            ((self.frame().mapped_pa + idx * page_size(
                (self.parent_level - 1) as PagingLevel,
            )) as Paddr) % PAGE_SIZE == 0,
    {
        let pa = self.frame().mapped_pa;
        let child_pa = (pa + idx * page_size((self.parent_level - 1) as PagingLevel)) as Paddr;
        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_spec_values();
        vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_spec_level1();
        vstd::arithmetic::power2::lemma2_to64();
        if self.parent_level == 2 {
            crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_divides(1, 2);
            assert(child_pa + page_size(1) <= MAX_PADDR) by {
                assert(idx * 4096 + 4096 <= 2097152);
            };
        } else {
            crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_va_align_page_size(pa, 2);
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(idx as int, page_size(2) as int);
            vstd::arithmetic::div_mod::lemma_add_mod_noop(
                pa as int,
                (idx * page_size(2)) as int,
                page_size(2) as int,
            );
        }
    }

    /// Helper: sub-page validity is preserved when the only slot that changed is the
    /// frame's own slot (and slots map and other slot owners are unchanged).
    pub proof fn frame_sub_pages_valid_preserved_at_own_slot(
        self,
        r0: MetaRegionOwners,
        r1: MetaRegionOwners,
    )
        requires
            self.inv(),
            r0.inv(),
            self.is_frame(),
            self.parent_level <= NR_LEVELS,
            self.frame_sub_pages_valid(r0),
            r0.slots == r1.slots,
            r0.slot_owners.dom() =~= r1.slot_owners.dom(),
            forall|i: int|
                #![trigger r1.slot_owners[i]]
                i != frame_to_index(self.meta_slot_paddr()->0) && r0.slot_owners.contains_key(i)
                    ==> r0.slot_owners[i] == r1.slot_owners[i],
        ensures
            self.frame_sub_pages_valid(r1),
    {
        if self.parent_level > 1 {
            let pa = self.frame().mapped_pa;
            let nr_pages = page_size(self.parent_level) / PAGE_SIZE;
            let self_idx = frame_to_index(self.meta_slot_paddr().unwrap());
            assert forall|j: usize|
                #![trigger frame_to_index((pa + j * PAGE_SIZE) as usize)]
                0 < j < nr_pages implies {
                let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                &&& r1.slots.contains_key(sub_idx)
                &&& r1.slot_owners[sub_idx].usage !is MMIO ==> {
                    &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                    &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() <= REF_COUNT_MAX
                }
            } by {
                let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                // From frame_sub_pages_valid(r0): slot existence is unconditional.
                // sub_idx != self_idx by arithmetic: pa is PAGE_SIZE-aligned, so
                // self_idx = pa / PAGE_SIZE, and sub_idx = (pa + j*PAGE_SIZE) / PAGE_SIZE
                //         = pa/PAGE_SIZE + j = self_idx + j > self_idx (since j >= 1).
                let pa_plus_int: int = pa + j * PAGE_SIZE;
                crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(
                self.parent_level);
                crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_div_mul_eq(
                    self.parent_level,
                );
                vstd::arithmetic::div_mod::lemma_div_multiples_vanish_quotient(
                    j as int,
                    pa as int,
                    PAGE_SIZE as int,
                );
                // Slot equality at sub_idx carries usage and rc forward.
            }
        }
    }

    /// Sub-page slot validity for huge frames (fine-grained: all 4KB pages within).
    ///
    /// When a frame at this entry has `parent_level > 1`, it is a huge page covering
    /// `page_size(parent_level)` bytes. Every 4KB sub-page within this range (excluding
    /// the j = 0 case which coincides with the frame's own slot) must be allocated
    /// (in the free pool) with `rc != UNUSED`.
    ///
    /// The fine-grained form (over `j * PAGE_SIZE` rather than `j * page_size(L-1)`) is
    /// what enables the recursive split case in `split_if_mapped_huge`: when splitting a
    /// 1GB frame into 2MB sub-frames, each 2MB sub-frame's own sub-page validity (over
    /// its 511 4KB sub-sub-pages) follows from the 1GB frame's fine-grained validity over
    /// the corresponding subrange of indices.
    pub open spec fn frame_sub_pages_valid(self, regions: MetaRegionOwners) -> bool {
        self.is_frame() && self.parent_level > 1 ==> {
            let pa = self.frame().mapped_pa;
            let nr_pages = page_size(self.parent_level) / PAGE_SIZE;
            forall|j: usize|
                #![trigger frame_to_index((pa + j * PAGE_SIZE) as usize)]
                0 < j < nr_pages ==> {
                    let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                    // Slot existence is unconditional — the metadata array spans all
                    // phys memory at boot, so every valid sub-page PA has an allocated slot.
                    &&& regions.slots.contains_key(
                        sub_idx,
                    )
                    // RC bookkeeping (`rc != UNUSED`, `rc > 0`) applies only to non-MMIO
                    // sub-pages. MMIO sub-page slots stay in the free pool with
                    // `rc == UNUSED` and `usage == MMIO`.
                    &&& regions.slot_owners[sub_idx].usage !is MMIO ==> {
                        &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value()
                            != REF_COUNT_UNUSED
                        &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                        &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value()
                            <= REF_COUNT_MAX
                    }
                }
        }
    }

    pub open spec fn metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        if self.is_node() {
            let idx = frame_to_index(self.meta_slot_paddr()->0);
            &&& regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            &&& 0 < regions.slot_owners[idx].inner_perms.ref_count.value() <= REF_COUNT_MAX
            &&& regions.slot_owners[idx].slot_vaddr == self.node().meta_vaddr()
            &&& regions.slots[idx].value().wf(regions.slot_owners[idx])
            &&& regions.slot_owners[idx].paths_in_pt == set![self.path]
            &&& self.node().metaregion_sound_node(regions)
        } else if self.is_frame() {
            let idx = frame_to_index(self.meta_slot_paddr()->0);
            &&& regions.slots.contains_key(idx)
            &&& regions.slots[idx].addr() == index_to_meta(idx)
            &&& regions.slots[idx].is_init()
            &&& regions.slots[idx].value().wf(regions.slot_owners[idx])
            &&& regions.slot_owners[idx].usage !is PageTable
            // Tracked vs MMIO discriminator is the slot's `usage`. MMIO slots
            // stay in the free pool with `rc == UNUSED`; tracked slots have
            // `rc > 0`. The slot's `usage == MMIO` is pinned by the paddr's
            // range membership via `axiom_mmio_usage_iff_mmio_paddr`.
            &&& regions.slot_owners[idx].usage !is MMIO ==> {
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    > 0
                // A mapped (tracked) frame is SHARED, never the UNIQUE sentinel
                // (`rc <= MAX < REF_COUNT_UNIQUE`). Lets the UNIQUE-branch
                // `paths_in_pt`-empty inv clause hold vacuously for mapped
                // frames whose `paths_in_pt` is non-empty.
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() <= REF_COUNT_MAX
            }
            &&& regions.slot_owners[idx].paths_in_pt.contains(self.path)
            &&& self.frame_sub_pages_valid(regions)
        } else {
            true
        }
    }

    /// An active page-table node cannot occupy a metadata slot whose refcount is
    /// still `REF_COUNT_UNUSED`.
    pub proof fn lemma_active_entry_not_in_free_pool(
        entry: Self,
        regions: MetaRegionOwners,
        free_idx: int,
    )
        requires
            regions.inv(),
            entry.inv(),
            entry.is_node(),
            entry.metaregion_sound(regions),
            regions.slots.contains_key(free_idx),
            regions.slot_owners[free_idx].inner_perms.ref_count.value() == REF_COUNT_UNUSED,
        ensures
            frame_to_index(entry.meta_slot_paddr()->0) != free_idx,
    {
        let idx = frame_to_index(entry.meta_slot_paddr().unwrap());
        if idx == free_idx {
            assert(false);
        }
    }

    pub open spec fn meta_slot_paddr(self) -> Option<Paddr> {
        if self.is_node() {
            Some(meta_to_frame(self.node().meta_vaddr()))
        } else if self.is_frame() {
            Some(self.frame().mapped_pa)
        } else {
            None
        }
    }

    pub open spec fn meta_slot_paddr_neq(self, other: Self) -> bool {
        self.meta_slot_paddr() is Some ==> other.meta_slot_paddr() is Some
            ==> self.meta_slot_paddr()->0 != other.meta_slot_paddr()->0
    }

    /// `metaregion_sound` transfers when `slot_owners` matches and `slots` is a superset.
    /// For nodes: only `slot_owners` matters. For frames: `slots.contains_key` and `slots[idx]`
    /// must be preserved, which holds when `slots` is a superset with values unchanged.
    pub proof fn metaregion_sound_slot_owners_only(self, r0: MetaRegionOwners, r1: MetaRegionOwners)
        requires
            self.inv(),
            self.metaregion_sound(r0),
            r0.slot_owners == r1.slot_owners,
            forall|k: int| r0.slots.contains_key(k) ==> #[trigger] r1.slots.contains_key(k),
            forall|k: int| r0.slots.contains_key(k) ==> r0.slots[k] == #[trigger] r1.slots[k],
        ensures
            self.metaregion_sound(r1),
    {
    }

    /// If `metaregion_sound(r0)` holds and `r1` differs from `r0` only at one slot index
    /// that this entry does not reference, then `metaregion_sound(r1)` also holds.
    pub proof fn metaregion_sound_one_slot_changed(
        self,
        r0: MetaRegionOwners,
        r1: MetaRegionOwners,
        changed_idx: int,
    )
        requires
            self.inv(),
            self.metaregion_sound(r0),
            forall|i: int|
                #![trigger r1.slot_owners[i]]
                i != changed_idx ==> r0.slot_owners[i] == r1.slot_owners[i],
            r0.slot_owners.dom() =~= r1.slot_owners.dom(),
            // slots preserved at the entry's index (frames read from slots)
            forall|k: int| r0.slots.contains_key(k) ==> #[trigger] r1.slots.contains_key(k),
            forall|k: int| r0.slots.contains_key(k) ==> r0.slots[k] == #[trigger] r1.slots[k],
            self.meta_slot_paddr() is Some ==> frame_to_index(self.meta_slot_paddr()->0)
                != changed_idx,
            // Huge frames: if changed_idx is one of this frame's 4KB sub-page slots and
            // that sub-slot is non-MMIO, the sub-page validity at changed_idx must still
            // hold in r1. MMIO sub-pages keep `usage == MMIO` and `rc == UNUSED`.
            self.is_frame() && self.parent_level > 1 ==> {
                let pa = self.frame().mapped_pa;
                let nr_pages = page_size(self.parent_level) / PAGE_SIZE;
                forall|j: usize|
                    0 < j < nr_pages ==> {
                        let sub_idx = #[trigger] frame_to_index((pa + j * PAGE_SIZE) as usize);
                        sub_idx != changed_idx || r1.slot_owners[sub_idx].usage is MMIO || (
                        r1.slots.contains_key(sub_idx)
                            && r1.slot_owners[sub_idx].inner_perms.ref_count.value()
                            != REF_COUNT_UNUSED
                            && r1.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                            && r1.slot_owners[sub_idx].inner_perms.ref_count.value()
                            <= REF_COUNT_MAX)
                    }
            },
        ensures
            self.metaregion_sound(r1),
    {
    }

    /// `metaregion_sound` is preserved when only `paths_in_pt` changes at a slot,
    /// `slots` is unchanged, and the new `paths_in_pt` is correct for any node at that index.
    pub proof fn metaregion_sound_paths_in_pt_changed(
        self,
        r0: MetaRegionOwners,
        r1: MetaRegionOwners,
        changed_idx: int,
    )
        requires
            self.inv(),
            r0.inv(),
            self.metaregion_sound(r0),
            r0.slots == r1.slots,
            r0.slot_owners.dom() =~= r1.slot_owners.dom(),
            // All slots other than changed_idx are entirely unchanged.
            forall|i: int|
                #![trigger r1.slot_owners[i]]
                i != changed_idx ==> r0.slot_owners[i] == r1.slot_owners[i],
            // At changed_idx, only paths_in_pt differs.
            r1.slot_owners[changed_idx].inner_perms == r0.slot_owners[changed_idx].inner_perms,
            r1.slot_owners[changed_idx].slot_vaddr == r0.slot_owners[changed_idx].slot_vaddr,
            r1.slot_owners[changed_idx].usage == r0.slot_owners[changed_idx].usage,
            // For nodes at changed_idx: the new paths_in_pt must match this entry's path.
            self.is_node() && self.meta_slot_paddr() is Some && frame_to_index(
                self.meta_slot_paddr()->0,
            ) == changed_idx ==> r1.slot_owners[changed_idx].paths_in_pt == set![self.path],
            // For frames at changed_idx: the new paths_in_pt must still contain this entry's path.
            self.is_frame() && self.meta_slot_paddr() is Some && frame_to_index(
                self.meta_slot_paddr()->0,
            ) == changed_idx ==> r1.slot_owners[changed_idx].paths_in_pt.contains(self.path),
            // For huge frames: if changed_idx is one of this frame's sub-page slots (j > 0),
            // the new paths_in_pt at changed_idx must remain empty.
            self.is_frame() && self.parent_level > 1 ==> {
                let pa = self.frame().mapped_pa;
                let sub_level = (self.parent_level - 1) as PagingLevel;
                forall|j: int|
                    0 < j < NR_ENTRIES ==> {
                        let sub_idx = #[trigger] frame_to_index(
                            (pa + j * page_size(sub_level)) as usize,
                        );
                        sub_idx != changed_idx || r1.slot_owners[changed_idx].paths_in_pt.is_empty()
                    }
            },
        ensures
            self.metaregion_sound(r1),
    {
        if self.meta_slot_paddr() is Some {
            let eidx = frame_to_index(self.meta_slot_paddr().unwrap());
            // Bridge `rc > 0` from r0 to r1: at `eidx == changed_idx` inner_perms
            // are identical; elsewhere the entire slot_owner is identical.
            if self.is_frame() {
                // Sub-page validity for huge frames: slot existence (unconditional)
                // plus `rc` bookkeeping when tracked.
                if self.parent_level > 1 {
                    let pa = self.frame().mapped_pa;
                    let nr_pages = page_size(self.parent_level) / PAGE_SIZE;
                    let self_idx = frame_to_index(self.meta_slot_paddr().unwrap());
                    assert forall|j: usize|
                        #![trigger frame_to_index((pa + j * PAGE_SIZE) as usize)]
                        0 < j < nr_pages implies {
                        let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                        &&& r1.slots.contains_key(sub_idx)
                        &&& r1.slot_owners[sub_idx].usage !is MMIO ==> {
                            &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value()
                                != REF_COUNT_UNUSED
                            &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                            &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value()
                                <= REF_COUNT_MAX
                        }
                    } by {
                        let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                        // From self.metaregion_sound(r0)'s frame arm (frame_sub_pages_valid(r0)).
                    }
                }
            }
        }
    }

    /// Two entries with the same physical address whose `paths_in_pt` matches their
    /// respective paths must have the same path.
    pub proof fn same_paddr_implies_same_path(self, other: Self, regions: MetaRegionOwners)
        requires
            self.meta_slot_paddr() is Some,
            self.meta_slot_paddr() == other.meta_slot_paddr(),
            regions.slot_owners[frame_to_index(self.meta_slot_paddr()->0)].paths_in_pt
                == set![self.path],
            regions.slot_owners[frame_to_index(self.meta_slot_paddr()->0)].paths_in_pt
                == set![other.path],
        ensures
            self.path == other.path,
    {
        assert(set![self.path].contains(other.path));
    }

    /// `metaregion_sound` is preserved when only `ref_count.value()` changes at this entry's slot
    /// and `slots` is unchanged.
    pub proof fn metaregion_sound_rc_value_changed(self, r0: MetaRegionOwners, r1: MetaRegionOwners)
        requires
            self.inv(),
            r0.inv(),
            self.metaregion_sound(r0),
            self.meta_slot_paddr() is Some,
            r0.slots == r1.slots,
            ({
                let idx = frame_to_index(self.meta_slot_paddr()->0);
                &&& r1.slot_owners[idx].inner_perms.ref_count.id()
                    == r0.slot_owners[idx].inner_perms.ref_count.id()
                &&& r1.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                &&& r1.slot_owners[idx].inner_perms.ref_count.value()
                    > 0
                // Needed to re-establish the node branch's SHARED range (`<= MAX`).
                &&& r1.slot_owners[idx].inner_perms.ref_count.value() <= REF_COUNT_MAX
                &&& r1.slot_owners[idx].inner_perms.storage
                    == r0.slot_owners[idx].inner_perms.storage
                &&& r1.slot_owners[idx].inner_perms.vtable_ptr
                    == r0.slot_owners[idx].inner_perms.vtable_ptr
                &&& r1.slot_owners[idx].inner_perms.in_list
                    == r0.slot_owners[idx].inner_perms.in_list
                &&& r1.slot_owners[idx].slot_vaddr == r0.slot_owners[idx].slot_vaddr
                &&& r1.slot_owners[idx].paths_in_pt
                    == r0.slot_owners[idx].paths_in_pt
                // `usage` is part of `metaregion_sound_node` (node-repark
                // discriminator), so it must be preserved to carry soundness.
                &&& r1.slot_owners[idx].usage == r0.slot_owners[idx].usage
            }),
            // All other slot_owners unchanged: preserves sub-page validity for huge frames.
            forall|i: int|
                #![trigger r1.slot_owners[i]]
                i != frame_to_index(self.meta_slot_paddr()->0) && r0.slot_owners.contains_key(i)
                    ==> r0.slot_owners[i] == r1.slot_owners[i],
        ensures
            self.metaregion_sound(r1),
    {
        if self.is_frame() && self.parent_level > 1 {
            let pa = self.frame().mapped_pa;
            let nr_pages = page_size(self.parent_level) / PAGE_SIZE;
            let self_idx = frame_to_index(self.meta_slot_paddr().unwrap());
            assert forall|j: usize|
                #![trigger frame_to_index((pa + j * PAGE_SIZE) as usize)]
                0 < j < nr_pages implies {
                let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                &&& r1.slots.contains_key(sub_idx)
                &&& r1.slot_owners[sub_idx].usage !is MMIO ==> {
                    &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                }
            } by {
                let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                let pa_plus_int: int = pa + j * PAGE_SIZE;
                crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(
                self.parent_level);
                crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_div_mul_eq(
                    self.parent_level,
                );
                // sub_idx = (pa + j*PAGE_SIZE) / PAGE_SIZE = pa/PAGE_SIZE + j (since pa % PAGE_SIZE == 0).
                vstd::arithmetic::div_mod::lemma_div_multiples_vanish_quotient(
                    j as int,
                    pa as int,
                    PAGE_SIZE as int,
                );
            }
        }
    }

    /// Two nodes whose `paths_in_pt` matches their paths have different addresses
    /// if they have different paths.
    pub proof fn nodes_different_paths_different_addrs(self, other: Self, regions: MetaRegionOwners)
        requires
            self.is_node(),
            other.is_node(),
            self.meta_slot_paddr() is Some ==> regions.slot_owners[frame_to_index(
                self.meta_slot_paddr()->0,
            )].paths_in_pt == set![self.path],
            other.meta_slot_paddr() is Some ==> regions.slot_owners[frame_to_index(
                other.meta_slot_paddr()->0,
            )].paths_in_pt == set![other.path],
            self.path != other.path,
        ensures
            self.node().meta_vaddr() != other.node().meta_vaddr(),
    {
        let slot_vaddr = self.node().meta_vaddr();
        let other_addr = other.node().meta_vaddr();
        let self_idx = frame_to_index(meta_to_frame(slot_vaddr));
        let other_idx = frame_to_index(meta_to_frame(other_addr));

        if slot_vaddr == other_addr {
            assert(set![self.path].contains(other.path));
            assert(false);  // Contradiction
        }
    }

    /// Two node entries with `metaregion_sound` under the same regions cannot share
    /// a meta slot paddr if their paths have different lengths.
    ///
    /// For nodes, `metaregion_sound` requires `paths_in_pt == set![path]` (singleton).
    /// Equal slot indices would force equal singleton sets, hence equal paths —
    /// contradicting the length difference.
    pub proof fn nodes_different_path_lengths_neq_slot(self, other: Self, regions: MetaRegionOwners)
        requires
            self.is_node(),
            other.is_node(),
            self.metaregion_sound(regions),
            other.metaregion_sound(regions),
            self.path.len() != other.path.len(),
        ensures
            self.meta_slot_paddr_neq(other),
    {
        let self_idx = frame_to_index(self.meta_slot_paddr().unwrap());
        let other_idx = frame_to_index(other.meta_slot_paddr().unwrap());
        if self_idx == other_idx {
            assert(set![self.path].contains(other.path));
            assert(false);
        }
    }
}

impl<C: PageTableConfig> EntryOwner<C> {
    /// Structural invariant of an entry owner. This is the whole of `inv()`,
    /// and is also used directly by `Child::invariants`.
    pub open spec fn inv_base(self) -> bool {
        &&& self.is_node() ==> {
            &&& self.node().inv()
            &&& self.parent_level == self.node().level + 1
        }
        &&& self.is_frame() ==> {
            // Architectural constraint: frames only exist at PT levels that the
            // ISA actually supports as leaves (4K, 2M, 1G on x86). `parent_level
            // == NR_LEVELS` would be a 512 GiB huge page, which no current arch
            // permits — and `Mapping::inv` would reject its page_size.
            &&& 1 <= self.parent_level < NR_LEVELS
            &&& has_safe_slot(self.frame().mapped_pa)
            &&& self.frame().mapped_pa % page_size(self.parent_level) == 0
            &&& self.frame().mapped_pa + page_size(self.parent_level) <= MAX_PADDR
            &&& C::raw_item_well_formed(
                self.frame().mapped_pa,
                self.parent_level,
                self.frame().prop,
            )
            &&& C::E::new_page_req(self.frame().mapped_pa, self.parent_level, self.frame().prop)
        }
        &&& self.is_borrowed() ==> { true }
        &&& self.path.inv()
    }
}

impl<C: PageTableConfig> Inv for EntryOwner<C> {
    open spec fn inv(self) -> bool {
        self.inv_base()
    }
}

impl<C: PageTableConfig> View for EntryOwner<C> {
    type V = EntryView<C>;

    open spec fn view(&self) -> <Self as View>::V {
        if self.is_frame() {
            let frame = self.frame();
            EntryView::Leaf {
                leaf: LeafPageTableEntryView {
                    map_va: vaddr(self.path) as int,
                    //                    frame_pa: self.base_addr as int,
                    //                    in_frame_index: self.index as int,
                    map_to_pa: frame.mapped_pa as int,
                    level: self.path.len() as u8,
                    prop: frame.prop,
                    phantom: PhantomData,
                },
            }
        } else if self.is_node() {
            let node = self.node();
            EntryView::Intermediate {
                node: IntermediatePageTableEntryView {
                    map_va: vaddr(self.path) as int,
                    //                    frame_pa: self.base_addr as int,
                    //                    in_frame_index: self.index as int,
                    map_to_pa: meta_to_frame(node.meta_vaddr()) as int,
                    level: self.path.len() as u8,
                    phantom: PhantomData,
                },
            }
        } else {
            EntryView::Absent
        }
    }
}

impl<C: PageTableConfig> InvView for EntryOwner<C> {
    proof fn view_preserves_inv(self) {
        // `EntryView::inv()` is trivially `true` (the view of an `EntryOwner`
        // is never inspected outside this trait obligation), so the
        // postcondition `self.view().inv()` discharges automatically.
    }
}

impl<'a, 'rcu, C: PageTableConfig> OwnerOf for Entry<'a, 'rcu, C> {
    type Owner = EntryOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.idx < NR_ENTRIES
        &&& owner.match_pte(self.pte, owner.parent_level)
        &&& has_safe_slot(self.pte.paddr())
    }
}

} // verus!
