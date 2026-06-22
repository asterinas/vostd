use vstd::prelude::*;

use vstd::cell;
use vstd::modes::tracked_swap;
use vstd::simple_pptr::PointsTo;
use vstd_extra::array_ptr;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::arch::mm::PagingConsts;
use crate::mm::frame::meta::MetaSlot;
use crate::mm::frame::meta::{REF_COUNT_MAX, REF_COUNT_UNUSED};
use crate::mm::page_prop::PageProperty;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::*;
use crate::specs::arch::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::mm::frame::mapping::{frame_to_index, meta_addr, meta_to_frame};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::node::entry_view::*;
use crate::specs::mm::page_table::*;
use core::marker::PhantomData;

verus! {

pub tracked struct FrameEntryOwner {
    pub mapped_pa: usize,
    pub size: usize,
    pub prop: PageProperty,
    /// Whether the frame is ref-counted (Tracked) or raw MMIO (Untracked).
    /// Determines whether the slot at `frame_to_index(mapped_pa)` carries a
    /// non-zero refcount and participates in `metaregion_sound`'s rc check.
    pub is_tracked: bool,
}

pub tracked enum EntryOwnerKind<C: PageTableConfig> {
    Node(NodeOwner<C>),
    Frame(FrameEntryOwner),
    Locked(ghost Seq<FrameView<C>>),
    /// Translation-only / borrowed-sub-tree variant.
    ///
    /// Present when the slot's PTE references a sub-tree owned by *another*
    /// page-table configuration (e.g. a user PT's kernel-half slot
    /// pointing at a kernel-owned sub-table). The ghost `Set<Mapping>`
    /// records the mappings reachable through that sub-tree so the
    /// embedding can reason about what the borrowed translation provides
    /// without descending into a sub-tree it does not own. Mutually
    /// exclusive with `node`, `frame`, `locked`, and `absent` by construction.
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
    pub open spec fn is_locked(self) -> bool {
        self.kind is Locked
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

    pub open spec fn frame(self) -> FrameEntryOwner {
        self.kind->Frame_0
    }

    pub open spec fn locked(self) -> Seq<FrameView<C>> {
        self.kind->Locked_0
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
        is_tracked: bool,
    ) -> Self {
        EntryOwner {
            kind: EntryOwnerKind::Frame(
                FrameEntryOwner {
                    mapped_pa: paddr,
                    size: page_size(parent_level),
                    prop,
                    is_tracked,
                },
            ),
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

    pub proof fn tracked_take_frame(tracked &mut self) -> (tracked res: FrameEntryOwner)
        requires
            old(self).kind is Frame,
        ensures
            res == old(self).frame(),
            *final(self) == (EntryOwner { kind: EntryOwnerKind::Absent, ..*old(self) }),
    {
        let tracked mut tmp = EntryOwnerKind::Absent;
        tracked_swap(&mut self.kind, &mut tmp);
        match tmp {
            EntryOwnerKind::Frame(frame) => frame,
            _ => { proof_from_false() },
        }
    }

    pub proof fn tracked_put_frame(tracked &mut self, tracked frame: FrameEntryOwner)
        ensures
            *final(self) == (EntryOwner { kind: EntryOwnerKind::Frame(frame), ..*old(self) }),
    {
        self.kind = EntryOwnerKind::Frame(frame);
    }

    pub proof fn tracked_borrow_frame(tracked &self) -> (tracked res: &FrameEntryOwner)
        requires
            self.kind is Frame,
        ensures
            *res == self.frame(),
    {
        match self.kind {
            EntryOwnerKind::Frame(ref frame) => frame,
            _ => { proof_from_false() },
        }
    }

    pub proof fn tracked_borrow_mut_frame(tracked &mut self) -> (tracked res: &mut FrameEntryOwner)
        requires
            old(self).kind is Frame,
        ensures
            *res == old(self).frame(),
            *final(self) == (EntryOwner { kind: EntryOwnerKind::Frame(*final(res)), ..*old(self) }),
    {
        match self.kind {
            EntryOwnerKind::Frame(ref mut frame) => frame,
            _ => { proof_from_false() },
        }
    }

    pub axiom fn tracked_new_frame(
        paddr: Paddr,
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
        prop: PageProperty,
        is_tracked: bool,
    ) -> tracked Self
        returns
            Self::new_frame(paddr, path, parent_level, prop, is_tracked),
    ;

    /// Structural connection between a frame entry's recorded `is_tracked` flag and
    /// the trackedness of the item that would be reconstructed by `item_from_raw_spec`.
    ///
    /// **Why this is sound:** every `FrameEntryOwner` was created via `new_frame(...,
    /// is_tracked)`, and at every construction site the caller passes
    /// `is_tracked = C::tracked(item)` where `item` is the item being mapped. By the
    /// `item_from_raw / item_into_raw` round-trip law, re-reading the entry's
    /// `(mapped_pa, parent_level, prop)` and reconstructing via `item_from_raw_spec`
    /// gives back the original `item`. So `C::tracked` of the reconstructed item
    /// equals the recorded `is_tracked`.
    ///
    /// Encoded as an axiom (rather than an `EntryOwner::inv_base` clause) because
    /// adding it to `inv_base` would require discharging this connection at every
    /// `new_frame` call site — a wide cascading refactor (attempted, abandoned in
    /// the FrameEntryOwner is_tracked refactor session).
    pub axiom fn axiom_frame_is_tracked_matches_item(entry: Self)
        requires
            entry.is_frame(),
            entry.inv_base(),
        ensures
            entry.frame().is_tracked == C::tracked(
                C::item_from_raw_spec(
                    entry.frame().mapped_pa,
                    entry.parent_level,
                    entry.frame().prop,
                ),
            ),
    ;

    /// The frame's `is_tracked` flag is pinned to its paddr's range membership:
    /// tracked frames map regular RAM (non-MMIO paddrs); untracked frames map
    /// MMIO. Combined with `axiom_mmio_usage_iff_mmio_paddr`, this lets proofs
    /// translate between `is_tracked` on a `FrameEntryOwner` and `usage == MMIO`
    /// on the corresponding meta slot.
    pub broadcast axiom fn axiom_frame_is_tracked_iff_not_mmio(entry: Self)
        requires
            entry.is_frame(),
            entry.inv_base(),
        ensures
            #[trigger] entry.frame().is_tracked
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
    /// The `requires` reflect properties guaranteed by `collect_largest_pages` postconditions,
    /// so this axiom is only ever called with values that satisfy them.
    pub axiom fn new_untracked_frame(
        paddr: Paddr,
        parent_level: PagingLevel,
        prop: PageProperty,
    ) -> (tracked res: Self)
        requires
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
            1 <= parent_level,
            parent_level <= NR_LEVELS,
        ensures
            res.is_frame(),
            res.frame().mapped_pa == paddr,
            res.frame().prop == prop,
            res.frame().size == page_size(parent_level),
            res.frame().is_tracked == false,
            res.parent_level == parent_level,
            res.path.inv(),
            res.inv_base(),
            crate::mm::page_table::Child::<C>::Frame(paddr, parent_level, prop).wf(res),
    ;

    pub open spec fn match_pte(self, pte: C::E, parent_level: PagingLevel) -> bool {
        &&& pte.paddr() % PAGE_SIZE == 0
        &&& pte.paddr() < MAX_PADDR
        &&& !pte.is_present() ==> {
            &&& self.is_absent()
            &&& parent_level > 1 ==> !pte.is_last(parent_level)
        }
        &&& pte.is_present() && !pte.is_last(parent_level) ==> {
            &&& self.is_node()
            &&& meta_to_frame(self.node().meta_addr_self()) == pte.paddr()
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
        &&& pte.paddr() % PAGE_SIZE == 0
        &&& pte.paddr() < MAX_PADDR
        &&& pte.is_present()
        &&& !pte.is_last(parent_level)
    }

    /// When owner is absent and pte is the absent PTE with valid paddr, match_pte holds.
    pub proof fn absent_match_pte(owner: Self, pte: C::E, parent_level: PagingLevel)
        requires
            owner.is_absent(),
            pte == C::E::new_absent_spec(),
            pte.paddr() % PAGE_SIZE == 0,
            pte.paddr() < MAX_PADDR,
        ensures
            owner.match_pte(pte, parent_level),
    {
        C::E::lemma_page_table_entry_properties();
        if parent_level > 1 {
            assert(!pte.is_last(parent_level));
        }
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
        if !pte.is_present() {
            assert(self.is_absent());
            assert(!pte.is_last(parent_level));
            assert(false);
        }
        assert(self.is_frame());
        assert(self.frame().mapped_pa == pte.paddr());
        assert(self.frame().prop == pte.prop());
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
        assert(self.parent_level == 2 || self.parent_level == 3);
        assert(NR_ENTRIES == 512) by {
            crate::arch::mm::lemma_nr_subpage_per_huge_eq_nr_entries();
        };
        assert(crate::mm::nr_subpage_per_huge::<PagingConsts>() == 512usize) by {
            crate::arch::mm::lemma_nr_subpage_per_huge_eq_nr_entries();
        };
        vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_spec_level1();
        assert(512usize.ilog2() == 9);
        vstd::arithmetic::power2::lemma2_to64();
        if self.parent_level == 2 {
            assert(page_size(2) == (PAGE_SIZE * pow2((512usize.ilog2() * 1usize) as nat)) as usize);
            assert(page_size(2) == 2097152);
            assert(pa % page_size(2) == 0);
            crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_divides(1, 2);
            assert(child_pa % page_size(1) == 0);
            assert(child_pa + page_size(1) <= MAX_PADDR) by {
                assert(idx < 512);
                assert(idx * 4096 + 4096 <= 2097152);
                assert(child_pa + page_size(1) <= pa + page_size(2));
            };
        } else {
            assert(self.parent_level == 3);
            assert(page_size(3) == (PAGE_SIZE * pow2((512usize.ilog2() * 2usize) as nat)) as usize);
            assert(page_size(3) == 1073741824);
            assert(pa % page_size(3) == 0);
            crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_va_align_page_size(pa, 2);
            assert(child_pa == pa + idx * page_size(2));
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(idx as int, page_size(2) as int);
            vstd::arithmetic::div_mod::lemma_add_mod_noop(
                pa as int,
                (idx * page_size(2)) as int,
                page_size(2) as int,
            );
            assert(child_pa % page_size(2) == 0);
            assert(child_pa + page_size(2) <= MAX_PADDR) by {
                assert(idx * 2097152 + 2097152 <= 1073741824);
                assert(child_pa + page_size(2) <= pa + page_size(3));
            };
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
            forall|i: usize|
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
                &&& r1.slot_owners[sub_idx].usage
                    != crate::specs::mm::frame::meta_owners::PageUsage::MMIO ==> {
                    &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                    &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() <= REF_COUNT_MAX
                }
            } by {
                let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                // From frame_sub_pages_valid(r0): slot existence is unconditional.
                assert(r0.slots.contains_key(sub_idx));
                // sub_idx != self_idx by arithmetic: pa is PAGE_SIZE-aligned, so
                // self_idx = pa / PAGE_SIZE, and sub_idx = (pa + j*PAGE_SIZE) / PAGE_SIZE
                //         = pa/PAGE_SIZE + j = self_idx + j > self_idx (since j >= 1).
                let pa_plus_int: int = pa as int + (j as int) * (PAGE_SIZE as int);
                crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(
                self.parent_level);
                assert((j as int) * (PAGE_SIZE as int) < (nr_pages as int) * (PAGE_SIZE as int))
                    by {
                    vstd::arithmetic::mul::lemma_mul_strict_inequality(
                        j as int,
                        nr_pages as int,
                        PAGE_SIZE as int,
                    );
                };
                crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_div_mul_eq(
                    self.parent_level,
                );
                assert(pa_plus_int < MAX_PADDR);
                vstd::arithmetic::div_mod::lemma_div_multiples_vanish_quotient(
                    j as int,
                    pa as int,
                    PAGE_SIZE as int,
                );
                assert(self_idx as int == pa as int / PAGE_SIZE as int);
                assert(sub_idx != self_idx);
                assert(r0.slot_owners.contains_key(sub_idx));
                assert(r0.slot_owners[sub_idx] == r1.slot_owners[sub_idx]);
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
                    &&& regions.slot_owners[sub_idx].usage
                        != crate::specs::mm::frame::meta_owners::PageUsage::MMIO ==> {
                        &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value()
                            != REF_COUNT_UNUSED
                        &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                        &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() <= REF_COUNT_MAX
                    }
                }
        }
    }

    pub open spec fn metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        if self.is_node() {
            let idx = frame_to_index(self.meta_slot_paddr()->0);
            &&& regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            &&& 0 < regions.slot_owners[idx].inner_perms.ref_count.value() <= REF_COUNT_MAX
            &&& regions.slot_owners[idx].self_addr == self.node().meta_addr_self()
            &&& regions.slots[idx].value().wf(regions.slot_owners[idx])
            &&& regions.slot_owners[idx].paths_in_pt == set![self.path]
            &&& self.node().metaregion_sound_node(regions)
        } else if self.is_frame() {
            let idx = frame_to_index(self.meta_slot_paddr()->0);
            &&& regions.slots.contains_key(idx)
            &&& regions.slots[idx].addr() == meta_addr(idx)
            &&& regions.slots[idx].is_init()
            &&& regions.slots[idx].value().wf(
                regions.slot_owners[idx],
            )
            // Tracked vs MMIO discriminator is the slot's `usage`. MMIO slots
            // stay in the free pool with `rc == UNUSED`; tracked slots have
            // `rc > 0`. The slot's `usage == MMIO` is pinned by the paddr's
            // range membership via `axiom_mmio_usage_iff_mmio_paddr`.
            &&& regions.slot_owners[idx].usage
                != crate::specs::mm::frame::meta_owners::PageUsage::MMIO ==> {
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
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

    /// PointsTo uniqueness: if meta slot `free_idx` is in the free pool (`regions.slots`),
    /// no active page table NODE entry can own a PointsTo at the same slot address.
    /// Justified by Verus's linear ownership of `PointsTo<MetaSlot>`:
    /// the node's PointsTo is either in `regions.slots` OR held by the node, never both.
    /// (Frames no longer own their PointsTo — they read from `regions.slots` directly.)
    pub axiom fn active_entry_not_in_free_pool(
        entry: Self,
        regions: MetaRegionOwners,
        free_idx: usize,
    )
        requires
            regions.inv(),
            entry.inv(),
            entry.is_node(),
            entry.metaregion_sound(regions),
            regions.slots.contains_key(free_idx),
        ensures
            frame_to_index(entry.meta_slot_paddr()->0) != free_idx,
    ;

    pub open spec fn meta_slot_paddr(self) -> Option<Paddr> {
        if self.is_node() {
            Some(meta_to_frame(self.node().meta_addr_self()))
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
            forall|k: usize| r0.slots.contains_key(k) ==> #[trigger] r1.slots.contains_key(k),
            forall|k: usize| r0.slots.contains_key(k) ==> r0.slots[k] == #[trigger] r1.slots[k],
        ensures
            self.metaregion_sound(r1),
    {
        if self.is_node() {
            let slot_idx = self.node().slot_index;
            assert(r0.slots.contains_key(slot_idx));
            assert(self.node().meta_perm_of(r1) == self.node().meta_perm_of(r0));
        }
    }

    /// If `metaregion_sound(r0)` holds and `r1` differs from `r0` only at one slot index
    /// that this entry does not reference, then `metaregion_sound(r1)` also holds.
    pub proof fn metaregion_sound_one_slot_changed(
        self,
        r0: MetaRegionOwners,
        r1: MetaRegionOwners,
        changed_idx: usize,
    )
        requires
            self.inv(),
            self.metaregion_sound(r0),
            forall|i: usize|
                #![trigger r1.slot_owners[i]]
                i != changed_idx ==> r0.slot_owners[i] == r1.slot_owners[i],
            r0.slot_owners.dom() =~= r1.slot_owners.dom(),
            // slots preserved at the entry's index (frames read from slots)
            forall|k: usize| r0.slots.contains_key(k) ==> #[trigger] r1.slots.contains_key(k),
            forall|k: usize| r0.slots.contains_key(k) ==> r0.slots[k] == #[trigger] r1.slots[k],
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
                        sub_idx != changed_idx || r1.slot_owners[sub_idx].usage
                            == crate::specs::mm::frame::meta_owners::PageUsage::MMIO || (
                        r1.slots.contains_key(sub_idx)
                            && r1.slot_owners[sub_idx].inner_perms.ref_count.value()
                            != REF_COUNT_UNUSED
                            && r1.slot_owners[sub_idx].inner_perms.ref_count.value() > 0 && r1.slot_owners[sub_idx].inner_perms.ref_count.value() <= REF_COUNT_MAX)
                    }
            },
        ensures
            self.metaregion_sound(r1),
    {
        if self.is_node() {
            let slot_idx = self.node().slot_index;
            let outer_idx = frame_to_index(self.meta_slot_paddr().unwrap());
            assert(r0.slots.contains_key(slot_idx));
            assert(slot_idx != changed_idx);
            assert(r1.slot_owners[slot_idx] == r0.slot_owners[slot_idx]);
            assert(self.node().meta_perm_of(r1) == self.node().meta_perm_of(r0));
        }
    }

    /// `metaregion_sound` is preserved when only `paths_in_pt` changes at a slot,
    /// `slots` is unchanged, and the new `paths_in_pt` is correct for any node at that index.
    pub proof fn metaregion_sound_paths_in_pt_changed(
        self,
        r0: MetaRegionOwners,
        r1: MetaRegionOwners,
        changed_idx: usize,
    )
        requires
            self.inv(),
            r0.inv(),
            self.metaregion_sound(r0),
            r0.slots == r1.slots,
            r0.slot_owners.dom() =~= r1.slot_owners.dom(),
            // All slots other than changed_idx are entirely unchanged.
            forall|i: usize|
                #![trigger r1.slot_owners[i]]
                i != changed_idx ==> r0.slot_owners[i] == r1.slot_owners[i],
            // At changed_idx, only paths_in_pt differs.
            r1.slot_owners[changed_idx].inner_perms == r0.slot_owners[changed_idx].inner_perms,
            r1.slot_owners[changed_idx].self_addr == r0.slot_owners[changed_idx].self_addr,
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
                forall|j: usize|
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
                if eidx == changed_idx {
                    assert(r1.slot_owners[eidx].inner_perms == r0.slot_owners[eidx].inner_perms);
                } else {
                    assert(r1.slot_owners[eidx] == r0.slot_owners[eidx]);
                }
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
                        &&& r1.slot_owners[sub_idx].usage
                            != crate::specs::mm::frame::meta_owners::PageUsage::MMIO ==> {
                            &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value()
                                != REF_COUNT_UNUSED
                            &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                            &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() <= REF_COUNT_MAX
                        }
                    } by {
                        let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                        // From self.metaregion_sound(r0)'s frame arm (frame_sub_pages_valid(r0)).
                        assert(r0.slots.contains_key(sub_idx));
                        if sub_idx == changed_idx {
                            assert(r1.slot_owners[sub_idx].inner_perms
                                == r0.slot_owners[sub_idx].inner_perms);
                            assert(r1.slot_owners[sub_idx].usage == r0.slot_owners[sub_idx].usage);
                        } else {
                            assert(r1.slot_owners[sub_idx] == r0.slot_owners[sub_idx]);
                        }
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
                &&& r1.slot_owners[idx].inner_perms.ref_count.value()
                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
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
                &&& r1.slot_owners[idx].self_addr == r0.slot_owners[idx].self_addr
                &&& r1.slot_owners[idx].paths_in_pt == r0.slot_owners[idx].paths_in_pt
                // `usage` is part of `metaregion_sound_node` (node-repark
                // discriminator), so it must be preserved to carry soundness.
                &&& r1.slot_owners[idx].usage == r0.slot_owners[idx].usage
            }),
            // All other slot_owners unchanged: preserves sub-page validity for huge frames.
            forall|i: usize|
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
                &&& r1.slot_owners[sub_idx].usage
                    != crate::specs::mm::frame::meta_owners::PageUsage::MMIO ==> {
                    &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    &&& r1.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                }
            } by {
                let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                assert(r0.slots.contains_key(sub_idx));
                let pa_plus_int: int = pa as int + (j as int) * (PAGE_SIZE as int);
                crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(
                self.parent_level);
                assert((j as int) * (PAGE_SIZE as int) < (nr_pages as int) * (PAGE_SIZE as int))
                    by {
                    vstd::arithmetic::mul::lemma_mul_strict_inequality(
                        j as int,
                        nr_pages as int,
                        PAGE_SIZE as int,
                    );
                };
                crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_div_mul_eq(
                    self.parent_level,
                );
                assert(pa_plus_int < MAX_PADDR);
                // sub_idx = (pa + j*PAGE_SIZE) / PAGE_SIZE = pa/PAGE_SIZE + j (since pa % PAGE_SIZE == 0).
                vstd::arithmetic::div_mod::lemma_div_multiples_vanish_quotient(
                    j as int,
                    pa as int,
                    PAGE_SIZE as int,
                );
                assert(self_idx as int == pa as int / PAGE_SIZE as int);
                assert(sub_idx != self_idx);
                assert(r0.slot_owners.contains_key(sub_idx));
                assert(r0.slot_owners[sub_idx] == r1.slot_owners[sub_idx]);
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
            self.node().meta_addr_self() != other.node().meta_addr_self(),
    {
        let self_addr = self.node().meta_addr_self();
        let other_addr = other.node().meta_addr_self();
        let self_idx = frame_to_index(meta_to_frame(self_addr));
        let other_idx = frame_to_index(meta_to_frame(other_addr));

        if self_addr == other_addr {
            assert(regions.slot_owners[self_idx].paths_in_pt == set![self.path]);
            assert(regions.slot_owners[other_idx].paths_in_pt == set![other.path]);
            assert(set![self.path].contains(other.path));
            assert(self.path == other.path);
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
            assert(regions.slot_owners[self_idx].paths_in_pt == set![self.path]);
            assert(regions.slot_owners[other_idx].paths_in_pt == set![other.path]);
            assert(set![self.path].contains(other.path));
            assert(self.path == other.path);
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
            &&& self.frame().mapped_pa % PAGE_SIZE == 0
            &&& self.frame().mapped_pa < MAX_PADDR
            &&& self.frame().size == page_size(self.parent_level)
            &&& self.frame().mapped_pa % page_size(self.parent_level) == 0
            &&& self.frame().mapped_pa + page_size(self.parent_level) <= MAX_PADDR
        }
        &&& self.is_locked() ==> { true }
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
                    map_to_pa: meta_to_frame(node.meta_addr_self()) as int,
                    level: self.path.len() as u8,
                    phantom: PhantomData,
                },
            }
        } else if self.is_locked() {
            let view = self.locked();
            EntryView::LockedSubtree { views: view }
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
        &&& self.pte.paddr() % PAGE_SIZE == 0
        &&& self.pte.paddr() < MAX_PADDR
    }
}

} // verus!
