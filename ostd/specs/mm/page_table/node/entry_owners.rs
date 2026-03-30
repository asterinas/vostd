use vstd::prelude::*;

use vstd::cell;
use vstd::simple_pptr::PointsTo;
use vstd_extra::array_ptr;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::mapping::{frame_to_index, meta_addr, meta_to_frame};
use crate::mm::frame::meta::MetaSlot;
use crate::mm::frame::meta::REF_COUNT_UNUSED;
use crate::mm::page_prop::PageProperty;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::arch::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::node::entry_view::*;
use crate::specs::mm::page_table::*;
use core::marker::PhantomData;

verus! {

pub tracked struct FrameEntryOwner {
    pub mapped_pa: usize,
    pub size: usize,
    pub prop: PageProperty,
    pub slot_perm: PointsTo<MetaSlot>,
}

pub tracked struct EntryOwner<C: PageTableConfig> {
    pub node: Option<NodeOwner<C>>,
    pub frame: Option<FrameEntryOwner>,
    pub locked: Option<Ghost<Seq<FrameView<C>>>>,
    pub absent: bool,
    pub in_scope: bool,
    pub path: TreePath<NR_ENTRIES>,
    pub parent_level: PagingLevel,
}

impl<C: PageTableConfig> EntryOwner<C> {
    pub open spec fn is_node(self) -> bool {
        self.node is Some
    }

    pub open spec fn is_frame(self) -> bool {
        self.frame is Some
    }

    pub open spec fn is_locked(self) -> bool {
        self.locked is Some
    }

    pub open spec fn is_absent(self) -> bool {
        self.absent
    }

    pub open spec fn new_absent_spec(path: TreePath<NR_ENTRIES>, parent_level: PagingLevel) -> Self {
        EntryOwner {
            node: None,
            frame: None,
            locked: None,
            absent: true,
            in_scope: true,
            path,
            parent_level,
        }
    }

    pub open spec fn new_frame_spec(paddr: Paddr, path: TreePath<NR_ENTRIES>, parent_level: PagingLevel, prop: PageProperty, slot_perm: PointsTo<MetaSlot>) -> Self {
        EntryOwner {
            node: None,
            frame: Some(FrameEntryOwner { mapped_pa: paddr, size: page_size(parent_level), prop, slot_perm }),
            locked: None,
            absent: false,
            in_scope: true,
            path,
            parent_level,
        }
    }

    pub open spec fn new_node_spec(node: NodeOwner<C>, path: TreePath<NR_ENTRIES>) -> Self {
        EntryOwner {
            node: Some(node),
            frame: None,
            locked: None,
            absent: false,
            in_scope: true,
            path,
            parent_level: (node.level + 1) as PagingLevel,
        }
    }

    pub axiom fn new_absent(path: TreePath<NR_ENTRIES>, parent_level: PagingLevel) -> tracked Self
        returns Self::new_absent_spec(path, parent_level);

    pub axiom fn new_frame(paddr: Paddr, path: TreePath<NR_ENTRIES>, parent_level: PagingLevel, prop: PageProperty, tracked slot_perm: PointsTo<MetaSlot>) -> tracked Self
        returns Self::new_frame_spec(paddr, path, parent_level, prop, slot_perm);

    /// Produces a slot permission for a frame address without requiring it from `regions.slots`.
    /// Used as a placeholder in cases (e.g. huge-page split) where the sub-frame slot perms
    /// are not yet fully tracked.  Replace with real perm threading when the split path is verified.
    pub axiom fn placeholder_slot_perm(paddr: Paddr, tracked regions: &MetaRegionOwners) -> (tracked res: PointsTo<MetaSlot>)
        requires
            regions.inv(),
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
        ensures
            res.addr() == meta_addr(frame_to_index(paddr)),
            res.is_init(),
            res.value().wf(regions.slot_owners[frame_to_index(paddr)]),
            regions.slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value() != REF_COUNT_UNUSED,
            regions.slot_owners[frame_to_index(paddr)].path_if_in_pt is None;

    pub axiom fn new_node(node: NodeOwner<C>, path: TreePath<NR_ENTRIES>) -> tracked Self
        returns Self::new_node_spec(node, path);

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
            res.frame.unwrap().mapped_pa == paddr,
            res.frame.unwrap().prop == prop,
            res.frame.unwrap().size == page_size(parent_level),
            res.parent_level == parent_level,
            res.path.inv(),
            res.in_scope,
            res.inv(),
            crate::mm::page_table::Child::<C>::Frame(paddr, parent_level, prop).wf(res);

    pub open spec fn match_pte(self, pte: C::E, parent_level: PagingLevel) -> bool {
        &&& pte.paddr() % PAGE_SIZE == 0
        &&& pte.paddr() < MAX_PADDR
        &&& !pte.is_present() ==> {
            &&& self.is_absent()
            &&& parent_level > 1 ==> !pte.is_last(parent_level)
        }
        &&& pte.is_present() && !pte.is_last(parent_level) ==> {
            &&& self.is_node()
            &&& meta_to_frame(self.node.unwrap().meta_perm.addr()) == pte.paddr()
        }
        &&& pte.is_present() && pte.is_last(parent_level) ==> {
            &&& self.is_frame()
            &&& self.frame.unwrap().mapped_pa == pte.paddr()
            &&& self.frame.unwrap().prop == pte.prop()
        }
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
        C::E::new_properties();
        assert(!pte.is_present());
        if parent_level > 1 {
            assert(!pte.is_last(parent_level));
        }
        if pte.is_present() && !pte.is_last(parent_level) {
            assert(pte.is_present());
            assert(!pte.is_present());
        }
        if pte.is_present() && pte.is_last(parent_level) {
            assert(pte.is_present());
            assert(!pte.is_present());
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
            self.frame.unwrap().mapped_pa == pte.paddr(),
            self.frame.unwrap().prop == pte.prop(),
    {
        if !pte.is_present() {
            assert(self.is_absent());
            assert(!pte.is_last(parent_level));
            assert(false);
        }
        assert(self.is_frame());
        assert(self.frame.unwrap().mapped_pa == pte.paddr());
        assert(self.frame.unwrap().prop == pte.prop());
    }

    pub proof fn huge_frame_split_child_at(self, regions: MetaRegionOwners, idx: usize)
        requires
            self.inv(),
            self.is_frame(),
            regions.inv(),
            1 < self.parent_level < NR_LEVELS,
            idx < NR_ENTRIES,
        ensures
            self.frame.unwrap().mapped_pa + idx * page_size((self.parent_level - 1) as PagingLevel) < MAX_PADDR,
            ((self.frame.unwrap().mapped_pa + idx * page_size((self.parent_level - 1) as PagingLevel)) as Paddr)
                % page_size((self.parent_level - 1) as PagingLevel) == 0,
            ((self.frame.unwrap().mapped_pa + idx * page_size((self.parent_level - 1) as PagingLevel)) as Paddr)
                + page_size((self.parent_level - 1) as PagingLevel) <= MAX_PADDR,
            ((self.frame.unwrap().mapped_pa + idx * page_size((self.parent_level - 1) as PagingLevel)) as Paddr) % PAGE_SIZE == 0,
    {
        let pa = self.frame.unwrap().mapped_pa;
        let child_pa = (pa + idx * page_size((self.parent_level - 1) as PagingLevel)) as Paddr;
        assert(self.parent_level == 2 || self.parent_level == 3);
        assert(NR_ENTRIES == 512) by {
            crate::specs::arch::paging_consts::lemma_nr_subpage_per_huge_eq_nr_entries();
        };
        assert(crate::mm::nr_subpage_per_huge::<PagingConsts>() == 512usize) by {
            crate::specs::arch::paging_consts::lemma_nr_subpage_per_huge_eq_nr_entries();
        };
        vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_spec_level1();
        assert(512usize.ilog2() == 9);
        assert(crate::mm::nr_subpage_per_huge::<PagingConsts>().ilog2() == 512usize.ilog2());
        vstd::arithmetic::power2::lemma2_to64();
        if self.parent_level == 2 {
            assert(page_size_spec(1) == 4096);
            assert(page_size_spec(2) == (PAGE_SIZE * pow2((512usize.ilog2() * 1usize) as nat)) as usize);
            assert(page_size_spec(2) == (4096 * pow2(9)) as usize);
            assert(page_size_spec(2) == 2097152);
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
            assert(page_size_spec(2) == (PAGE_SIZE * pow2((512usize.ilog2() * 1usize) as nat)) as usize);
            assert(page_size_spec(2) == (4096 * pow2(9)) as usize);
            assert(page_size_spec(2) == 2097152);
            assert(page_size_spec(3) == (PAGE_SIZE * pow2((512usize.ilog2() * 2usize) as nat)) as usize);
            assert(page_size_spec(3) == (4096 * pow2(18)) as usize);
            assert(page_size_spec(3) == 1073741824);
            assert(pa % page_size(3) == 0);
            assert(pa % PAGE_SIZE == 0);
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
                assert(idx < 512);
                assert(idx * 2097152 + 2097152 <= 1073741824);
                assert(child_pa + page_size(2) <= pa + page_size(3));
            };
        }
        assert(child_pa < MAX_PADDR);
        assert(child_pa % PAGE_SIZE == 0);
    }

    pub open spec fn expected_raw_count(self) -> usize {
        if self.in_scope {
            0
        } else {
            1
        }
    }

    pub open spec fn relate_region(self, regions: MetaRegionOwners) -> bool {
        if self.is_node() {
            let idx = frame_to_index(self.meta_slot_paddr().unwrap());
            &&& regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            &&& regions.slot_owners[idx].raw_count == self.expected_raw_count()
            &&& regions.slot_owners[idx].self_addr == self.node.unwrap().meta_perm.addr()
            &&& self.node.unwrap().meta_perm.points_to.value().wf(regions.slot_owners[idx])
            &&& regions.slot_owners[idx].path_if_in_pt is Some ==>
                regions.slot_owners[idx].path_if_in_pt.unwrap() == self.path
        } else if self.is_frame() {
            let idx = frame_to_index(self.meta_slot_paddr().unwrap());
            &&& self.frame.unwrap().slot_perm.addr() == meta_addr(idx)
            &&& self.frame.unwrap().slot_perm.is_init()
            &&& self.frame.unwrap().slot_perm.value().wf(regions.slot_owners[idx])
            &&& regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            &&& regions.slot_owners[idx].path_if_in_pt is Some ==>
                regions.slot_owners[idx].path_if_in_pt.unwrap() == self.path
        } else {
            true
        }
    }

    /// PointsTo uniqueness: if meta slot `free_idx` is in the free pool (`regions.slots`),
    /// no active page table entry can own a PointsTo at the same slot address.
    /// Justified by Verus's linear ownership of `PointsTo<MetaSlot>`:
    /// the slot's PointsTo is either in `regions.slots` OR held by an active entry, never both.
    pub axiom fn active_entry_not_in_free_pool(
        entry: Self,
        regions: MetaRegionOwners,
        free_idx: usize,
    )
        requires
            regions.inv(),
            entry.inv(),
            entry.relate_region(regions),
            regions.slots.contains_key(free_idx),
            entry.meta_slot_paddr() is Some,
        ensures
            frame_to_index(entry.meta_slot_paddr().unwrap()) != free_idx;

    pub axiom fn get_path(self) -> tracked TreePath<NR_ENTRIES>
        returns self.path;

    pub open spec fn meta_slot_paddr(self) -> Option<Paddr> {
        if self.is_node() {
            Some(meta_to_frame(self.node.unwrap().meta_perm.addr()))
        } else if self.is_frame() {
            Some(self.frame.unwrap().mapped_pa)
        } else {
            None
        }
    }

    pub open spec fn meta_slot_paddr_neq(self, other: Self) -> bool {
        self.meta_slot_paddr() is Some ==>
        other.meta_slot_paddr() is Some ==>
        self.meta_slot_paddr().unwrap() != other.meta_slot_paddr().unwrap()
    }

    /// `relate_region` only uses `regions.slot_owners`, not `regions.slots`.
    /// So if two `MetaRegionOwners` have the same `slot_owners`, `relate_region` transfers.
    pub proof fn relate_region_slot_owners_only(self, r0: MetaRegionOwners, r1: MetaRegionOwners)
        requires
            self.relate_region(r0),
            r0.slot_owners == r1.slot_owners,
        ensures
            self.relate_region(r1),
    {
        // relate_region is an open spec fn referencing only r.slot_owners[idx],
        // so equality of slot_owners makes the two predicates equivalent.
    }

    /// If `relate_region(r0)` holds and `r1` differs from `r0` only at one slot index
    /// that this entry does not reference, then `relate_region(r1)` also holds.
    pub proof fn relate_region_one_slot_changed(self, r0: MetaRegionOwners, r1: MetaRegionOwners, changed_idx: usize)
        requires
            self.relate_region(r0),
            forall |i: usize| #![trigger r1.slot_owners[i]]
                i != changed_idx ==> r0.slot_owners[i] == r1.slot_owners[i],
            r0.slot_owners.dom() =~= r1.slot_owners.dom(),
            self.meta_slot_paddr() is Some ==>
                frame_to_index(self.meta_slot_paddr().unwrap()) != changed_idx,
        ensures
            self.relate_region(r1),
    {
        // relate_region only reads slot_owners[frame_to_index(self.meta_slot_paddr().unwrap())]
        // which is unchanged since frame_to_index != changed_idx.
    }

    /// Under `relate_region` + `path_if_in_pt is Some`, two entries with the same physical
    /// address must have the same path. Equivalently, different paths ↔ different paddrs.
    /// This is the fundamental paddr-uniqueness invariant: `path_if_in_pt` encodes the
    /// unique path for each physical address in the page table.
    pub proof fn same_paddr_implies_same_path(self, other: Self, regions: MetaRegionOwners)
        requires
            self.meta_slot_paddr() is Some,
            self.meta_slot_paddr() == other.meta_slot_paddr(),
            self.relate_region(regions),
            other.relate_region(regions),
            regions.slot_owners[
                frame_to_index(self.meta_slot_paddr().unwrap())
            ].path_if_in_pt is Some,
        ensures
            self.path == other.path,
    {
        let pa = self.meta_slot_paddr().unwrap();
        let idx = frame_to_index(pa);
        // relate_region for both self and other: path_if_in_pt is Some => path_if_in_pt == self.path
        // The precondition gives path_if_in_pt is Some, so the conditional fires.
        assert(regions.slot_owners[idx].path_if_in_pt.unwrap() == self.path);
        assert(regions.slot_owners[idx].path_if_in_pt.unwrap() == other.path);
    }

    /// `relate_region` is preserved when only `ref_count.value()` changes at this entry's slot.
    pub proof fn relate_region_rc_value_changed(self, r0: MetaRegionOwners, r1: MetaRegionOwners)
        requires
            self.relate_region(r0),
            self.meta_slot_paddr() is Some,
            ({
                let idx = frame_to_index(self.meta_slot_paddr().unwrap());
                &&& r1.slot_owners[idx].inner_perms.ref_count.id()
                    == r0.slot_owners[idx].inner_perms.ref_count.id()
                &&& r1.slot_owners[idx].inner_perms.ref_count.value()
                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                &&& r1.slot_owners[idx].inner_perms.storage
                    == r0.slot_owners[idx].inner_perms.storage
                &&& r1.slot_owners[idx].inner_perms.vtable_ptr
                    == r0.slot_owners[idx].inner_perms.vtable_ptr
                &&& r1.slot_owners[idx].inner_perms.in_list
                    == r0.slot_owners[idx].inner_perms.in_list
                &&& r1.slot_owners[idx].path_if_in_pt == r0.slot_owners[idx].path_if_in_pt
                &&& r1.slot_owners[idx].self_addr == r0.slot_owners[idx].self_addr
                &&& r1.slot_owners[idx].raw_count == r0.slot_owners[idx].raw_count
            }),
        ensures
            self.relate_region(r1),
    {
    }

    /// Two nodes satisfying relate_region with the same regions have different addresses
    /// if and only if they have different paths.
    pub proof fn nodes_different_paths_different_addrs(
        self,
        other: Self,
        regions: MetaRegionOwners,
    )
        requires
            self.is_node(),
            other.is_node(),
            self.relate_region(regions),
            self.meta_slot_paddr() is Some ==> regions.slot_owners[frame_to_index(self.meta_slot_paddr().unwrap())].path_if_in_pt is Some,
            other.meta_slot_paddr() is Some ==> regions.slot_owners[frame_to_index(other.meta_slot_paddr().unwrap())].path_if_in_pt is Some,
            other.relate_region(regions),
            self.path != other.path,
        ensures
            self.node.unwrap().meta_perm.addr() != other.node.unwrap().meta_perm.addr(),
    {
        let self_addr = self.node.unwrap().meta_perm.addr();
        let other_addr = other.node.unwrap().meta_perm.addr();
        let self_idx = frame_to_index(meta_to_frame(self_addr));
        let other_idx = frame_to_index(meta_to_frame(other_addr));

        if self_addr == other_addr {
            assert(regions.slot_owners[self_idx].path_if_in_pt == Some(self.path));
            assert(regions.slot_owners[other_idx].path_if_in_pt == Some(other.path));
//            assert(Some(self.path) == Some(other.path));
            assert(self.path == other.path);
            assert(false); // Contradiction
        }
    }
}

impl<C: PageTableConfig> EntryOwner<C> {
    /// Structural invariant without `!in_scope`. Used by `Child::invariants`
    /// for entries that have been taken out of the tree (`in_scope == true`).
    pub open spec fn inv_base(self) -> bool {
        &&& self.node is Some ==> {
            &&& self.frame is None
            &&& self.locked is None
            &&& self.node.unwrap().inv()
            &&& !self.absent
        }
        &&& self.frame is Some ==> {
            &&& self.node is None
            &&& self.locked is None
            &&& !self.absent
            &&& self.frame.unwrap().mapped_pa % PAGE_SIZE == 0
            &&& self.frame.unwrap().mapped_pa < MAX_PADDR
            &&& self.frame.unwrap().size == page_size(self.parent_level)
            &&& self.frame.unwrap().mapped_pa % page_size(self.parent_level) == 0
            &&& self.frame.unwrap().mapped_pa + page_size(self.parent_level) <= MAX_PADDR
        }
        &&& self.locked is Some ==> {
            &&& self.frame is None
            &&& self.node is None
            &&& !self.absent
        }
        &&& self.path.inv()
    }
}

impl<C: PageTableConfig> Inv for EntryOwner<C> {
    open spec fn inv(self) -> bool {
        &&& !self.in_scope
        &&& self.inv_base()
    }
}

impl<C: PageTableConfig> View for EntryOwner<C> {
    type V = EntryView<C>;

    #[verifier::external_body]
    open spec fn view(&self) -> <Self as View>::V {
        if let Some(frame) = self.frame {
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
        } else if let Some(node) = self.node {
            EntryView::Intermediate {
                node: IntermediatePageTableEntryView {
                    map_va: vaddr(self.path) as int,
                    //                    frame_pa: self.base_addr as int,
                    //                    in_frame_index: self.index as int,
                    map_to_pa: meta_to_frame(node.meta_perm.addr()) as int,
                    level: self.path.len() as u8,
                    phantom: PhantomData,
                },
            }
        } else if let Some(view) = self.locked {
            EntryView::LockedSubtree { views: view@ }
        } else {
            EntryView::Absent
        }
    }
}

impl<C: PageTableConfig> InvView for EntryOwner<C> {
    proof fn view_preserves_inv(self) {
        admit()
    }
}

impl<'rcu, C: PageTableConfig> OwnerOf for Entry<'rcu, C> {
    type Owner = EntryOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.idx < NR_ENTRIES
        &&& owner.match_pte(self.pte, owner.parent_level)
        &&& self.pte.paddr() % PAGE_SIZE == 0
        &&& self.pte.paddr() < MAX_PADDR
    }
}

} // verus!
