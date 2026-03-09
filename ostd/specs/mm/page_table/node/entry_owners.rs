use vstd::prelude::*;

use vstd::cell;
use vstd::simple_pptr::PointsTo;
use vstd_extra::array_ptr;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::mapping::{frame_to_index, meta_to_frame};
use crate::mm::page_prop::PageProperty;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::mm::frame::meta::REF_COUNT_UNUSED;
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

    pub open spec fn new_frame_spec(paddr: Paddr, path: TreePath<NR_ENTRIES>, parent_level: PagingLevel, prop: PageProperty) -> Self {
        EntryOwner {
            node: None,
            frame: Some(FrameEntryOwner { mapped_pa: paddr, size: page_size(parent_level), prop }),
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

    pub axiom fn new_frame(paddr: Paddr, path: TreePath<NR_ENTRIES>, parent_level: PagingLevel, prop: PageProperty) -> tracked Self
        returns Self::new_frame_spec(paddr, path, parent_level, prop);

    pub axiom fn new_node(node: NodeOwner<C>, path: TreePath<NR_ENTRIES>) -> tracked Self
        returns Self::new_node_spec(node, path);

    pub open spec fn match_pte(self, pte: C::E, parent_level: PagingLevel) -> bool {
        &&& pte.paddr() % PAGE_SIZE == 0
        &&& pte.paddr() < MAX_PADDR
        &&& !pte.is_present() ==> {
            self.is_absent()
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
        if pte.is_present() && !pte.is_last(parent_level) {
            assert(pte.is_present());
            assert(!pte.is_present());
        }
        if pte.is_present() && pte.is_last(parent_level) {
            assert(pte.is_present());
            assert(!pte.is_present());
        }
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
            regions.slot_owners[frame_to_index(self.meta_slot_paddr().unwrap())].path_if_in_pt is Some ==>
            regions.slot_owners[frame_to_index(self.meta_slot_paddr().unwrap())].path_if_in_pt.unwrap() == self.path
        } else {
            true
        }
    }

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

impl<C: PageTableConfig> Inv for EntryOwner<C> {
    open spec fn inv(self) -> bool {
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
        }
        &&& self.locked is Some ==> {
            &&& self.frame is None
            &&& self.node is None
            &&& !self.absent
        }
        &&& self.path.inv()
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
