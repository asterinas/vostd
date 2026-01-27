use vstd::prelude::*;

use vstd::cell;
use vstd::simple_pptr::PointsTo;
use vstd_extra::array_ptr;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::mapping::meta_to_frame;
use crate::mm::page_prop::PageProperty;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::arch::*;
use crate::specs::mm::page_table::owners::*;
use core::marker::PhantomData;

verus! {

pub tracked struct FrameEntryOwner {
    pub mapped_pa: usize,
    pub size: usize,
    pub prop: PageProperty,
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct EntryOwner<C: PageTableConfig> {
    pub node: Option<NodeOwner<C>>,
    pub frame: Option<FrameEntryOwner>,
    pub locked: Option<Ghost<Seq<FrameView<C>>>>,
    pub absent: bool,
    pub path: TreePath<CONST_NR_ENTRIES>,
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

    pub open spec fn new_absent_spec() -> Self {
        EntryOwner {
            node: None,
            frame: None,
            locked: None,
            absent: true,
            path: TreePath::new(Seq::empty()),
        }
    }

    pub open spec fn new_frame_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        EntryOwner {
            node: None,
            frame: Some(FrameEntryOwner { mapped_pa: paddr, size: page_size(level), prop }),
            locked: None,
            absent: false,
            path: TreePath::new(Seq::empty()),
        }
    }

    pub open spec fn new_node_spec(node: NodeOwner<C>) -> Self {
        EntryOwner {
            node: Some(node),
            frame: None,
            locked: None,
            absent: false,
            path: TreePath::new(Seq::empty()),
        }
    }

    pub axiom fn new_absent() -> tracked Self
        returns Self::new_absent_spec();

    pub axiom fn new_frame(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> tracked Self
        returns Self::new_frame_spec(paddr, level, prop);

    pub axiom fn new_node(node: NodeOwner<C>) -> tracked Self
        returns Self::new_node_spec(node);

    pub open spec fn match_pte(self, pte: C::E, level: PagingLevel) -> bool {
        &&& pte.paddr() % PAGE_SIZE() == 0
        &&& pte.paddr() < MAX_PADDR()
        &&& !pte.is_present() ==> {
            self.is_absent()
        }
        &&& pte.is_present() && !pte.is_last(level) ==> {
            &&& self.is_node()
            &&& meta_to_frame(self.node.unwrap().meta_perm.addr()) == pte.paddr()
        }
        &&& pte.is_present() && pte.is_last(level) ==> {
            &&& self.is_frame()
            &&& self.frame.unwrap().mapped_pa == pte.paddr()
            &&& self.frame.unwrap().prop == pte.prop()
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
            &&& self.frame.unwrap().mapped_pa % PAGE_SIZE() == 0
            &&& self.frame.unwrap().mapped_pa < MAX_PADDR()
        }
        &&& self.locked is Some ==> {
            &&& self.frame is None
            &&& self.node is None
            &&& !self.absent
        }
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
                    level: (self.path.len() + 1) as u8,
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
                    level: (self.path.len() + 1) as u8,
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
        &&& self.idx < NR_ENTRIES()
        &&& self.pte.paddr() % PAGE_SIZE() == 0
        &&& self.pte.paddr() < MAX_PADDR()
    }
}

} // verus!
