use vstd::prelude::*;

use vstd::simple_pptr::PointsTo;
use vstd::cell;
use vstd_extra::array_ptr;
use vstd_extra::ghost_tree::*;

use super::*;

verus! {

pub tracked struct NodeEntryOwner<'rcu, C: PageTableConfig> {
    pub as_node: NodeOwner<C>,
    pub guard_perm: PointsTo<PageTableGuard<'rcu, C>>,
    pub children_perm: array_ptr::PointsTo<Entry<'rcu, C>, CONST_NR_ENTRIES>,
    pub nr_children_perm: vstd::cell::PointsTo<u16>,
}

impl<'rcu, C: PageTableConfig> Inv for NodeEntryOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& self.guard_perm.is_init()
        &&& self.guard_perm.value().inner.inner.0.ptr.addr() == self.as_node.meta_perm.addr()
        &&& self.guard_perm.value().inner.inner.0.wf(self.as_node)
        &&& self.as_node.inv()
        &&& self.as_node.meta_perm.value().nr_children.id() == self.nr_children_perm.id()
        &&& self.nr_children_perm.is_init()
        &&& 0 <= self.nr_children_perm.value() <= NR_ENTRIES()
        &&& meta_to_frame(self.as_node.meta_perm.addr()) < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR()
        &&& meta_to_frame(self.as_node.meta_perm.addr()) == self.children_perm.addr()
        &&& forall|i: int|
            0 <= i < NR_ENTRIES() ==> self.children_perm.is_init(i as int) ==> {
                &&& #[trigger] self.children_perm.opt_value()[i as int].value().node == self.guard_perm.pptr()
            }
    }
}

/*impl<'rcu, C: PageTableConfig> NodeEntryOwner<'rcu, C> {
    pub open spec fn relate_slot_owner(self, slot_own: &MetaSlotOwner) -> bool {
        &&& slot_own.inv()
        &&& self.as_node.meta_perm@.ptr.value().wf(*slot_own)
        &&& self.as_node.meta_perm@.addr() == slot_own.self_addr
    }
}*/

pub tracked struct FrameEntryOwner {
    pub mapped_pa: usize,
    pub prop: PageProperty,
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct EntryOwner<'rcu, C: PageTableConfig> {
    pub node: Option<NodeEntryOwner<'rcu, C>>,
    pub frame: Option<FrameEntryOwner>,
    pub locked: Option<Ghost<Seq<FrameView<C>>>>,
    pub absent: bool,
//    pub base_addr: usize,
    pub guard_addr: usize,
//    pub index: usize,
    pub path: TreePath<CONST_NR_ENTRIES>,
}

impl<'rcu, C: PageTableConfig> EntryOwner<'rcu, C> {
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

    // An `Entry` carries a pointer to the guard for its parent node,
    // which from the perspective of a single `EntryOwner` must be provided
    // separately. Its inner pointer corresponds to the base address of the entry.
    pub open spec fn relate_parent_guard_perm(self, guard_perm: PointsTo<PageTableGuard<'rcu, C>>) -> bool {
        &&& guard_perm.addr() == self.guard_addr
        &&& guard_perm.is_init()
//        &&& guard_perm.value().inner.inner.0.ptr.addr() == self.base_addr
    }
}

impl<'rcu, C: PageTableConfig> Inv for EntryOwner<'rcu, C> {
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
        }
        &&& self.locked is Some ==> {
            &&& self.frame is None
            &&& self.node is None
            &&& !self.absent
        }
    }
}

impl<'rcu, C: PageTableConfig> View for EntryOwner<'rcu, C> {
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
                    phantom: PhantomData
                }
            }
        }
        else if let Some(node) = self.node {
            EntryView::Intermediate {
                node: IntermediatePageTableEntryView{
                    map_va: vaddr(self.path) as int,
//                    frame_pa: self.base_addr as int,
//                    in_frame_index: self.index as int,
                    map_to_pa: meta_to_frame(node.as_node.meta_perm.addr()) as int,
                    level: (self.path.len() + 1) as u8,
                    phantom: PhantomData
                }
            }
        } else if let Some(view) = self.locked {
            EntryView::LockedSubtree {
                views: view@
            }
        } else {
            EntryView::Absent
        }
    }
}

impl<'rcu, C: PageTableConfig> InvView for EntryOwner<'rcu, C> {
    proof fn view_preserves_inv(self) {
        admit()
    }
}

impl<'rcu, C: PageTableConfig> OwnerOf for Entry<'rcu, C> {
    type Owner = EntryOwner<'rcu, C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.node.addr() == owner.guard_addr
        &&& self.idx < NR_ENTRIES()
        &&& self.pte.paddr() % PAGE_SIZE() == 0
        &&& self.pte.paddr() < MAX_PADDR()
    }
}

} // verus!
