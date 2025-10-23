use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::*;

use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::ghost_tree;
use vstd_extra::ownership::*;
use vstd_extra::prelude::TreeNodeValue;

use crate::prelude::*;

use std::ops::Deref;

verus! {

pub tracked struct PageMetaOwner {
    pub nr_children: Tracked<vstd::cell::PointsTo<u16>>,
    pub stray: Tracked<vstd::cell::PointsTo<bool>>,
}

impl Inv for PageMetaOwner {
    open spec fn inv(self) -> bool {
        &&& self.nr_children@.is_init()
        &&& self.stray@.is_init()
    }
}

pub ghost struct PageMetaModel {
    pub nr_children: u16,
    pub stray: bool,
}

impl Inv for PageMetaModel {
    open spec fn inv(self) -> bool {
        true
    }
}

impl InvView for PageMetaOwner {
    type V = PageMetaModel;

    open spec fn view(self) -> <Self as InvView>::V {
        PageMetaModel { nr_children: self.nr_children@.value(), stray: self.stray@.value() }
    }

    proof fn view_preserves_inv(&self) {
    }
}

impl<C: PageTableConfig> OwnerOf for PageTablePageMeta<C> {
    type Owner = PageMetaOwner;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        &&& self.nr_children.id() == owner.nr_children@.id()
        &&& self.stray.id() == owner.stray@.id()
    }
}

pub tracked struct NodeOwner<C: PageTableConfig> {
    pub meta_own: PageMetaOwner,
    pub meta_perm: Tracked<vstd_extra::cast_ptr::PointsTo<MetaSlotStorage, PageTablePageMeta<C>>>,
}

impl<C: PageTableConfig> Inv for NodeOwner<C> {
    open spec fn inv(self) -> bool {
        &&& self.meta_perm@.points_to@.is_init()
        &&& <PageTablePageMeta<C> as Repr<MetaSlotStorage>>::wf(self.meta_perm@.points_to@.value())
        &&& self.meta_own.inv()
        &&& self.meta_perm@.value().wf(&self.meta_own)
        &&& self.meta_perm@.is_init()
        &&& self.meta_perm@.wf()
    }
}

impl<C: PageTableConfig> InvView for NodeOwner<C> {
    type V = NodeModel<C>;

    open spec fn view(self) -> <Self as InvView>::V {
        NodeModel { meta: self.meta_perm@.value() }
    }

    proof fn view_preserves_inv(&self) {
    }
}

pub ghost struct NodeModel<C: PageTableConfig> {
    pub meta: PageTablePageMeta<C>,
}

impl<C: PageTableConfig> Inv for NodeModel<C> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<C: PageTableConfig> OwnerOf for PageTableNode<C> {
    type Owner = NodeOwner<C>;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        true
    }
}

pub tracked struct EntryOwner<'rcu, C: PageTableConfig> {
    pub node_own: NodeOwner<C>,
    pub guard_perm: Tracked<PointsTo<PageTableGuard<'rcu, C>>>,
    pub children_perm: Option<array_ptr::PointsTo<Entry<'rcu, C>, CONST_NR_ENTRIES>>,
    pub slot_perm: Tracked<PointsTo<MetaSlot>>,
}

impl<'rcu, C: PageTableConfig> Inv for EntryOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& self.guard_perm@.is_init()
        &&& self.guard_perm@.value().inner.inner.ptr == self.slot_perm@.pptr()
        &&& self.guard_perm@.value().inner.inner.wf(&self.node_own)
        &&& self.node_own.inv()
        &&& self.slot_perm@.is_init()
        &&& self.slot_perm@.value().storage == self.node_own.meta_perm@.points_to@.pptr()
        &&& self.node_own.meta_perm@.pptr().ptr.0 == self.slot_perm@.value().storage.addr()
        &&& self.node_own.meta_perm@.pptr().addr == self.slot_perm@.value().storage.addr()
        &&& meta_to_frame(self.slot_perm@.addr()) < VMALLOC_BASE_VADDR()
            - LINEAR_MAPPING_BASE_VADDR()
    }
}

impl<'rcu, C: PageTableConfig> EntryOwner<'rcu, C> {
    pub open spec fn relate_slot_owner(self, slot_own: &MetaSlotOwner) -> bool {
        &&& slot_own.inv()
        &&& self.slot_perm@.value().wf(&slot_own)
        &&& self.slot_perm@.addr() == slot_own.self_addr
    }
}

impl<'rcu, C: PageTableConfig> InvView for EntryOwner<'rcu, C> {
    type V = NodeModel<C>;

    open spec fn view(self) -> <Self as InvView>::V {
        NodeModel { meta: self.node_own.meta_perm@.value() }
    }

    proof fn view_preserves_inv(&self) {
    }
}

impl<'rcu, C: PageTableConfig> OwnerOf for Entry<'rcu, C> {
    type Owner = EntryOwner<'rcu, C>;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        &&& self.idx < NR_ENTRIES()
        &&& self.pte.paddr() % PAGE_SIZE() == 0
        &&& self.pte.paddr() < MAX_PADDR()
        &&& self.node == owner.guard_perm@.pptr()
    }
}

pub tracked struct OwnerInTree<'rcu, C: PageTableConfig> {
    pub tree_node: Option<EntryOwner<'rcu, C>>,
}

impl<'rcu, C: PageTableConfig> Inv for OwnerInTree<'rcu, C> {
    open spec fn inv(self) -> bool {
        match self.tree_node {
            Some(owner) => owner.inv(),
            None => true,
        }
    }
}

impl<'rcu, C: PageTableConfig> TreeNodeValue for OwnerInTree<'rcu, C> {
    open spec fn default() -> Self {
        Self { tree_node: None }
    }

    proof fn default_preserves_inv()
        ensures
            #[trigger] Self::default().inv(),
    {
    }
}

pub tracked struct OwnerAsTreeNode<'rcu, C: PageTableConfig> {
    pub inner: ghost_tree::Node<OwnerInTree<'rcu, C>, CONST_NR_ENTRIES, CONST_NR_LEVELS>,
}

impl<'rcu, C: PageTableConfig> Deref for OwnerAsTreeNode<'rcu, C> {
    type Target = ghost_tree::Node<OwnerInTree<'rcu, C>, CONST_NR_ENTRIES, CONST_NR_LEVELS>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'rcu, C: PageTableConfig> OwnerAsTreeNode<'rcu, C> {
    pub open spec fn valid_ptrs(&self) -> bool {
        forall|i: usize|
            0 <= i < NR_ENTRIES() ==> self.inner.children[i as int] is Some ==> {
                &&& self.inner.value.tree_node.unwrap().children_perm.unwrap().is_init(i as int)
                &&& self.inner.children[i as int].unwrap().value.tree_node is Some
                &&& self.inner.value.tree_node.unwrap().children_perm.unwrap().opt_value()[i as int].value().wf(
                &self.inner.children[i as int].unwrap().value.tree_node.unwrap())
            }
    }
}

/* ****** Phase I models ****** */

pub tracked struct PageTableNodeOwner {
    pub paddr: usize,
    // Metadata
    pub is_pt: bool,  // if the node is a page table or a raw page
    pub is_tracked: bool,  // if the node is tracked
    pub nr_raws: nat,  // number of RawPageTableNodes
    pub is_locked: bool,  // whether the node is locked
    pub in_cpu: nat,  // number of CPUs that are currently using the node
    pub nr_parents: nat,  // number of parents
    // Sub-owners
    pub entries: [Option<PageTableEntry>; CONST_NR_ENTRIES],
}

pub ghost struct PageTableNodeModel {
    pub paddr: usize,
    // Metadata
    pub is_pt: bool,  // if the node is a page table or a raw page
    pub is_tracked: bool,  // if the node is tracked
    pub nr_raws: nat,  // number of RawPageTableNodes
    pub is_locked: bool,  // whether the node is locked
    pub in_cpu: nat,  // number of CPUs that are currently using the node
    pub nr_parents: nat,  // number of parents
    // Sub-owners
    pub entries: [Option<PageTableEntry>; CONST_NR_ENTRIES],
}

impl Inv for PageTableNodeOwner {
    open spec fn inv(self) -> bool {
        true
    }
}

impl Inv for PageTableNodeModel {
    open spec fn inv(self) -> bool {
        true
    }
}

impl InvView for PageTableNodeOwner {
    type V = PageTableNodeModel;

    open spec fn view(self) -> Self::V {
        PageTableNodeModel {
            paddr: self.paddr,
            is_pt: self.is_pt,
            is_tracked: self.is_tracked,
            nr_raws: self.nr_raws,
            is_locked: self.is_locked,
            in_cpu: self.in_cpu,
            nr_parents: self.nr_parents,
            entries: self.entries,
        }
    }

    proof fn view_preserves_inv(&self) {
    }
}

impl TreeNodeValue for PageTableNodeModel {
    open spec fn default() -> Self {
        Self {
            paddr: 0,
            is_pt: true,
            is_tracked: true,
            nr_raws: 0,
            is_locked: false,
            in_cpu: 0,
            nr_parents: 0,
            entries: [None;CONST_NR_ENTRIES],
        }
    }

    proof fn default_preserves_inv()
        ensures
            #[trigger] Self::default().inv(),
    {
    }
}

impl<C: PageTableConfig> ModelOf for PageTableNode<C> {

}

pub type PageTableTreeModel = ghost_tree::Tree<
    PageTableNodeValue,
    CONST_NR_ENTRIES,
    CONST_NR_LEVELS,
>;

pub tracked struct PageTableOwner<C: PageTableConfig> {
    pub tree: PageTableTreeModel,
    pub perms: Map<usize, PointsTo<PageTableNode<C>>>,
}

pub tracked struct PageTableModel {
    pub tree: ghost_tree::Tree<PageTableNodeModel, CONST_NR_ENTRIES, CONST_NR_LEVELS>,
    pub flat: Map<usize, Option<Mapping>>,
}

impl<C: PageTableConfig> Inv for PageTableOwner<C> {
    open spec fn inv(self) -> bool {
        true
        //        forall |path: TreePath|
        //            inv_at()

    }
}

pub tracked struct Mapping {
    pub tracked pa: usize,
    pub tracked is_locked: bool,
    pub page_size:
        usize,/*  TODO: below are some "payload" fields that do not directly impact verification of the page table,
            but which will be important for the long-term goal of merging verification targets into a single,
            end-to-end verified system. We omit these for now.
        pub flags: PageFlags,
        pub privilege: PrivilegedPageFlags,
        pub cache: CachePolicy, */
}

impl Mapping {
    pub open spec fn inv(self) -> bool {
        &&& set![4096, 2097152, 1073741824].contains(self.page_size)
        &&& self.pa % self.page_size == 0
    }
}

pub type PageTablePathModel = Map<usize, Tracked<Seq<PageTableNodeValue>>>;

pub type PageTableMapModel = Map<usize, Option<Mapping>>;

/*#[rustc_has_incoherent_inherent_impls]
pub tracked struct PageTableModel {
    pub tracked tree: PageTableTreeModel,
    pub tracked path: PageTablePathModel,
    pub tracked flat: PageTableMapModel,
}*/

pub open spec fn tree_to_path_refinement(tv: PageTableTreeModel, pv: PageTablePathModel) -> bool {
    forall|nr: usize| #[trigger]
        tv.trace(PageTableTreePathModel::from_va((nr * CONST_PAGE_SIZE) as usize).view()) == pv[nr]
}

pub open spec fn path_to_flat_refinement(pv: PageTablePathModel, fv: PageTableMapModel) -> bool {
    forall|nr: usize| #[trigger] fv[nr] == as_mapping(pv[nr]@)
}

pub open spec fn tree_to_flat_refinement(tv: PageTableTreeModel, fv: PageTableMapModel) -> bool {
    forall|nr: usize| #[trigger]
        fv[nr] == as_mapping(
            tv.trace(PageTableTreePathModel::from_va((nr * CONST_PAGE_SIZE) as usize)@),
        )
}

pub proof fn page_table_model_refinement_composable(
    tv: PageTableTreeModel,
    pv: PageTablePathModel,
    fv: PageTableMapModel,
)
    requires
        tree_to_path_refinement(tv, pv),
        path_to_flat_refinement(pv, fv),
    ensures
        tree_to_flat_refinement(tv, fv),
{
}

// TODO: define the following spec function
// pa == path.last().pa
// flags == AND(path[*].flags)
// ...
pub open spec fn as_mapping(path: Seq<PageTableNodeValue>) -> Option<Mapping> {
    let node = path.last();
    let depth = path.len();
    let size = page_size_at_level::<CONST_NR_LEVELS>(depth as int);
    if (node.is_pt) {
        None
    } else {
        Some(
            Mapping {
                pa: node.paddr,
                is_locked: node.is_locked,
                page_size: 4096,  // TODO: page size based on depth
            },
        )
    }
}

// TODO: convert a DynPage to a PageTableNodeModel
//    pub open spec fn as_node(page: DynPage) -> PageTableNodeModel;
impl PageTableModel {
    // pub open spec fn tree_nodes_refinement(self) -> bool {
    //     forall |i:usize|
    //         #[trigger]
    //         self.get_node(PageTableTreePathModel::from_path(self.nodes[i]@.value.path)) == Some(self.nodes[i]@)
    // }
    // pub open spec fn nodes_mapped_refinement(self) -> bool {
    //     forall |i:int|
    //         self.mapped[i].is_Some() ==>
    //         exists |j:int|
    //             #[trigger]
    //             self.nodes[i as usize]@.value.perms.unwrap().value().index(j) == self.mapped[i].unwrap()
    // }
    pub open spec fn inv(self) -> bool {
        &&& self.tree.inv()
        //        &&& tree_to_flat_refinement(self.tree, self.flat)

    }
}

} // verus!
