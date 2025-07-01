use vstd::prelude::*;

use vstd_extra::ghost_tree;

use crate::prelude::*;

verus! {

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

#[rustc_has_incoherent_inherent_impls]
pub tracked struct PageTableModel {
    pub tracked tree: PageTableTreeModel,
    pub tracked path: PageTablePathModel,
    pub tracked flat: PageTableMapModel,
}

pub open spec fn tree_to_path_refinement(tv: PageTableTreeModel, pv: PageTablePathModel) -> bool {
    forall|nr: usize| #[trigger]
        tv.inner.trace(PageTableTreePathModel::from_va((nr * CONST_PAGE_SIZE) as usize).view())
            == pv[nr]
}

pub open spec fn path_to_flat_refinement(pv: PageTablePathModel, fv: PageTableMapModel) -> bool {
    forall|nr: usize| #[trigger] fv[nr] == as_mapping(pv[nr]@)
}

pub open spec fn tree_to_flat_refinement(tv: PageTableTreeModel, fv: PageTableMapModel) -> bool {
    forall|nr: usize| #[trigger]
        fv[nr] == as_mapping(
            tv.inner.trace(PageTableTreePathModel::from_va((nr * CONST_PAGE_SIZE) as usize)@),
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
    //         self.mapped[i] is Some ==>
    //         exists |j:int|
    //             #[trigger]
    //             self.nodes[i as usize]@.value.perms.unwrap().value().index(j) == self.mapped[i].unwrap()
    // }
    pub open spec fn inv(self) -> bool {
        &&& self.tree.inv()
        &&& tree_to_path_refinement(self.tree, self.path)
        &&& path_to_flat_refinement(self.path, self.flat)
    }
}

} // verus!
