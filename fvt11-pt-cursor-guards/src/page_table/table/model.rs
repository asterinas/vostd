use vstd::prelude::*;
use vstd_extra::prelude::*;

use aster_common::prelude::*;

verus! {

impl PageTableModel {
    #[rustc_allow_incoherent_impl]
    #[verifier::inline]
    pub open spec fn on_tree(self, node: PageTableNodeModel) -> bool
        recommends
            self.inv(),
            node@.inv(),
    {
        self.tree@.on_tree(node@)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn get_nodes(self, path: PageTableTreePathModel) -> (res: Seq<PageTableNodeValue>)
        recommends
            self.inv(),
            path.inv(),
    {
        self.tree@.trace(path.inner)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn get_node(self, path: PageTableTreePathModel) -> Option<PageTableNodeModel>
        recommends
            self.inv(),
            path.inv(),
    {
        let res = self.tree@.seek(path@);
        match res {
            Some(node) => Some(PageTableNodeModel::from_node(node)),
            None => None,
        }
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn get_node_empty_is_root(self, path: PageTableTreePathModel)
        requires
            path.inner.len() == 0,
        ensures
            self.get_node(path) == Some(PageTableNodeModel::from_node(self.tree@.root)),
    {
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn get_path(self, node: PageTableNodeModel) -> (res: PageTableTreePathModel)
        recommends
            self.inv(),
            node@.inv(),
            self.tree@.on_tree(node@),
    {
        PageTableTreePathModel::from_path(self.tree@.get_path(node@))
    }
}

} // verus!
