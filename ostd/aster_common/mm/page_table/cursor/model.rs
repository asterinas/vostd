use vstd::prelude::*;

use crate::prelude::*;
use vstd_extra::prelude::TreePath;

verus! {

pub tracked struct ConcreteCursor {
    pub tracked tree: PageTableTreeModel,
    pub tracked locked_subtree: PageTableNodeModel,
    pub tracked path: PageTableTreePathModel,
}

impl ConcreteCursor {
    pub open spec fn inv(self) -> bool {
        &&& self.tree.inv()
        &&& self.path.inv()
        //        &&& self.tree.on_tree(self.locked_subtree)

    }

    #[verifier::inline]
    pub open spec fn virt_addr_spec(self) -> usize {
        self.path.vaddr()
    }

    pub proof fn lemma_pop_level_spec_preserves_vaddr(self, n: int)
        requires
            self.path.inner.len() == n,
            n > 0,
            self.path.inner.inv(),
            self.path.inner.0[n - 1] == 0,
        ensures
            self.pop_level_spec().path.vaddr() == self.path.vaddr(),
    {
        let ghost orig = self.path.inner;
        let ghost popped = orig.pop_tail().1;
        assert(self.pop_level_spec().path.inner == popped);
        PageTableTreePathModel::rec_vaddr_pop_0(orig, n, 0);
    }

    pub proof fn lemma_push_level_spec_preserves_vaddr(self, n: int)
        requires
            self.path.inner.len() == n,
            n < NR_LEVELS(),
            self.path.inner.inv(),
        ensures
            self.push_level_spec().path.vaddr() == self.path.vaddr(),
    {
        let ghost orig = self.path.inner;
        let ghost pushed = orig.push_tail(0 as usize);
        assert(self.push_level_spec().path.inner == pushed);
        PageTableTreePathModel::rec_vaddr_push_0(orig, n, 0);
    }

    pub open spec fn get_nodes(self, path: PageTableTreePathModel) -> (res: Seq<PageTableNodeValue>)
        recommends
            self.inv(),
            path.inv(),
    {
        self.tree.trace(path@)
    }
}

} // verus!
