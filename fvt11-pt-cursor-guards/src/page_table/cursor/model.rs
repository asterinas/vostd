use vstd::prelude::*;

use vstd_extra::prelude::{TreePath};
use aster_common::prelude::{
    AbstractState, PageTableNode, PageTableModel, PageTableTreePathModel, PageTableTreeModel,
    PageTableNodeModel, pte_index, page_size_at_level,
};

use super::super::{
    node::model::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE},
};

verus! {

pub tracked struct ConcreteCursor {
    pub tracked locked_subtree: PageTableNodeModel,
    pub tracked path: PageTableTreePathModel,
}

impl ConcreteCursor {
    pub open spec fn inv(self, s: AbstractState) -> bool {
        &&& self.path.inv()
        &&& s.page_table.tree@.on_tree(self.locked_subtree@)
        &&& s.page_table.get_nodes(self.path).len() == self.path.len() + 1
    }

    #[verifier::inline]
    pub open spec fn virt_addr_spec(self) -> usize {
        self.path.vaddr()
    }

    pub open spec fn push_level_spec(self) -> ConcreteCursor {
        ConcreteCursor {
            path: PageTableTreePathModel { inner: self.path.inner.push_tail(0 as usize) },
            ..self
        }
    }

    pub open spec fn pop_level_spec(self) -> ConcreteCursor {
        let (tail, popped) = self.path.inner.pop_tail();
        ConcreteCursor { path: PageTableTreePathModel { inner: popped }, ..self }
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

    pub proof fn lemma_pop_level_spec_len(self)
        requires
            self.path@.len() > 0,
        ensures
            self.pop_level_spec().path@.len() == self.path@.len() - 1,
    {
    }

    pub proof fn lemma_pop_level_spec_prepends(self, s: AbstractState)
        requires
            self.path@.len() > 0,
        ensures
            forall|i: int|
                0 <= i < self.path@.len() - 1 ==> self.pop_level_spec().path@.0[i]
                    == #[trigger] self.path@.0[i],
    {
    }

    pub proof fn lemma_push_level_spec_preserves_vaddr(self, n: int)
        requires
            self.path.inner.len() == n,
            n < NR_LEVELS,
            self.path.inner.inv(),
        ensures
            self.push_level_spec().path.vaddr() == self.path.vaddr(),
    {
        let ghost orig = self.path.inner;
        let ghost pushed = orig.push_tail(0 as usize);
        assert(self.push_level_spec().path.inner == pushed);
        PageTableTreePathModel::rec_vaddr_push_0(orig, n, 0);
    }

    pub proof fn lemma_push_level_spec_len(self)
        ensures
            self.push_level_spec().path@.len() == self.path@.len() + 1,
    {
    }

    pub proof fn lemma_push_level_spec_extends(self, s: AbstractState)
        ensures
            forall|i: int|
                0 <= i < self.path@.len() ==> self.push_level_spec().path@.0[i]
                    == #[trigger] self.path@.0[i],
    {
    }

    pub open spec fn inc_pop_aligned_rec(path: TreePath<NR_ENTRIES>) -> TreePath<NR_ENTRIES>
        decreases path.len(),
    {
        if path.len() == 0 {
            path
        } else {
            let n = path.len();
            let val = path.0[n - 1];
            let new_path = path.0.update(n - 1, (val + 1) as usize);

            if new_path[n - 1] % NR_ENTRIES == 0 {
                let (tail, popped) = path.pop_tail();
                Self::inc_pop_aligned_rec(popped)
            } else {
                path
            }
        }
    }

    pub open spec fn move_forward_spec(self) -> ConcreteCursor {
        ConcreteCursor {
            path: PageTableTreePathModel { inner: Self::inc_pop_aligned_rec(self.path.inner) },
            ..self
        }
    }
}

} // verus!
