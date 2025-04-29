use vstd::prelude::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;

use vstd_extra::ghost_tree;

use vstd_extra::prelude::Node;
use crate::prelude::*;

verus! {

pub tracked struct PageTableNodeModel {
    pub tracked inner: ghost_tree::Node<PageTableNodeValue, CONST_NR_ENTRIES, CONST_NR_LEVELS>,
}

impl View for PageTableNodeModel {
    type V = ghost_tree::Node<PageTableNodeValue, CONST_NR_ENTRIES, CONST_NR_LEVELS>;

    open spec fn view(&self) -> Self::V {
        self.inner
    }
}

pub open spec fn between(low: usize, high: usize, i: usize) -> bool {
    low < i <= high
}

impl PageTableNodeModel {
    pub open spec fn valid_ptrs(&self) -> bool {
        forall|i: usize| #[trigger]
            between(0, CONST_NR_ENTRIES, i) ==> forall|
                child: Node<PageTableNodeValue, CONST_NR_ENTRIES, CONST_NR_LEVELS>,
            |
                self.inner.children.index(i as int) == Some(child)
                    ==> self.inner.value.perms.unwrap().wf()
                    && self.inner.value.perms.unwrap().is_init(i as int)
                    && self.inner.value.perms.unwrap().opt_value()[i as int].value().paddr()
                    == child.value.paddr
    }

    pub open spec fn from_node(
        node: ghost_tree::Node<PageTableNodeValue, CONST_NR_ENTRIES, CONST_NR_LEVELS>,
    ) -> PageTableNodeModel {
        PageTableNodeModel { inner: node }
    }
}

pub tracked struct PageTableTreeModel {
    pub tracked inner: ghost_tree::Tree<PageTableNodeValue, CONST_NR_ENTRIES, CONST_NR_LEVELS>,
}

impl View for PageTableTreeModel {
    type V = ghost_tree::Tree<PageTableNodeValue, CONST_NR_ENTRIES, CONST_NR_LEVELS>;

    open spec fn view(&self) -> Self::V {
        self.inner
    }
}

impl PageTableTreeModel {
    pub open spec fn inv(&self) -> bool {
        &&& self.inner.inv()
        &&& forall|node: PageTableNodeModel| #[trigger] self.inner.on_tree(node@) ==> node@.inv()
    }

    pub open spec fn root_paddr(&self) -> Paddr {
        self.inner.root.value.paddr
    }
}

} // verus!
