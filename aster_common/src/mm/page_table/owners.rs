use vstd::prelude::*;

use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;
use vstd_extra::prelude::TreeNodeValue;

use super::*;

use std::ops::Deref;

verus! {

pub tracked struct OwnerInTree<'rcu, C: PageTableConfig> {
    pub tree_node: Option<EntryOwner<'rcu, C>>,
}

impl<'rcu, C: PageTableConfig> Inv for OwnerInTree<'rcu, C> {
    open spec fn inv(&self) -> bool {
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
    pub inner: Node<OwnerInTree<'rcu, C>, CONST_NR_ENTRIES, CONST_NR_LEVELS>,
}

impl<'rcu, C: PageTableConfig> Deref for OwnerAsTreeNode<'rcu, C> {
    type Target = Node<OwnerInTree<'rcu, C>, CONST_NR_ENTRIES, CONST_NR_LEVELS>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'rcu, C: PageTableConfig> OwnerAsTreeNode<'rcu, C> {
    pub open spec fn valid_ptrs(self) -> bool {
        forall|i: usize| #![auto]
            0 <= i < NR_ENTRIES() ==> self.inner.children[i as int] is Some ==> {
                &&& self.inner.value.tree_node.unwrap().children_perm.unwrap().is_init(i as int)
                &&& self.inner.children[i as int].unwrap().value.tree_node is Some
                &&& self.inner.value.tree_node.unwrap().children_perm.unwrap().opt_value()[i as int].value().wf(
                &self.inner.children[i as int].unwrap().value.tree_node.unwrap())
            }
    }
}

#[verusfmt::skip]
pub tracked struct PageTableOwner<'rcu, C: PageTableConfig> {
    pub tree: Tree<OwnerInTree<'rcu, C>, CONST_NR_ENTRIES, CONST_NR_LEVELS>,
    //    pub perms: Map<TreePath<CONST_NR_ENTRIES, CONST_NR_LEVELS>, PointsTo<>>
}

pub tracked struct CursorModel {
    pub path: TreePath<CONST_NR_ENTRIES>,
}

} // verus!
