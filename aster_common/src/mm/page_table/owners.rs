use vstd::prelude::*;

use vstd::arithmetic::power2::pow2;
use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;
use vstd_extra::prelude::TreeNodeValue;

use super::*;

use std::ops::Deref;

verus! {

#[verifier::inline]
pub open spec fn vaddr_shift_bits<const L: usize>(idx: int) -> nat
    recommends
        0 < L,
        idx < L,
{
    (12 + 9 * (L - 1 - idx)) as nat
}

#[verifier::inline]
pub open spec fn vaddr_shift<const L: usize>(idx: int) -> usize
    recommends
        0 < L,
        idx < L,
{
    pow2(vaddr_shift_bits::<L>(idx)) as usize
}

#[verifier::inline]
pub open spec fn vaddr_make<const L: usize>(idx: int, offset: usize) -> usize
    recommends
        0 < L,
        idx < L,
        0 <= offset < 512,
{
    (vaddr_shift::<L>(idx) * offset) as usize
}

pub open spec fn rec_vaddr(path: TreePath<CONST_NR_ENTRIES>, idx: int) -> usize
/*        recommends
        0 < NR_LEVELS(),
        path.len() <= NR_LEVELS(),
        0 <= idx <= path.len(),*/
    decreases path.len() - idx,
    when 0 <= idx <= path.len()
{
    if idx == path.len() {
        0
    } else {
        let offset: usize = path.index(idx);
        (vaddr_make::<CONST_NR_LEVELS>(idx, offset) + rec_vaddr(path, idx + 1)) as usize
    }
}

pub open spec fn vaddr(path: TreePath<CONST_NR_ENTRIES>) -> usize
{
    rec_vaddr(path, 0)
}

/*
impl<'rcu, C: PageTableConfig> EntryState<'rcu, C> {
    open spec fn get_entry(self) -> Option<EntryOwner<'rcu, C>> {
        match self {
            Self::Present(owner) => Some(owner),
            _ => None,
        }
    }
}
*/

pub tracked struct OwnerInTree<'rcu, C: PageTableConfig> {
    pub tree_node: EntryOwner<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> Inv for OwnerInTree<'rcu, C> {
    open spec fn inv(self) -> bool {
        true/*        match self.tree_node {
            Self::Present(owner) => owner.inv(),
            Self::Absent => true,
            Self::Locked => true,
        }*/

    }
}

impl<'rcu, C: PageTableConfig> TreeNodeValue for EntryOwner<'rcu, C> {
    open spec fn default() -> Self {
        Self {
            node: None,
            frame: None,
            locked: None,
            absent: true,
            index: 0,
            base_addr: 0,
            guard_addr: 0,
            path: TreePath(Seq::empty())
        }
    }

    proof fn default_preserves_inv()
        ensures
            #[trigger] Self::default().inv(),
    {
    }
}

pub type OwnerNode<'rcu, C> = Node<EntryOwner<'rcu, C>, CONST_NR_ENTRIES, CONST_NR_LEVELS>;

pub tracked struct OwnerAsTreeNode<'rcu, C: PageTableConfig> {
    pub inner: OwnerNode<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> Deref for OwnerAsTreeNode<'rcu, C> {
    type Target = Node<EntryOwner<'rcu, C>, CONST_NR_ENTRIES, CONST_NR_LEVELS>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'rcu, C: PageTableConfig> OwnerAsTreeNode<'rcu, C> {
    pub open spec fn is_leaf(self) -> bool {
        &&& self.inner.value.is_frame()
        //        &&& self.value.get_entry().unwrap().node_owner.meta_own.nr_children@
        &&& self.inner.children.len() == 0
    }

    pub open spec fn valid_ptrs(self) -> bool {
        forall|i: usize|
            #![auto]
            0 <= i < NR_ENTRIES() ==> self.inner.children[i as int] is Some ==> {
                &&& self.inner.value.node is Some
                &&& self.inner.value.node.unwrap().children_perm.is_init(i as int)
                //                &&& self.inner.children[i as int].unwrap().value.tree_node is Some
                &&& self.inner.value.node.unwrap().children_perm.opt_value()[i as int].value().wf(
                    self.inner.children[i as int].unwrap().value,
                )
            }
    }
    
    pub open spec fn view_rec(node: OwnerNode<'rcu, C>, chain: Map<int, IntermediatePageTableEntryView<C>>, level: int) -> Seq<FrameView<C>>
        decreases NR_LEVELS() - level,
    {
        if NR_LEVELS() - level <= 0 {
            Seq::empty()
        } else if node.value.is_frame() {
            Seq::empty().push(node.value@->leaf.to_frame_view(chain))
        } else if node.value.is_node() {
            let chain = chain.insert(level, node.value@ -> node);
            node.children.flat_map(|child: Option<OwnerNode<'rcu, C>>| Self::view_rec(child.unwrap(), chain, level + 1))
        } else if node.value.is_locked() {
            node.value.locked.unwrap()@
        } else {
            Seq::empty()
        }
    }
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct PageTableOwner<'rcu, C: PageTableConfig> {
    pub tree: OwnerAsTreeNode<'rcu, C>,
}

pub tracked struct PageTableView<C: PageTableConfig> {
    pub leaves: Seq<FrameView<C>>
}

impl<'rcu, C: PageTableConfig> View for PageTableOwner<'rcu, C> {
    type V = PageTableView<C>;

    open spec fn view(&self) -> Self::V {
        PageTableView { 
            leaves: OwnerAsTreeNode::view_rec(self.tree.inner, Map::empty(), 0)
        }
    }
}

} // verus!
