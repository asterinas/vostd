use vstd::prelude::*;

use vstd::arithmetic::power2::pow2;
use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::extern_const::*;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;
use vstd_extra::prelude::TreeNodeValue;

use super::*;

use core::ops::Deref;

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

pub open spec fn rec_vaddr(
    path: TreePath<CONST_NR_ENTRIES>,
    idx: int,
) -> usize/*        recommends
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

pub open spec fn vaddr(path: TreePath<CONST_NR_ENTRIES>) -> usize {
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

impl<'rcu, C: PageTableConfig, const L: usize> TreeNodeValue<L> for EntryOwner<'rcu, C> {
    open spec fn default(lv: nat) -> Self {
        Self {
            node: None,
            frame: None,
            locked: None,
            absent: true,
            guard_addr: 0,
            path: TreePath(Seq::empty()),
        }
    }

    proof fn default_preserves_inv() {
    }

    open spec fn la_inv(self, lv: nat) -> bool {
        self.is_node() ==> lv < L - 1
    }

    proof fn default_preserves_la_inv() {
    }

    open spec fn rel_children(self, child: Option<Self>) -> bool {
        if self.is_node() {
            &&& child is Some
            &&& child.unwrap().relate_parent_guard_perm(self.node.unwrap().guard_perm)
        } else {
            &&& child is None
        }
    }

    proof fn default_preserves_rel_children(self, lv: nat) {
        admit()
    }
}

extern_const!(
pub INC_LEVELS [INC_LEVELS_SPEC, CONST_INC_LEVELS]: usize = CONST_NR_LEVELS + 1
);

/// `OwnerSubtree` is a tree `Node` (from `vstd_extra::ghost_tree`) containing an `EntryOwner`.
/// It lives in a tree of maximum depth 5. Page table nodes can be at levels 0-3, and their entries are their children at the next
/// level down. This means that level 4, the lowest level, can only contain frame entries as it consists of the entries of level 1 page tables.
///
/// Level correspondences: tree level 0 ==> level 4 page table
///                        tree level 1 ==> level 3 page table (the level 4 page table does not map frames directly)
///                        tree level 2 ==> level 2 page table, or frame mapped by level 3 table
///                        tree level 3 ==> level 1 page table, or frame mapped by level 2 table
///                        tree level 4 ==> frame mapped by level 1 table
pub type OwnerSubtree<'rcu, C> = Node<EntryOwner<'rcu, C>, CONST_NR_ENTRIES, CONST_INC_LEVELS>;

pub tracked struct OwnerAsTreeNode<'rcu, C: PageTableConfig> {
    pub inner: OwnerSubtree<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> Deref for OwnerAsTreeNode<'rcu, C> {
    type Target = OwnerSubtree<'rcu, C>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'rcu, C: PageTableConfig> OwnerAsTreeNode<'rcu, C> {
    /// A leaf entry cannot have children
    pub open spec fn is_leaf(self) -> bool {
        &&& self.inner.value.is_frame()
        &&& forall|i: int| 0 <= i < NR_ENTRIES() ==> self.inner.children[i] is None
    }

    pub open spec fn is_table(self) -> bool {
        &&& self.inner.value.is_node()
    }

    pub open spec fn valid_ptrs(self) -> bool {
        forall|i: usize|
            #![auto]
            0 <= i < NR_ENTRIES() ==> self.inner.children[i as int] is Some ==> {
                &&& self.inner.value.node is Some
                &&& self.inner.value.node.unwrap().children_perm.is_init(
                    i as int,
                )
                //                &&& self.inner.children[i as int].unwrap().value.tree_node is Some
                &&& self.inner.value.node.unwrap().children_perm.opt_value()[i as int].value().wf(
                    self.inner.children[i as int].unwrap().value,
                )
            }
    }

    pub open spec fn view_rec(
        node: OwnerSubtree<'rcu, C>,  /*chain: Map<int, IntermediatePageTableEntryView<C>>,*/
        level: int,
    ) -> Seq<FrameView<C>>
        decreases level,
    {
        if level <= 1 {
            Seq::empty()
        } else if node.value.is_frame() {
            Seq::empty().push(node.value@->leaf.to_frame_view(  /*chain*/ ))
        } else if node.value.is_node() {
            //            let chain = chain.insert(level, node.value@ -> node);
            node.children.flat_map(
                |child: Option<OwnerSubtree<'rcu, C>>| Self::view_rec(child.unwrap(), level - 1),
            )
        } else if node.value.is_locked() {
            node.value.locked.unwrap()@
        } else {
            Seq::empty()
        }
    }
}

impl<'rcu, C: PageTableConfig> Inv for OwnerAsTreeNode<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& self.is_table() ==> {
            &&& forall|i: int|
                0 <= i < NR_ENTRIES() ==> {
                    &&& self.inner.children[i] is Some
                    &&& self.inner.children[i].unwrap().inv()
                }
        }
        &&& self.inner.value.inv()
        &&& self.inner.inv()
    }
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct PageTableOwner<'rcu, C: PageTableConfig> {
    pub tree: OwnerAsTreeNode<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> Inv for PageTableOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        self.tree.inv()
    }
}

pub tracked struct PageTableView<C: PageTableConfig> {
    pub leaves: Seq<FrameView<C>>,
}

impl<'rcu, C: PageTableConfig> View for PageTableOwner<'rcu, C> {
    type V = PageTableView<C>;

    open spec fn view(&self) -> Self::V {
        PageTableView { leaves: OwnerAsTreeNode::view_rec(self.tree.inner, 4) }
    }
}

} // verus!
