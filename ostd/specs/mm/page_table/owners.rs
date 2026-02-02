use vstd::prelude::*;

use vstd::arithmetic::power2::pow2;
use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::extern_const::*;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;
use vstd_extra::prelude::TreeNodeValue;

use crate::mm::{
    page_table::{EntryOwner, FrameView},
    MAX_NR_LEVELS,
};

use crate::specs::arch::*;
use crate::specs::mm::page_table::*;

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

impl<C: PageTableConfig, const L: usize> TreeNodeValue<L> for EntryOwner<C> {
    open spec fn default(lv: nat) -> Self {
        Self {
            path: TreePath::new(Seq::empty()),
            node: None,
            frame: None,
            locked: None,
            absent: true,
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
//            &&& child.unwrap().relate_parent_guard_perm(self.node.unwrap().guard_perm)
        } else {
            &&& child is None
        }
    }

    proof fn default_preserves_rel_children(self, lv: nat) {
        admit()
    }
}

impl<C: PageTableConfig, const L: usize> TreeNodeView<L> for EntryOwner<C> {
    open spec fn view_rec_step(self, rec: Seq<EntryView<C>>) -> Seq<EntryView<C>> {
        if self.is_node() {
            rec
        } else {
            Seq::empty().push(self.view())
        }
    }
}

extern_const!(
pub INC_LEVELS [INC_LEVELS_SPEC, CONST_INC_LEVELS]: usize = CONST_NR_LEVELS + 1
);

/// `OwnerSubtree` is a tree `Node` (from `vstd_extra::ghost_tree`) containing `EntryOwner`s.
/// It lives in a tree of maximum depth 5. Page table nodes can be at levels 0-3, and their entries are their children at the next
/// level down. This means that level 4, the lowest level, can only contain frame entries as it consists of the entries of level 1 page tables.
///
/// Level correspondences: tree level 0 ==> level 4 page table
///                        tree level 1 ==> level 3 page table (the level 4 page table does not map frames directly)
///                        tree level 2 ==> level 2 page table, or frame mapped by level 3 table
///                        tree level 3 ==> level 1 page table, or frame mapped by level 2 table
///                        tree level 4 ==> frame mapped by level 1 table
pub type OwnerSubtree<C> = Node<EntryOwner<C>, CONST_NR_ENTRIES, CONST_INC_LEVELS>;

pub struct PageTableOwner<C: PageTableConfig>(pub OwnerSubtree<C>);

impl<C: PageTableConfig> PageTableOwner<C> {
    pub open spec fn unlocked<'rcu>(subtree: OwnerSubtree<C>, guards: Guards<'rcu, C>) -> bool
        decreases INC_LEVELS() - subtree.level when subtree.inv()
    {
        if subtree.value.is_node() {
            &&& guards.unlocked(subtree.value.node.unwrap().meta_perm.addr())
            &&& forall|child| #![auto] subtree.children.contains(Some(child)) ==> Self::unlocked(child, guards)
        } else {
            true
        }
    }
}

} // verus!
