use vstd::prelude::*;

use core::ops::Range;

use vstd::arithmetic::power2::pow2;
use vstd::seq::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;
use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::extern_const::*;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;
use vstd_extra::prelude::TreeNodeValue;
use vstd_extra::undroppable::*;

use crate::mm::{
    page_table::{EntryOwner, FrameView},
    MAX_NR_LEVELS, Paddr, Vaddr,
};

use crate::specs::arch::*;
use crate::specs::mm::page_table::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::mm::page_table::PageTableGuard;

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
            parent_level: (INC_LEVELS() - lv + 1) as PagingLevel,
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
            &&& child.unwrap().path.len() == self.node.unwrap().level
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

/// `OwnerSubtree` is a tree `Node` (from `vstd_extra::ghost_tree`) containing `EntryOwner`s.
/// It lives in a tree of maximum depth 5. Page table nodes can be at levels 0-3, and their entries are their children at the next
/// level down. This means that level 4, the lowest level, can only contain frame entries as it consists of the entries of level 1 page tables.
///
/// Level correspondences: tree level 0 ==> path length 0 ==> level 4 page table
///                        tree level 1 ==> path length 1 ==> level 3 page table (the level 4 page table does not map frames directly)
///                        tree level 2 ==> path length 2 ==> level 2 page table or frame mapped by level 3 table
///                        tree level 3 ==> path length 3 ==> level 1 page table or frame mapped by level 2 table
///                        tree level 4 ==> path length 4 ==> frame mapped by level 1 table
pub type OwnerSubtree<C> = Node<EntryOwner<C>, CONST_NR_ENTRIES, CONST_INC_LEVELS>;

pub struct PageTableOwner<C: PageTableConfig>(pub OwnerSubtree<C>);

impl<C: PageTableConfig> PageTableOwner<C> {

    /*
    pub proof fn never_drop_preserves_unlocked<'rcu>(
        subtree: OwnerSubtree<C>,
        path: TreePath<CONST_NR_ENTRIES>,
        guard: PageTableGuard<'rcu, C>,
        guards0: Guards<'rcu, C>,
        guards1: Guards<'rcu, C>
    )
        requires
            subtree.inv(),
            Self::unlocked(subtree, path, guards0),
            <PageTableGuard<'rcu, C> as Undroppable>::constructor_requires(guard,guards0),
            <PageTableGuard<'rcu, C> as Undroppable>::constructor_ensures(guard, guards0, guards1),
        ensures
            Self::unlocked(subtree, path, guards1),
        decreases INC_LEVELS() - subtree.level
    {
        admit();
    }
    */

    pub open spec fn view_rec(self, path: TreePath<CONST_NR_ENTRIES>) -> Set<Mapping>
        decreases INC_LEVELS() - path.len() when self.0.inv() && path.len() <= INC_LEVELS() - 1
    {
        if self.0.value.is_frame() {
            let vaddr = vaddr(path);
            let pt_level = INC_LEVELS() - path.len();
            let page_size = page_size(pt_level as PagingLevel);
    
            set![Mapping {
                va_range: Range { start: vaddr, end: (vaddr + page_size) as Vaddr },
                pa_range: Range {
                    start: self.0.value.frame.unwrap().mapped_pa,
                    end: (self.0.value.frame.unwrap().mapped_pa + page_size) as Paddr,
                },
                page_size: page_size,
                property: self.0.value.frame.unwrap().prop,
            }]
        } else if self.0.value.is_node() && path.len() < INC_LEVELS() - 1 {
            Set::new(
                |m: Mapping| exists|i:int| 0 <= i < self.0.children.len() &&
                    self.0.children[i] is Some &&
                    PageTableOwner(self.0.children[i].unwrap()).view_rec(path.push_tail(i as usize)).contains(m)
            )
        } else {
            set![]
        }
    }

    pub proof fn view_rec_contains(self, path: TreePath<CONST_NR_ENTRIES>, m: Mapping)
        requires
            self.0.inv(),
            path.len() < INC_LEVELS() - 1,
            path.len() == self.0.level,
            self.view_rec(path).contains(m),
            self.0.value.is_node()
        ensures
            exists|i:int| #![auto] 0 <= i < self.0.children.len() &&
            self.0.children[i] is Some &&
            PageTableOwner(self.0.children[i].unwrap()).view_rec(path.push_tail(i as usize)).contains(m)
    { }

    pub proof fn view_rec_contains_choose(self, path: TreePath<CONST_NR_ENTRIES>, m: Mapping) -> (i: int)
        requires
            self.0.inv(),
            path.len() < INC_LEVELS() - 1,
            path.len() == self.0.level,
            self.view_rec(path).contains(m),
            self.0.value.is_node(),
        ensures
            0 <= i < self.0.children.len() &&
            self.0.children[i] is Some &&
            PageTableOwner(self.0.children[i].unwrap()).view_rec(path.push_tail(i as usize)).contains(m)
    {
        choose|i:int| #![auto] 0 <= i < self.0.children.len() &&
            self.0.children[i] is Some &&
            PageTableOwner(self.0.children[i].unwrap()).view_rec(path.push_tail(i as usize)).contains(m)
    }

    pub proof fn view_rec_vaddr_range(self, path: TreePath<CONST_NR_ENTRIES>, m: Mapping)
        requires
            self.0.inv(),
            path.len() <= INC_LEVELS() - 1,
            path.len() == self.0.level,
            self.view_rec(path).contains(m),
        ensures
            vaddr(path) <= m.va_range.start < m.va_range.end <= vaddr(path) + page_size(path.len() as PagingLevel),
    {
        admit();
    }

    pub proof fn view_rec_disjoint_vaddrs(self, path: TreePath<CONST_NR_ENTRIES>, m1: Mapping, m2: Mapping)
        requires
            self.0.inv(),
            path.len() <= INC_LEVELS() - 1,
            path.len() == self.0.level,
            self.view_rec(path).contains(m1),
            self.view_rec(path).contains(m2),
            m1 != m2,
        ensures
            m1.va_range.end <= m2.va_range.start || m2.va_range.end <= m1.va_range.start
        decreases INC_LEVELS() - path.len()
    {
        broadcast use group_set_properties;

        if self.0.value.is_frame() {
            assert(self.view_rec(path).is_singleton());
        } else if self.0.value.is_node() {
            self.view_rec_contains(path, m1);
            self.view_rec_contains(path, m2);

            let i1 = self.view_rec_contains_choose(path, m1);
            let i2 = self.view_rec_contains_choose(path, m2);

            if i1 == i2 {
                PageTableOwner(self.0.children[i1].unwrap()).view_rec_disjoint_vaddrs(path.push_tail(i1 as usize), m1, m2);
            } else if i1 < i2 {
                let page_size = page_size((path.len() + 1) as PagingLevel);
                // TODO: connect TreePath to AbstractVaddr
                assert(vaddr(path.push_tail(i1 as usize)) + page_size <= vaddr(path.push_tail(i2 as usize))) by { admit(); };
                PageTableOwner(self.0.children[i1].unwrap()).view_rec_vaddr_range(path.push_tail(i1 as usize), m1);
                PageTableOwner(self.0.children[i2].unwrap()).view_rec_vaddr_range(path.push_tail(i2 as usize), m2);
            } else {
                let page_size = page_size((path.len() + 1) as PagingLevel);
                assert(vaddr(path.push_tail(i2 as usize)) + page_size <= vaddr(path.push_tail(i1 as usize))) by { admit(); };
                PageTableOwner(self.0.children[i2].unwrap()).view_rec_vaddr_range(path.push_tail(i2 as usize), m2);
                PageTableOwner(self.0.children[i1].unwrap()).view_rec_vaddr_range(path.push_tail(i1 as usize), m1);
            }
        }
    }

    pub open spec fn relate_region_pred(regions: MetaRegionOwners)
        -> (spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool) {
        |entry: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>| entry.relate_region(regions)
    }

    pub open spec fn relate_region(self, regions: MetaRegionOwners) -> bool
        decreases INC_LEVELS() - self.0.level when self.0.inv()
    {
        self.0.tree_predicate_map(self.0.value.path, Self::relate_region_pred(regions))
    }

    /// An absent entry contributes no mappings - view_rec returns the empty set.
    pub proof fn view_rec_absent_empty(self, path: TreePath<CONST_NR_ENTRIES>)
        requires
            self.0.inv(),
            self.0.value.is_absent(),
            path.len() <= INC_LEVELS() - 1,
        ensures
            self.view_rec(path) =~= set![],
    {
        // is_absent() implies !is_frame() and !is_node() by the EntryOwner invariant
        // Therefore view_rec falls through to the else branch returning set![]
    }
}

impl<C: PageTableConfig> Inv for PageTableOwner<C> {
    open spec fn inv(self) -> bool {
        &&& self.0.inv()
        &&& self.0.value.path.len() <= INC_LEVELS() - 1
    }
}

impl<C: PageTableConfig> View for PageTableOwner<C> {
    type V = PageTableView;

    open spec fn view(&self) -> <Self as View>::V {
        let mappings = self.view_rec(self.0.value.path);
        PageTableView {
            mappings
        }
    }
}

} // verus!
