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
    Paddr, Vaddr, MAX_NR_LEVELS,
};

use crate::mm::page_table::PageTableGuard;
use crate::specs::arch::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::*;
use crate::mm::frame::frame_to_index;

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

/// Sibling paths (same prefix, different last index) have disjoint VA ranges.
/// This is a fundamental property of page table virtual address layout:
/// each entry at a given level covers a distinct, non-overlapping range.
pub proof fn sibling_paths_disjoint(
    prefix: TreePath<CONST_NR_ENTRIES>,
    j: usize,
    k: usize,
    size: usize,
)
    requires
        j < NR_ENTRIES(),
        k < NR_ENTRIES(),
        j != k,
        size == page_size((prefix.len() + 1) as PagingLevel),
    ensures
        vaddr(prefix.push_tail(j)) + size <= vaddr(prefix.push_tail(k))
        || vaddr(prefix.push_tail(k)) + size <= vaddr(prefix.push_tail(j)),
{
    admit()
}

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

    open spec fn rel_children(self, i: int, child: Option<Self>) -> bool {
        if self.is_node() {
            &&& child is Some
            &&& child.unwrap().path.len() == self.node.unwrap().tree_level + 1
            &&& child.unwrap().match_pte(self.node.unwrap().children_perm.value()[i], self.node.unwrap().level)
            &&& child.unwrap().path == self.path.push_tail(i as usize)
        } else {
            &&& child is None
        }
    }

    proof fn default_preserves_rel_children(self, i: int, lv: nat) {
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
                |m: Mapping| exists|i:int|
                #![trigger self.0.children[i]]
                0 <= i < self.0.children.len() &&
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

    /// An absent entry contributes no mappings - view_rec returns the empty set.
    pub proof fn view_rec_absent_empty(self, path: TreePath<CONST_NR_ENTRIES>)
        requires
            self.0.inv(),
            self.0.value.is_absent(),
            path.len() <= INC_LEVELS() - 1,
        ensures
            self.view_rec(path) =~= set![],
    { }

    pub open spec fn relate_region_pred(regions: MetaRegionOwners)
        -> (spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool) {
        |entry: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>| entry.relate_region(regions)
    }

    pub open spec fn relate_region(self, regions: MetaRegionOwners) -> bool
        decreases INC_LEVELS() - self.0.level when self.0.inv()
    {
        self.0.tree_predicate_map(self.0.value.path, Self::relate_region_pred(regions))
    }

    /// Predicate: all nodes in the tree have their paths tracked in regions
    pub open spec fn path_tracked_pred(regions: MetaRegionOwners)
        -> spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool
    {   
        |entry: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>| {
            &&& regions.slot_owners.contains_key(frame_to_index(entry.meta_slot_paddr()))
            &&& regions.slot_owners[frame_to_index(entry.meta_slot_paddr())].path_if_in_pt is Some
        }
    }

    pub open spec fn relate_region_tracked_pred(regions: MetaRegionOwners)
        -> spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool
    {
        |entry: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>| {
            &&& regions.slot_owners.contains_key(frame_to_index(entry.meta_slot_paddr()))
            &&& regions.slot_owners[frame_to_index(entry.meta_slot_paddr())].path_if_in_pt is Some
            &&& regions.slot_owners[frame_to_index(entry.meta_slot_paddr())].path_if_in_pt.unwrap() == path
        }
    }

    pub open spec fn path_correct_pred()
        -> spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool
    {
        |entry: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>| {
            entry.path == path
        }
    }
/*
    pub proof fn view_rec_inversion(self, path: TreePath<CONST_NR_ENTRIES>, regions: MetaRegionOwners, m: Mapping)
    -> (res: (EntryOwner<C>, spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool))
        requires
            self.0.inv(),
            path.len() <= INC_LEVELS() - 1,
            path.len() == self.0.level,
            self.view_rec(path).contains(m),
            self.0.tree_predicate_map(path, Self::path_tracked_pred(regions)),
        ensures
            OwnerSubtree::implies(Self::relate_region_tracked_pred(regions), res.1)
        decreases INC_LEVELS() - path.len()
    {
        if self.0.value.is_frame() {
            let f = |owner: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>| {
                owner.is_frame() ==>
                owner.frame.unwrap().mapped_pa == m.pa_range.start ==>
                owner == self.0.value };
            assert(OwnerSubtree::implies(Self::relate_region_tracked_pred(regions), f));
            (self.0.value, f)
        } else if self.0.value.is_node() {
            self.view_rec_contains(path, m);
            let i = self.view_rec_contains_choose(path, m);
            let (res, f) = PageTableOwner(self.0.children[i].unwrap()).view_rec_inversion(path.push_tail(i as usize), regions, m);
            assume(OwnerSubtree::implies(Self::relate_region_tracked_pred(regions), f));
            (res, f)
        } else {
            proof_from_false()
        }
    }*/

    /// Spec function: path1 is a prefix of path2
    pub open spec fn is_prefix_of<const N: usize>(
        prefix: TreePath<N>,
        path: TreePath<N>,
    ) -> bool {
        &&& prefix.len() <= path.len()
        &&& forall |i: int| 0 <= i < prefix.len() ==> prefix.index(i) == path.index(i)
    }

    /// Transitivity of is_prefix_of
    pub proof fn prefix_transitive<const N: usize>(
        p1: TreePath<N>,
        p2: TreePath<N>,
        p3: TreePath<N>,
    )
        requires
            Self::is_prefix_of(p1, p2),
            Self::is_prefix_of(p2, p3),
        ensures
            Self::is_prefix_of(p1, p3),
    {
        assert(p1.len() <= p3.len());
        assert forall |i: int| 0 <= i < p1.len() implies p1.index(i) == p3.index(i) by {
            assert(p1.index(i) == p2.index(i));
            assert(p2.index(i) == p3.index(i));
        };
    }

    pub proof fn prefix_push_different_indices(
        prefix: TreePath<CONST_NR_ENTRIES>,
        path: TreePath<CONST_NR_ENTRIES>,
        i: usize,
        j: usize,
    )
        requires
            prefix.inv(),
            path.inv(),
            i != j,
            Self::is_prefix_of(prefix.push_tail(i), path),
        ensures
            !Self::is_prefix_of(prefix.push_tail(j), path),
    {
        assert(path.index(prefix.len() as int) == i);
    }

    pub open spec fn is_at_pred(entry: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>)
        -> spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool
    {
        |entry0: EntryOwner<C>, path0: TreePath<CONST_NR_ENTRIES>| {
            path0 == path ==> entry0 == entry
        }
    }

    pub open spec fn path_in_tree_pred(path: TreePath<CONST_NR_ENTRIES>)
        -> spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool
    {
        |entry: EntryOwner<C>, path0: TreePath<CONST_NR_ENTRIES>|
            Self::is_prefix_of(path0, path) ==>
            !entry.is_node() ==>
            path == path0
    }

    pub proof fn is_at_pred_eq(path: TreePath<CONST_NR_ENTRIES>, entry1: EntryOwner<C>, entry2: EntryOwner<C>)
        requires
            entry1.inv(),
            OwnerSubtree::implies(Self::is_at_pred(entry1, path), Self::is_at_pred(entry2, path)),
        ensures
            entry1 == entry2,
    {
        assert(Self::is_at_pred(entry1, path)(entry1, path) ==>
               Self::is_at_pred(entry2, path)(entry1, path));
    }

    pub proof fn is_at_holds_when_on_wrong_path(
        subtree: OwnerSubtree<C>,
        root_path: TreePath<CONST_NR_ENTRIES>,
        dest_path: TreePath<CONST_NR_ENTRIES>,
        entry: EntryOwner<C>,
    )
        requires
            subtree.inv(),
            dest_path.inv(),
            !Self::is_prefix_of(root_path, dest_path),
            root_path.len() <= INC_LEVELS() - 1,
            root_path.len() == subtree.level,
        ensures
            subtree.tree_predicate_map(root_path, Self::is_at_pred(entry, dest_path)),
        decreases INC_LEVELS() - root_path.len()
    {
        if subtree.value.is_node() {
            assert forall |i: int| 0 <= i < NR_ENTRIES() implies
                subtree.children[i as int].unwrap().tree_predicate_map(root_path.push_tail(i as usize), Self::is_at_pred(entry, dest_path)) by {
                    Self::is_at_holds_when_on_wrong_path(subtree.children[i as int].unwrap(),
                        root_path.push_tail(i as usize), dest_path, entry);
                };
        }
    }

    /// Counterintuitive: the predicate is vacuously true when the path is not a prefix of the target path,
    /// because it is actually a liveness property: if we keep following the path, we will eventually reach it.
    /// This covers when we are not following it.
    pub proof fn path_in_tree_holds_when_on_wrong_path(
        subtree: OwnerSubtree<C>,
        root_path: TreePath<CONST_NR_ENTRIES>,
        dest_path: TreePath<CONST_NR_ENTRIES>,
    )
        requires
            subtree.inv(),
            dest_path.inv(),
            !Self::is_prefix_of(root_path, dest_path),
            root_path.len() <= INC_LEVELS() - 1,
            root_path.len() == subtree.level,
        ensures
            subtree.tree_predicate_map(root_path, Self::path_in_tree_pred(dest_path)),
        decreases INC_LEVELS() - root_path.len()
    {
        if subtree.value.is_node() {
            assert forall |i: int| 0 <= i < NR_ENTRIES() implies
                subtree.children[i as int].unwrap().tree_predicate_map(root_path.push_tail(i as usize), Self::path_in_tree_pred(dest_path)) by {
                    Self::path_in_tree_holds_when_on_wrong_path(subtree.children[i as int].unwrap(),
                        root_path.push_tail(i as usize), dest_path);
                };
        }
    }

    pub proof fn is_at_eq_rec(
        subtree: OwnerSubtree<C>,
        root_path: TreePath<CONST_NR_ENTRIES>,
        dest_path: TreePath<CONST_NR_ENTRIES>,
        entry1: EntryOwner<C>,
        entry2: EntryOwner<C>
    )
        requires
            subtree.inv(),
            dest_path.inv(),
            root_path.inv(),
            Self::is_prefix_of(root_path, dest_path),
            root_path.len() <= INC_LEVELS() - 1,
            root_path.len() == subtree.level,
            subtree.tree_predicate_map(root_path, Self::path_in_tree_pred(dest_path)),
            subtree.tree_predicate_map(root_path, Self::is_at_pred(entry1, dest_path)),
            subtree.tree_predicate_map(root_path, Self::is_at_pred(entry2, dest_path)),
        ensures
            entry1 == entry2,
        decreases INC_LEVELS() - root_path.len()
    {
        if root_path == dest_path {
            assert(subtree.value == entry1);
            assert(subtree.value == entry2);
            assert(entry1 == entry2);
        } else if subtree.level == INC_LEVELS() - 1 || !subtree.value.is_node() {
            proof_from_false()
        } else {
            assert(root_path.len() < dest_path.len()) by { admit() };
            let i = dest_path.index(root_path.len() as int);
            assert(0 <= i < NR_ENTRIES());
            assert(subtree.children[i as int] is Some);
            assert(Self::is_prefix_of(root_path.push_tail(i), dest_path));
            Self::is_at_eq_rec(subtree.children[i as int].unwrap(), root_path.push_tail(i as usize),
                dest_path, entry1, entry2);
        }
    }

    pub proof fn view_rec_inversion(self,
        path: TreePath<CONST_NR_ENTRIES>,
        regions: MetaRegionOwners,
        m: Mapping,
    ) -> (entry: EntryOwner<C>)
        requires
            self.0.inv(),
            path.len() == self.0.level,
            self.view_rec(path).contains(m),
            self.0.tree_predicate_map(path, Self::path_correct_pred()),
            self.0.tree_predicate_map(path, Self::relate_region_tracked_pred(regions)),
        ensures
            Self::is_prefix_of(path, entry.path),
            regions.slot_owners[frame_to_index(m.pa_range.start)].path_if_in_pt == Some(entry.path),
            m.va_range.start == vaddr(entry.path),
            m.page_size == page_size((INC_LEVELS() - entry.path.len()) as PagingLevel),
            entry.is_frame(),
            m.property == entry.frame.unwrap().prop,
            self.0.tree_predicate_map(path, Self::is_at_pred(entry, entry.path)),
            self.0.tree_predicate_map(path, Self::path_in_tree_pred(entry.path)),
            entry.inv(),
        decreases INC_LEVELS() - path.len()
    {
        if self.0.value.is_frame() {
            assert(Self::is_prefix_of(path, self.0.value.path));
            assert(self.0.tree_predicate_map(path, Self::is_at_pred(self.0.value, self.0.value.path)));
            assert(self.0.tree_predicate_map(path, Self::path_in_tree_pred(self.0.value.path)));
            self.0.value
        } else if self.0.value.is_node() {
            self.view_rec_contains(path, m);
            let i = self.view_rec_contains_choose(path, m);
            let entry = PageTableOwner(self.0.children[i].unwrap()).view_rec_inversion(path.push_tail(i as usize), regions, m);
            Self::prefix_transitive(path, path.push_tail(i as usize), entry.path);
            assert(self.0.tree_predicate_map(path, Self::is_at_pred(entry, entry.path))) by {
                assert forall |j: int| 0 <= j < NR_ENTRIES() && self.0.children[j] is Some implies 
                    self.0.children[j].unwrap().tree_predicate_map(path.push_tail(j as usize),
                        Self::is_at_pred(entry, entry.path))
                by {
                    if j != i {
                        assert(!Self::is_prefix_of(path.push_tail(j as usize), entry.path)) by {
                            Self::prefix_push_different_indices(path, entry.path, i as usize, j as usize);
                        }
                        Self::is_at_holds_when_on_wrong_path(self.0.children[j].unwrap(),
                            path.push_tail(j as usize), entry.path, entry);
                    }
                };
            };
            assert(self.0.tree_predicate_map(path, Self::path_in_tree_pred(entry.path))) by {
                assert forall |j: int| 0 <= j < NR_ENTRIES() && self.0.children[j] is Some implies 
                    self.0.children[j].unwrap().tree_predicate_map(path.push_tail(j as usize),
                        Self::path_in_tree_pred(entry.path))
                by {
                    if j != i {
                        assert(!Self::is_prefix_of(path.push_tail(j as usize), entry.path)) by {
                            Self::prefix_push_different_indices(path, entry.path, i as usize, j as usize);
                        }
                        Self::path_in_tree_holds_when_on_wrong_path(self.0.children[j].unwrap(),
                            path.push_tail(j as usize), entry.path);
                    }
                };
            };
            entry
        } else {
            proof_from_false()
        }
    }

    pub proof fn view_rec_inversion_unique(self,
        path: TreePath<CONST_NR_ENTRIES>,
        regions: MetaRegionOwners,
        m1: Mapping,
        m2: Mapping,
    )
        requires
            self.0.inv(),
            path.len() <= INC_LEVELS() - 1,
            path.len() == self.0.level,
            self.view_rec(path).contains(m1),
            self.view_rec(path).contains(m2),
            m1.pa_range.start == m2.pa_range.start,
            m1.inv(),
            m2.inv(),
            self.0.tree_predicate_map(path, Self::path_tracked_pred(regions)),
            self.0.tree_predicate_map(path, Self::path_correct_pred()),
            self.0.tree_predicate_map(path, Self::relate_region_tracked_pred(regions)),
        ensures
            m1 == m2,
    {
        let entry1 = self.view_rec_inversion(path, regions, m1);
        let entry2 = self.view_rec_inversion(path, regions, m2);

        assert(self.0.tree_predicate_map(path, Self::is_at_pred(entry1, entry1.path)));
        assert(self.0.tree_predicate_map(path, Self::is_at_pred(entry2, entry2.path)));

        Self::is_at_eq_rec(self.0, path, entry1.path, entry1, entry2);
    }

}

impl<C: PageTableConfig> Inv for PageTableOwner<C> {
    open spec fn inv(self) -> bool {
        &&& self.0.inv()
        &&& self.0.value.path.len() <= INC_LEVELS() - 1
        &&& self.0.value.path.inv()
        &&& self.0.value.path.len() == self.0.level
        &&& self.0.tree_predicate_map(self.0.value.path, Self::path_correct_pred())
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
