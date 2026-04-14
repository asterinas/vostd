use vstd::prelude::*;

use core::ops::Range;

use vstd::arithmetic::power2::pow2;
use vstd::seq::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;
use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::drop_tracking::*;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;
use vstd_extra::prelude::TreeNodeValue;

use crate::mm::{page_table::EntryOwner, Paddr, PagingLevel, Vaddr, MAX_NR_LEVELS};

use crate::mm::frame::frame_to_index;
use crate::mm::page_table::{page_size_spec, PageTableEntryTrait, PageTableGuard};

use crate::specs::arch::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::*;
use crate::specs::mm::page_table::cursor::page_size_lemmas::{
    lemma_page_size_divides, lemma_page_size_ge_page_size, lemma_page_size_spec_values,
};

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
    path: TreePath<NR_ENTRIES>,
    idx: int,
) -> usize/*        recommends
        0 < NR_LEVELS,
        path.len() <= NR_LEVELS,
        0 <= idx <= path.len(),*/

    decreases path.len() - idx,
    when 0 <= idx <= path.len()
{
    if idx == path.len() {
        0
    } else {
        let offset: usize = path.index(idx);
        (vaddr_make::<NR_LEVELS>(idx, offset) + rec_vaddr(path, idx + 1)) as usize
    }
}

pub open spec fn vaddr(path: TreePath<NR_ENTRIES>) -> usize {
    rec_vaddr(path, 0)
}

/// page_size is monotonically increasing in its argument.
pub proof fn page_size_monotonic(a: PagingLevel, b: PagingLevel)
    requires
        1 <= a <= NR_LEVELS + 1,
        1 <= b <= NR_LEVELS + 1,
        a <= b,
    ensures
        page_size(a) <= page_size(b),
{
    if a == b {
    } else {
        let ps_a = page_size(a);
        let ps_b = page_size(b);

        assert(ps_a == page_size_spec(a));
        assert(ps_b == page_size_spec(b));

        lemma_page_size_ge_page_size(a);
        lemma_page_size_ge_page_size(b);
        assert(ps_a > 0);
        assert(ps_b > 0);

        lemma_page_size_divides(a, b);
        assert(ps_b % ps_a == 0);

        assert(ps_a <= ps_b) by {
            if ps_b < ps_a {
                vstd::arithmetic::div_mod::lemma_small_mod(ps_b as nat, ps_a as nat);
                assert(ps_b % ps_a == ps_b);
                assert(ps_b % ps_a == 0);
                assert(false);
            }
        }
    }
}

/// Sibling paths (same prefix, different last index) have disjoint VA ranges,
/// separated by at least the child page size.
///
/// Generic in `C` only so the proof can reach
/// `PageTableOwner<C>::lemma_vaddr_push_tail_eq`; the body does not depend
/// on `C`.
pub proof fn sibling_paths_disjoint<C: PageTableConfig>(
    prefix: TreePath<NR_ENTRIES>,
    j: usize,
    k: usize,
    size: usize,
)
    requires
        prefix.inv(),
        prefix.len() < INC_LEVELS - 1,
        j < NR_ENTRIES,
        k < NR_ENTRIES,
        j != k,
        size == page_size((INC_LEVELS - prefix.len() - 1) as PagingLevel),
    ensures
        vaddr(prefix.push_tail(j)) + size <= vaddr(prefix.push_tail(k))
        || vaddr(prefix.push_tail(k)) + size <= vaddr(prefix.push_tail(j)),
{
    PageTableOwner::<C>::lemma_vaddr_push_tail_eq(prefix, j);
    PageTableOwner::<C>::lemma_vaddr_push_tail_eq(prefix, k);
    let s = size as int;
    let vp = vaddr(prefix) as int;
    let vj = vaddr(prefix.push_tail(j)) as int;
    let vk = vaddr(prefix.push_tail(k)) as int;
    if j < k {
        assert(vj + s <= vk) by (nonlinear_arith)
            requires vj == vp + (j as int) * s,
                     vk == vp + (k as int) * s,
                     j < k, s >= 0;
    } else {
        assert(vk + s <= vj) by (nonlinear_arith)
            requires vj == vp + (j as int) * s,
                     vk == vp + (k as int) * s,
                     k < j, s >= 0;
    }
}

impl<C: PageTableConfig, const L: usize> TreeNodeValue<L> for EntryOwner<C> {
    open spec fn default(lv: nat) -> Self {
        Self {
            in_scope: false,
            path: TreePath::new(Seq::empty()),
            parent_level: (INC_LEVELS - lv) as PagingLevel,
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
            &&& child.unwrap().parent_level == self.node.unwrap().level
        } else {
            &&& child is None
        }
    }

    proof fn default_preserves_rel_children(self, lv: nat) {
        admit()
    }
}

pub const INC_LEVELS: usize = NR_LEVELS + 1;

/// `OwnerSubtree` is a tree `Node` (from `vstd_extra::ghost_tree`) containing `EntryOwner`s.
/// It lives in a tree of maximum depth 5. Page table nodes can be at levels 0-3, and their entries are their children at the next
/// level down. This means that level 4, the lowest level, can only contain frame entries as it consists of the entries of level 1 page tables.
///
/// Level correspondences: tree level 0 ==> path length 0 ==> level 4 page table
///                        tree level 1 ==> path length 1 ==> level 3 page table (the level 4 page table does not map frames directly)
///                        tree level 2 ==> path length 2 ==> level 2 page table or frame mapped by level 3 table
///                        tree level 3 ==> path length 3 ==> level 1 page table or frame mapped by level 2 table
///                        tree level 4 ==> path length 4 ==> frame mapped by level 1 table
pub type OwnerSubtree<C> = Node<EntryOwner<C>, NR_ENTRIES, INC_LEVELS>;

/// Specifies that `owner` is the ghost owner of a newly allocated empty page table node at the given level.
/// Captures the structural post-conditions of `PageTableNode::alloc`.
pub open spec fn allocated_empty_node_owner<C: PageTableConfig>(owner: OwnerSubtree<C>, level: PagingLevel) -> bool {
    &&& owner.inv()
    &&& owner.value.is_node()
    &&& owner.value.path == TreePath::<NR_ENTRIES>::new(Seq::empty())
    &&& owner.value.parent_level == level
    &&& owner.value.node.unwrap().level == level - 1
    &&& owner.value.node.unwrap().inv()
    &&& !owner.value.node.unwrap().children_perm.value().all(|child: C::E| child.is_present())
    &&& forall |i: int| #![auto] 0 <= i < NR_ENTRIES ==> {
        &&& owner.children[i] is Some
        &&& owner.children[i].unwrap().value.is_absent()
        &&& !owner.children[i].unwrap().value.in_scope
        &&& owner.children[i].unwrap().value.inv()
        &&& owner.children[i].unwrap().value.path == owner.value.path.push_tail(i as usize)
    }
    &&& forall |i: int| #![auto] 0 <= i < NR_ENTRIES ==>
        owner.children[i].unwrap().value.match_pte(
            owner.value.node.unwrap().children_perm.value()[i],
            owner.children[i].unwrap().value.parent_level,
        )
    &&& forall |i: int| #![auto] 0 <= i < NR_ENTRIES ==>
        owner.children[i].unwrap().value.parent_level == owner.value.node.unwrap().level
}

pub struct PageTableOwner<C: PageTableConfig>(pub OwnerSubtree<C>);

impl<C: PageTableConfig> PageTableOwner<C> {

    /// For a top-level (root) page table, entries at indices outside of
    /// `C::TOP_LEVEL_INDEX_RANGE_spec()` are absent. This ensures that
    /// UserPtConfig and KernelPtConfig page tables manage disjoint portions
    /// of the virtual address space.
    pub open spec fn top_level_indices_absent(self) -> bool {
        let range = C::TOP_LEVEL_INDEX_RANGE_spec();
        self.0.value.is_node() ==>
        forall|i: int|
            #![trigger self.0.children[i]]
            0 <= i < NR_ENTRIES
            && !(range.start <= i < range.end)
            ==> self.0.children[i] is Some
                && self.0.children[i].unwrap().value.is_absent()
    }

    pub open spec fn view_rec(self, path: TreePath<NR_ENTRIES>) -> Set<Mapping>
        decreases INC_LEVELS - path.len() when self.0.inv() && path.len() <= INC_LEVELS - 1
    {
        if self.0.value.is_frame() {
            let vaddr = vaddr(path);
            let pt_level = INC_LEVELS - path.len();
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
        } else if self.0.value.is_node() && path.len() < INC_LEVELS - 1 {
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

    pub proof fn view_rec_contains(self, path: TreePath<NR_ENTRIES>, m: Mapping)
        requires
            self.0.inv(),
            path.len() < INC_LEVELS - 1,
            path.len() == self.0.level,
            self.view_rec(path).contains(m),
            self.0.value.is_node()
        ensures
            exists|i:int| #![auto] 0 <= i < self.0.children.len() &&
            self.0.children[i] is Some &&
            PageTableOwner(self.0.children[i].unwrap()).view_rec(path.push_tail(i as usize)).contains(m)
    { }

    pub proof fn view_rec_contains_choose(self, path: TreePath<NR_ENTRIES>, m: Mapping) -> (i: int)
        requires
            self.0.inv(),
            path.len() < INC_LEVELS - 1,
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

    /// Closed-form for `vaddr(path.push_tail(i))` by case-split on `path.len() ∈ {0,1,2,3}`.
    #[verifier::rlimit(400)]
    pub proof fn lemma_vaddr_push_tail_eq(path: TreePath<NR_ENTRIES>, i: usize)
        requires
            path.inv(),
            path.len() < INC_LEVELS - 1,
            i < NR_ENTRIES,
        ensures
            vaddr(path.push_tail(i)) as int
                == vaddr(path) as int
                    + (i as int)
                        * (page_size((INC_LEVELS - path.len() - 1) as PagingLevel) as int),
            vaddr(path) as int
                + (i as int + 1)
                    * (page_size((INC_LEVELS - path.len() - 1) as PagingLevel) as int)
                <= usize::MAX as int,
    {
        broadcast use TreePath::push_tail_property;
        broadcast use TreePath::index_satisfies_elem_inv;
        lemma_page_size_spec_values();
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        let pt = path.push_tail(i);
        if path.len() >= 1 {
            Self::lemma_vaddr_path_alignment_and_bound(path);
        }
        if path.len() == 0 {
            assert(rec_vaddr(path, 0) == 0);
            assert(pt.len() == 1);
            assert(rec_vaddr(pt, 1) == 0);
            assert(rec_vaddr(pt, 0) == (vaddr_make::<NR_LEVELS>(0, i) + 0) as usize);
            assert(vaddr_make::<NR_LEVELS>(0, i) == 0x80_0000_0000usize * i) by (compute);
            assert(page_size(4) == 0x80_0000_0000usize);
            assert(0x80_0000_0000usize * (i + 1) <= usize::MAX) by (nonlinear_arith)
                requires i < 512;
        } else if path.len() == 1 {
            let i0 = path.index(0);
            assert(0 <= i0 < NR_ENTRIES);
            assert(rec_vaddr(path, 1) == 0);
            assert(rec_vaddr(path, 0) == vaddr_make::<NR_LEVELS>(0, i0) as usize);
            assert(vaddr_make::<NR_LEVELS>(0, i0) == 0x80_0000_0000usize * i0) by (compute);
            assert(rec_vaddr(path, 0) == 0x80_0000_0000usize * i0);
            assert(pt.len() == 2);
            assert(pt.index(0) == i0);
            assert(pt.index(1) == i);
            assert(rec_vaddr(pt, 2) == 0);
            assert(rec_vaddr(pt, 1) == vaddr_make::<NR_LEVELS>(1, i) as usize);
            assert(vaddr_make::<NR_LEVELS>(1, i) == 0x4000_0000usize * i) by (compute);
            assert(rec_vaddr(pt, 0) as int == (0x80_0000_0000usize * i0) as int + (0x4000_0000usize * i) as int);
            assert(page_size(3) == 0x4000_0000usize);
            assert(0x80_0000_0000usize * i0 + 0x4000_0000usize * (i + 1) <= usize::MAX) by (nonlinear_arith)
                requires i0 < 512, i < 512;
        } else if path.len() == 2 {
            let i0 = path.index(0); let i1 = path.index(1);
            assert(0 <= i0 < NR_ENTRIES); assert(0 <= i1 < NR_ENTRIES);
            assert(rec_vaddr(path, 2) == 0);
            assert(rec_vaddr(path, 1) == vaddr_make::<NR_LEVELS>(1, i1) as usize);
            assert(rec_vaddr(path, 0) == (vaddr_make::<NR_LEVELS>(0, i0) + vaddr_make::<NR_LEVELS>(1, i1)) as usize);
            assert(vaddr_make::<NR_LEVELS>(0, i0) == 0x80_0000_0000usize * i0) by (compute);
            assert(vaddr_make::<NR_LEVELS>(1, i1) == 0x4000_0000usize * i1) by (compute);
            assert(pt.len() == 3);
            assert(pt.index(0) == i0); assert(pt.index(1) == i1); assert(pt.index(2) == i);
            assert(rec_vaddr(pt, 3) == 0);
            assert(rec_vaddr(pt, 2) == vaddr_make::<NR_LEVELS>(2, i) as usize);
            assert(rec_vaddr(pt, 1) == (vaddr_make::<NR_LEVELS>(1, i1) + vaddr_make::<NR_LEVELS>(2, i)) as usize);
            assert(rec_vaddr(pt, 0) == (vaddr_make::<NR_LEVELS>(0, i0)
                + vaddr_make::<NR_LEVELS>(1, i1) + vaddr_make::<NR_LEVELS>(2, i)) as usize);
            assert(vaddr_make::<NR_LEVELS>(2, i) == 0x20_0000usize * i) by (compute);
            assert(page_size(2) == 0x20_0000usize);
            assert(0x80_0000_0000usize * i0 + 0x4000_0000usize * i1 + 0x20_0000usize * (i + 1)
                <= usize::MAX) by (nonlinear_arith)
                requires i0 < 512, i1 < 512, i < 512;
        } else {
            assert(path.len() == 3);
            let i0 = path.index(0); let i1 = path.index(1); let i2 = path.index(2);
            assert(0 <= i0 < NR_ENTRIES); assert(0 <= i1 < NR_ENTRIES); assert(0 <= i2 < NR_ENTRIES);
            assert(rec_vaddr(path, 3) == 0);
            assert(rec_vaddr(path, 2) == vaddr_make::<NR_LEVELS>(2, i2) as usize);
            assert(rec_vaddr(path, 1) == (vaddr_make::<NR_LEVELS>(1, i1) + vaddr_make::<NR_LEVELS>(2, i2)) as usize);
            assert(rec_vaddr(path, 0) == (vaddr_make::<NR_LEVELS>(0, i0)
                + vaddr_make::<NR_LEVELS>(1, i1) + vaddr_make::<NR_LEVELS>(2, i2)) as usize);
            assert(vaddr_make::<NR_LEVELS>(0, i0) == 0x80_0000_0000usize * i0) by (compute);
            assert(vaddr_make::<NR_LEVELS>(1, i1) == 0x4000_0000usize * i1) by (compute);
            assert(vaddr_make::<NR_LEVELS>(2, i2) == 0x20_0000usize * i2) by (compute);
            assert(pt.len() == 4);
            assert(pt.index(0) == i0); assert(pt.index(1) == i1);
            assert(pt.index(2) == i2); assert(pt.index(3) == i);
            assert(rec_vaddr(pt, 4) == 0);
            assert(rec_vaddr(pt, 3) == vaddr_make::<NR_LEVELS>(3, i) as usize);
            assert(rec_vaddr(pt, 2) == (vaddr_make::<NR_LEVELS>(2, i2) + vaddr_make::<NR_LEVELS>(3, i)) as usize);
            assert(rec_vaddr(pt, 1) == (vaddr_make::<NR_LEVELS>(1, i1)
                + vaddr_make::<NR_LEVELS>(2, i2) + vaddr_make::<NR_LEVELS>(3, i)) as usize);
            assert(rec_vaddr(pt, 0) == (vaddr_make::<NR_LEVELS>(0, i0)
                + vaddr_make::<NR_LEVELS>(1, i1) + vaddr_make::<NR_LEVELS>(2, i2)
                + vaddr_make::<NR_LEVELS>(3, i)) as usize);
            assert(vaddr_make::<NR_LEVELS>(3, i) == 0x1000usize * i) by (compute);
            assert(page_size(1) == 0x1000usize);
            assert(0x80_0000_0000usize * i0 + 0x4000_0000usize * i1
                + 0x20_0000usize * i2 + 0x1000usize * (i + 1) <= usize::MAX) by (nonlinear_arith)
                requires i0 < 512, i1 < 512, i2 < 512, i < 512;
        }
    }

    pub proof fn view_rec_vaddr_range(self, path: TreePath<NR_ENTRIES>, m: Mapping)
        requires
            self.0.inv(),
            path.inv(),
            path.len() <= INC_LEVELS - 1,
            path.len() == self.0.level,
            self.0.value.parent_level == (INC_LEVELS - self.0.level) as PagingLevel,
            self.view_rec(path).contains(m),
        ensures
            vaddr(path) <= m.va_range.start,
            m.va_range.start < m.va_range.end,
            m.va_range.end <= vaddr(path) + page_size((INC_LEVELS - path.len()) as PagingLevel),
        decreases INC_LEVELS - path.len(),
    {
        lemma_page_size_spec_values();
        if self.0.value.is_frame() {
            Self::lemma_vaddr_path_alignment_and_bound(path);
            let frame = self.0.value.frame.unwrap();
            let pt_level = (INC_LEVELS - path.len()) as PagingLevel;
            let expected = Mapping {
                va_range: Range {
                    start: vaddr(path),
                    end: (vaddr(path) + page_size(pt_level)) as Vaddr,
                },
                pa_range: Range {
                    start: frame.mapped_pa,
                    end: (frame.mapped_pa + page_size(pt_level)) as Paddr,
                },
                page_size: page_size(pt_level),
                property: frame.prop,
            };
            assert(self.view_rec(path) =~= set![expected]);
            assert(m == expected);
            assert(page_size(pt_level) > 0);
        } else if self.0.value.is_node() && path.len() < INC_LEVELS - 1 {
            let i = choose|i: int|
                #![trigger self.0.children[i]]
                0 <= i < self.0.children.len()
                    && self.0.children[i] is Some
                    && PageTableOwner(self.0.children[i].unwrap())
                        .view_rec(path.push_tail(i as usize)).contains(m);
            let child = PageTableOwner(self.0.children[i].unwrap());
            path.push_tail_preserves_inv(i as usize);
            path.push_tail_property_len(i as usize);
            child.view_rec_vaddr_range(path.push_tail(i as usize), m);
            Self::lemma_vaddr_push_tail_eq(path, i as usize);

            let parent_ps = page_size((INC_LEVELS - path.len()) as PagingLevel) as int;
            let child_ps = page_size((INC_LEVELS - path.len() - 1) as PagingLevel) as int;
            vstd::arithmetic::power2::lemma2_to64();
            vstd::arithmetic::power2::lemma2_to64_rest();
            if path.len() == 0 {
                assert(parent_ps == 0x1_0000_0000_0000);
                assert(child_ps == 0x80_0000_0000);
            } else if path.len() == 1 {
                assert(parent_ps == 0x80_0000_0000);
                assert(child_ps == 0x4000_0000);
            } else if path.len() == 2 {
                assert(parent_ps == 0x4000_0000);
                assert(child_ps == 0x20_0000);
            } else {
                assert(path.len() == 3);
                assert(parent_ps == 0x20_0000);
                assert(child_ps == 0x1000);
            }
            assert(parent_ps == 512 * child_ps) by (nonlinear_arith)
                requires
                    (parent_ps == 0x1_0000_0000_0000 && child_ps == 0x80_0000_0000)
                    || (parent_ps == 0x80_0000_0000 && child_ps == 0x4000_0000)
                    || (parent_ps == 0x4000_0000 && child_ps == 0x20_0000)
                    || (parent_ps == 0x20_0000 && child_ps == 0x1000);
            assert((i + 1) * child_ps <= 512 * child_ps) by (nonlinear_arith)
                requires 0 <= i < 512, child_ps >= 0;
        }
    }

    pub proof fn view_rec_disjoint_vaddrs(self, path: TreePath<NR_ENTRIES>, m1: Mapping, m2: Mapping)
        requires
            self.0.inv(),
            path.inv(),
            path.len() <= INC_LEVELS - 1,
            path.len() == self.0.level,
            self.0.value.parent_level == (INC_LEVELS - self.0.level) as PagingLevel,
            self.view_rec(path).contains(m1),
            self.view_rec(path).contains(m2),
            m1 != m2,
        ensures
            m1.va_range.end <= m2.va_range.start || m2.va_range.end <= m1.va_range.start
        decreases INC_LEVELS - path.len()
    {
        broadcast use group_set_properties;

        if self.0.value.is_frame() {
            assert(self.view_rec(path).is_singleton());
        } else if self.0.value.is_node() {
            self.view_rec_contains(path, m1);
            self.view_rec_contains(path, m2);

            let i1 = self.view_rec_contains_choose(path, m1);
            let i2 = self.view_rec_contains_choose(path, m2);

            path.push_tail_preserves_inv(i1 as usize);
            path.push_tail_preserves_inv(i2 as usize);
            path.push_tail_property_len(i1 as usize);
            path.push_tail_property_len(i2 as usize);

            if i1 == i2 {
                PageTableOwner(self.0.children[i1].unwrap()).view_rec_disjoint_vaddrs(path.push_tail(i1 as usize), m1, m2);
            } else {
                let child_ps = page_size((INC_LEVELS - path.len() - 1) as PagingLevel);
                PageTableOwner(self.0.children[i1].unwrap()).view_rec_vaddr_range(path.push_tail(i1 as usize), m1);
                PageTableOwner(self.0.children[i2].unwrap()).view_rec_vaddr_range(path.push_tail(i2 as usize), m2);
                if i1 < i2 {
                    sibling_paths_disjoint::<C>(path, i1 as usize, i2 as usize, child_ps);
                } else {
                    sibling_paths_disjoint::<C>(path, i2 as usize, i1 as usize, child_ps);
                }
            }
        }
    }

    /// `view_rec` is finite: bounded by NR_ENTRIES branching and INC_LEVELS depth.
    /// Proven by induction on `INC_LEVELS - path.len()`, collapsing the
    /// `Set::new` existential into a `flatten` of a finite domain-map.
    pub proof fn view_rec_finite(self, path: TreePath<NR_ENTRIES>)
        requires
            self.0.inv(),
            path.len() <= INC_LEVELS - 1,
            path.len() == self.0.level,
        ensures
            self.view_rec(path).finite(),
        decreases INC_LEVELS - path.len()
    {
        broadcast use group_set_properties;

        if self.0.value.is_frame() {
            // Singleton set is finite.
            assert(self.view_rec(path).finite());
        } else if self.0.value.is_node() && path.len() < INC_LEVELS - 1 {
            // Recurse into each child: establish finiteness for each Some child.
            assert forall |i: int| 0 <= i < NR_ENTRIES && self.0.children[i] is Some implies
                PageTableOwner(self.0.children[i].unwrap())
                    .view_rec(path.push_tail(i as usize)).finite()
            by {
                let child = self.0.children[i].unwrap();
                // From self.0.inv(): inv_children gives child.level == self.0.level + 1
                // and child.inv() (since path.len() < INC_LEVELS - 1 means not a leaf).
                PageTableOwner(child).view_rec_finite(path.push_tail(i as usize));
            };

            // Domain map: map each index to the child's view_rec set (or empty).
            let f = |i: int| -> Set<Mapping> {
                if 0 <= i < NR_ENTRIES && self.0.children[i] is Some {
                    PageTableOwner(self.0.children[i].unwrap())
                        .view_rec(path.push_tail(i as usize))
                } else {
                    Set::<Mapping>::empty()
                }
            };
            let dom: Set<int> = Set::new(|i: int| 0 <= i < NR_ENTRIES);
            assert(dom =~= int::range_set(0int, NR_ENTRIES as int));
            vstd::set_lib::range_set_properties::<int>(0int, NR_ENTRIES as int);
            assert(dom.finite());
            dom.lemma_map_finite(f);
            let ss = dom.map(f);
            assert(ss.finite());

            // Every element of ss is finite.
            assert forall |s: Set<Mapping>| ss.contains(s) implies s.finite() by {
                let i = choose |i: int| dom.contains(i) && f(i) == s;
                if 0 <= i < NR_ENTRIES && self.0.children[i] is Some {
                    // finiteness established above
                } else {
                    assert(s =~= Set::<Mapping>::empty());
                }
            };

            ss.lemma_flatten_finite();
            // view_rec(path) = { m | exists i, children[i] is Some ∧ child.view_rec(...).contains(m) }
            //                = union over i of f(i)
            //                = ss.flatten()
            assert(self.view_rec(path) =~= ss.flatten()) by {
                assert forall |m: Mapping| self.view_rec(path).contains(m) implies
                    ss.flatten().contains(m)
                by {
                    let i = choose |i: int|
                        #![trigger self.0.children[i]]
                        0 <= i < self.0.children.len() &&
                        self.0.children[i] is Some &&
                        PageTableOwner(self.0.children[i].unwrap())
                            .view_rec(path.push_tail(i as usize)).contains(m);
                    assert(dom.contains(i));
                    assert(ss.contains(f(i)));
                    assert(f(i).contains(m));
                };
                assert forall |m: Mapping| ss.flatten().contains(m) implies
                    self.view_rec(path).contains(m)
                by {
                    let s = choose |s: Set<Mapping>| ss.contains(s) && s.contains(m);
                    let i = choose |i: int| dom.contains(i) && f(i) == s;
                    assert(0 <= i < NR_ENTRIES && self.0.children[i] is Some);
                };
            };
        } else {
            // Empty set
            assert(self.view_rec(path) =~= Set::<Mapping>::empty());
        }
    }

    /// Every mapping in `view_rec` has `page_size ∈ {4K, 2M, 1G}`.
    ///
    /// Structural induction using the invariant that `parent_level` of each
    /// subtree equals `INC_LEVELS - tree_level`, chained through `rel_children`.
    /// At a leaf frame, `parent_level < NR_LEVELS` (from the tightened
    /// `inv_base`) ensures the page size is one of the allowed values.
    pub proof fn view_rec_mapping_page_size(self, path: TreePath<NR_ENTRIES>)
        requires
            self.0.inv(),
            path.len() <= INC_LEVELS - 1,
            path.len() == self.0.level,
            self.0.value.parent_level == (INC_LEVELS - self.0.level) as PagingLevel,
        ensures
            forall |m: Mapping| #[trigger] self.view_rec(path).contains(m) ==>
                set![4096usize, 2097152usize, 1073741824usize].contains(m.page_size),
        decreases INC_LEVELS - path.len()
    {
        if self.0.value.is_frame() {
            // `inv_base` (tightened) gives `1 <= parent_level < NR_LEVELS`.
            // Combined with `parent_level == INC_LEVELS - path.len()`,
            // `INC_LEVELS - path.len() ∈ {1, 2, 3}`, and `page_size` lands in
            // {4K, 2M, 1G} by the arithmetic lemma.
            lemma_page_size_spec_values();
        } else if self.0.value.is_node() && path.len() < INC_LEVELS - 1 {
            // `inv_base` for nodes: `parent_level == node.level + 1`.
            // So `node.level == parent_level - 1 == INC_LEVELS - self.0.level - 1`.
            // `rel_children`: child's parent_level == node.level.
            // Child's tree_level == self.0.level + 1. Hence
            // `child.parent_level == INC_LEVELS - child.level`.
            assert forall |m: Mapping| #[trigger] self.view_rec(path).contains(m) implies
                set![4096usize, 2097152usize, 1073741824usize].contains(m.page_size)
            by {
                let i = choose |i: int|
                    #![trigger self.0.children[i]]
                    0 <= i < self.0.children.len() &&
                    self.0.children[i] is Some &&
                    PageTableOwner(self.0.children[i].unwrap())
                        .view_rec(path.push_tail(i as usize)).contains(m);
                let child = self.0.children[i].unwrap();
                PageTableOwner(child).view_rec_mapping_page_size(path.push_tail(i as usize));
            };
        } else {
            // Empty set.
        }
    }

    /// Path-level arithmetic facts consumed by `view_rec_mapping_inv`:
    /// every `vaddr(path)` is aligned to `page_size(INC_LEVELS - path.len())`
    /// and `vaddr(path) + page_size(...)` cannot overflow usize.
    ///
    /// Proved by case analysis on `path.len() ∈ {0, 1, 2, 3, 4}`, unrolling
    /// `rec_vaddr` and using concrete `pow2` values.
    #[verifier::rlimit(400)]
    proof fn lemma_vaddr_path_alignment_and_bound(path: TreePath<NR_ENTRIES>)
        requires
            path.inv(),
            path.len() <= INC_LEVELS - 1,
            1 <= INC_LEVELS - path.len() <= NR_LEVELS,
        ensures
            vaddr(path) % page_size((INC_LEVELS - path.len()) as PagingLevel) == 0,
            vaddr(path) + page_size((INC_LEVELS - path.len()) as PagingLevel) <= usize::MAX,
    {
        lemma_page_size_spec_values();
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        broadcast use TreePath::index_satisfies_elem_inv;
        // NR_LEVELS = 4; each index is < 512.
        // rec_vaddr values per path.len():
        //   0: 0
        //   1: i0 * 2^39
        //   2: i0 * 2^39 + i1 * 2^30
        //   3: i0 * 2^39 + i1 * 2^30 + i2 * 2^21
        //   4: i0 * 2^39 + i1 * 2^30 + i2 * 2^21 + i3 * 2^12
        // page_size(INC_LEVELS - path.len()) per path.len():
        //   1: 2^39, 2: 2^30, 3: 2^21, 4: 2^12
        // In each case every term is a multiple of the smallest (= page_size).
        if path.len() == 0 {
            assert(rec_vaddr(path, 0) == 0);
        } else if path.len() == 1 {
            let i0 = path.index(0);
            assert(0 <= i0 < NR_ENTRIES);
            assert(rec_vaddr(path, 1) == 0);
            assert(rec_vaddr(path, 0) == (vaddr_make::<NR_LEVELS>(0, i0) + rec_vaddr(path, 1)) as usize);
            assert(vaddr_make::<NR_LEVELS>(0, i0) == 0x80_0000_0000usize * i0) by (compute);
            assert(rec_vaddr(path, 0) == 0x80_0000_0000usize * i0);
            assert(page_size(4) == 0x80_0000_0000usize);
            assert((0x80_0000_0000usize * i0) % 0x80_0000_0000 == 0) by (nonlinear_arith);
            assert(0x80_0000_0000usize * i0 + 0x80_0000_0000 <= usize::MAX) by (nonlinear_arith)
                requires i0 < 512;
        } else if path.len() == 2 {
            let i0 = path.index(0); let i1 = path.index(1);
            assert(0 <= i0 < NR_ENTRIES); assert(0 <= i1 < NR_ENTRIES);
            assert(rec_vaddr(path, 2) == 0);
            assert(rec_vaddr(path, 1) == (vaddr_make::<NR_LEVELS>(1, i1) + rec_vaddr(path, 2)) as usize);
            assert(rec_vaddr(path, 0) == (vaddr_make::<NR_LEVELS>(0, i0) + rec_vaddr(path, 1)) as usize);
            assert(vaddr_make::<NR_LEVELS>(0, i0) == 0x80_0000_0000usize * i0) by (compute);
            assert(vaddr_make::<NR_LEVELS>(1, i1) == 0x4000_0000usize * i1) by (compute);
            let s = (0x80_0000_0000usize * i0 + 0x4000_0000usize * i1) as int;
            assert(rec_vaddr(path, 0) == s);
            assert(page_size(3) == 0x4000_0000usize);
            assert(s % 0x4000_0000 == 0) by (nonlinear_arith)
                requires s == 0x80_0000_0000 * i0 + 0x4000_0000 * i1;
            assert(s + 0x4000_0000 <= usize::MAX) by (nonlinear_arith)
                requires s == 0x80_0000_0000 * i0 + 0x4000_0000 * i1, i0 < 512, i1 < 512;
        } else if path.len() == 3 {
            let i0 = path.index(0); let i1 = path.index(1); let i2 = path.index(2);
            assert(0 <= i0 < NR_ENTRIES); assert(0 <= i1 < NR_ENTRIES); assert(0 <= i2 < NR_ENTRIES);
            assert(rec_vaddr(path, 3) == 0);
            assert(rec_vaddr(path, 2) == (vaddr_make::<NR_LEVELS>(2, i2) + rec_vaddr(path, 3)) as usize);
            assert(rec_vaddr(path, 1) == (vaddr_make::<NR_LEVELS>(1, i1) + rec_vaddr(path, 2)) as usize);
            assert(rec_vaddr(path, 0) == (vaddr_make::<NR_LEVELS>(0, i0) + rec_vaddr(path, 1)) as usize);
            assert(vaddr_make::<NR_LEVELS>(0, i0) == 0x80_0000_0000usize * i0) by (compute);
            assert(vaddr_make::<NR_LEVELS>(1, i1) == 0x4000_0000usize * i1) by (compute);
            assert(vaddr_make::<NR_LEVELS>(2, i2) == 0x20_0000usize * i2) by (compute);
            let s = (0x80_0000_0000usize * i0 + 0x4000_0000usize * i1 + 0x20_0000usize * i2) as int;
            assert(rec_vaddr(path, 0) == s);
            assert(page_size(2) == 0x20_0000usize);
            assert(s % 0x20_0000 == 0) by (nonlinear_arith)
                requires s == 0x80_0000_0000 * i0 + 0x4000_0000 * i1 + 0x20_0000 * i2;
            assert(s + 0x20_0000 <= usize::MAX) by (nonlinear_arith)
                requires s == 0x80_0000_0000 * i0 + 0x4000_0000 * i1 + 0x20_0000 * i2,
                i0 < 512, i1 < 512, i2 < 512;
        } else {
            assert(path.len() == 4);
            let i0 = path.index(0); let i1 = path.index(1);
            let i2 = path.index(2); let i3 = path.index(3);
            assert(0 <= i0 < NR_ENTRIES); assert(0 <= i1 < NR_ENTRIES);
            assert(0 <= i2 < NR_ENTRIES); assert(0 <= i3 < NR_ENTRIES);
            assert(rec_vaddr(path, 4) == 0);
            assert(rec_vaddr(path, 3) == (vaddr_make::<NR_LEVELS>(3, i3) + rec_vaddr(path, 4)) as usize);
            assert(rec_vaddr(path, 2) == (vaddr_make::<NR_LEVELS>(2, i2) + rec_vaddr(path, 3)) as usize);
            assert(rec_vaddr(path, 1) == (vaddr_make::<NR_LEVELS>(1, i1) + rec_vaddr(path, 2)) as usize);
            assert(rec_vaddr(path, 0) == (vaddr_make::<NR_LEVELS>(0, i0) + rec_vaddr(path, 1)) as usize);
            assert(vaddr_make::<NR_LEVELS>(0, i0) == 0x80_0000_0000usize * i0) by (compute);
            assert(vaddr_make::<NR_LEVELS>(1, i1) == 0x4000_0000usize * i1) by (compute);
            assert(vaddr_make::<NR_LEVELS>(2, i2) == 0x20_0000usize * i2) by (compute);
            assert(vaddr_make::<NR_LEVELS>(3, i3) == 0x1000usize * i3) by (compute);
            let s = (0x80_0000_0000usize * i0 + 0x4000_0000usize * i1
                + 0x20_0000usize * i2 + 0x1000usize * i3) as int;
            assert(rec_vaddr(path, 0) == s);
            assert(page_size(1) == 0x1000usize);
            assert(s % 0x1000 == 0) by (nonlinear_arith)
                requires s == 0x80_0000_0000 * i0 + 0x4000_0000 * i1 + 0x20_0000 * i2 + 0x1000 * i3;
            assert(s + 0x1000 <= usize::MAX) by (nonlinear_arith)
                requires s == 0x80_0000_0000 * i0 + 0x4000_0000 * i1 + 0x20_0000 * i2 + 0x1000 * i3,
                i0 < 512, i1 < 512, i2 < 512, i3 < 512;
        }
    }

    /// Every mapping in `view_rec` satisfies `Mapping::inv()`.
    ///
    /// Structural induction on the subtree. At a leaf frame, the PA-side
    /// clauses follow from `FrameEntryOwner::inv_base`, the VA-size clause
    /// by construction, the page-size clause from the tightened
    /// `parent_level < NR_LEVELS` constraint plus the arithmetic identity
    /// `page_size(k) ∈ {4K, 2M, 1G}` for `k ∈ {1, 2, 3}`, and VA alignment
    /// + no-overflow via `lemma_vaddr_path_alignment_and_bound`.
    pub proof fn view_rec_mapping_inv(self, path: TreePath<NR_ENTRIES>)
        requires
            self.0.inv(),
            path.inv(),
            path.len() <= INC_LEVELS - 1,
            path.len() == self.0.level,
            self.0.value.parent_level == (INC_LEVELS - self.0.level) as PagingLevel,
        ensures
            forall |m: Mapping| #[trigger] self.view_rec(path).contains(m) ==> m.inv(),
        decreases INC_LEVELS - path.len()
    {
        if self.0.value.is_frame() {
            lemma_page_size_spec_values();
            let frame = self.0.value.frame.unwrap();
            let pt_level = (INC_LEVELS - path.len()) as PagingLevel;
            // Establish path.inv() → indices are all < NR_ENTRIES.
            // The frame's owner invariant carries path == self.0.value.path
            // with .inv() via inv_base. We rely on path being this value.
            Self::lemma_vaddr_path_alignment_and_bound(path);
            // Build the unique mapping explicitly and prove its inv(), then
            // lift to the singleton set. Doing it this way avoids Verus
            // trigger flakiness inside `assert forall`.
            let m = Mapping {
                va_range: Range {
                    start: vaddr(path),
                    end: (vaddr(path) + page_size(pt_level)) as Vaddr,
                },
                pa_range: Range {
                    start: frame.mapped_pa,
                    end: (frame.mapped_pa + page_size(pt_level)) as Paddr,
                },
                page_size: page_size(pt_level),
                property: frame.prop,
            };
            assert(self.view_rec(path) =~= set![m]);
            assert(set![4096usize, 2097152usize, 1073741824usize].contains(m.page_size));
            // End-alignment: `start + page_size` with `start % page_size == 0`
            // and `page_size > 0` implies `(start + page_size) % page_size == 0`.
            let ps = page_size(pt_level) as int;
            assert(ps > 0);
            assert((frame.mapped_pa as int + ps) % ps == 0) by (nonlinear_arith)
                requires (frame.mapped_pa as int) % ps == 0, ps > 0;
            assert((vaddr(path) as int + ps) % ps == 0) by (nonlinear_arith)
                requires (vaddr(path) as int) % ps == 0, ps > 0;
            assert(m.inv());
        } else if self.0.value.is_node() && path.len() < INC_LEVELS - 1 {
            assert forall |m: Mapping| #[trigger] self.view_rec(path).contains(m) implies m.inv()
            by {
                let i = choose |i: int|
                    #![trigger self.0.children[i]]
                    0 <= i < self.0.children.len() &&
                    self.0.children[i] is Some &&
                    PageTableOwner(self.0.children[i].unwrap())
                        .view_rec(path.push_tail(i as usize)).contains(m);
                let child = self.0.children[i].unwrap();
                path.push_tail_preserves_inv(i as usize);
                PageTableOwner(child).view_rec_mapping_inv(path.push_tail(i as usize));
            };
        } else {
            // Empty set — trivially true.
        }
    }

    /// An absent entry contributes no mappings - view_rec returns the empty set.
    pub proof fn view_rec_absent_empty(self, path: TreePath<NR_ENTRIES>)
        requires
            self.0.inv(),
            self.0.value.is_absent(),
            path.len() <= INC_LEVELS - 1,
        ensures
            self.view_rec(path) =~= set![],
    { }

    /// A node with nr_children == 0 has no present PTEs, so all children are absent
    /// and the subtree contributes no mappings.
    ///
    /// Axiom: the link between `nr_children` and the count of present PTEs is maintained
    /// by `Entry::replace` / `Entry::new` but not yet formalised as a `NodeOwner` invariant.
    pub axiom fn view_rec_nr_children_zero_empty(self, path: TreePath<NR_ENTRIES>)
        requires
            self.0.inv(),
            self.0.value.is_node(),
            self.0.value.node.unwrap().meta_own.nr_children.value() == 0,
            path.len() <= INC_LEVELS - 1,
            path.len() == self.0.level,
        ensures
            self.view_rec(path) =~= set![];

    pub open spec fn metaregion_sound_pred(regions: MetaRegionOwners)
        -> (spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool) {
        |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>| entry.metaregion_sound(regions)
    }

    pub open spec fn metaregion_sound(self, regions: MetaRegionOwners) -> bool
        decreases INC_LEVELS - self.0.level when self.0.inv()
    {
        self.0.tree_predicate_map(self.0.value.path, Self::metaregion_sound_pred(regions))
    }

    /// `PageTableOwner::metaregion_sound` is preserved across regions changes
    /// that (a) keep `slot_owners` exactly equal and (b) only grow the `slots`
    /// map (existing keys preserved with the same values). Both conditions are
    /// satisfied by `Entry::to_ref` and similar `borrow_paddr` operations.
    pub proof fn metaregion_sound_preserved_slot_owners_eq(
        self,
        r0: MetaRegionOwners,
        r1: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.metaregion_sound(r0),
            r0.slot_owners == r1.slot_owners,
            forall |k: usize| r0.slots.contains_key(k) ==> #[trigger] r1.slots.contains_key(k),
            forall |k: usize| r0.slots.contains_key(k) ==> r0.slots[k] == #[trigger] r1.slots[k],
        ensures
            self.metaregion_sound(r1),
    {
        Self::metaregion_sound_preserved_slot_owners_eq_subtree(
            self.0, self.0.value.path, r0, r1);
    }

    /// Recursive helper: same preservation property, applied to an arbitrary subtree.
    pub proof fn metaregion_sound_preserved_slot_owners_eq_subtree(
        subtree: OwnerSubtree<C>,
        path: TreePath<NR_ENTRIES>,
        r0: MetaRegionOwners,
        r1: MetaRegionOwners,
    )
        requires
            subtree.inv(),
            subtree.tree_predicate_map(path, Self::metaregion_sound_pred(r0)),
            r0.slot_owners == r1.slot_owners,
            forall |k: usize| r0.slots.contains_key(k) ==> #[trigger] r1.slots.contains_key(k),
            forall |k: usize| r0.slots.contains_key(k) ==> r0.slots[k] == #[trigger] r1.slots[k],
        ensures
            subtree.tree_predicate_map(path, Self::metaregion_sound_pred(r1)),
        decreases INC_LEVELS - subtree.level
    {
        // The root entry: its metaregion_sound transfers via the per-entry lemma.
        subtree.value.metaregion_sound_slot_owners_only(r0, r1);
        // Recursively for each Some child.
        if subtree.level < INC_LEVELS - 1 {
            assert forall |i: int|
                #![trigger subtree.children[i]]
                0 <= i < NR_ENTRIES && subtree.children[i] is Some
                implies subtree.children[i].unwrap().tree_predicate_map(
                    path.push_tail(i as usize),
                    Self::metaregion_sound_pred(r1),
                ) by {
                Self::metaregion_sound_preserved_slot_owners_eq_subtree(
                    subtree.children[i].unwrap(),
                    path.push_tail(i as usize),
                    r0, r1,
                );
            }
        }
    }

    /// `PageTableOwner::metaregion_sound` is preserved across a single
    /// `slot_owner` change at index `changed_idx`, provided no entry in the
    /// tree references `changed_idx` (neither as its primary slot nor as a
    /// huge-frame sub-page slot). This is the right shape for `borrow`-style
    /// operations that bump `raw_count` at one slot.
    pub proof fn metaregion_sound_preserved_one_slot_changed(
        self,
        r0: MetaRegionOwners,
        r1: MetaRegionOwners,
        changed_idx: usize,
    )
        requires
            self.inv(),
            self.metaregion_sound(r0),
            forall |i: usize| #![trigger r1.slot_owners[i]]
                i != changed_idx ==> r0.slot_owners[i] == r1.slot_owners[i],
            r0.slot_owners.dom() =~= r1.slot_owners.dom(),
            forall |k: usize| r0.slots.contains_key(k) ==> #[trigger] r1.slots.contains_key(k),
            forall |k: usize| r0.slots.contains_key(k) ==> r0.slots[k] == #[trigger] r1.slots[k],
            // No tree entry's primary slot is at changed_idx.
            self.0.tree_predicate_map(
                self.0.value.path,
                |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                    e.meta_slot_paddr() is Some
                        ==> frame_to_index(e.meta_slot_paddr().unwrap()) != changed_idx,
            ),
            // For huge-frame entries, none of their sub-page slots is at changed_idx
            // either; provided as a separate condition because the per-entry lemma
            // requires it.
            self.0.tree_predicate_map(
                self.0.value.path,
                |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                    e.is_frame() && e.parent_level > 1 ==> {
                        let pa = e.frame.unwrap().mapped_pa;
                        let nr_pages = page_size(e.parent_level) / PAGE_SIZE;
                        forall |j: usize| 0 < j < nr_pages ==> {
                            let sub_idx = #[trigger] frame_to_index((pa + j * PAGE_SIZE) as usize);
                            sub_idx != changed_idx
                            || (
                                r1.slots.contains_key(sub_idx)
                                && r1.slot_owners[sub_idx].inner_perms.ref_count.value() != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                            )
                        }
                    },
            ),
        ensures
            self.metaregion_sound(r1),
    {
        Self::metaregion_sound_preserved_one_slot_changed_subtree(
            self.0, self.0.value.path, r0, r1, changed_idx);
    }

    pub proof fn metaregion_sound_preserved_one_slot_changed_subtree(
        subtree: OwnerSubtree<C>,
        path: TreePath<NR_ENTRIES>,
        r0: MetaRegionOwners,
        r1: MetaRegionOwners,
        changed_idx: usize,
    )
        requires
            subtree.inv(),
            subtree.tree_predicate_map(path, Self::metaregion_sound_pred(r0)),
            forall |i: usize| #![trigger r1.slot_owners[i]]
                i != changed_idx ==> r0.slot_owners[i] == r1.slot_owners[i],
            r0.slot_owners.dom() =~= r1.slot_owners.dom(),
            forall |k: usize| r0.slots.contains_key(k) ==> #[trigger] r1.slots.contains_key(k),
            forall |k: usize| r0.slots.contains_key(k) ==> r0.slots[k] == #[trigger] r1.slots[k],
            subtree.tree_predicate_map(
                path,
                |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                    e.meta_slot_paddr() is Some
                        ==> frame_to_index(e.meta_slot_paddr().unwrap()) != changed_idx,
            ),
            subtree.tree_predicate_map(
                path,
                |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                    e.is_frame() && e.parent_level > 1 ==> {
                        let pa = e.frame.unwrap().mapped_pa;
                        let nr_pages = page_size(e.parent_level) / PAGE_SIZE;
                        forall |j: usize| 0 < j < nr_pages ==> {
                            let sub_idx = #[trigger] frame_to_index((pa + j * PAGE_SIZE) as usize);
                            sub_idx != changed_idx
                            || (
                                r1.slots.contains_key(sub_idx)
                                && r1.slot_owners[sub_idx].inner_perms.ref_count.value() != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                            )
                        }
                    },
            ),
        ensures
            subtree.tree_predicate_map(path, Self::metaregion_sound_pred(r1)),
        decreases INC_LEVELS - subtree.level
    {
        subtree.value.metaregion_sound_one_slot_changed(r0, r1, changed_idx);
        if subtree.level < INC_LEVELS - 1 {
            assert forall |i: int|
                #![trigger subtree.children[i]]
                0 <= i < NR_ENTRIES && subtree.children[i] is Some
                implies subtree.children[i].unwrap().tree_predicate_map(
                    path.push_tail(i as usize),
                    Self::metaregion_sound_pred(r1),
                ) by {
                Self::metaregion_sound_preserved_one_slot_changed_subtree(
                    subtree.children[i].unwrap(),
                    path.push_tail(i as usize),
                    r0, r1, changed_idx,
                );
            }
        }
    }

    /// Predicate: all entries in the tree have their paths correctly tracked in regions.
    /// Strengthened form: `path_if_in_pt == Some(entry.path)` (not just `is Some`).
    pub open spec fn path_tracked_pred(regions: MetaRegionOwners)
        -> spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool
    {
        |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>| {
            // Only nodes track path_if_in_pt (frames can be shared).
            entry.is_node() && entry.meta_slot_paddr() is Some ==> {
                &&& regions.slot_owners.contains_key(frame_to_index(entry.meta_slot_paddr().unwrap()))
                &&& regions.slot_owners[frame_to_index(entry.meta_slot_paddr().unwrap())].path_if_in_pt
                        == Some(entry.path)
            }
        }
    }

    pub open spec fn relate_region_tracked_pred(regions: MetaRegionOwners)
        -> spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool
    {
        |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>| {
            &&& entry.meta_slot_paddr() is Some
            &&& regions.slot_owners.contains_key(frame_to_index(entry.meta_slot_paddr().unwrap()))
            &&& regions.slot_owners[frame_to_index(entry.meta_slot_paddr().unwrap())].path_if_in_pt is Some
            &&& regions.slot_owners[frame_to_index(entry.meta_slot_paddr().unwrap())].path_if_in_pt.unwrap() == path
        }
    }

    pub open spec fn path_correct_pred()
        -> spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool
    {
        |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>| {
            entry.path == path
        }
    }

    pub open spec fn not_in_scope_pred()
        -> spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool
    {
        |entry: EntryOwner<C>, _path: TreePath<NR_ENTRIES>| !entry.in_scope
    }

    /// Every entry in an OwnerSubtree has `!in_scope`.
    /// Follows from `EntryOwner::inv()` including `!in_scope`, propagated through the tree.
    pub proof fn tree_not_in_scope(subtree: OwnerSubtree<C>, path: TreePath<NR_ENTRIES>)
        requires
            subtree.inv(),
        ensures
            subtree.tree_predicate_map(path, Self::not_in_scope_pred()),
        decreases INC_LEVELS - subtree.level,
    {
        // subtree.inv() => inv_node() => value.inv() => !value.in_scope
        if subtree.level < INC_LEVELS - 1 {
            assert forall |i: int|
                0 <= i < subtree.children.len()
                && (#[trigger] subtree.children[i]) is Some implies
                subtree.children[i].unwrap().tree_predicate_map(
                    path.push_tail(i as usize), Self::not_in_scope_pred())
            by {
                Self::tree_not_in_scope(
                    subtree.children[i].unwrap(), path.push_tail(i as usize));
            };
        }
    }

    /// All mappings in a subtree's `view_rec` have
    /// `page_size <= page_size(INC_LEVELS - path.len())`.
    pub proof fn view_rec_page_size_bound(self, path: TreePath<NR_ENTRIES>, m: Mapping)
        requires
            self.0.inv(),
            path.len() <= INC_LEVELS - 1,
            self.view_rec(path).contains(m),
        ensures
            m.page_size <= page_size((INC_LEVELS - path.len()) as PagingLevel),
        decreases INC_LEVELS - path.len(),
    {
        if self.0.value.is_node() && path.len() < INC_LEVELS - 1 {
            let i = choose|i: int|
                #![auto]
                0 <= i < self.0.children.len()
                    && self.0.children[i] is Some
                    && PageTableOwner(self.0.children[i].unwrap())
                        .view_rec(path.push_tail(i as usize)).contains(m);
            PageTableOwner(self.0.children[i].unwrap())
                .view_rec_page_size_bound(path.push_tail(i as usize), m);
            page_size_monotonic(
                (INC_LEVELS - path.len() - 1) as PagingLevel,
                (INC_LEVELS - path.len()) as PagingLevel,
            );
        }
    }

    /// For a node subtree, all mappings have
    /// `page_size <= page_size(INC_LEVELS - path.len() - 1)`.
    pub proof fn view_rec_node_page_size_bound(self, path: TreePath<NR_ENTRIES>, m: Mapping)
        requires
            self.0.inv(),
            self.0.value.is_node(),
            path.len() < INC_LEVELS - 1,
            self.view_rec(path).contains(m),
        ensures
            m.page_size <= page_size(((INC_LEVELS - path.len()) - 1) as PagingLevel),
        decreases INC_LEVELS - path.len(),
    {
        let i = choose|i: int|
            #![auto]
            0 <= i < self.0.children.len()
                && self.0.children[i] is Some
                && PageTableOwner(self.0.children[i].unwrap())
                    .view_rec(path.push_tail(i as usize)).contains(m);
        PageTableOwner(self.0.children[i].unwrap())
            .view_rec_page_size_bound(path.push_tail(i as usize), m);
    }

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
        prefix: TreePath<NR_ENTRIES>,
        path: TreePath<NR_ENTRIES>,
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

    pub open spec fn is_at_pred(entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>)
        -> spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool
    {
        |entry0: EntryOwner<C>, path0: TreePath<NR_ENTRIES>| {
            path0 == path ==> entry0 == entry
        }
    }

    pub open spec fn path_in_tree_pred(path: TreePath<NR_ENTRIES>)
        -> spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool
    {
        |entry: EntryOwner<C>, path0: TreePath<NR_ENTRIES>|
            Self::is_prefix_of(path0, path) ==>
            !entry.is_node() ==>
            path == path0
    }

    pub proof fn is_at_pred_eq(path: TreePath<NR_ENTRIES>, entry1: EntryOwner<C>, entry2: EntryOwner<C>)
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
        root_path: TreePath<NR_ENTRIES>,
        dest_path: TreePath<NR_ENTRIES>,
        entry: EntryOwner<C>,
    )
        requires
            subtree.inv(),
            dest_path.inv(),
            !Self::is_prefix_of(root_path, dest_path),
            root_path.len() <= INC_LEVELS - 1,
            root_path.len() == subtree.level,
        ensures
            subtree.tree_predicate_map(root_path, Self::is_at_pred(entry, dest_path)),
        decreases INC_LEVELS - root_path.len()
    {
        if subtree.value.is_node() {
            assert forall |i: int| 0 <= i < NR_ENTRIES implies
                (#[trigger] subtree.children[i as int]).unwrap().tree_predicate_map(root_path.push_tail(i as usize), Self::is_at_pred(entry, dest_path)) by {
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
        root_path: TreePath<NR_ENTRIES>,
        dest_path: TreePath<NR_ENTRIES>,
    )
        requires
            subtree.inv(),
            dest_path.inv(),
            !Self::is_prefix_of(root_path, dest_path),
            root_path.len() <= INC_LEVELS - 1,
            root_path.len() == subtree.level,
        ensures
            subtree.tree_predicate_map(root_path, Self::path_in_tree_pred(dest_path)),
        decreases INC_LEVELS - root_path.len()
    {
        if subtree.value.is_node() {
            assert forall |i: int| 0 <= i < NR_ENTRIES implies
                (#[trigger] subtree.children[i as int]).unwrap().tree_predicate_map(root_path.push_tail(i as usize), Self::path_in_tree_pred(dest_path)) by {
                    Self::path_in_tree_holds_when_on_wrong_path(subtree.children[i as int].unwrap(),
                        root_path.push_tail(i as usize), dest_path);
                };
        }
    }

    /// If a subtree satisfies `inv()` and the root entry's `path` field equals the structural root
    /// path, then the subtree satisfies `tree_predicate_map(path, path_correct_pred())`.
    /// This is proved by induction using `rel_children` (which stores `child.path == parent.path.push_tail(i)`)
    /// from `Node::inv_children()`.
    pub proof fn inv_implies_path_correct(
        subtree: OwnerSubtree<C>,
        path: TreePath<NR_ENTRIES>,
    )
        requires
            subtree.inv(),
            path.inv(),
            path.len() <= INC_LEVELS - 1,
            path.len() == subtree.level,
            subtree.value.path == path,
        ensures
            subtree.tree_predicate_map(path, Self::path_correct_pred()),
        decreases INC_LEVELS - path.len()
    {
        if subtree.level < INC_LEVELS - 1 {
            assert forall|i: int| #![auto]
                0 <= i < NR_ENTRIES && subtree.children[i] is Some implies
                subtree.children[i].unwrap().tree_predicate_map(
                    path.push_tail(i as usize),
                    Self::path_correct_pred(),
                ) by {
                let child = subtree.children[i].unwrap();
                // From Node::inv_children + rel_children: child.value.path == path.push_tail(i)
                assert(child.value.path == path.push_tail(i as usize)) by {
                    assert(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::rel_children(subtree.value, i, Some(child.value)));
                    if subtree.value.is_node() {
                        assert(child.value.path == subtree.value.path.push_tail(i as usize));
                    } else {
                        // rel_children with is_not_node() requires child is None → contradiction
                        assert(false);
                    }
                };
                assert(child.inv());
                assert(child.level == subtree.level + 1);
                assert((path.push_tail(i as usize)).len() == child.level) by {
                    path.push_tail_property_len(i as usize);
                };
                Self::inv_implies_path_correct(child, path.push_tail(i as usize));
            };
        }
    }

    /// For entries in a subtree rooted at `path_j` whose `path_j` is not a prefix of
    /// `old_entry.path`, no entry in the subtree shares a physical address with `old_entry`.
    ///
    /// Proof sketch: by `inv_implies_path_correct`, every entry `e` at structural position `p`
    /// has `e.path == p`.  Since `!is_prefix_of(path_j, old_entry.path)`, no structural position
    /// in the subtree equals `old_entry.path`.  Combined with `path_tracked_pred`
    /// uniqueness (via `same_paddr_implies_same_path`), same paddr would force same path — contradiction.
    /// Entries in a subtree whose path is disjoint from `old_entry`'s path
    /// have different physical addresses from `old_entry`.
    /// Uses `metaregion_sound` (which includes `path_if_in_pt` for nodes) to derive
    /// that same-paddr entries would share `path_if_in_pt`, contradicting path disjointness.
    pub axiom fn neq_old_from_path_disjoint(
        subtree: OwnerSubtree<C>,
        path_j: TreePath<NR_ENTRIES>,
        old_entry: EntryOwner<C>,
        regions: MetaRegionOwners,
    )
        requires
            subtree.inv(),
            subtree.value.path == path_j,
            path_j.len() == subtree.level,
            path_j.inv(),
            path_j.len() <= INC_LEVELS - 1,
            subtree.tree_predicate_map(path_j, Self::metaregion_sound_pred(regions)),
            old_entry.is_node(),
            old_entry.meta_slot_paddr() is Some,
            regions.slot_owners[
                frame_to_index(old_entry.meta_slot_paddr().unwrap())
            ].path_if_in_pt == Some(old_entry.path),
            !Self::is_prefix_of(path_j, old_entry.path),
        ensures
            subtree.tree_predicate_map(
                path_j,
                |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| e.meta_slot_paddr_neq(old_entry),
            );

    pub proof fn is_at_eq_rec(
        subtree: OwnerSubtree<C>,
        root_path: TreePath<NR_ENTRIES>,
        dest_path: TreePath<NR_ENTRIES>,
        entry1: EntryOwner<C>,
        entry2: EntryOwner<C>
    )
        requires
            subtree.inv(),
            dest_path.inv(),
            root_path.inv(),
            Self::is_prefix_of(root_path, dest_path),
            root_path.len() <= INC_LEVELS - 1,
            root_path.len() == subtree.level,
            subtree.tree_predicate_map(root_path, Self::path_in_tree_pred(dest_path)),
            subtree.tree_predicate_map(root_path, Self::is_at_pred(entry1, dest_path)),
            subtree.tree_predicate_map(root_path, Self::is_at_pred(entry2, dest_path)),
        ensures
            entry1 == entry2,
        decreases INC_LEVELS - root_path.len()
    {
        if root_path == dest_path {
            assert(subtree.value == entry1);
            assert(subtree.value == entry2);
            assert(entry1 == entry2);
        } else if subtree.level == INC_LEVELS - 1 || !subtree.value.is_node() {
            proof_from_false()
        } else {
            assert(root_path.len() < dest_path.len()) by {
                assert(root_path.len() <= dest_path.len());
                if root_path.len() == dest_path.len() {
                    assert(root_path =~= dest_path) by {
                        assert(root_path.0.len() == dest_path.0.len());
                        assert forall |i: int| 0 <= i < root_path.0.len() implies #[trigger] root_path.0[i] == dest_path.0[i] by {
                            assert(root_path.index(i) == dest_path.index(i));
                        };
                    };
                    assert(root_path == dest_path);
                    assert(false);
                }
            };
            let i = dest_path.index(root_path.len() as int);
            assert(0 <= i < NR_ENTRIES);
            assert(subtree.children[i as int] is Some);
            assert(Self::is_prefix_of(root_path.push_tail(i), dest_path));
            Self::is_at_eq_rec(subtree.children[i as int].unwrap(), root_path.push_tail(i as usize),
                dest_path, entry1, entry2);
        }
    }

    pub proof fn view_rec_inversion(self,
        path: TreePath<NR_ENTRIES>,
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
            m.page_size == page_size((INC_LEVELS - entry.path.len()) as PagingLevel),
            entry.is_frame(),
            m.property == entry.frame.unwrap().prop,
            self.0.tree_predicate_map(path, Self::is_at_pred(entry, entry.path)),
            self.0.tree_predicate_map(path, Self::path_in_tree_pred(entry.path)),
            entry.inv(),
        decreases INC_LEVELS - path.len()
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
                assert forall |j: int| 0 <= j < NR_ENTRIES && #[trigger] self.0.children[j] is Some implies
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
                assert forall |j: int| 0 <= j < NR_ENTRIES && #[trigger] self.0.children[j] is Some implies
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
        path: TreePath<NR_ENTRIES>,
        regions: MetaRegionOwners,
        m1: Mapping,
        m2: Mapping,
    )
        requires
            self.0.inv(),
            path.len() <= INC_LEVELS - 1,
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
        &&& self.0.value.is_node()
        &&& self.0.value.path.len() <= INC_LEVELS - 1
        &&& self.0.value.path.inv()
        &&& self.0.value.path.len() == self.0.level
        // (A) Ghost-tree depth determines the paging-level of the parent.
        //     For the root (depth 0) this is `INC_LEVELS == NR_LEVELS + 1`.
        &&& self.0.value.parent_level == (INC_LEVELS - self.0.level) as PagingLevel
        // (B) The node's internal `tree_level` tracks the ghost-tree depth.
        //     Combined with `NodeOwner::inv`'s `tree_level == INC_LEVELS - level - 1`
        //     this pins the node's paging level: `level == NR_LEVELS - path.len()`.
        &&& self.0.value.node.unwrap().tree_level == self.0.value.path.len()
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
