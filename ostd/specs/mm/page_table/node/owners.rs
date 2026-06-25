use vstd::cell::pcell_maybe_uninit;
use vstd::prelude::*;

use vstd::cell;
use vstd::simple_pptr::*;

use crate::arch::mm::PagingConsts;
use crate::mm::frame::meta::mapping::meta_to_frame;
use crate::mm::frame::meta::{META_SLOT_SIZE, MetaSlot};
use crate::mm::kspace::FRAME_METADATA_RANGE;
use crate::mm::kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR};
use crate::mm::paddr_to_vaddr;
use crate::mm::page_table::PageTableGuard;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::{MAX_NR_PAGES, MAX_PADDR, NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::mm::frame::mapping::{frame_to_index, max_meta_slots, meta_addr};
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::owners::INC_LEVELS;

use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::ghost_tree::TreePath;
use vstd_extra::ownership::*;

verus! {

// ─── Present-PTE counting ──────────────────────────────────────────────────────
// The intended meaning of `nr_children`: the number of *present* PTEs in the
// node's `children_perm` array. `metaregion_sound_node` ties `nr_children` to
// `count_present(children_perm.value())` (a settled-node invariant), which lets
// the `nr_children_*_slot_bound` boundary facts be proven rather than axiomatized.
/// Number of present PTEs among the first `n` entries of `s`.
pub open spec fn count_present_upto<E: PageTableEntryTrait>(s: Seq<E>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        count_present_upto(s, n - 1) + if s[n - 1].is_present() {
            1int
        } else {
            0int
        }
    }
}

/// Number of present PTEs in `s`.
pub open spec fn count_present<E: PageTableEntryTrait>(s: Seq<E>) -> int {
    count_present_upto(s, s.len() as int)
}

/// `count_present_upto` is between `0` and `n`.
pub proof fn lemma_count_present_upto_bound<E: PageTableEntryTrait>(s: Seq<E>, n: int)
    requires
        0 <= n,
    ensures
        0 <= count_present_upto(s, n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_count_present_upto_bound(s, n - 1);
    }
}

/// An absent slot below `n` makes the count strictly less than `n`.
pub proof fn lemma_count_present_upto_absent<E: PageTableEntryTrait>(s: Seq<E>, n: int, idx: int)
    requires
        0 <= idx < n,
        !s[idx].is_present(),
    ensures
        count_present_upto(s, n) < n,
    decreases n,
{
    lemma_count_present_upto_bound(s, n - 1);
    if idx < n - 1 {
        lemma_count_present_upto_absent(s, n - 1, idx);
    }
}

/// A present slot below `n` makes the count at least `1`.
pub proof fn lemma_count_present_upto_present<E: PageTableEntryTrait>(s: Seq<E>, n: int, idx: int)
    requires
        0 <= idx < n,
        s[idx].is_present(),
    ensures
        count_present_upto(s, n) >= 1,
    decreases n,
{
    lemma_count_present_upto_bound(s, n - 1);
    if idx < n - 1 {
        lemma_count_present_upto_present(s, n - 1, idx);
    }
}

/// Updating slot `idx` (with `idx < n`) shifts the count by the change in that
/// slot's present-indicator.
pub proof fn lemma_count_present_upto_update<E: PageTableEntryTrait>(
    s: Seq<E>,
    n: int,
    idx: int,
    pte: E,
)
    requires
        0 <= idx < n <= s.len(),
    ensures
        count_present_upto(s.update(idx, pte), n) == count_present_upto(s, n) - (
        if s[idx].is_present() {
            1int
        } else {
            0int
        }) + (if pte.is_present() {
            1int
        } else {
            0int
        }),
    decreases n,
{
    let s2 = s.update(idx, pte);
    if n - 1 == idx {
        // The first `idx` entries are unchanged.
        assert(count_present_upto(s2, n - 1) == count_present_upto(s, n - 1)) by {
            lemma_count_present_upto_unchanged(s, s2, n - 1, idx);
        }
        assert(s2[n - 1] == pte);
    } else {
        lemma_count_present_upto_update(s, n - 1, idx, pte);
        assert(s2[n - 1] == s[n - 1]);
    }
}

/// A zero present-count up to `n` means every slot below `n` is absent.
pub proof fn lemma_count_present_upto_zero_all_absent<E: PageTableEntryTrait>(s: Seq<E>, n: int)
    requires
        count_present_upto(s, n) == 0,
        0 <= n,
    ensures
        forall|k: int| 0 <= k < n ==> !#[trigger] s[k].is_present(),
    decreases n,
{
    if n > 0 {
        lemma_count_present_upto_bound(s, n - 1);
        lemma_count_present_upto_zero_all_absent(s, n - 1);
    }
}

/// If two sequences agree on `[0, n)`, their counts up to `n` are equal.
pub proof fn lemma_count_present_upto_unchanged<E: PageTableEntryTrait>(
    s: Seq<E>,
    s2: Seq<E>,
    n: int,
    idx: int,
)
    requires
        0 <= n <= idx,
        forall|k: int| 0 <= k < n ==> s[k] == s2[k],
    ensures
        count_present_upto(s2, n) == count_present_upto(s, n),
    decreases n,
{
    if n > 0 {
        lemma_count_present_upto_unchanged(s, s2, n - 1, idx);
    }
}

pub tracked struct PageMetaOwner {
    pub nr_children: pcell_maybe_uninit::PointsTo<u16>,
    pub stray: pcell_maybe_uninit::PointsTo<bool>,
}

impl Inv for PageMetaOwner {
    open spec fn inv(self) -> bool {
        &&& self.nr_children.is_init()
        &&& 0 <= self.nr_children.value() <= NR_ENTRIES
        &&& self.stray.is_init()
    }
}

pub ghost struct PageMetaModel {
    pub nr_children: u16,
    pub stray: bool,
}

impl Inv for PageMetaModel {
    open spec fn inv(self) -> bool {
        true
    }
}

impl View for PageMetaOwner {
    type V = PageMetaModel;

    open spec fn view(&self) -> <Self as View>::V {
        PageMetaModel { nr_children: self.nr_children.value(), stray: self.stray.value() }
    }
}

impl InvView for PageMetaOwner {
    proof fn view_preserves_inv(self) {
    }
}

impl<C: PageTableConfig> OwnerOf for PageTablePageMeta<C> {
    type Owner = PageMetaOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.nr_children.id() == owner.nr_children.id()
        &&& self.stray.id() == owner.stray.id()
        &&& 0 <= owner.nr_children.value() <= NR_ENTRIES
    }
}

/// # Verification Design
/// The owner type for a page table node. It contains:
/// - `meta_own`, a `PageMetaOwner`, which holds the permissions for node-specific
///   metadata fields, `nr_children` and `stray`
/// - `children_perm` is an array permission for the underlying frame in which the node
///   is allocated, interpreted as an array of `NR_ENTRIES` page table entries
/// - `slot_index` identifies the underlying frame's index in the metadata region
/// - Each node is a page table with a level between 1 and 4 (on x86); `level` tracks
///   the level of this node.
/// - `tree_level` is the level field of the `ghost_tree::Node` that carries this object.
///   Carried here for convenience, though it can be computed from `level`.
pub tracked struct NodeOwner<C: PageTableConfig> {
    pub meta_own: PageMetaOwner,
    pub children_perm: array_ptr::PointsTo<C::E, NR_ENTRIES>,
    pub level: PagingLevel,
    pub tree_level: int,
    pub slot_index: usize,
}

impl<C: PageTableConfig> Inv for NodeOwner<C> {
    open spec fn inv(self) -> bool {
        &&& self.meta_own.inv()
        &&& 0 <= self.meta_own.nr_children.value() <= NR_ENTRIES
        &&& 1 <= self.level <= NR_LEVELS
        &&& self.children_perm.is_init_all()
        &&& self.children_perm.addr() == paddr_to_vaddr(meta_to_frame(meta_addr(self.slot_index)))
        &&& self.tree_level == INC_LEVELS - self.level - 1
        &&& self.slot_index < max_meta_slots() as usize
        &&& FRAME_METADATA_RANGE.start <= meta_addr(self.slot_index) < FRAME_METADATA_RANGE.end
        &&& meta_addr(self.slot_index) % META_SLOT_SIZE == 0
        &&& meta_to_frame(meta_addr(self.slot_index)) < VMALLOC_BASE_VADDR
            - LINEAR_MAPPING_BASE_VADDR
        &&& meta_to_frame(meta_addr(self.slot_index)) < MAX_PADDR
        &&& meta_to_frame(meta_addr(self.slot_index)) == self.children_perm.addr()
        &&& self.slot_index == frame_to_index(meta_to_frame(meta_addr(self.slot_index)))
    }
}

impl<C: PageTableConfig> NodeOwner<C> {
    /// The meta address of this node's slot, computed from `slot_index`.
    /// Always equals `self.meta_perm.addr()` under `inv()`.
    pub open spec fn meta_addr_self(self) -> Vaddr {
        meta_addr(self.slot_index)
    }

    /// Reconstructs a metadata cast_ptr from `regions` at `self.slot_index`.
    /// The borrow-model home of the node's metadata perm.
    pub open spec fn meta_perm_of(
        self,
        regions: MetaRegionOwners,
    ) -> vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<PageTablePageMeta<C>>> {
        vstd_extra::cast_ptr::PointsTo::new_spec(
            regions.slots[self.slot_index],
            regions.slot_owners[self.slot_index].inner_perms,
        )
    }

    /// Regions-tied invariants that used to live in `NodeOwner::inv()` via
    /// the now-removed `meta_perm` field. Establishes the bridge between
    /// the NodeOwner and the slot perm parked in regions.
    pub open spec fn metaregion_sound_node(self, regions: MetaRegionOwners) -> bool {
        let idx = self.slot_index;
        &&& regions.slots.contains_key(idx)
        &&& self.meta_perm_of(regions).is_init()
        &&& self.meta_perm_of(regions).wf(&self.meta_perm_of(regions).inner_perms)
        &&& self.meta_perm_of(regions).value().metadata.wf(self.meta_own)
        &&& self.level == self.meta_perm_of(regions).value().metadata.level
        &&& self.meta_own.nr_children.id() == self.meta_perm_of(
            regions,
        ).value().metadata.nr_children.id()
        // A page-table node's slot is tracked with `PageTable` usage (set at
        // allocation via `get_node_from_unused_spec`). This discriminates node
        // slots from data-frame slots (`Frame`/MMIO) by `usage` alone, so a
        // freshly-allocated node (whose slot was `UNUSED`) can't collide with an
        // existing live node — giving `alloc_if_none`/`split` the parent≠child
        // slot distinctness without a PointsTo-linearity axiom.
        &&& regions.slot_owners[self.slot_index].usage
            == PageUsage::PageTable
        // `nr_children` counts the present PTEs in `children_perm`. A settled-node
        // invariant (it is momentarily broken mid-`replace`/`alloc_if_none`, between
        // the PTE write and the counter update, which is why it lives here rather
        // than in `inv()`). Lets `nr_children_*_slot_bound` be proven, not axiomatized.
        &&& self.count_consistent()
    }

    /// `nr_children` equals the number of present PTEs in `children_perm`.
    /// Held by a settled node (see `metaregion_sound_node`'s use site).
    pub open spec fn count_consistent(self) -> bool {
        self.meta_own.nr_children.value() == count_present(self.children_perm.value())
    }
}

impl<C: PageTableConfig> NodeOwner<C> {
    // TODO: this is a bizzare structure; `set_children_perm` needs to actually be
    // defined to satisfy the axiom, which can then be deleted.
    pub uninterp spec fn set_children_perm(self, idx: usize, pte: C::E) -> Self;

    #[verifier::external_body]
    pub axiom fn set_children_perm_axiom(self, idx: usize, pte: C::E)
        requires
            self.inv(),
            idx < NR_ENTRIES,
        ensures
            self.set_children_perm(idx, pte).inv(),
            self.set_children_perm(idx, pte).meta_own == self.meta_own,
            self.set_children_perm(idx, pte).slot_index == self.slot_index,
            self.set_children_perm(idx, pte).level == self.level,
            self.set_children_perm(idx, pte).tree_level == self.tree_level,
            self.set_children_perm(idx, pte).children_perm.addr() == self.children_perm.addr(),
            self.set_children_perm(idx, pte).children_perm.value()
                == self.children_perm.value().update(idx as int, pte),
    ;

    /// If a slot in `children_perm` holds a non-present PTE, then
    /// `nr_children < NR_ENTRIES`. Proven (no longer axiomatized) from the
    /// `count_consistent` invariant: `nr_children` counts present PTEs, and an
    /// absent slot means not all `NR_ENTRIES` slots are present.
    pub proof fn nr_children_absent_slot_bound(self, idx: usize)
        requires
            self.inv(),
            self.count_consistent(),
            self.children_perm.value().len() == NR_ENTRIES,
            idx < NR_ENTRIES,
            !self.children_perm.value()[idx as int].is_present(),
        ensures
            self.meta_own.nr_children.value() < NR_ENTRIES,
    {
        lemma_count_present_upto_absent(self.children_perm.value(), NR_ENTRIES as int, idx as int);
    }

    /// If a slot in `children_perm` holds a present PTE, then `nr_children > 0`.
    /// Dual of [`Self::nr_children_absent_slot_bound`]; proven from
    /// `count_consistent`.
    pub proof fn nr_children_present_slot_bound(self, idx: usize)
        requires
            self.inv(),
            self.count_consistent(),
            self.children_perm.value().len() == NR_ENTRIES,
            idx < NR_ENTRIES,
            self.children_perm.value()[idx as int].is_present(),
        ensures
            self.meta_own.nr_children.value() > 0,
    {
        lemma_count_present_upto_present(self.children_perm.value(), NR_ENTRIES as int, idx as int);
    }
}

impl<'rcu, C: PageTableConfig> NodeOwner<C> {
    pub open spec fn relate_guard(self, guard: PageTableGuard<'rcu, C>) -> bool {
        &&& guard.inner.inner@.ptr.addr() == self.meta_addr_self()
        &&& guard.inner.inner@.wf(self)
    }
}

pub ghost struct NodeModel<C: PageTableConfig> {
    pub level: PagingLevel,
    pub _phantom: core::marker::PhantomData<C>,
}

impl<C: PageTableConfig> Inv for NodeModel<C> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<C: PageTableConfig> View for NodeOwner<C> {
    type V = NodeModel<C>;

    open spec fn view(&self) -> <Self as View>::V {
        NodeModel { level: self.level, _phantom: core::marker::PhantomData }
    }
}

impl<C: PageTableConfig> InvView for NodeOwner<C> {
    proof fn view_preserves_inv(self) {
    }
}

impl<C: PageTableConfig> OwnerOf for PageTableNode<C> {
    type Owner = NodeOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.ptr.addr() == owner.meta_addr_self()
    }
}

impl<C: PageTableConfig> PageTableNode<C> {
    pub open spec fn invariants(self, owner: NodeOwner<C>) -> bool {
        &&& owner.inv()
        &&& self.wf(
            owner,
        )
        //        &&& owner.meta_perm.wf(&owner.meta_perm.inner_perms)
        //        &&& owner.meta_perm.addr() == self.ptr.addr()
        //        &&& owner.meta_perm.addr() == self.ptr.addr()

    }
}

} // verus!
