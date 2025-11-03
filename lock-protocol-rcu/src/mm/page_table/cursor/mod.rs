mod locking;
// pub mod spec_helpers;

use std::{
    any::TypeId,
    borrow::{Borrow, BorrowMut},
    cell::Cell,
    char::MAX,
    marker::PhantomData,
    ops::Range,
};
use core::ops::Deref;

use vstd::{
    arithmetic::{mul::*, div_mod::*, power::*, power2::*},
    calc,
    layout::is_power_2,
    invariant,
    pervasive::VecAdditionalExecFns,
    prelude::*,
    raw_ptr::MemContents,
    seq::axiom_seq_update_different,
};
use vstd::bits::*;
use vstd::tokens::SetToken;

use crate::helpers::{align_ext::*, math::lemma_usize_mod_0_maintain_after_add};
use crate::mm::{
    page_table::GLOBAL_CPU_NUM,
    page_table::node::{PageTableNode, PageTableGuard},
    page_table::node::entry::Entry,
    page_table::node::child::{Child, ChildRef},
    frame::{self, meta::AnyFrameMeta},
    nr_subpage_per_huge,
    page_prop::PageProperty,
    page_size, page_size_spec, lemma_page_size_spec_properties, lemma_page_size_increases,
    lemma_page_size_geometric, lemma_page_size_adjacent_levels,
    vm_space::Token,
    Paddr, Vaddr, MAX_USERSPACE_VADDR, PAGE_SIZE,
};
use crate::task::DisabledPreemptGuard;
use crate::sync::rcu::RcuDrop;
use crate::sync::spinlock::guard_forget::SubTreeForgotGuard;

use crate::spec::{
    lock_protocol::LockProtocolModel,
    common::{
        NodeId, valid_va_range, vaddr_is_aligned, va_level_to_trace, va_level_to_offset,
        va_level_to_nid, lemma_va_level_to_trace_valid,
    },
    node_helper::{self, group_node_helper_lemmas},
    rcu::{
        SpecInstance, NodeToken, PteArrayToken, FreePaddrToken, PteArrayState, PteState, TreeSpec,
    },
};

use super::{
    lemma_addr_aligned_propagate, lemma_carry_ends_at_nonzero_result_bits,
    lemma_pte_index_alternative_spec, node, pte_index, pte_index_mask, PageTable, PageTableConfig,
    PageTableEntryTrait, PageTableError, PagingConsts, PagingConstsTrait, PagingLevel,
};

use crate::mm::NR_ENTRIES;

verus! {

pub open spec fn va_range_wf<C: PageTableConfig>(va: Range<Vaddr>) -> bool {
    &&& valid_va_range::<C>(va)
    &&& va.start < va.end
    &&& vaddr_is_aligned::<C>(va.start)
    &&& vaddr_is_aligned::<C>(va.end)
}

pub open spec fn va_range_get_guard_level_rec<C: PageTableConfig>(
    va: Range<Vaddr>,
    level: PagingLevel,
) -> PagingLevel
    recommends
        va_range_wf::<C>(va),
        1 <= level <= C::NR_LEVELS_SPEC(),
    decreases level,
    when 1 <= level <= C::NR_LEVELS_SPEC()
{
    if level == 1 {
        1
    } else {
        let st = va.start;
        let en = (va.end - 1) as usize;

        if va_level_to_offset::<C>(st, level) == va_level_to_offset::<C>(en, level) {
            va_range_get_guard_level_rec::<C>(va, (level - 1) as PagingLevel)
        } else {
            level
        }
    }
}

pub open spec fn va_range_get_guard_level<C: PageTableConfig>(va: Range<Vaddr>) -> PagingLevel
    recommends
        va_range_wf::<C>(va),
{
    va_range_get_guard_level_rec::<C>(va, C::NR_LEVELS_SPEC())
}

pub proof fn lemma_va_range_get_guard_level_rec<C: PageTableConfig>(
    va: Range<Vaddr>,
    level: PagingLevel,
)
    requires
        va_range_wf::<C>(va),
        1 <= level <= C::NR_LEVELS_SPEC(),
    ensures
        1 <= va_range_get_guard_level_rec::<C>(va, level) <= level,
    decreases level,
{
    if level > 1 {
        let st = va.start;
        let en = (va.end - 1) as usize;
        if va_level_to_offset::<C>(st, level) == va_level_to_offset::<C>(en, level) {
            lemma_va_range_get_guard_level_rec::<C>(va, (level - 1) as PagingLevel);
        }
    }
}

pub proof fn lemma_va_range_get_guard_level<C: PageTableConfig>(va: Range<Vaddr>)
    requires
        va_range_wf::<C>(va),
    ensures
        1 <= va_range_get_guard_level::<C>(va) <= C::NR_LEVELS_SPEC(),
{
    assert(1 <= C::NR_LEVELS_SPEC()) by {
        C::lemma_consts_properties();
    }
    lemma_va_range_get_guard_level_rec::<C>(va, C::NR_LEVELS_SPEC());
}

pub open spec fn va_range_get_tree_path<C: PageTableConfig>(va: Range<Vaddr>) -> Seq<NodeId>
    recommends
        va_range_wf::<C>(va),
{
    let guard_level = va_range_get_guard_level::<C>(va);
    let trace = va_level_to_trace::<C>(va.start, guard_level);
    node_helper::trace_to_tree_path::<C>(trace)
}

pub proof fn lemma_va_range_get_tree_path<C: PageTableConfig>(va: Range<Vaddr>)
    requires
        va_range_wf::<C>(va),
    ensures
        forall|i|
            #![auto]
            0 <= i < va_range_get_tree_path::<C>(va).len() ==> node_helper::valid_nid::<C>(
                va_range_get_tree_path::<C>(va)[i],
            ),
        va_range_get_tree_path::<C>(va).len() == C::NR_LEVELS_SPEC() - va_range_get_guard_level::<
            C,
        >(va) + 1,
{
    broadcast use group_node_helper_lemmas;

    let guard_level = va_range_get_guard_level::<C>(va);
    lemma_va_range_get_guard_level::<C>(va);
    let trace = va_level_to_trace::<C>(va.start, guard_level);
    let path = va_range_get_tree_path::<C>(va);
    assert forall|i| 0 <= i < path.len() implies #[trigger] node_helper::valid_nid::<C>(
        path[i],
    ) by {
        let nid = path[i];
        if i == 0 {
            assert(nid == node_helper::root_id::<C>());
            node_helper::lemma_root_id::<C>();
        } else {
            let sub_trace = trace.subrange(0, i);
            assert(nid == node_helper::trace_to_nid::<C>(sub_trace));
            lemma_va_level_to_trace_valid::<C>(va.start, guard_level);
        }
    }
}

pub open spec fn va_range_get_guard_nid<C: PageTableConfig>(va: Range<Vaddr>) -> NodeId {
    let path = va_range_get_tree_path::<C>(va);
    let level = va_range_get_guard_level::<C>(va);
    let idx = C::NR_LEVELS_SPEC() - level;
    path[idx]
}

/// The cursor for traversal over the page table.
///
/// A slot is a PTE at any levels, which correspond to a certain virtual
/// memory range sized by the "page size" of the current level.
///
/// A cursor is able to move to the next slot, to read page properties,
/// and even to jump to a virtual address directly.
// #[derive(Debug)] // TODO: Implement `Debug` for `Cursor`.
pub struct Cursor<'rcu, C: PageTableConfig> {
    /// The current path of the cursor.
    ///
    /// The level 1 page table lock guard is at index 0, and the level N page
    /// table lock guard is at index N - 1.
    pub path: [Option<PageTableGuard<'rcu, C>>; MAX_NR_LEVELS],
    /// The level of the page table that the cursor currently points to.
    pub level: PagingLevel,
    /// The top-most level that the cursor is allowed to access.
    ///
    /// From `level` to `guard_level`, the nodes are held in `path`.
    pub guard_level: PagingLevel,
    /// The virtual address that the cursor currently points to.
    pub va: Vaddr,
    /// The virtual address range that is locked.
    pub barrier_va: Range<Vaddr>,
    /// This also make all the operation in the `Cursor::new` performed in a
    /// RCU read-side critical section.
    // #[expect(dead_code)]
    pub preempt_guard: &'rcu DisabledPreemptGuard,
    // Ghost types
    pub inst: Tracked<SpecInstance<C>>,
    pub g_level: Ghost<PagingLevel>,  // Ghost level, used in 'unlock_range'
}

/// The maximum value of `PagingConstsTrait::NR_LEVELS`.
pub const MAX_NR_LEVELS: usize = 5;

// #[derive(Clone, Debug)] // TODO: Implement Debug and Clone for PageTableItem
pub enum PageTableItem<C: PageTableConfig> {
    NotMapped { va: Vaddr, len: usize },
    Mapped { va: Vaddr, page: Paddr, prop: PageProperty },
    StrayPageTable { pt: RcuDrop<PageTableNode<C>>, va: Vaddr, len: usize },
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    /// Well-formedness of the cursor.
    pub open spec fn wf(&self) -> bool {
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
        &&& self.wf_path()
        &&& self.guards_in_path_relation()
        &&& self.wf_va()
        &&& self.wf_level()
    }

    pub open spec fn adjacent_guard_is_child(&self, level: PagingLevel) -> bool
        recommends
            self.get_guard_level(level) is Some,
            self.get_guard_level((level - 1) as PagingLevel) is Some,
    {
        let nid1 = self.get_guard_level_unwrap(level).nid();
        let nid2 = self.get_guard_level_unwrap((level - 1) as PagingLevel).nid();
        node_helper::is_child::<C>(nid1, nid2)
    }

    pub open spec fn guards_in_path_relation(&self) -> bool
        recommends
            self.wf_path(),
    {
        &&& forall|level: PagingLevel|
            #![trigger self.adjacent_guard_is_child(level)]
            self.g_level@ < level <= self.guard_level ==> self.adjacent_guard_is_child(level)
    }

    proof fn lemma_guards_in_path_relation_rec(&self, max_level: PagingLevel, level: PagingLevel)
        requires
            self.wf(),
            self.g_level@ <= level <= max_level <= self.guard_level,
        ensures
            node_helper::in_subtree_range::<C>(
                self.get_guard_level_unwrap(max_level).nid(),
                self.get_guard_level_unwrap(level).nid(),
            ),
        decreases max_level - level,
    {
        if level == max_level {
            let rt = self.get_guard_level_unwrap(max_level).nid();
            assert(node_helper::in_subtree_range::<C>(rt, rt)) by {
                assert(node_helper::valid_nid::<C>(rt));
                node_helper::lemma_tree_size_spec_table::<C>();
            };
        } else {
            self.lemma_guards_in_path_relation_rec(max_level, (level + 1) as PagingLevel);
            let rt = self.get_guard_level_unwrap(max_level).nid();
            let pa = self.get_guard_level_unwrap((level + 1) as PagingLevel).nid();
            let ch = self.get_guard_level_unwrap(level).nid();
            assert(node_helper::in_subtree::<C>(rt, pa)) by {
                assert(node_helper::in_subtree_range::<C>(rt, pa));
                node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(rt, pa);
            };
            assert(node_helper::is_child::<C>(pa, ch)) by {
                assert(self.adjacent_guard_is_child((level + 1) as PagingLevel));
            };
            node_helper::lemma_in_subtree_is_child_in_subtree::<C>(rt, pa, ch);
            assert(node_helper::in_subtree_range::<C>(rt, ch)) by {
                node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(rt, ch);
            };
        }
    }

    pub proof fn lemma_guards_in_path_relation(&self, max_level: PagingLevel)
        requires
            self.wf(),
            self.g_level@ <= max_level <= self.guard_level,
        ensures
            forall|level: PagingLevel|
                #![trigger self.get_guard_level_unwrap(level)]
                self.g_level@ <= level <= max_level ==> node_helper::in_subtree_range::<C>(
                    self.get_guard_level_unwrap(max_level).nid(),
                    self.get_guard_level_unwrap(level).nid(),
                ),
    {
        assert forall|level: PagingLevel|
            #![trigger self.get_guard_level_unwrap(level)]
            self.g_level@ <= level <= max_level implies {
            node_helper::in_subtree_range::<C>(
                self.get_guard_level_unwrap(max_level).nid(),
                self.get_guard_level_unwrap(level).nid(),
            )
        } by {
            self.lemma_guards_in_path_relation_rec(max_level, level);
        }
    }

    pub open spec fn wf_path(&self) -> bool {
        &&& C::NR_LEVELS_SPEC() <= self.path.len()
        &&& forall|level: PagingLevel|
            #![trigger self.get_guard_level(level)]
            #![trigger self.get_guard_level_unwrap(level)]
            1 <= level <= C::NR_LEVELS_SPEC() ==> {
                if level > self.guard_level {
                    self.get_guard_level(level) is None
                } else if level >= self.g_level@ {
                    &&& self.get_guard_level(level) is Some
                    &&& self.get_guard_level_unwrap(level).wf()
                    &&& self.get_guard_level_unwrap(level).inst_id() == self.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        self.get_guard_level_unwrap(level).nid(),
                    )
                    &&& self.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value()
                        == false
                    &&& self.get_guard_level_unwrap(level).guard->Some_0.in_protocol() == true
                    &&& va_level_to_nid::<C>(self.va, level) == self.get_guard_level_unwrap(
                        level,
                    ).nid()
                } else {
                    self.get_guard_level(level) is None
                }
            }
    }

    // TODO
    /// Well-formedness of the cursor's virtual address.
    pub open spec fn wf_va(&self) -> bool {
        &&& self.barrier_va.start < self.barrier_va.end
            < MAX_USERSPACE_VADDR
        // We allow the cursor to be at the end of the range.
        &&& self.barrier_va.start <= self.va <= self.barrier_va.end
        &&& self.va % page_size::<C>(1) == 0
    }

    /// Well-formedness of the cursor's level and guard level.
    pub open spec fn wf_level(&self) -> bool {
        &&& 1 <= self.level <= self.guard_level <= C::NR_LEVELS_SPEC() <= MAX_NR_LEVELS
        &&& self.level <= self.g_level@ <= self.guard_level
    }

    pub open spec fn get_guard_idx(&self, idx: int) -> Option<PageTableGuard<C>> {
        self.path[idx]
    }

    pub open spec fn get_guard_idx_unwrap(&self, idx: int) -> PageTableGuard<C>
        recommends
            self.get_guard_idx(idx) is Some,
    {
        self.get_guard_idx(idx)->Some_0
    }

    pub open spec fn get_guard_level(&self, level: PagingLevel) -> Option<PageTableGuard<C>> {
        self.get_guard_idx(level - 1)
    }

    pub open spec fn get_guard_level_unwrap(&self, level: PagingLevel) -> PageTableGuard<C>
        recommends
            self.get_guard_level(level) is Some,
    {
        self.get_guard_level(level)->Some_0
    }

    pub open spec fn constant_fields_unchanged(&self, old: &Self) -> bool {
        &&& self.guard_level == old.guard_level
        &&& self.barrier_va =~= old.barrier_va
        &&& self.inst =~= old.inst
    }
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    pub open spec fn guard_in_path_nid_diff(
        &self,
        level1: PagingLevel,
        level2: PagingLevel,
    ) -> bool {
        self.get_guard_level_unwrap(level1).nid() != self.get_guard_level_unwrap(level2).nid()
    }

    pub proof fn lemma_guard_in_path_relation_implies_nid_diff(&self)
        requires
            self.wf(),
        ensures
            forall|level1: PagingLevel, level2: PagingLevel|
                self.g_level@ <= level1 < level2 <= self.guard_level && self.g_level@ <= level2
                    <= self.guard_level && level1 != level2
                    ==> #[trigger] self.guard_in_path_nid_diff(level1, level2),
    {
    }

    pub proof fn lemma_guard_in_path_relation_implies_in_subtree_range(&self)
        requires
            self.wf(),
        ensures
            forall|level: PagingLevel|
                self.g_level@ <= level <= self.guard_level
                    ==> #[trigger] node_helper::in_subtree_range::<C>(
                    self.get_guard_level_unwrap(self.guard_level).nid(),
                    self.get_guard_level_unwrap(level).nid(),
                ),
    {
        assert forall|level: PagingLevel| self.g_level@ <= level <= self.guard_level implies {
            #[trigger] node_helper::in_subtree_range::<C>(
                self.get_guard_level_unwrap(self.guard_level).nid(),
                self.get_guard_level_unwrap(level).nid(),
            )
        } by {
            let guard_nid = self.get_guard_level_unwrap(self.guard_level).nid();
            let nid = self.get_guard_level_unwrap(level).nid();
            self.guard_in_path_relation_implies_in_subtree_induction(level);
            assert(node_helper::in_subtree::<C>(guard_nid, nid));
            node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(guard_nid, nid);
        }
    }

    pub proof fn guard_in_path_relation_implies_in_subtree_induction(&self, level: PagingLevel)
        requires
            self.wf(),
            self.g_level@ <= level <= self.guard_level,
        ensures
            node_helper::in_subtree::<C>(
                self.get_guard_level_unwrap(self.guard_level).nid(),
                self.get_guard_level_unwrap(level).nid(),
            ),
        decreases self.guard_level - level,
    {
        let guard_nid = self.get_guard_level_unwrap(self.guard_level).nid();
        if level == self.guard_level {
            node_helper::lemma_in_subtree_self::<C>(guard_nid);
        } else {
            assert(self.adjacent_guard_is_child((level + 1) as PagingLevel)) by {
                self.guards_in_path_relation();
            };
            let parent_nid = self.get_guard_level_unwrap((level + 1) as PagingLevel).nid();
            let nid = self.get_guard_level_unwrap(level).nid();
            self.guard_in_path_relation_implies_in_subtree_induction((level + 1) as PagingLevel);
            assert(node_helper::in_subtree::<C>(guard_nid, parent_nid));
            assert(node_helper::in_subtree::<C>(parent_nid, nid));
            assert(node_helper::in_subtree::<C>(guard_nid, nid));
        }
    }

    pub open spec fn rec_put_guard_from_path(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
        cur_level: PagingLevel,
    ) -> SubTreeForgotGuard<C>
        recommends
            self.g_level@ - 1 <= cur_level <= self.guard_level,
        decreases cur_level - self.g_level@,
    {
        if cur_level < self.g_level@ {
            forgot_guards
        } else {
            let res = if cur_level == self.g_level@ {
                forgot_guards
            } else {
                self.rec_put_guard_from_path(forgot_guards, (cur_level - 1) as PagingLevel)
            };
            let guard = self.get_guard_level_unwrap(cur_level);
            res.put_spec(
                guard.nid(),
                guard.guard->Some_0.inner@,
                guard.inner.deref().meta_spec().lock,
            )
        }
    }

    pub proof fn lemma_rec_put_guard_from_path_basic(&self, forgot_guards: SubTreeForgotGuard<C>)
        requires
            self.wf(),
            forgot_guards.wf(),
        ensures
            self.rec_put_guard_from_path(forgot_guards, (self.g_level@ - 1) as PagingLevel)
                =~= forgot_guards,
    {
    }

    pub open spec fn put_guard_from_path_bottom_up(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
        max_level: PagingLevel,
    ) -> SubTreeForgotGuard<C> {
        SubTreeForgotGuard {
            inner: forgot_guards.inner.union_prefer_right(
                Map::new(
                    |nid: NodeId|
                        {
                            exists|level: PagingLevel|
                                self.g_level@ <= level <= max_level
                                    && #[trigger] self.get_guard_level_unwrap(level).nid() == nid
                        },
                    |nid: NodeId|
                        {
                            let level = choose|level: PagingLevel|
                                self.g_level@ <= level <= max_level
                                    && #[trigger] self.get_guard_level_unwrap(level).nid() == nid;
                            let guard = self.get_guard_level_unwrap(level);
                            let inner = guard.guard->Some_0.inner@;
                            let spin_lock = guard.meta_spec().lock;
                            (inner, Ghost(spin_lock))
                        },
                ),
            ),
        }
    }

    pub proof fn lemma_put_guard_from_path_bottom_up_basic(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
    )
        requires
            self.wf(),
            forgot_guards.wf(),
        ensures
            self.put_guard_from_path_bottom_up(forgot_guards, (self.g_level@ - 1) as PagingLevel)
                =~= forgot_guards,
    {
        let ghost _forgot_guards = self.put_guard_from_path_bottom_up(
            forgot_guards,
            (self.g_level@ - 1) as PagingLevel,
        );
        assert(_forgot_guards.inner =~= forgot_guards.inner) by {
            assert forall|nid: NodeId| forgot_guards.inner.dom().contains(nid) implies {
                _forgot_guards.inner.dom().contains(nid)
            } by {};
            assert forall|nid: NodeId| _forgot_guards.inner.dom().contains(nid) implies {
                forgot_guards.inner.dom().contains(nid)
            } by {};
        }
    }

    pub proof fn lemma_put_guard_from_path_bottom_up_eq_with_rec(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
        cur_level: PagingLevel,
    )
        requires
            self.wf(),
            forgot_guards.wf(),
            self.wf_with_forgot_guards_nid_not_contained(forgot_guards),
            self.g_level@ - 1 <= cur_level <= self.guard_level,
        ensures
            self.rec_put_guard_from_path(forgot_guards, cur_level)
                =~= self.put_guard_from_path_bottom_up(forgot_guards, cur_level),
        decreases cur_level,
    {
        if cur_level < self.g_level@ {
            self.lemma_rec_put_guard_from_path_basic(forgot_guards);
            self.lemma_put_guard_from_path_bottom_up_basic(forgot_guards);
        } else {
            let rec_res = self.rec_put_guard_from_path(
                forgot_guards,
                (cur_level - 1) as PagingLevel,
            );
            let bottom_up_res = self.put_guard_from_path_bottom_up(
                forgot_guards,
                (cur_level - 1) as PagingLevel,
            );
            assert(rec_res =~= bottom_up_res) by {
                self.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                    forgot_guards,
                    (cur_level - 1) as PagingLevel,
                );
            };
            let guard = self.get_guard_level_unwrap(cur_level);
            let res_put_cur_level = rec_res.put_spec(
                guard.nid(),
                guard.guard->Some_0.inner@,
                guard.inner.deref().meta_spec().lock,
            );
            assert(res_put_cur_level.inner =~= self.rec_put_guard_from_path(
                forgot_guards,
                cur_level,
            ).inner);
            assert(res_put_cur_level.inner =~= self.put_guard_from_path_bottom_up(
                forgot_guards,
                cur_level,
            ).inner);
        }
    }

    pub open spec fn put_guard_from_path_top_down(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
        min_level: PagingLevel,
    ) -> SubTreeForgotGuard<C> {
        SubTreeForgotGuard {
            inner: forgot_guards.inner.union_prefer_right(
                Map::new(
                    |nid: NodeId|
                        {
                            exists|level: PagingLevel|
                                min_level <= level <= self.guard_level
                                    && #[trigger] self.get_guard_level_unwrap(level).nid() == nid
                        },
                    |nid: NodeId|
                        {
                            let level = choose|level: PagingLevel|
                                min_level <= level <= self.guard_level
                                    && #[trigger] self.get_guard_level_unwrap(level).nid() == nid;
                            let guard = self.get_guard_level_unwrap(level);
                            let inner = guard.guard->Some_0.inner@;
                            let spin_lock = guard.meta_spec().lock;
                            (inner, Ghost(spin_lock))
                        },
                ),
            ),
        }
    }

    pub proof fn lemma_put_guard_from_path_top_down_basic(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
    )
        requires
            self.wf(),
            forgot_guards.wf(),
        ensures
            self.put_guard_from_path_top_down(forgot_guards, (self.guard_level + 1) as PagingLevel)
                =~= forgot_guards,
    {
        let ghost _forgot_guards = self.put_guard_from_path_top_down(
            forgot_guards,
            (self.guard_level + 1) as PagingLevel,
        );
        assert(_forgot_guards.inner =~= forgot_guards.inner) by {
            assert forall|nid: NodeId| forgot_guards.inner.dom().contains(nid) implies {
                _forgot_guards.inner.dom().contains(nid)
            } by {};
            assert forall|nid: NodeId| _forgot_guards.inner.dom().contains(nid) implies {
                forgot_guards.inner.dom().contains(nid)
            } by {};
        }
    }

    pub proof fn lemma_put_guard_from_path_top_down_basic1(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
    )
        requires
            self.wf(),
            forgot_guards.wf(),
            self.wf_with_forgot_guards_nid_not_contained(forgot_guards),
        ensures
            self.put_guard_from_path_top_down(forgot_guards, self.g_level@) =~= {
                let guard = self.get_guard_level_unwrap(self.g_level@);
                let inner = guard.guard->Some_0.inner@;
                let spin_lock = guard.meta_spec().lock;
                self.put_guard_from_path_top_down(
                    forgot_guards,
                    (self.g_level@ + 1) as PagingLevel,
                ).put_spec(guard.nid(), inner, spin_lock)
            },
    {
        let top_down_g_level = self.put_guard_from_path_top_down(forgot_guards, self.g_level@);
        let top_down_p1 = self.put_guard_from_path_top_down(
            forgot_guards,
            (self.g_level@ + 1) as PagingLevel,
        );
        let guard = self.get_guard_level_unwrap(self.g_level@);
        let guard_nid = guard.nid();
        let inner = guard.guard->Some_0.inner@;
        let spin_lock = guard.inner.deref().meta_spec().lock;
        let top_down_p1_put = top_down_p1.put_spec(guard_nid, inner, spin_lock);
        if self.g_level@ == self.guard_level {
            assert(top_down_p1.inner =~= forgot_guards.inner) by {
                self.lemma_put_guard_from_path_top_down_basic(forgot_guards);
            };
            assert(top_down_p1_put.inner =~= top_down_g_level.inner);
        } else {
            assert(top_down_g_level.inner =~= top_down_p1_put.inner) by {
                assert forall|nid: NodeId| top_down_g_level.inner.dom().contains(nid) implies {
                    top_down_p1_put.inner.dom().contains(nid)
                } by {};
                assert forall|nid: NodeId| top_down_p1_put.inner.dom().contains(nid) implies {
                    top_down_g_level.inner.dom().contains(nid)
                } by {};
            };
        }
    }

    pub proof fn lemma_put_guard_from_path_bottom_up_eq_with_top_down(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
    )
        requires
            self.wf(),
            forgot_guards.wf(),
            self.wf_with_forgot_guards_nid_not_contained(forgot_guards),
        ensures
            self.put_guard_from_path_bottom_up(forgot_guards, self.guard_level)
                =~= self.put_guard_from_path_top_down(forgot_guards, self.g_level@),
    {
    }

    // Trivial but nontrivial for Verus.
    pub proof fn lemma_cursor_eq_implie_forgot_guards_eq(
        cursor1: Self,
        cursor2: Self,
        forgot_guards: SubTreeForgotGuard<C>,
    )
        requires
            cursor1.guard_level == cursor2.guard_level,
            cursor1.g_level == cursor2.g_level,
            cursor1.path =~= cursor2.path,
        ensures
            cursor1.rec_put_guard_from_path(forgot_guards, cursor1.guard_level)
                =~= cursor2.rec_put_guard_from_path(forgot_guards, cursor2.guard_level),
    {
        admit();
    }

    pub open spec fn wf_with_forgot_guards_nid_not_contained(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
    ) -> bool {
        forall|level: PagingLevel|
            #![trigger self.get_guard_level_unwrap(level)]
            self.g_level@ <= level <= self.guard_level ==> {
                !forgot_guards.inner.dom().contains(self.get_guard_level_unwrap(level).nid())
            }
    }

    pub open spec fn wf_with_forgot_guards(&self, forgot_guards: SubTreeForgotGuard<C>) -> bool {
        &&& {
            let res = self.rec_put_guard_from_path(forgot_guards, self.guard_level);
            {
                &&& res.wf()
                &&& res.is_root_and_contained(self.get_guard_level_unwrap(self.guard_level).nid())
            }
        }
        &&& self.wf_with_forgot_guards_nid_not_contained(forgot_guards)
    }

    pub open spec fn guards_in_path_wf_with_forgot_guards_singleton(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
        level: PagingLevel,
    ) -> bool {
        let guard = self.get_guard_level_unwrap(level);
        let _forgot_guards = self.rec_put_guard_from_path(
            forgot_guards,
            (level - 1) as PagingLevel,
        );
        {
            &&& _forgot_guards.wf()
            &&& _forgot_guards.is_sub_root(guard.nid())
            &&& _forgot_guards.children_are_contained(
                guard.nid(),
                guard.guard->Some_0.view_pte_token().value(),
            )
        }
    }

    pub open spec fn guards_in_path_wf_with_forgot_guards(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
    ) -> bool {
        forall|level: PagingLevel|
            self.g_level@ <= level <= self.guard_level
                ==> #[trigger] self.guards_in_path_wf_with_forgot_guards_singleton(
                forgot_guards,
                level,
            )
    }

    pub proof fn lemma_wf_with_forgot_guards_sound(&self, forgot_guards: SubTreeForgotGuard<C>)
        requires
            self.wf(),
            forgot_guards.wf(),
            self.wf_with_forgot_guards(forgot_guards),
        ensures
            self.guards_in_path_wf_with_forgot_guards(forgot_guards),
    {
        // assert forall |_nid: NodeId|
        //             #[trigger] forgot_guards.inner.dom().contains(_nid) && _nid != nid
        //         implies {
        //             !node_helper::in_subtree_range::<C>(_nid, nid)
        //         } by {
        //             if node_helper::in_subtree_range::<C>(_nid, nid) {
        //                 let sub_rt_nid = self.get_guard_level_unwrap(self.guard_level).nid();
        //                 if node_helper::in_subtree_range::<C>(sub_rt_nid, _nid) {
        //                     assert(
        //                         exists |level: PagingLevel|
        //                             old(self).level < level <= old(self).guard_level &&
        //                             _nid == #[trigger] old(self).get_guard_level_unwrap(level).nid()
        //                     ) by { admit(); };
        //                 } else {
        //                     assert forall |__nid: NodeId|
        //                         #[trigger] forgot_guards.inner.dom().contains(__nid)
        //                     implies {
        //                         node_helper::in_subtree_range::<C>(sub_rt_nid, __nid)
        //                     } by {
        //                         assert(forgot_guards.is_root(sub_rt_nid));
        //                     };
        //                 }
        //             }
        //         };
        admit();
    }

    pub proof fn lemma_push_level_sustains_wf_with_forgot_guards(
        pre: Self,
        post: Self,
        guard: PageTableGuard<C>,
        forgot_guards: SubTreeForgotGuard<C>,
    )
        requires
            pre.wf(),
            post.wf(),
            pre.wf_push_level(post, guard),
            guard.wf(),
            guard.inst_id() == pre.inst@.id(),
            guard.guard->Some_0.stray_perm().value() == false,
            guard.guard->Some_0.in_protocol() == true,
            guard.level_spec() == pre.level - 1,
            forgot_guards.wf(),
            pre.wf_with_forgot_guards(
                {
                    let nid = guard.nid();
                    let inner = guard.guard->Some_0.inner@;
                    let spin_lock = guard.inner.deref().meta_spec().lock;
                    forgot_guards.put_spec(nid, inner, spin_lock)
                },
            ),
            forgot_guards.is_sub_root(guard.nid()),
            forgot_guards.children_are_contained(
                guard.nid(),
                guard.guard->Some_0.inner@.pte_token->Some_0.value(),
            ),
        ensures
            post.wf_with_forgot_guards(forgot_guards),
    {
        admit();
    }

    pub proof fn lemma_pop_level_sustains_wf_with_forgot_guards(
        pre: Self,
        post: Self,
        forgot_guards: SubTreeForgotGuard<C>,
    )
        requires
            pre.wf(),
            post.wf(),
            pre.wf_pop_level(post),
            forgot_guards.wf(),
            pre.wf_with_forgot_guards(forgot_guards),
        ensures
            post.wf_with_forgot_guards(
                {
                    let guard = pre.get_guard_level_unwrap(pre.level);
                    let nid = guard.nid();
                    let inner = guard.guard->Some_0.inner@;
                    let spin_lock = guard.inner.deref().meta_spec().lock;
                    forgot_guards.put_spec(nid, inner, spin_lock)
                },
            ),
    {
        admit();
    }
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    // Trusted
    #[verifier::external_body]
    pub fn take(&mut self, i: usize) -> (res: Option<PageTableGuard<'a, C>>)
        requires
            old(self).wf_path(),
            0 <= i < C::NR_LEVELS_SPEC(),
            old(self).level <= i + 1 <= old(self).guard_level,
            i + 1 == old(self).g_level@,
        ensures
            self.wf_path(),
            self.g_level@ == old(self).g_level@ + 1,
            self.constant_fields_unchanged(old(self)),
            self.level == old(self).level,
            self.va == old(self).va,
            res =~= old(self).path[i as int],
            self.path[i as int] is None,
            forall|_i|
                #![trigger self.path[_i]]
                0 <= _i < C::NR_LEVELS_SPEC() && _i != i ==> self.path[_i] =~= old(self).path[_i],
    {
        self.g_level = Ghost((self.g_level@ + 1) as PagingLevel);
        self.path[i].take()
    }

    fn no_op() {
    }
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[verifier::external_body]
    pub fn new(
        pt: &'a PageTable<C>,
        guard: &'a DisabledPreemptGuard,
        va: &Range<Vaddr>,
        m: Tracked<LockProtocolModel<C>>,
    ) -> (res: (Self, Tracked<SubTreeForgotGuard<C>>, Tracked<LockProtocolModel<C>>))
        requires
            pt.wf(),
            va_range_wf::<C>(*va),
            m@.inv(),
            m@.inst_id() == pt.inst@.id(),
            m@.state() is Void,
        ensures
            res.0.wf(),
            res.0.wf_with_forgot_guards(res.1@),
            res.1@.wf(),
            res.1@.is_root_and_contained(va_range_get_guard_nid::<C>(*va)),
            res.2@.inv(),
            res.2@.inst_id() == pt.inst@.id(),
            res.2@.state() is Locked,
            res.2@.sub_tree_rt() == va_range_get_guard_nid::<C>(*va),
    {
        // if !is_valid_range::<C>(va) || va.is_empty() {
        //     assert(false);
        // }
        // if va.start % C::BASE_PAGE_SIZE() != 0 || va.end % C::BASE_PAGE_SIZE() != 0 {
        //     assert(false);
        // }
        // const { assert!(C::NR_LEVELS() as usize <= MAX_NR_LEVELS) };
        let res = locking::lock_range(pt, guard, va, m);
        let cursor = res.0;
        let tracked model = res.1.get();
        let tracked forgot_guards = res.2.get();

        (cursor, Tracked(forgot_guards), Tracked(model))
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    pub fn query(&mut self, forgot_guards: Tracked<SubTreeForgotGuard<C>>) -> (res: (
        Result<Option<(Paddr, PagingLevel, PageProperty)>, PageTableError>,
        Tracked<SubTreeForgotGuard<C>>,
    ))
        requires
            old(self).wf(),
            old(self).g_level@ == old(self).level,
            forgot_guards@.wf(),
            old(self).wf_with_forgot_guards(forgot_guards@),
        ensures
            self.wf(),
            self.g_level@ == self.level,
            res.1@.wf(),
            self.wf_with_forgot_guards(res.1@),
    {
        if self.va >= self.barrier_va.end {
            return (Err(PageTableError::InvalidVaddr(self.va)), forgot_guards);
        }
        let tracked forgot_guards = forgot_guards.get();

        let ghost cur_va = self.va;

        let rcu_guard = self.preempt_guard;

        loop
            invariant
                self.wf(),
                self.constant_fields_unchanged(old(self)),
                self.g_level@ == self.level,
                cur_va == self.va == old(self).va < self.barrier_va.end,
                forgot_guards.wf(),
                self.wf_with_forgot_guards(forgot_guards),
            decreases self.level,
        {
            let ghost _cursor = *self;
            let ghost _forgot_guards = forgot_guards;

            let level = self.level;
            let ghost cur_level = self.level;

            let cur_entry = self.cur_entry();
            let cur_node = self.path[(self.level - 1) as usize].as_ref().unwrap();
            let child = cur_entry.to_ref(cur_node);
            match child {
                ChildRef::PageTable(pt) => {
                    let ghost nid = pt.nid@;
                    let ghost spin_lock = forgot_guards.get_lock(nid);
                    assert(forgot_guards.is_sub_root_and_contained(nid)) by {
                        C::lemma_consts_properties();
                        C::lemma_nr_subpage_per_huge_is_512();
                        self.lemma_wf_with_forgot_guards_sound(forgot_guards);
                        self.lemma_rec_put_guard_from_path_basic(forgot_guards);
                        let pa_guard = self.get_guard_level_unwrap(self.level);
                        let pa_inner = pa_guard.guard->Some_0.inner@;
                        let pa_spin_lock = pa_guard.meta_spec().lock;
                        let pa_nid = pa_guard.nid();
                        let idx = pte_index::<C>(self.va, self.level);
                        assert(node_helper::is_child::<C>(pa_nid, nid)) by {
                            assert(nid == node_helper::get_child::<C>(pa_nid, idx as nat));
                            node_helper::lemma_level_dep_relation::<C>(pa_nid);
                            node_helper::lemma_get_child_sound::<C>(pa_nid, idx as nat);
                        };
                        assert(pa_inner.pte_token->Some_0.value().is_alive(idx as nat));
                        let __forgot_guards = self.rec_put_guard_from_path(
                            forgot_guards,
                            self.level,
                        );
                        // Mark: maybe helpful for proving lemma_wf_with_forgot_guards_sound
                        assert(__forgot_guards.wf()) by {
                            // assert(__forgot_guards.is_sub_root_and_contained(pa_nid));
                            // assert forall |nid: NodeId|
                            //     #[trigger] __forgot_guards.inner.dom().contains(nid)
                            // implies {
                            //     __forgot_guards.children_are_contained(
                            //         nid,
                            //         __forgot_guards.get_guard_inner(nid).pte_token->Some_0.value(),
                            //     )
                            // } by {
                            //     let pte_array = __forgot_guards.get_guard_inner(nid).pte_token->Some_0.value();
                            //     if nid == pa_nid {
                            //         if node_helper::is_not_leaf::<C>(nid) {
                            //             assert(__forgot_guards.children_are_contained(nid, pte_array));
                            //         }
                            //     } else {
                            //         assert(!node_helper::in_subtree_range::<C>(nid, pa_nid));
                            //         if node_helper::is_not_leaf::<C>(nid) {
                            //             assert forall |i: nat|
                            //                 0 <= i < 512
                            //             implies {
                            //                 #[trigger] pte_array.is_alive(i) <==>
                            //                     __forgot_guards.inner.dom().contains(node_helper::get_child::<C>(nid, i))
                            //             } by {
                            //                 let ch = node_helper::get_child::<C>(nid, i);
                            //                 assert(ch != pa_nid) by {
                            //                     assert(node_helper::in_subtree_range::<C>(nid, ch)) by {
                            //                         node_helper::lemma_get_child_sound::<C>(nid, i);
                            //                         node_helper::lemma_is_child_implies_in_subtree::<C>(nid, ch);
                            //                         node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(nid, ch);
                            //                     }
                            //                 };
                            //             };
                            //         }
                            //     }
                            // };
                            if self.level < self.guard_level {
                                assert(self.guards_in_path_wf_with_forgot_guards_singleton(
                                    forgot_guards,
                                    (self.level + 1) as PagingLevel,
                                ));
                            }
                        };
                        assert(__forgot_guards.is_sub_root_and_contained(pa_nid)) by {
                            assert(self.guards_in_path_wf_with_forgot_guards_singleton(
                                forgot_guards,
                                self.level,
                            ));
                        };
                        assert(__forgot_guards =~= forgot_guards.put_spec(
                            pa_nid,
                            pa_inner,
                            pa_spin_lock,
                        ));
                        assert(forgot_guards.is_sub_root(nid)) by {
                            assert forall|_nid: NodeId| #[trigger]
                                forgot_guards.inner.dom().contains(_nid) && _nid != nid implies {
                                !node_helper::in_subtree_range::<C>(_nid, nid)
                            } by {
                                assert(__forgot_guards.inner.dom().contains(_nid));
                                assert(__forgot_guards.inner.dom().contains(nid));
                                assert(__forgot_guards.is_sub_root(pa_nid));
                                assert(!forgot_guards.inner.dom().contains(pa_nid));
                                assert(_nid != pa_nid);
                                assert(!node_helper::in_subtree_range::<C>(_nid, pa_nid));
                                if node_helper::in_subtree_range::<C>(_nid, nid) {
                                    assert(node_helper::in_subtree_range::<C>(_nid, pa_nid)) by {
                                        node_helper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range::<
                                            C,
                                        >(_nid, pa_nid, nid);
                                    };
                                }
                            };
                        };
                    };
                    let tracked forgot_guard = forgot_guards.tracked_take(nid);
                    // Admitted due to the same reason as PageTableNode::from_raw.
                    assert(pt.deref().meta_spec().lock =~= spin_lock) by {
                        admit();
                    };
                    let guard = pt.make_guard_unchecked(
                        rcu_guard,
                        Tracked(forgot_guard),
                        Ghost(spin_lock),
                    );
                    assert(self.level > 1) by {
                        assert(self.level == self.get_guard_level_unwrap(self.level).level_spec());
                    };
                    assert(guard.level_spec() == self.level - 1) by {
                        assert(self.level == self.get_guard_level_unwrap(self.level).level_spec());
                    };
                    assert(node_helper::is_child::<C>(
                        self.get_guard_level_unwrap(self.level).nid(),
                        guard.nid(),
                    )) by {
                        let idx = pte_index::<C>(self.va, self.level);
                        let _guard = self.get_guard_level_unwrap(self.level);
                        assert(_guard.level_spec() > 1);
                        node_helper::lemma_level_dep_relation::<C>(_guard.nid());
                        node_helper::lemma_get_child_sound::<C>(_guard.nid(), idx as nat);
                    };
                    self.push_level(guard);
                    assert(self.wf_with_forgot_guards(forgot_guards)) by {
                        let _nid = guard.nid();
                        let _inner = guard.guard->Some_0.inner@;
                        let _spin_lock = guard.inner.deref().meta_spec().lock;
                        assert(_nid == nid);
                        assert(_spin_lock =~= spin_lock);
                        assert(_inner =~= _forgot_guards.get_guard_inner(nid)) by {
                            assert(_inner =~= forgot_guard);
                        };
                        assert(_forgot_guards =~= forgot_guards.put_spec(_nid, _inner, _spin_lock))
                            by {
                            assert(forgot_guards =~= _forgot_guards.take_spec(_nid));
                            _forgot_guards.lemma_take_put(_nid);
                        };
                        Self::lemma_push_level_sustains_wf_with_forgot_guards(
                            _cursor,
                            *self,
                            guard,
                            forgot_guards,
                        );
                    }
                    continue ;
                },
                ChildRef::None => return (Ok(None), Tracked(forgot_guards)),
                ChildRef::Frame(pa, ch_level, prop) => {
                    return (Ok(Some((pa, ch_level, prop))), Tracked(forgot_guards));
                },
            };
        }
    }

    /// Traverses forward in the current level to the next PTE.
    ///
    /// If reached the end of a page table node, it leads itself up to the next page of the parent
    /// page if possible.
    pub(in crate::mm) fn move_forward(
        &mut self,
        forgot_guards: Tracked<SubTreeForgotGuard<C>>,
    ) -> (res: Tracked<SubTreeForgotGuard<C>>)
        requires
            old(self).wf(),
            old(self).g_level@ == old(self).level,
            forgot_guards@.wf(),
            old(self).wf_with_forgot_guards(forgot_guards@),
            old(self).va + page_size::<C>(old(self).level) <= old(self).barrier_va.end,
        ensures
            self.wf(),
            self.g_level@ == self.level,
            self.constant_fields_unchanged(old(self)),
            self.va == align_down(old(self).va, page_size::<C>(old(self).level)) + page_size::<C>(
                old(self).level,
            ),
            self.level >= old(self).level,
            res@.wf(),
            self.wf_with_forgot_guards(res@),
            forall|level: PagingLevel|
                #![trigger self.get_guard_level(level)]
                self.level <= level <= self.guard_level ==> self.get_guard_level(level) =~= old(
                    self,
                ).get_guard_level(level),
            self.rec_put_guard_from_path(res@, self.guard_level) =~= old(
                self,
            ).rec_put_guard_from_path(forgot_guards@, old(self).guard_level),
    {
        let tracked forgot_guards = forgot_guards.get();
        let ghost _forgot_guards = forgot_guards;

        assert(1 <= self.level <= C::NR_LEVELS());
        let cur_page_size = page_size::<C>(self.level);
        let next_va = align_down(self.va, cur_page_size) + cur_page_size;
        assert(self.va < next_va <= self.va + cur_page_size) by {
            let aligned_va = align_down(self.va, cur_page_size) as int;
            lemma_page_size_spec_properties::<C>(self.level);
            assert(0 <= self.va % cur_page_size <= self.va && 0 <= self.va % cur_page_size
                < cur_page_size) by (nonlinear_arith)
                requires
                    self.va >= 0,
                    cur_page_size > 0,
            ;
            assert(aligned_va as int == self.va as int - self.va as int % cur_page_size as int);
            assert(next_va - self.va == cur_page_size - self.va % cur_page_size);
            assert(0 < cur_page_size - self.va % cur_page_size <= cur_page_size);
        }
        let ghost old_path = self.path;
        assert(next_va % page_size::<C>(self.level) == 0) by (nonlinear_arith)
            requires
                next_va == align_down(self.va, cur_page_size) + cur_page_size,
                cur_page_size == page_size::<C>(self.level),
                align_down(self.va, cur_page_size) % cur_page_size == 0,
        ;
        while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0
            invariant
                next_va % page_size::<C>(self.level) == 0,
                self.wf(),
                self.g_level@ == self.level,
                self.constant_fields_unchanged(old(self)),
                self.va == old(self).va,
                self.level >= old(self).level,
                forall|level: PagingLevel|
                    #![trigger self.get_guard_level(level)]
                    self.level <= level <= self.guard_level ==> self.get_guard_level(level) =~= old(
                        self,
                    ).get_guard_level(level),
                forgot_guards.wf(),
                self.wf_with_forgot_guards(forgot_guards),
                self.rec_put_guard_from_path(forgot_guards, self.guard_level) =~= old(
                    self,
                ).rec_put_guard_from_path(_forgot_guards, old(self).guard_level),
            decreases self.guard_level - self.level,
        {
            let ghost _cursor = *self;
            let res = self.pop_level(Tracked(forgot_guards));
            proof {
                forgot_guards = res.get();
            }
            proof {
                assert(next_va % page_size::<C>((self.level - 1) as u8) == 0);
                assert(pte_index::<C>(next_va, (self.level - 1) as u8) == 0);
                assert(1 <= self.level <= C::NR_LEVELS());
                lemma_addr_aligned_propagate::<C>(next_va, self.level);

                assert forall|level: PagingLevel|
                    #![trigger self.get_guard_level(level)]
                    self.level <= level <= self.guard_level implies {
                    self.get_guard_level(level) =~= old(self).get_guard_level(level)
                } by {
                    assert(self.get_guard_level(level) =~= _cursor.get_guard_level(level));
                };
            }
        }
        assert(self.wf());
        assert(self.wf_with_forgot_guards(forgot_guards));
        let ghost _cursor = *self;
        self.va = next_va;
        assert(self.wf()) by {
            assert(self.wf_path()) by {
                assert forall|level: PagingLevel|
                    #![trigger self.get_guard_level(level)]
                    #![trigger self.get_guard_level_unwrap(level)]
                    1 <= level <= C::NR_LEVELS_SPEC() implies {
                    if level > self.guard_level {
                        self.get_guard_level(level) is None
                    } else if level >= self.g_level@ {
                        &&& self.get_guard_level(level) is Some
                        &&& self.get_guard_level_unwrap(level).wf()
                        &&& level == node_helper::nid_to_level::<C>(
                            self.get_guard_level_unwrap(level).nid(),
                        )
                        &&& self.get_guard_level_unwrap(level).inst_id() == self.inst@.id()
                        &&& self.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value()
                            == false
                        &&& self.get_guard_level_unwrap(level).guard->Some_0.in_protocol() == true
                        &&& va_level_to_nid::<C>(self.va, level) == self.get_guard_level_unwrap(
                            level,
                        ).nid()
                    } else {
                        self.get_guard_level(level) is None
                    }
                } by {
                    assert(self.guard_level == _cursor.guard_level);
                    assert(self.g_level@ == _cursor.g_level@);
                    if level > _cursor.guard_level {
                        assert(_cursor.get_guard_level(level) is None);
                    } else if level >= _cursor.g_level@ {
                        assert({
                            &&& _cursor.get_guard_level(level) is Some
                            &&& _cursor.get_guard_level_unwrap(level).wf()
                            &&& _cursor.get_guard_level_unwrap(level).inst_id()
                                == _cursor.inst@.id()
                            &&& level == node_helper::nid_to_level::<C>(
                                _cursor.get_guard_level_unwrap(level).nid(),
                            )
                            &&& _cursor.get_guard_level_unwrap(
                                level,
                            ).guard->Some_0.stray_perm().value() == false
                            &&& _cursor.get_guard_level_unwrap(level).guard->Some_0.in_protocol()
                                == true
                        });
                        assert(va_level_to_nid::<C>(self.va, level) == self.get_guard_level_unwrap(
                            level,
                        ).nid()) by {
                            admit();
                        };  // TODO
                    } else {
                        assert(_cursor.get_guard_level(level) is None);
                    }
                }
            };
            assert(self.guards_in_path_relation()) by {
                assert forall|level: PagingLevel|
                    #![trigger self.adjacent_guard_is_child(level)]
                    self.g_level@ < level <= self.guard_level implies {
                    self.adjacent_guard_is_child(level)
                } by {
                    assert(_cursor.adjacent_guard_is_child(level));
                }
            }
            assert(self.wf_va()) by {
                lemma_page_size_spec_properties::<C>(1);
                lemma_page_size_spec_properties::<C>(old(self).level);
                assert(cur_page_size % page_size::<C>(1) == 0) by {
                    admit();
                };
                let k1 = cur_page_size / page_size::<C>(1);
                assert(cur_page_size == k1 * page_size::<C>(1)) by {
                    admit();
                };
                assert(next_va % cur_page_size == 0) by {
                    lemma_align_down_basic(old(self).va, cur_page_size);
                };
                let k2 = next_va / cur_page_size;
                assert(next_va == k2 * cur_page_size) by {
                    admit();
                };
                assert(next_va % page_size::<C>(1) == 0) by {
                    assert(k2 * k1 * page_size::<C>(1) == next_va) by {
                        lemma_mul_is_associative(k2 as int, k1 as int, page_size::<C>(1) as int);
                    };
                    lemma_mod_multiples_basic(k2 * k1, page_size::<C>(1) as int);
                };
            };
        }
        assert(self.wf_with_forgot_guards(forgot_guards)) by {
            let res1 = self.rec_put_guard_from_path(forgot_guards, self.guard_level);
            let res2 = _cursor.rec_put_guard_from_path(forgot_guards, _cursor.guard_level);
            assert(res1 =~= res2) by {
                assert(self.guard_level == _cursor.guard_level);
                assert(self.g_level@ == _cursor.g_level@);
                assert(self.path =~= _cursor.path);
                Self::lemma_cursor_eq_implie_forgot_guards_eq(*self, _cursor, forgot_guards);
            };
            assert({
                &&& res1.wf()
                &&& res1.is_root_and_contained(self.get_guard_level_unwrap(self.guard_level).nid())
            });
            assert forall|level: PagingLevel|
                #![trigger self.get_guard_level_unwrap(level)]
                self.g_level@ <= level <= self.guard_level implies {
                !forgot_guards.inner.dom().contains(self.get_guard_level_unwrap(level).nid())
            } by {
                assert(!forgot_guards.inner.dom().contains(
                    _cursor.get_guard_level_unwrap(level).nid(),
                ))
            }
        }
        assert forall|level: PagingLevel|
            #![trigger self.get_guard_level(level)]
            self.level <= level <= self.guard_level implies {
            self.get_guard_level(level) =~= old(self).get_guard_level(level)
        } by {
            assert(self.get_guard_level(level) =~= _cursor.get_guard_level(level));
        };
        let ghost cursor = *self;
        assert(cursor.rec_put_guard_from_path(forgot_guards, cursor.guard_level)
            =~= _cursor.rec_put_guard_from_path(forgot_guards, _cursor.guard_level)) by {
            let full_forgot_guards_pre = _cursor.rec_put_guard_from_path(
                forgot_guards,
                _cursor.guard_level,
            );
            let full_forgot_guards_post = cursor.rec_put_guard_from_path(
                forgot_guards,
                cursor.guard_level,
            );
            assert(full_forgot_guards_pre.inner =~= full_forgot_guards_post.inner) by {
                _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                    forgot_guards,
                    _cursor.guard_level,
                );
                cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                    forgot_guards,
                    cursor.guard_level,
                );
                assert forall|nid: NodeId|
                    full_forgot_guards_pre.inner.dom().contains(nid) implies {
                    full_forgot_guards_post.inner.dom().contains(nid)
                } by {
                    if forgot_guards.inner.dom().contains(nid) {
                    } else {
                        assert(exists|level: PagingLevel|
                            _cursor.g_level@ <= level <= _cursor.guard_level
                                && #[trigger] _cursor.get_guard_level_unwrap(level).nid() == nid);
                        let level = choose|level: PagingLevel|
                            _cursor.g_level@ <= level <= _cursor.guard_level
                                && #[trigger] _cursor.get_guard_level_unwrap(level).nid() == nid;
                        assert(cursor.get_guard_level_unwrap(level).nid() == nid);
                    }
                };
                assert forall|nid: NodeId|
                    full_forgot_guards_post.inner.dom().contains(nid) implies {
                    full_forgot_guards_pre.inner.dom().contains(nid)
                } by {
                    if forgot_guards.inner.dom().contains(nid) {
                    } else {
                        assert(exists|level: PagingLevel|
                            cursor.g_level@ <= level <= cursor.guard_level
                                && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid);
                        let level = choose|level: PagingLevel|
                            cursor.g_level@ <= level <= cursor.guard_level
                                && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid;
                        assert(_cursor.get_guard_level_unwrap(level).nid() == nid);
                    }
                };
            };
        };

        Tracked(forgot_guards)
    }

    pub fn virt_addr(&self) -> Vaddr
        returns
            self.va,
    {
        self.va
    }

    pub open spec fn wf_pop_level(self, post: Self) -> bool {
        &&& post.level == self.level + 1
        &&& post.g_level@ == self.g_level@ + 1
        &&& forall|level: PagingLevel|
            #![trigger self.get_guard_level(level)]
            #![trigger self.get_guard_level_unwrap(level)]
            1 <= level <= self.guard_level && level != self.level ==> {
                self.get_guard_level(level) =~= post.get_guard_level(level)
            }
        &&& self.get_guard_level(self.level) is Some
        &&& post.get_guard_level(
            self.level,
        ) is None
        // Other fields remain unchanged.
        &&& self.constant_fields_unchanged(&post)
        &&& self.va == post.va
    }

    /// Goes up a level.
    fn pop_level(&mut self, forgot_guards: Tracked<SubTreeForgotGuard<C>>) -> (res: Tracked<
        SubTreeForgotGuard<C>,
    >)
        requires
            old(self).wf(),
            old(self).g_level@ == old(self).level,
            old(self).level < old(self).guard_level,
            forgot_guards@.wf(),
            old(self).wf_with_forgot_guards(forgot_guards@),
        ensures
            old(self).wf_pop_level(*self),
            self.wf(),
            self.g_level@ == self.level,
            res@.wf(),
            self.wf_with_forgot_guards(res@),
            self.rec_put_guard_from_path(res@, self.guard_level) =~= old(
                self,
            ).rec_put_guard_from_path(forgot_guards@, old(self).guard_level),
    {
        let ghost init_forgot_guards = forgot_guards@;
        let tracked mut forgot_guards = forgot_guards.get();

        let ghost _cursor = *self;

        let guard_opt = self.take((self.level - 1) as usize);
        assert(guard_opt is Some) by {
            assert(old(self).get_guard_level(self.level) is Some);
        };
        let guard = guard_opt.unwrap();
        assert(guard.wf());
        assert(guard.guard is Some);
        let ghost nid = guard.nid();
        let ghost spin_lock = guard.deref().deref().meta_spec().lock;
        let tracked inner = guard.guard.tracked_unwrap();
        let tracked forgot_guard = inner.inner.get();
        proof {
            assert(forgot_guard =~= old(self).get_guard_level_unwrap(
                old(self).level,
            ).guard->Some_0.inner@);
            assert(!forgot_guards.inner.dom().contains(nid));
            assert(forgot_guard.stray_perm.value() == false);
            assert(forgot_guard.in_protocol == true);
            assert(forgot_guards.is_sub_root(nid)) by {
                old(self).lemma_wf_with_forgot_guards_sound(forgot_guards);
                old(self).lemma_rec_put_guard_from_path_basic(forgot_guards);
                assert(old(self).guards_in_path_wf_with_forgot_guards_singleton(
                    forgot_guards,
                    old(self).g_level@,
                ));
            };
            assert(forgot_guards.children_are_contained(
                nid,
                forgot_guard.pte_token->Some_0.value(),
            )) by {
                old(self).lemma_wf_with_forgot_guards_sound(forgot_guards);
                old(self).lemma_rec_put_guard_from_path_basic(forgot_guards);
                assert(old(self).guards_in_path_wf_with_forgot_guards_singleton(
                    forgot_guards,
                    old(self).g_level@,
                ));
            };
            forgot_guards.tracked_put(nid, forgot_guard, spin_lock);
        }

        self.path[(self.level - 1) as usize] = None;

        self.level = self.level + 1;

        assert(self.wf()) by {
            assert(self.wf_path()) by {
                assert forall|level: PagingLevel|
                    #![trigger self.get_guard_level(level)]
                    #![trigger self.get_guard_level_unwrap(level)]
                    1 <= level <= C::NR_LEVELS_SPEC() implies {
                    if level > self.guard_level {
                        self.get_guard_level(level) is None
                    } else if level >= self.g_level@ {
                        &&& self.get_guard_level(level) is Some
                        &&& self.get_guard_level_unwrap(level).wf()
                        &&& self.get_guard_level_unwrap(level).inst_id() == self.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            self.get_guard_level_unwrap(level).nid(),
                        )
                        &&& self.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value()
                            == false
                        &&& self.get_guard_level_unwrap(level).guard->Some_0.in_protocol() == true
                        &&& va_level_to_nid::<C>(self.va, level) == self.get_guard_level_unwrap(
                            level,
                        ).nid()
                    } else {
                        self.get_guard_level(level) is None
                    }
                } by {
                    assert(self.guard_level == old(self).guard_level);
                    assert(self.g_level@ == old(self).g_level@ + 1);
                    if level > self.guard_level {
                        assert(self.path[level - 1] =~= old(self).path[level - 1]);
                    } else if level >= self.g_level@ {
                        assert(self.path[level - 1] =~= old(self).path[level - 1]);
                    } else {
                        if level == self.g_level@ - 1 {
                            assert(self.get_guard_level(level) is None);
                        } else {
                            assert(self.path[level - 1] =~= old(self).path[level - 1]);
                            assert(old(self).get_guard_level(level) is None);
                        }
                    }
                }
            };
            assert(self.guards_in_path_relation()) by {
                assert forall|level: PagingLevel|
                    #![trigger self.adjacent_guard_is_child(level)]
                    self.g_level@ < level <= self.guard_level implies {
                    self.adjacent_guard_is_child(level)
                } by {
                    assert(old(self).adjacent_guard_is_child(level));
                }
            }
        };
        assert(self.wf_with_forgot_guards(forgot_guards)) by {
            Self::lemma_pop_level_sustains_wf_with_forgot_guards(
                *old(self),
                *self,
                init_forgot_guards,
            );
        };

        let ghost cursor = *self;

        assert(cursor.rec_put_guard_from_path(forgot_guards, cursor.guard_level)
            =~= _cursor.rec_put_guard_from_path(init_forgot_guards, _cursor.guard_level)) by {
            let full_forgot_guards_pre = _cursor.rec_put_guard_from_path(
                init_forgot_guards,
                _cursor.guard_level,
            );
            let full_forgot_guards_post = cursor.rec_put_guard_from_path(
                forgot_guards,
                cursor.guard_level,
            );
            let _nid = _cursor.get_guard_level_unwrap(_cursor.level).nid();
            assert(full_forgot_guards_pre.inner =~= full_forgot_guards_post.inner) by {
                _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                    init_forgot_guards,
                    _cursor.guard_level,
                );
                cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                    forgot_guards,
                    cursor.guard_level,
                );
                assert forall|nid: NodeId|
                    full_forgot_guards_pre.inner.dom().contains(nid) implies {
                    full_forgot_guards_post.inner.dom().contains(nid)
                } by {
                    if nid == _nid {
                    } else if init_forgot_guards.inner.dom().contains(nid) {
                    } else {
                        assert(exists|level: PagingLevel|
                            _cursor.g_level@ <= level <= _cursor.guard_level
                                && #[trigger] _cursor.get_guard_level_unwrap(level).nid() == nid);
                        let level = choose|level: PagingLevel|
                            _cursor.g_level@ <= level <= _cursor.guard_level
                                && #[trigger] _cursor.get_guard_level_unwrap(level).nid() == nid;
                        assert(cursor.get_guard_level_unwrap(level).nid() == nid);
                    }
                };
                assert forall|nid: NodeId|
                    full_forgot_guards_post.inner.dom().contains(nid) implies {
                    full_forgot_guards_pre.inner.dom().contains(nid)
                } by {
                    if nid == _nid {
                    } else if forgot_guards.inner.dom().contains(nid) {
                    } else {
                        assert(exists|level: PagingLevel|
                            cursor.g_level@ <= level <= cursor.guard_level
                                && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid);
                        let level = choose|level: PagingLevel|
                            cursor.g_level@ <= level <= cursor.guard_level
                                && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid;
                        assert(_cursor.get_guard_level_unwrap(level).nid() == nid);
                    }
                };
            }
        };

        Tracked(forgot_guards)
    }

    pub open spec fn wf_push_level(self, post: Self, child_pt: PageTableGuard<'a, C>) -> bool {
        &&& post.level == self.level - 1
        &&& post.g_level@ == self.g_level@ - 1
        &&& forall|level: PagingLevel|
            #![trigger self.get_guard_level(level)]
            #![trigger self.get_guard_level_unwrap(level)]
            1 <= level <= post.guard_level && level != post.level ==> {
                self.get_guard_level(level) =~= post.get_guard_level(level)
            }
        &&& self.get_guard_level(post.level) is None
        &&& post.get_guard_level(post.level) =~= Some(
            child_pt,
        )
        // Other fields remain unchanged.
        &&& self.constant_fields_unchanged(&post)
        &&& self.va == post.va
    }

    /// Goes down a level to a child page table.
    fn push_level(&mut self, child_pt: PageTableGuard<'a, C>)
        requires
            old(self).wf(),
            old(self).level > 1,
            old(self).g_level@ == old(self).level,
            child_pt.wf(),
            child_pt.inst_id() == old(self).inst@.id(),
            child_pt.guard->Some_0.stray_perm().value() == false,
            child_pt.guard->Some_0.in_protocol() == true,
            child_pt.level_spec() == old(self).level - 1,
            node_helper::is_child::<C>(
                old(self).get_guard_level_unwrap(old(self).level).nid(),
                child_pt.nid(),
            ),
        ensures
            old(self).wf_push_level(*self, child_pt),
            self.wf(),
            self.g_level@ == self.level,
    {
        self.level = self.level - 1;
        self.g_level = Ghost(self.level);

        self.path[(self.level - 1) as usize] = Some(child_pt);

        assert(self.wf()) by {
            assert(self.wf_path()) by {
                assert forall|level: PagingLevel|
                    #![trigger self.get_guard_level(level)]
                    #![trigger self.get_guard_level_unwrap(level)]
                    1 <= level <= C::NR_LEVELS_SPEC() implies {
                    if level > self.guard_level {
                        self.get_guard_level(level) is None
                    } else if level >= self.g_level@ {
                        &&& self.get_guard_level(level) is Some
                        &&& self.get_guard_level_unwrap(level).wf()
                        &&& self.get_guard_level_unwrap(level).inst_id() == self.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            self.get_guard_level_unwrap(level).nid(),
                        )
                        &&& self.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value()
                            == false
                        &&& self.get_guard_level_unwrap(level).guard->Some_0.in_protocol() == true
                        &&& va_level_to_nid::<C>(self.va, level) == self.get_guard_level_unwrap(
                            level,
                        ).nid()
                    } else {
                        self.get_guard_level(level) is None
                    }
                } by {
                    assert(self.guard_level == old(self).guard_level);
                    assert(self.g_level@ == old(self).g_level@ - 1);
                    if level > self.guard_level {
                        assert(self.path[level - 1] =~= old(self).path[level - 1]);
                    } else if level >= self.g_level@ {
                        if level == self.g_level@ {
                            assert(self.get_guard_level(level) is Some);
                            assert(self.get_guard_level_unwrap(level) =~= child_pt);
                            assert(va_level_to_nid::<C>(self.va, level) == child_pt.nid()) by {
                                admit();
                            };  // TODO
                        } else {
                            assert(self.path[level - 1] =~= old(self).path[level - 1]);
                        }
                    } else {
                        assert(self.path[level - 1] =~= old(self).path[level - 1]);
                        assert(old(self).get_guard_level(level) is None);
                    }
                };
            };
            assert(self.guards_in_path_relation()) by {
                assert forall|level: PagingLevel|
                    #![trigger self.adjacent_guard_is_child(level)]
                    self.g_level@ < level <= self.guard_level implies {
                    self.adjacent_guard_is_child(level)
                } by {
                    if level > self.g_level@ + 1 {
                        assert(old(self).adjacent_guard_is_child(level));
                    }
                }
            }
        };
    }

    pub open spec fn cur_node(&self) -> Option<PageTableGuard<C>> {
        self.path[self.level - 1]
    }

    pub open spec fn cur_node_unwrap(&self) -> PageTableGuard<C> {
        self.cur_node()->Some_0
    }

    // Note that mut types are not supported in Verus.
    // fn cur_entry(&mut self) -> Entry<'_, C> {
    fn cur_entry(&self) -> (res: Entry<C>)
        requires
            self.wf(),
            self.g_level@ == self.level,
        ensures
            res.wf(self.get_guard_level_unwrap(self.level)),
            res.idx == pte_index::<C>(self.va, self.level),
    {
        assert(self.get_guard_level(self.level) is Some);
        let cur_node = self.path[(self.level - 1) as usize].as_ref().unwrap();
        let idx = pte_index::<C>(self.va, self.level);
        Entry::new_at(idx, cur_node)
    }
}

/// The cursor of a page table that is capable of map, unmap or protect pages.
///
/// It has all the capabilities of a [`Cursor`], which can navigate over the
/// page table corresponding to the address range. A virtual address range
/// in a page table can only be accessed by one cursor, regardless of the
/// mutability of the cursor.
// #[derive(Debug)] // TODO: Implement `Debug` for `CursorMut`.
pub struct CursorMut<'a, C: PageTableConfig>(pub Cursor<'a, C>);

impl<'a, C: PageTableConfig> CursorMut<'a, C> {
    //     /// Creates a cursor claiming exclusive access over the given range.
    //     ///
    //     /// The cursor created will only be able to map, query or jump within the given
    //     /// range. Out-of-bound accesses will result in panics or errors as return values,
    //     /// depending on the access method.
    //     // pub(super) fn new(pt: &'a PageTable<C>, va: &Range<Vaddr>) -> Result<Self, PageTableError> {
    //     //     Cursor::new(pt, va).map(|inner| Self(inner))
    //     // }
    //     /// Gets the current virtual address.
    //     pub fn virt_addr(&self) -> Vaddr {
    //         self.0.virt_addr()
    //     }
    pub open spec fn path_contained(&self, forgot_guards: SubTreeForgotGuard<C>) -> bool {
        forall|level: PagingLevel|
            1 <= level <= self.0.guard_level ==> {
                #[trigger] forgot_guards.inner.dom().contains(
                    va_level_to_nid::<C>(self.0.va, level),
                )
            }
    }

    pub open spec fn new_item_relate(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
        item: C::Item,
    ) -> bool {
        let nid = va_level_to_nid::<C>(self.0.va, 1);
        let idx = pte_index::<C>(self.0.va, 1);
        let guard = forgot_guards.get_guard_inner(nid);

        C::item_into_raw_spec(item).0 == guard.perms.inner.value()[idx as int].inner.paddr()
    }

    //     /// Maps the range starting from the current address to an item.
    //     ///
    //     /// It returns the previously mapped item if that exists.
    //     ///
    //     /// Note that the item `C::Item`, when converted to a raw item, if the page property
    //     /// indicate that it is marked metadata, the function is essentially `mark`.
    //     ///
    //     /// # Panics
    //     ///
    //     /// This function will panic if
    //     ///  - the virtual address range to be mapped is out of the range;
    //     ///  - the alignment of the page is not satisfied by the virtual address;
    //     ///  - it is already mapped to a huge page while the caller wants to map a smaller one.
    //     ///
    //     /// # Safety
    //     ///
    //     /// The caller should ensure that the virtual range being mapped does
    //     /// not affect kernel's memory safety.
    #[verifier::spinoff_prover]
    pub fn map(
        &mut self,
        item: C::Item,
        forgot_guards: Tracked<SubTreeForgotGuard<C>>,
        Tracked(m): Tracked<&LockProtocolModel<C>>,
    ) -> (res: (PageTableItem<C>, Tracked<SubTreeForgotGuard<C>>))
        requires
            old(self).0.wf(),
            old(self).0.g_level@ == old(self).0.level,
            // old(self).0.va % page_size::<C>(1) == 0,
            C::item_into_raw_spec(item).1 == 1,
            old(self).0.va + page_size::<C>(C::item_into_raw_spec(item).1) <= old(
                self,
            ).0.barrier_va.end,
            forgot_guards@.wf(),
            old(self).0.wf_with_forgot_guards(forgot_guards@),
            m.inv(),
            m.inst_id() == old(self).0.inst@.id(),
            m.state() is Locked,
            m.sub_tree_rt() == old(self).0.get_guard_level_unwrap(old(self).0.guard_level).nid(),
        ensures
            self.0.wf(),
            self.0.constant_fields_unchanged(&old(self).0),
            self.0.va > old(self).0.va,
            res.1@.wf(),
            self.0.wf_with_forgot_guards(res.1@),
            // The map succeeds.
            old(self).path_contained(self.0.rec_put_guard_from_path(res.1@, self.0.guard_level)),
            // TODO: Post condition of res.0
            old(self).new_item_relate(
                self.0.rec_put_guard_from_path(res.1@, self.0.guard_level),
                item,
            ),
    {
        let tracked mut forgot_guards = forgot_guards.get();

        let preempt_guard = self.0.preempt_guard;

        let (pa, level, prop) = C::item_into_raw(item);
        assert(level == 1);

        let end = self.0.va + page_size::<C>(level);

        assert(self.0.level >= level);

        // Go down if not applicable.
        while self.0.level != level
            invariant
                old(self).0.wf(),
                self.0.wf(),
                self.0.g_level@ == self.0.level,
                self.0.constant_fields_unchanged(&old(self).0),
                // VA should be unchanged in the loop.
                self.0.va == old(self).0.va,
                // forall |_level: PagingLevel|
                //     #![trigger old(self).0.get_guard_level(_level)]
                //     #![trigger old(self).0.get_guard_level_unwrap(_level)]
                //     old(self).0.level <= _level <= old(self).0.guard_level ==> {
                //         self.0.get_guard_level(_level) =~= old(self).0.get_guard_level(_level)
                //     },
                self.0.get_guard_level_unwrap(self.0.guard_level).nid() =~= old(
                    self,
                ).0.get_guard_level_unwrap(self.0.guard_level).nid(),
                self.0.level <= old(self).0.level,
                self.0.level >= level && level == 1,
                self.0.va < self.0.barrier_va.end,
                forgot_guards.wf(),
                self.0.wf_with_forgot_guards(forgot_guards),
                m.inv(),
                m.inst_id() == old(self).0.inst@.id(),
                m.state() is Locked,
                m.sub_tree_rt() == old(self).0.get_guard_level_unwrap(
                    old(self).0.guard_level,
                ).nid(),
            ensures
                self.0.level == 1,
            decreases self.0.level,
        {
            proof {
                C::lemma_nr_subpage_per_huge_is_512();
                C::lemma_consts_properties();
            }

            let ghost _forgot_guards = forgot_guards;
            let ghost _cursor = self.0;

            let cur_level = self.0.level;
            let ghost cur_va = self.0.va;
            let mut cur_entry = self.0.cur_entry();
            let cur_node = self.0.path[(self.0.level - 1) as usize].as_ref().unwrap();
            let child = cur_entry.to_ref(cur_node);
            match child {
                ChildRef::PageTable(pt) => {
                    assert(cur_level == self.0.cur_node_unwrap().level_spec());
                    assert(cur_level - 1 == pt.level_spec());
                    let ghost nid = pt.nid@;
                    let ghost spin_lock = forgot_guards.get_lock(nid);
                    assert(forgot_guards.is_sub_root_and_contained(nid)) by {
                        self.0.lemma_wf_with_forgot_guards_sound(forgot_guards);
                        self.0.lemma_rec_put_guard_from_path_basic(forgot_guards);
                        let pa_guard = self.0.get_guard_level_unwrap(self.0.level);
                        let pa_inner = pa_guard.guard->Some_0.inner@;
                        let pa_spin_lock = pa_guard.meta_spec().lock;
                        let pa_nid = pa_guard.nid();
                        let idx = pte_index::<C>(self.0.va, self.0.level);
                        assert(node_helper::is_child::<C>(pa_nid, nid)) by {
                            assert(nid == node_helper::get_child::<C>(pa_nid, idx as nat));
                            assert(cur_level > 1);
                            node_helper::lemma_level_dep_relation::<C>(pa_nid);
                            node_helper::lemma_get_child_sound::<C>(pa_nid, idx as nat);
                        };
                        assert(pa_inner.pte_token->Some_0.value().is_alive(idx as nat));
                        let __forgot_guards = self.0.rec_put_guard_from_path(
                            forgot_guards,
                            self.0.level,
                        );
                        assert(__forgot_guards.wf()) by {
                            if self.0.level < self.0.guard_level {
                                assert(self.0.guards_in_path_wf_with_forgot_guards_singleton(
                                    forgot_guards,
                                    (self.0.level + 1) as PagingLevel,
                                ));
                            }
                        };
                        assert(__forgot_guards.is_sub_root_and_contained(pa_nid)) by {
                            assert(self.0.guards_in_path_wf_with_forgot_guards_singleton(
                                forgot_guards,
                                self.0.level,
                            ));
                        };
                        assert(__forgot_guards =~= forgot_guards.put_spec(
                            pa_nid,
                            pa_inner,
                            pa_spin_lock,
                        ));
                        assert(forgot_guards.is_sub_root(nid)) by {
                            assert forall|_nid: NodeId| #[trigger]
                                forgot_guards.inner.dom().contains(_nid) && _nid != nid implies {
                                !node_helper::in_subtree_range::<C>(_nid, nid)
                            } by {
                                assert(__forgot_guards.inner.dom().contains(_nid));
                                assert(__forgot_guards.inner.dom().contains(nid));
                                assert(__forgot_guards.is_sub_root(pa_nid));
                                assert(!forgot_guards.inner.dom().contains(pa_nid));
                                assert(_nid != pa_nid);
                                assert(!node_helper::in_subtree_range::<C>(_nid, pa_nid));
                                if node_helper::in_subtree_range::<C>(_nid, nid) {
                                    assert(node_helper::in_subtree_range::<C>(_nid, pa_nid)) by {
                                        node_helper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range::<
                                            C,
                                        >(_nid, pa_nid, nid);
                                    };
                                }
                            };
                        };
                    };
                    let tracked forgot_guard = forgot_guards.tracked_take(nid);
                    // Admitted due to the same reason as PageTableNode::from_raw.
                    assert(pt.deref().meta_spec().lock =~= spin_lock) by {
                        admit();
                    };
                    let child_pt = pt.make_guard_unchecked(
                        preempt_guard,
                        Tracked(forgot_guard),
                        Ghost(spin_lock),
                    );
                    assert(node_helper::is_child::<C>(
                        self.0.get_guard_level_unwrap(self.0.level).nid(),
                        child_pt.nid(),
                    )) by {
                        let idx = pte_index::<C>(self.0.va, self.0.level);
                        let _guard = self.0.get_guard_level_unwrap(self.0.level);
                        assert(_guard.level_spec() > 1);
                        node_helper::lemma_level_dep_relation::<C>(_guard.nid());
                        node_helper::lemma_get_child_sound::<C>(_guard.nid(), idx as nat);
                    };
                    self.0.push_level(child_pt);
                    assert(self.0.wf_with_forgot_guards(forgot_guards)) by {
                        let _nid = child_pt.nid();
                        let _inner = child_pt.guard->Some_0.inner@;
                        let _spin_lock = child_pt.inner.deref().meta_spec().lock;
                        assert(_nid == nid);
                        assert(_spin_lock =~= spin_lock);
                        assert(_inner =~= _forgot_guards.get_guard_inner(nid)) by {
                            assert(_inner =~= forgot_guard);
                        };
                        assert(_forgot_guards =~= forgot_guards.put_spec(_nid, _inner, _spin_lock))
                            by {
                            assert(forgot_guards =~= _forgot_guards.take_spec(_nid));
                            _forgot_guards.lemma_take_put(_nid);
                        };
                        Cursor::lemma_push_level_sustains_wf_with_forgot_guards(
                            _cursor,
                            self.0,
                            child_pt,
                            forgot_guards,
                        );
                    }
                    assert(self.0.get_guard_level_unwrap(self.0.guard_level).nid() =~= old(
                        self,
                    ).0.get_guard_level_unwrap(self.0.guard_level).nid());
                },
                ChildRef::None => {
                    assert(self.0.cur_node_unwrap().level_spec() == cur_level);
                    let mut cur_node = self.0.take((self.0.level - 1) as usize).unwrap();
                    let ghost _cur_node = cur_node;
                    assert(node_helper::is_not_leaf::<C>(cur_node.nid())) by {
                        assert(cur_node.level_spec() > 1);
                        node_helper::lemma_level_dep_relation::<C>(cur_node.nid());
                    };
                    assert(m.node_is_locked(cur_node.nid())) by {
                        assert(self.0.guard_level == old(self).0.guard_level);
                        let guard_level = old(self).0.guard_level;
                        assert(_cursor.get_guard_level_unwrap(guard_level).nid() =~= old(
                            self,
                        ).0.get_guard_level_unwrap(guard_level).nid());
                        assert(m.sub_tree_rt() == old(self).0.get_guard_level_unwrap(
                            guard_level,
                        ).nid());
                        assert(node_helper::in_subtree_range::<C>(
                            _cursor.get_guard_level_unwrap(guard_level).nid(),
                            cur_node.nid(),
                        )) by {
                            assert(_cursor.wf());
                            _cursor.lemma_guards_in_path_relation(_cursor.guard_level);
                        };
                    };
                    let res = cur_entry.protocol_alloc_if_none(
                        preempt_guard,
                        &mut cur_node,
                        Tracked(m),
                    );
                    assert(cur_node.wf());
                    assert(cur_node.inst_id() == self.0.inst@.id());
                    assert(node_helper::nid_to_level::<C>(cur_node.nid()) == self.0.level);
                    assert(cur_node.guard->Some_0.stray_perm().value() == false);
                    assert(cur_node.guard->Some_0.in_protocol() == true);
                    let child_pt = res.unwrap();
                    self.0.path[(self.0.level - 1) as usize] = Some(cur_node);
                    self.0.g_level = Ghost((self.0.g_level@ - 1) as PagingLevel);

                    assert(self.0.get_guard_level_unwrap(self.0.guard_level).nid() =~= old(
                        self,
                    ).0.get_guard_level_unwrap(self.0.guard_level).nid());

                    assert(self.0.wf()) by {
                        assert(self.0.wf_path()) by {
                            let cursor = self.0;
                            assert forall|level: PagingLevel|
                                #![trigger cursor.get_guard_level(level)]
                                #![trigger cursor.get_guard_level_unwrap(level)]
                                1 <= level <= C::NR_LEVELS_SPEC() implies {
                                if level > cursor.guard_level {
                                    cursor.get_guard_level(level) is None
                                } else if level >= cursor.g_level@ {
                                    &&& cursor.get_guard_level(level) is Some
                                    &&& cursor.get_guard_level_unwrap(level).wf()
                                    &&& cursor.get_guard_level_unwrap(level).inst_id()
                                        == cursor.inst@.id()
                                    &&& level == node_helper::nid_to_level::<C>(
                                        cursor.get_guard_level_unwrap(level).nid(),
                                    )
                                    &&& cursor.get_guard_level_unwrap(
                                        level,
                                    ).guard->Some_0.stray_perm().value() == false
                                    &&& cursor.get_guard_level_unwrap(
                                        level,
                                    ).guard->Some_0.in_protocol() == true
                                    &&& va_level_to_nid::<C>(cursor.va, level)
                                        == cursor.get_guard_level_unwrap(level).nid()
                                } else {
                                    cursor.get_guard_level(level) is None
                                }
                            } by {
                                assert(cursor.guard_level == _cursor.guard_level);
                                assert(cursor.g_level@ == _cursor.g_level@);
                                if level > cursor.guard_level {
                                    assert(cursor.path[level - 1] =~= _cursor.path[level - 1]);
                                } else if level >= cursor.g_level@ {
                                    if level == cursor.g_level@ {
                                        assert(cursor.get_guard_level(level) is Some);
                                        assert(cursor.get_guard_level_unwrap(level) =~= cur_node);
                                    } else {
                                        assert(cursor.path[level - 1] =~= _cursor.path[level - 1]);
                                    }
                                } else {
                                    assert(cursor.path[level - 1] =~= _cursor.path[level - 1]);
                                    assert(_cursor.get_guard_level(level) is None);
                                }
                            };
                        };
                        assert(self.0.guards_in_path_relation()) by {
                            let cursor = self.0;
                            assert forall|level: PagingLevel|
                                #![trigger cursor.adjacent_guard_is_child(level)]
                                cursor.g_level@ < level <= cursor.guard_level implies {
                                cursor.adjacent_guard_is_child(level)
                            } by {
                                assert(_cursor.adjacent_guard_is_child(level));
                            }
                        }
                    };
                    assert(node_helper::is_child::<C>(cur_node.nid(), child_pt.nid())) by {
                        let idx = pte_index::<C>(self.0.va, self.0.level);
                        node_helper::lemma_get_child_sound::<C>(cur_node.nid(), idx as nat);
                    }
                    let ghost __cursor = self.0;
                    assert(__cursor.wf_with_forgot_guards_nid_not_contained(forgot_guards)) by {
                        assert forall|level: PagingLevel|
                            #![trigger __cursor.get_guard_level_unwrap(level)]
                            __cursor.g_level@ <= level <= __cursor.guard_level implies {
                            !(forgot_guards.inner.dom().contains(
                                __cursor.get_guard_level_unwrap(level).nid(),
                            ))
                        } by {
                            assert(__cursor.get_guard_level_unwrap(level).nid()
                                == _cursor.get_guard_level_unwrap(level).nid());
                        };
                    };
                    self.0.push_level(child_pt);
                    assert(self.0.wf_with_forgot_guards(forgot_guards)) by {
                        assert(__cursor.wf_with_forgot_guards(
                            {
                                let nid = child_pt.nid();
                                let inner = child_pt.guard->Some_0.inner@;
                                let spin_lock = child_pt.inner.deref().meta_spec().lock;
                                forgot_guards.put_spec(nid, inner, spin_lock)
                            },
                        )) by {
                            let __forgot_guards = forgot_guards.put_spec(
                                child_pt.nid(),
                                child_pt.guard->Some_0.inner@,
                                child_pt.inner.deref().meta_spec().lock,
                            );
                            assert(__forgot_guards.wf()) by {
                                let idx = pte_index::<C>(_cursor.va, _cursor.level);
                                assert(_cursor.wf_with_forgot_guards(forgot_guards));
                                _cursor.lemma_wf_with_forgot_guards_sound(forgot_guards);
                                assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                    forgot_guards,
                                    _cursor.level,
                                ));
                                _cursor.lemma_rec_put_guard_from_path_basic(forgot_guards);
                                assert(!forgot_guards.inner.dom().contains(child_pt.nid())) by {
                                    assert(forgot_guards.children_are_contained(
                                        _cur_node.nid(),
                                        _cur_node.guard->Some_0.view_pte_token().value(),
                                    ));
                                    assert(_cur_node.guard->Some_0.view_pte_token().value().is_void(
                                        idx as nat,
                                    ));
                                };
                                assert(forgot_guards.is_sub_root(child_pt.nid())) by {
                                    assert(forgot_guards.is_sub_root(_cur_node.nid()));
                                    assert(node_helper::is_child::<C>(
                                        _cur_node.nid(),
                                        child_pt.nid(),
                                    ));
                                    assert(!forgot_guards.inner.dom().contains(_cur_node.nid()));
                                    assert forall|nid: NodeId| #[trigger]
                                        forgot_guards.inner.dom().contains(nid) && nid
                                            != child_pt.nid() implies {
                                        !node_helper::in_subtree_range::<C>(nid, child_pt.nid())
                                    } by {
                                        assert(nid != _cur_node.nid());
                                        assert(!node_helper::in_subtree_range::<C>(
                                            nid,
                                            _cur_node.nid(),
                                        ));
                                        node_helper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range::<
                                            C,
                                        >(nid, _cur_node.nid(), child_pt.nid());
                                    };
                                };
                                assert(forgot_guards.children_are_contained(
                                    child_pt.nid(),
                                    child_pt.guard->Some_0.view_pte_token().value(),
                                )) by {
                                    assert(child_pt.guard->Some_0.inner@.pte_token->Some_0.value()
                                        =~= PteArrayState::empty());
                                    _cursor.lemma_wf_with_forgot_guards_sound(forgot_guards);
                                    assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                        forgot_guards,
                                        _cursor.level,
                                    ));
                                    _cursor.lemma_rec_put_guard_from_path_basic(forgot_guards);
                                    assert(forgot_guards.children_are_contained(
                                        _cur_node.nid(),
                                        _cur_node.guard->Some_0.view_pte_token().value(),
                                    ));
                                    let idx = pte_index::<C>(_cursor.va, _cursor.level);
                                    let _pte_array =
                                        _cur_node.guard->Some_0.view_pte_token().value();
                                    assert(_pte_array.is_void(idx as nat));
                                    assert(forgot_guards.sub_tree_not_contained(child_pt.nid()));
                                    let __pte_array =
                                        child_pt.guard->Some_0.inner@.pte_token->Some_0.value();
                                    if node_helper::is_not_leaf::<C>(child_pt.nid()) {
                                        assert forall|i: nat|
                                            0 <= i < nr_subpage_per_huge::<C>() implies {
                                            #[trigger] __pte_array.is_alive(i)
                                                <==> forgot_guards.inner.dom().contains(
                                                node_helper::get_child::<C>(child_pt.nid(), i),
                                            )
                                        } by {
                                            let ch = node_helper::get_child::<C>(child_pt.nid(), i);
                                            assert(__pte_array.is_void(i));
                                            assert(node_helper::in_subtree_range::<C>(
                                                child_pt.nid(),
                                                ch,
                                            )) by {
                                                node_helper::lemma_get_child_sound::<C>(
                                                    child_pt.nid(),
                                                    i,
                                                );
                                                node_helper::lemma_is_child_implies_in_subtree::<C>(
                                                    child_pt.nid(),
                                                    ch,
                                                );
                                                node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                    C,
                                                >(child_pt.nid(), ch);
                                            };
                                        };
                                        assert forall|i: nat|
                                            0 <= i < nr_subpage_per_huge::<C>() implies {
                                            #[trigger] __pte_array.is_void(i)
                                                ==> forgot_guards.sub_tree_not_contained(
                                                node_helper::get_child::<C>(child_pt.nid(), i),
                                            )
                                        } by {
                                            let ch = node_helper::get_child::<C>(child_pt.nid(), i);
                                            assert(__pte_array.is_void(i));
                                            assert forall|__nid: NodeId| #[trigger]
                                                forgot_guards.inner.dom().contains(__nid) implies {
                                                !node_helper::in_subtree_range::<C>(ch, __nid)
                                            } by {
                                                if node_helper::in_subtree_range::<C>(ch, __nid) {
                                                    assert(node_helper::in_subtree_range::<C>(
                                                        child_pt.nid(),
                                                        __nid,
                                                    )) by {
                                                        node_helper::lemma_get_child_sound::<C>(
                                                            child_pt.nid(),
                                                            i,
                                                        );
                                                        node_helper::lemma_is_child_bound::<C>(
                                                            child_pt.nid(),
                                                            ch,
                                                        );
                                                        node_helper::lemma_is_child_nid_increasing::<
                                                            C,
                                                        >(child_pt.nid(), ch);
                                                    };
                                                }
                                            }
                                        }
                                    }
                                };
                                assert forall|nid: NodeId| #[trigger]
                                    __forgot_guards.inner.dom().contains(nid) implies {
                                    __forgot_guards.children_are_contained(
                                        nid,
                                        __forgot_guards.get_guard_inner(
                                            nid,
                                        ).pte_token->Some_0.value(),
                                    )
                                } by {
                                    let pte_array = __forgot_guards.get_guard_inner(
                                        nid,
                                    ).pte_token->Some_0.value();
                                    if node_helper::is_not_leaf::<C>(nid) {
                                        assert forall|i: nat|
                                            0 <= i < nr_subpage_per_huge::<C>() implies {
                                            #[trigger] pte_array.is_alive(i)
                                                <==> __forgot_guards.inner.dom().contains(
                                                node_helper::get_child::<C>(nid, i),
                                            )
                                        } by {
                                            let ch = node_helper::get_child::<C>(nid, i);
                                            if nid == _cur_node.nid() {
                                            } else if nid == child_pt.nid() {
                                                if __forgot_guards.inner.dom().contains(ch) {
                                                    assert(pte_array.is_alive(i)) by {
                                                        assert(ch != child_pt.nid()) by {
                                                            node_helper::lemma_get_child_sound::<C>(
                                                                child_pt.nid(),
                                                                i,
                                                            );
                                                            node_helper::lemma_is_child_nid_increasing::<
                                                                C,
                                                            >(child_pt.nid(), ch);
                                                        };
                                                        assert(forgot_guards.inner.dom().contains(
                                                            ch,
                                                        ));
                                                    };
                                                }
                                            } else {
                                                if pte_array.is_alive(i) {
                                                    assert(__forgot_guards.inner.dom().contains(
                                                        ch,
                                                    ));
                                                }
                                                if __forgot_guards.inner.dom().contains(ch) {
                                                    assert(pte_array.is_alive(i)) by {
                                                        if ch == child_pt.nid() {
                                                            node_helper::lemma_get_child_sound::<C>(
                                                                nid,
                                                                i,
                                                            );
                                                            node_helper::lemma_is_child_implies_same_pa::<
                                                                C,
                                                            >(_cur_node.nid(), nid, child_pt.nid());
                                                        }
                                                    };
                                                }
                                            }
                                        };
                                        assert forall|i: nat|
                                            0 <= i < nr_subpage_per_huge::<C>() implies {
                                            #[trigger] pte_array.is_void(i)
                                                ==> __forgot_guards.sub_tree_not_contained(
                                                node_helper::get_child::<C>(nid, i),
                                            )
                                        } by {
                                            if pte_array.is_void(i) {
                                                let ch = node_helper::get_child::<C>(nid, i);
                                                assert forall|_nid: NodeId| #[trigger]
                                                    __forgot_guards.inner.dom().contains(
                                                        _nid,
                                                    ) implies {
                                                    !node_helper::in_subtree_range::<C>(ch, _nid)
                                                } by {
                                                    if _nid == nid {
                                                        node_helper::lemma_get_child_sound::<C>(
                                                            nid,
                                                            i,
                                                        );
                                                        node_helper::lemma_is_child_nid_increasing::<
                                                            C,
                                                        >(nid, ch);
                                                    } else {
                                                        if nid == child_pt.nid() {
                                                        } else {
                                                            assert(forgot_guards.sub_tree_not_contained(
                                                            ch));
                                                            if _nid == child_pt.nid() {
                                                                _cursor.lemma_wf_with_forgot_guards_sound(
                                                                forgot_guards);
                                                                assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                                                forgot_guards, _cursor.level));
                                                                _cursor.lemma_rec_put_guard_from_path_basic(
                                                                forgot_guards);
                                                                assert(forgot_guards.children_are_contained(

                                                                    _cur_node.nid(),
                                                                    _cur_node.guard->Some_0.view_pte_token().value(),
                                                                ));
                                                                let idx = pte_index::<C>(
                                                                    _cursor.va,
                                                                    _cursor.level,
                                                                );
                                                                let _pte_array =
                                                                    _cur_node.guard->Some_0.view_pte_token().value();
                                                                assert(_pte_array.is_void(
                                                                    idx as nat,
                                                                ));
                                                                assert(forgot_guards.sub_tree_not_contained(
                                                                child_pt.nid()));
                                                                if node_helper::in_subtree_range::<
                                                                    C,
                                                                >(ch, child_pt.nid()) {
                                                                    assert(node_helper::in_subtree_range::<
                                                                        C,
                                                                    >(ch, cur_node.nid())) by {
                                                                        assert(ch != child_pt.nid())
                                                                            by {
                                                                            if ch
                                                                                == child_pt.nid() {
                                                                                node_helper::lemma_get_child_sound::<
                                                                                    C,
                                                                                >(nid, i);
                                                                                assert(node_helper::is_child::<
                                                                                    C,
                                                                                >(nid, ch));
                                                                                assert(node_helper::is_child::<
                                                                                    C,
                                                                                >(
                                                                                    cur_node.nid(),
                                                                                    child_pt.nid(),
                                                                                ));
                                                                                node_helper::lemma_is_child_implies_same_pa::<
                                                                                    C,
                                                                                >(
                                                                                    nid,
                                                                                    cur_node.nid(),
                                                                                    ch,
                                                                                );
                                                                            }
                                                                        };
                                                                        node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                                            C,
                                                                        >(ch, child_pt.nid());
                                                                        node_helper::lemma_child_in_subtree_implies_in_subtree::<
                                                                            C,
                                                                        >(
                                                                            ch,
                                                                            cur_node.nid(),
                                                                            child_pt.nid(),
                                                                        );
                                                                        node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                                            C,
                                                                        >(ch, cur_node.nid());
                                                                    };
                                                                }
                                                                admit();  // Special
                                                            }
                                                        }
                                                    }
                                                };
                                            }
                                        };
                                    } else {
                                    }
                                };
                            };
                            let full_forgot_guards_pre = _cursor.rec_put_guard_from_path(
                                forgot_guards,
                                _cursor.guard_level,
                            );
                            _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                                forgot_guards,
                                _cursor.guard_level,
                            );
                            _cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(
                                forgot_guards,
                            );
                            assert(full_forgot_guards_pre.get_guard_inner(cur_node.nid())
                                =~= _cur_node.guard->Some_0.inner@) by {
                                _cursor.lemma_put_guard_from_path_top_down_basic1(forgot_guards);
                            };
                            assert(full_forgot_guards_pre.get_lock(cur_node.nid())
                                =~= _cur_node.meta_spec().lock) by {
                                _cursor.lemma_put_guard_from_path_top_down_basic1(forgot_guards);
                            };
                            let full_forgot_guards_post = __cursor.rec_put_guard_from_path(
                                forgot_guards,
                                __cursor.guard_level,
                            );
                            __cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                                forgot_guards,
                                __cursor.guard_level,
                            );
                            __cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(
                                forgot_guards,
                            );
                            let full_forgot_guard_target = __cursor.rec_put_guard_from_path(
                                __forgot_guards,
                                __cursor.guard_level,
                            );
                            __cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                                __forgot_guards,
                                __cursor.guard_level,
                            );
                            __cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(
                                __forgot_guards,
                            );
                            assert(full_forgot_guards_post =~= full_forgot_guards_pre.put_spec(
                                cur_node.nid(),
                                cur_node.guard->Some_0.inner@,
                                cur_node.meta_spec().lock,
                            )) by {
                                let forgot_guards1 = _cursor.put_guard_from_path_top_down(
                                    forgot_guards,
                                    (_cursor.g_level@ + 1) as PagingLevel,
                                );
                                let forgot_guards2 = __cursor.put_guard_from_path_top_down(
                                    forgot_guards,
                                    (__cursor.g_level@ + 1) as PagingLevel,
                                );
                                assert(forgot_guards1.inner =~= forgot_guards2.inner) by {
                                    assert forall|nid: NodeId| #[trigger]
                                        forgot_guards1.inner.dom().contains(nid) implies {
                                        &&& forgot_guards2.inner.dom().contains(nid)
                                        &&& forgot_guards2.inner[nid] =~= forgot_guards1.inner[nid]
                                    } by {
                                        if forgot_guards.inner.dom().contains(nid) {
                                        } else {
                                            assert(exists|level: PagingLevel|
                                                _cursor.g_level@ <= level <= _cursor.guard_level
                                                    && #[trigger] _cursor.get_guard_level_unwrap(
                                                    level,
                                                ).nid() == nid);
                                            let level = choose|level: PagingLevel|
                                                _cursor.g_level@ <= level <= _cursor.guard_level
                                                    && #[trigger] _cursor.get_guard_level_unwrap(
                                                    level,
                                                ).nid() == nid;
                                            assert(__cursor.get_guard_level_unwrap(level).nid()
                                                == nid);
                                        }
                                    };
                                    assert forall|nid: NodeId| #[trigger]
                                        forgot_guards2.inner.dom().contains(nid) implies {
                                        &&& forgot_guards1.inner.dom().contains(nid)
                                        &&& forgot_guards1.inner[nid] =~= forgot_guards2.inner[nid]
                                    } by {
                                        if forgot_guards.inner.dom().contains(nid) {
                                        } else {
                                            assert(exists|level: PagingLevel|
                                                __cursor.g_level@ <= level <= __cursor.guard_level
                                                    && #[trigger] __cursor.get_guard_level_unwrap(
                                                    level,
                                                ).nid() == nid);
                                            let level = choose|level: PagingLevel|
                                                __cursor.g_level@ <= level <= __cursor.guard_level
                                                    && #[trigger] __cursor.get_guard_level_unwrap(
                                                    level,
                                                ).nid() == nid;
                                            assert(_cursor.get_guard_level_unwrap(level).nid()
                                                == nid);
                                        }
                                    };
                                };
                                _cursor.lemma_put_guard_from_path_top_down_basic1(forgot_guards);
                                __cursor.lemma_put_guard_from_path_top_down_basic1(forgot_guards);
                                assert(full_forgot_guards_pre =~= forgot_guards1.put_spec(
                                    _cur_node.nid(),
                                    _cur_node.guard->Some_0.inner@,
                                    _cur_node.meta_spec().lock,
                                ));
                                assert(full_forgot_guards_post =~= forgot_guards2.put_spec(
                                    cur_node.nid(),
                                    cur_node.guard->Some_0.inner@,
                                    cur_node.meta_spec().lock,
                                ));
                                assert(forgot_guards1.put_spec(
                                    _cur_node.nid(),
                                    _cur_node.guard->Some_0.inner@,
                                    _cur_node.meta_spec().lock,
                                ).put_spec(
                                    cur_node.nid(),
                                    cur_node.guard->Some_0.inner@,
                                    cur_node.meta_spec().lock,
                                ) =~= forgot_guards1.put_spec(
                                    cur_node.nid(),
                                    cur_node.guard->Some_0.inner@,
                                    cur_node.meta_spec().lock,
                                )) by {
                                    assert(_cur_node.nid() == cur_node.nid());
                                    let map1 = forgot_guards1.put_spec(
                                        _cur_node.nid(),
                                        _cur_node.guard->Some_0.inner@,
                                        _cur_node.meta_spec().lock,
                                    ).put_spec(
                                        cur_node.nid(),
                                        cur_node.guard->Some_0.inner@,
                                        cur_node.meta_spec().lock,
                                    ).inner;
                                    let map2 = forgot_guards1.put_spec(
                                        cur_node.nid(),
                                        cur_node.guard->Some_0.inner@,
                                        cur_node.meta_spec().lock,
                                    ).inner;
                                    assert(map1 =~= map2);
                                };
                            };
                            assert(full_forgot_guard_target =~= full_forgot_guards_post.put_spec(
                                child_pt.nid(),
                                child_pt.guard->Some_0.inner@,
                                child_pt.inner.deref().meta_spec().lock,
                            )) by {
                                let _full_forgot_guards_post = full_forgot_guards_post.put_spec(
                                    child_pt.nid(),
                                    child_pt.guard->Some_0.inner@,
                                    child_pt.inner.deref().meta_spec().lock,
                                );
                                assert(!full_forgot_guards_post.inner.dom().contains(
                                    child_pt.nid(),
                                )) by {
                                    let idx = pte_index::<C>(_cursor.va, _cursor.level);
                                    assert(!forgot_guards.inner.dom().contains(child_pt.nid())) by {
                                        assert(forgot_guards.children_are_contained(
                                            _cur_node.nid(),
                                            _cur_node.guard->Some_0.view_pte_token().value(),
                                        )) by {
                                            assert(_cursor.wf_with_forgot_guards(forgot_guards));
                                            _cursor.lemma_wf_with_forgot_guards_sound(
                                                forgot_guards,
                                            );
                                            assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                            forgot_guards, _cursor.level));
                                            _cursor.lemma_rec_put_guard_from_path_basic(
                                                forgot_guards,
                                            );
                                        };
                                        assert(_cur_node.guard->Some_0.view_pte_token().value().is_void(
                                        idx as nat));
                                    };
                                    assert forall|level: PagingLevel|
                                        #![trigger __cursor.get_guard_level_unwrap(level)]
                                        __cursor.g_level@ <= level <= __cursor.guard_level implies {
                                        __cursor.get_guard_level_unwrap(level).nid()
                                            != child_pt.nid()
                                    } by {
                                        if __cursor.get_guard_level_unwrap(level).nid()
                                            == child_pt.nid() {
                                            __cursor.lemma_guards_in_path_relation(level);
                                            assert(node_helper::in_subtree_range::<C>(
                                                child_pt.nid(),
                                                _cur_node.nid(),
                                            ));
                                            node_helper::lemma_is_child_nid_increasing::<C>(
                                                _cur_node.nid(),
                                                child_pt.nid(),
                                            );
                                        }
                                    }
                                };
                                assert(full_forgot_guard_target.inner
                                    =~= _full_forgot_guards_post.inner);
                            };

                            assert(full_forgot_guards_pre.inner.dom().contains(cur_node.nid()));
                            assert(!full_forgot_guards_pre.inner.dom().contains(child_pt.nid()));
                            full_forgot_guards_pre.lemma_alloc_hold_wf(
                                cur_node.nid(),
                                child_pt.nid(),
                                pte_index::<C>(_cursor.va, _cursor.level) as nat,
                                cur_node.guard->Some_0.inner@,
                                cur_node.meta_spec().lock,
                                child_pt.guard->Some_0.inner@,
                                child_pt.meta_spec().lock,
                            );

                            assert(full_forgot_guard_target.is_root_and_contained(
                                __cursor.get_guard_level_unwrap(__cursor.guard_level).nid(),
                            )) by {
                                let nid = __cursor.get_guard_level_unwrap(
                                    __cursor.guard_level,
                                ).nid();
                                assert forall|_nid: NodeId| #[trigger]
                                    full_forgot_guard_target.inner.dom().contains(_nid) implies {
                                    node_helper::in_subtree_range::<C>(nid, _nid)
                                } by {
                                    if __forgot_guards.inner.dom().contains(_nid) {
                                        if _nid == child_pt.nid() {
                                            assert(node_helper::in_subtree_range::<C>(
                                                nid,
                                                cur_node.nid(),
                                            )) by {
                                                _cursor.lemma_guard_in_path_relation_implies_in_subtree_range();
                                            };
                                            node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                                nid,
                                                cur_node.nid(),
                                            );
                                            assert(node_helper::is_child::<C>(
                                                cur_node.nid(),
                                                child_pt.nid(),
                                            ));
                                            node_helper::lemma_in_subtree_is_child_in_subtree::<C>(
                                                nid,
                                                cur_node.nid(),
                                                child_pt.nid(),
                                            );
                                            node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                                nid,
                                                child_pt.nid(),
                                            );
                                        }
                                    } else {
                                        assert(exists|level: PagingLevel|
                                            __cursor.g_level@ <= level <= __cursor.guard_level
                                                && #[trigger] __cursor.get_guard_level_unwrap(
                                                level,
                                            ).nid() == _nid);
                                        let level = choose|level: PagingLevel|
                                            __cursor.g_level@ <= level <= __cursor.guard_level
                                                && #[trigger] __cursor.get_guard_level_unwrap(
                                                level,
                                            ).nid() == _nid;
                                        __cursor.lemma_guard_in_path_relation_implies_in_subtree_range();
                                    }
                                };
                            };

                            assert forall|level: PagingLevel|
                                #![trigger __cursor.get_guard_level_unwrap(level)]
                                __cursor.g_level@ <= level <= __cursor.guard_level implies {
                                !__forgot_guards.inner.dom().contains(
                                    __cursor.get_guard_level_unwrap(level).nid(),
                                )
                            } by {};
                        };
                        assert(forgot_guards.is_sub_root(child_pt.nid())) by {
                            assert(forgot_guards =~= _forgot_guards);
                            assert(_forgot_guards.is_sub_root(cur_node.nid())) by {
                                assert(_cursor.wf_with_forgot_guards(forgot_guards));
                                _cursor.lemma_wf_with_forgot_guards_sound(forgot_guards);
                                assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                    forgot_guards,
                                    _cursor.level,
                                ));
                                _cursor.lemma_rec_put_guard_from_path_basic(forgot_guards);
                            };
                            assert forall|_nid: NodeId| #[trigger]
                                forgot_guards.inner.dom().contains(_nid) && _nid
                                    != child_pt.nid() implies {
                                !node_helper::in_subtree_range::<C>(_nid, child_pt.nid())
                            } by {
                                assert(!node_helper::in_subtree_range::<C>(_nid, cur_node.nid()));
                                assert(node_helper::is_child::<C>(cur_node.nid(), child_pt.nid()));
                                node_helper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range::<
                                    C,
                                >(_nid, cur_node.nid(), child_pt.nid());
                            };
                        };
                        assert(forgot_guards.children_are_contained(
                            child_pt.nid(),
                            child_pt.guard->Some_0.inner@.pte_token->Some_0.value(),
                        )) by {
                            assert(child_pt.guard->Some_0.inner@.pte_token->Some_0.value()
                                =~= PteArrayState::empty());
                            _cursor.lemma_wf_with_forgot_guards_sound(forgot_guards);
                            assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                forgot_guards,
                                _cursor.level,
                            ));
                            _cursor.lemma_rec_put_guard_from_path_basic(forgot_guards);
                            assert(forgot_guards.children_are_contained(
                                _cur_node.nid(),
                                _cur_node.guard->Some_0.view_pte_token().value(),
                            ));
                            let idx = pte_index::<C>(_cursor.va, _cursor.level);
                            let _pte_array = _cur_node.guard->Some_0.view_pte_token().value();
                            assert(_pte_array.is_void(idx as nat));
                            assert(forgot_guards.sub_tree_not_contained(child_pt.nid()));
                            let __pte_array =
                                child_pt.guard->Some_0.inner@.pte_token->Some_0.value();
                            if node_helper::is_not_leaf::<C>(child_pt.nid()) {
                                assert forall|i: nat| 0 <= i < nr_subpage_per_huge::<C>() implies {
                                    #[trigger] __pte_array.is_alive(i)
                                        <==> forgot_guards.inner.dom().contains(
                                        node_helper::get_child::<C>(child_pt.nid(), i),
                                    )
                                } by {
                                    let ch = node_helper::get_child::<C>(child_pt.nid(), i);
                                    assert(__pte_array.is_void(i));
                                    assert(node_helper::in_subtree_range::<C>(child_pt.nid(), ch))
                                        by {
                                        node_helper::lemma_get_child_sound::<C>(child_pt.nid(), i);
                                        node_helper::lemma_is_child_implies_in_subtree::<C>(
                                            child_pt.nid(),
                                            ch,
                                        );
                                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                            child_pt.nid(),
                                            ch,
                                        );
                                    };
                                };
                                assert forall|i: nat| 0 <= i < nr_subpage_per_huge::<C>() implies {
                                    #[trigger] __pte_array.is_void(i)
                                        ==> forgot_guards.sub_tree_not_contained(
                                        node_helper::get_child::<C>(child_pt.nid(), i),
                                    )
                                } by {
                                    let ch = node_helper::get_child::<C>(child_pt.nid(), i);
                                    assert(__pte_array.is_void(i));
                                    assert forall|__nid: NodeId| #[trigger]
                                        forgot_guards.inner.dom().contains(__nid) implies {
                                        !node_helper::in_subtree_range::<C>(ch, __nid)
                                    } by {
                                        if node_helper::in_subtree_range::<C>(ch, __nid) {
                                            assert(node_helper::in_subtree_range::<C>(
                                                child_pt.nid(),
                                                __nid,
                                            )) by {
                                                node_helper::lemma_get_child_sound::<C>(
                                                    child_pt.nid(),
                                                    i,
                                                );
                                                node_helper::lemma_is_child_bound::<C>(
                                                    child_pt.nid(),
                                                    ch,
                                                );
                                                node_helper::lemma_is_child_nid_increasing::<C>(
                                                    child_pt.nid(),
                                                    ch,
                                                );
                                            };
                                        }
                                    }
                                }
                            }
                        };
                        Cursor::lemma_push_level_sustains_wf_with_forgot_guards(
                            __cursor,
                            self.0,
                            child_pt,
                            forgot_guards,
                        );
                    };
                },
                ChildRef::Frame(_, _, _) => {
                    assume(false);  // We do not support huge page.
                },
            }
            continue ;
        }
        assert(self.0.level == 1);
        assert(self.0.wf());

        let ghost _cursor = self.0;
        let ghost _forgot_guards = forgot_guards;

        let mut cur_entry = self.0.cur_entry();
        let mut cur_node = self.0.take((self.0.level - 1) as usize).unwrap();
        let ghost _cur_node = cur_node;
        let old_entry = cur_entry.replace(Child::Frame(pa, level, prop), &mut cur_node);
        assert(old_entry !is PageTable) by {
            if old_entry is PageTable {
                let ch = old_entry->PageTable_0.deref().nid@;
                assert(node_helper::is_child::<C>(cur_node.nid(), ch));
                node_helper::lemma_is_child_level_relation::<C>(cur_node.nid(), ch);
                node_helper::lemma_nid_to_dep_up_bound::<C>(ch);
                node_helper::lemma_level_dep_relation::<C>(ch);
            }
        };
        self.0.path[(self.0.level - 1) as usize] = Some(cur_node);
        self.0.g_level = Ghost((self.0.g_level@ - 1) as PagingLevel);
        assert(cur_node.wf());
        assert(cur_node.inst_id() == self.0.inst@.id());
        assert(node_helper::nid_to_level::<C>(cur_node.nid()) == 1);
        assert(cur_node.guard->Some_0.stray_perm().value() == false);
        assert(cur_node.guard->Some_0.in_protocol() == true);

        assert(self.0.wf()) by {
            assert(self.0.wf_path()) by {
                let cursor = self.0;
                assert forall|level: PagingLevel|
                    #![trigger cursor.get_guard_level(level)]
                    #![trigger cursor.get_guard_level_unwrap(level)]
                    1 <= level <= C::NR_LEVELS_SPEC() implies {
                    if level > cursor.guard_level {
                        cursor.get_guard_level(level) is None
                    } else if level >= cursor.g_level@ {
                        &&& cursor.get_guard_level(level) is Some
                        &&& cursor.get_guard_level_unwrap(level).wf()
                        &&& cursor.get_guard_level_unwrap(level).inst_id() == cursor.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            cursor.get_guard_level_unwrap(level).nid(),
                        )
                        &&& cursor.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value()
                            == false
                        &&& cursor.get_guard_level_unwrap(level).guard->Some_0.in_protocol() == true
                        &&& va_level_to_nid::<C>(cursor.va, level) == cursor.get_guard_level_unwrap(
                            level,
                        ).nid()
                    } else {
                        cursor.get_guard_level(level) is None
                    }
                } by {
                    assert(cursor.guard_level == _cursor.guard_level);
                    assert(cursor.g_level@ == _cursor.g_level@);
                    if level > cursor.guard_level {
                        assert(cursor.path[level - 1] =~= _cursor.path[level - 1]);
                    } else if level >= cursor.g_level@ {
                        if level == cursor.g_level@ {
                            assert(cursor.get_guard_level(level) is Some);
                            assert(cursor.get_guard_level_unwrap(level) =~= cur_node);
                        } else {
                            assert(cursor.path[level - 1] =~= _cursor.path[level - 1]);
                        }
                    } else {
                        assert(cursor.path[level - 1] =~= _cursor.path[level - 1]);
                        assert(_cursor.get_guard_level(level) is None);
                    }
                };
            };
            assert(self.0.guards_in_path_relation()) by {
                let cursor = self.0;
                assert forall|level: PagingLevel|
                    #![trigger cursor.adjacent_guard_is_child(level)]
                    cursor.g_level@ < level <= cursor.guard_level implies {
                    cursor.adjacent_guard_is_child(level)
                } by {
                    assert(_cursor.adjacent_guard_is_child(level));
                }
            }
        };
        assert(self.0.wf_with_forgot_guards(forgot_guards)) by {
            let cursor = self.0;
            assert(self.0.level == 1);
            assert(cursor.g_level@ == _cursor.g_level@);
            assert(cursor.guard_level == _cursor.guard_level);
            assert(cursor.wf_with_forgot_guards_nid_not_contained(forgot_guards)) by {
                assert forall|level: PagingLevel|
                    #![trigger cursor.get_guard_level_unwrap(level)]
                    cursor.g_level@ <= level <= cursor.guard_level implies {
                    !forgot_guards.inner.dom().contains(cursor.get_guard_level_unwrap(level).nid())
                } by {
                    assert(cursor.get_guard_level_unwrap(level).nid()
                        == _cursor.get_guard_level_unwrap(level).nid());
                };
            };
            let full_forgot_guards_pre = _cursor.rec_put_guard_from_path(
                _forgot_guards,
                _cursor.guard_level,
            );
            _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                _forgot_guards,
                _cursor.guard_level,
            );
            _cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(_forgot_guards);
            let full_forgot_guards_post = cursor.rec_put_guard_from_path(
                forgot_guards,
                cursor.guard_level,
            );
            cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                forgot_guards,
                cursor.guard_level,
            );
            cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(forgot_guards);
            assert(full_forgot_guards_post.wf()) by {
                assert(full_forgot_guards_post =~= full_forgot_guards_pre.put_spec(
                    cur_node.nid(),
                    cur_node.guard->Some_0.inner@,
                    cur_node.meta_spec().lock,
                )) by {
                    let _full_forgot_guards_pre = full_forgot_guards_pre.put_spec(
                        cur_node.nid(),
                        cur_node.guard->Some_0.inner@,
                        cur_node.meta_spec().lock,
                    );
                    assert(full_forgot_guards_post.inner =~= _full_forgot_guards_pre.inner) by {
                        assert forall|nid: NodeId| #[trigger]
                            full_forgot_guards_post.inner.dom().contains(nid) implies {
                            &&& _full_forgot_guards_pre.inner.dom().contains(nid)
                            &&& _full_forgot_guards_pre.inner[nid]
                                =~= full_forgot_guards_post.inner[nid]
                        } by {
                            if nid == cur_node.nid() {
                            } else if forgot_guards.inner.dom().contains(nid) {
                            } else {
                                assert(exists|level: PagingLevel|
                                    cursor.g_level@ <= level <= cursor.guard_level
                                        && #[trigger] cursor.get_guard_level_unwrap(level).nid()
                                        == nid);
                                let level = choose|level: PagingLevel|
                                    cursor.g_level@ <= level <= cursor.guard_level
                                        && #[trigger] cursor.get_guard_level_unwrap(level).nid()
                                        == nid;
                                assert(_cursor.get_guard_level_unwrap(level).nid() == nid);
                            }
                        };
                        assert forall|nid: NodeId| #[trigger]
                            _full_forgot_guards_pre.inner.dom().contains(nid) implies {
                            &&& full_forgot_guards_post.inner.dom().contains(nid)
                            &&& full_forgot_guards_post.inner[nid]
                                =~= _full_forgot_guards_pre.inner[nid]
                        } by {
                            if nid == cur_node.nid() {
                                assert(cursor.get_guard_level_unwrap(cursor.level).nid() == nid);
                            } else if forgot_guards.inner.dom().contains(nid) {
                            } else {
                                assert(exists|level: PagingLevel|
                                    _cursor.g_level@ <= level <= _cursor.guard_level
                                        && #[trigger] _cursor.get_guard_level_unwrap(level).nid()
                                        == nid);
                                let level = choose|level: PagingLevel|
                                    _cursor.g_level@ <= level <= _cursor.guard_level
                                        && #[trigger] _cursor.get_guard_level_unwrap(level).nid()
                                        == nid;
                                assert(cursor.get_guard_level_unwrap(level).nid() == nid);
                            }
                        };
                    };
                };

                assert(full_forgot_guards_pre.get_lock(cur_node.nid())
                    =~= _cur_node.meta_spec().lock) by {
                    _cursor.lemma_put_guard_from_path_top_down_basic1(forgot_guards);
                };

                full_forgot_guards_pre.lemma_replace_with_equal_guard_hold_wf(
                    cur_node.nid(),
                    cur_node.guard->Some_0.inner@,
                    cur_node.meta_spec().lock,
                );
            };
            assert(full_forgot_guards_pre.inner.dom() =~= full_forgot_guards_post.inner.dom()) by {
                _cursor.lemma_put_guard_from_path_top_down_basic1(_forgot_guards);
                cursor.lemma_put_guard_from_path_top_down_basic1(forgot_guards);
                assert forall|nid: NodeId|
                    full_forgot_guards_pre.inner.dom().contains(nid) implies {
                    full_forgot_guards_post.inner.dom().contains(nid)
                } by {
                    if nid == cur_node.nid() {
                    } else if forgot_guards.inner.dom().contains(nid) {
                    } else {
                        assert(exists|level: PagingLevel|
                            _cursor.g_level@ <= level <= _cursor.guard_level
                                && #[trigger] _cursor.get_guard_level_unwrap(level).nid() == nid);
                        let level = choose|level: PagingLevel|
                            _cursor.g_level@ <= level <= _cursor.guard_level
                                && #[trigger] _cursor.get_guard_level_unwrap(level).nid() == nid;
                        assert(cursor.get_guard_level_unwrap(level).nid() == nid);
                    }
                };
                assert forall|nid: NodeId|
                    full_forgot_guards_post.inner.dom().contains(nid) implies {
                    full_forgot_guards_pre.inner.dom().contains(nid)
                } by {
                    if nid == cur_node.nid() {
                    } else if forgot_guards.inner.dom().contains(nid) {
                    } else {
                        assert(exists|level: PagingLevel|
                            cursor.g_level@ <= level <= cursor.guard_level
                                && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid);
                        let level = choose|level: PagingLevel|
                            cursor.g_level@ <= level <= cursor.guard_level
                                && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid;
                        assert(_cursor.get_guard_level_unwrap(level).nid() == nid);
                    }
                };
            };
        };

        let old_va = self.0.va;
        let old_len = page_size::<C>(self.0.level);

        let ghost __cursor = self.0;
        let ghost __forgot_guards = forgot_guards;

        let res = self.0.move_forward(Tracked(forgot_guards));
        proof {
            forgot_guards = res.get();
        }

        let res = match old_entry {
            Child::Frame(pa, level, prop) => PageTableItem::Mapped {
                va: old_va,
                page: pa,
                prop: prop,
            },
            Child::None => PageTableItem::NotMapped { va: old_va, len: old_len },
            Child::PageTable(pt) => PageTableItem::StrayPageTable { pt, va: old_va, len: old_len },
        };

        assert(old(self).path_contained(
            self.0.rec_put_guard_from_path(forgot_guards, self.0.guard_level),
        )) by {
            let cursor = self.0;
            let full_forgot_guards_pre = _cursor.rec_put_guard_from_path(
                _forgot_guards,
                _cursor.guard_level,
            );
            let full_forgot_guards_mid = __cursor.rec_put_guard_from_path(
                __forgot_guards,
                __cursor.guard_level,
            );
            let full_forgot_guards_post = cursor.rec_put_guard_from_path(
                forgot_guards,
                cursor.guard_level,
            );

            assert(full_forgot_guards_mid =~= full_forgot_guards_post);

            assert forall|level: PagingLevel| 1 <= level <= self.0.guard_level implies {
                #[trigger] full_forgot_guards_mid.inner.dom().contains(
                    va_level_to_nid::<C>(_cursor.va, level),
                )
            } by {
                let nid = va_level_to_nid::<C>(_cursor.va, level);
                assert(nid == _cursor.get_guard_level_unwrap(level).nid());
                assert(full_forgot_guards_pre.inner.dom().contains(nid)) by {
                    _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                        _forgot_guards,
                        _cursor.guard_level,
                    );
                };
                assert(full_forgot_guards_mid =~= full_forgot_guards_pre.put_spec(
                    cur_node.nid(),
                    cur_node.guard->Some_0.inner@,
                    cur_node.meta_spec().lock,
                )) by {
                    let _full_forgot_guards_pre = full_forgot_guards_pre.put_spec(
                        cur_node.nid(),
                        cur_node.guard->Some_0.inner@,
                        cur_node.meta_spec().lock,
                    );
                    assert(full_forgot_guards_mid.inner =~= _full_forgot_guards_pre.inner) by {
                        _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                            _forgot_guards,
                            _cursor.guard_level,
                        );
                        __cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                            __forgot_guards,
                            __cursor.guard_level,
                        );
                        assert forall|nid: NodeId| #[trigger]
                            full_forgot_guards_mid.inner.dom().contains(nid) implies {
                            &&& _full_forgot_guards_pre.inner.dom().contains(nid)
                            &&& _full_forgot_guards_pre.inner[nid]
                                =~= full_forgot_guards_mid.inner[nid]
                        } by {
                            if nid == cur_node.nid() {
                            } else if __forgot_guards.inner.dom().contains(nid) {
                            } else {
                                assert(exists|level: PagingLevel|
                                    __cursor.g_level@ <= level <= __cursor.guard_level
                                        && #[trigger] __cursor.get_guard_level_unwrap(level).nid()
                                        == nid);
                                let level = choose|level: PagingLevel|
                                    __cursor.g_level@ <= level <= __cursor.guard_level
                                        && #[trigger] __cursor.get_guard_level_unwrap(level).nid()
                                        == nid;
                                assert(_cursor.get_guard_level_unwrap(level).nid() == nid);
                            }
                        };
                        assert forall|nid: NodeId| #[trigger]
                            _full_forgot_guards_pre.inner.dom().contains(nid) implies {
                            &&& full_forgot_guards_mid.inner.dom().contains(nid)
                            &&& full_forgot_guards_mid.inner[nid]
                                =~= _full_forgot_guards_pre.inner[nid]
                        } by {
                            if nid == cur_node.nid() {
                            } else if _forgot_guards.inner.dom().contains(nid) {
                            } else {
                                assert(exists|level: PagingLevel|
                                    _cursor.g_level@ <= level <= _cursor.guard_level
                                        && #[trigger] _cursor.get_guard_level_unwrap(level).nid()
                                        == nid);
                                let level = choose|level: PagingLevel|
                                    _cursor.g_level@ <= level <= _cursor.guard_level
                                        && #[trigger] _cursor.get_guard_level_unwrap(level).nid()
                                        == nid;
                                assert(__cursor.get_guard_level_unwrap(level).nid() == nid);
                            }
                        };
                    };
                };
            };
            assert forall|level: PagingLevel| 1 <= level <= self.0.guard_level implies {
                #[trigger] full_forgot_guards_post.inner.dom().contains(
                    va_level_to_nid::<C>(_cursor.va, level),
                )
            } by {};
        };
        assert(old(self).new_item_relate(
            self.0.rec_put_guard_from_path(forgot_guards, self.0.guard_level),
            item,
        )) by {
            let cursor = self.0;
            let nid = va_level_to_nid::<C>(_cursor.va, 1);
            assert(nid == __cursor.get_guard_level_unwrap(1).nid());
            let idx = pte_index::<C>(_cursor.va, 1);
            assert(_cursor.va == __cursor.va);
            assert(__cursor.get_guard_level(1) is Some);
            let guard = __cursor.get_guard_level_unwrap(1);
            assert(C::item_into_raw_spec(item).0
                == guard.guard->Some_0.inner@.perms.inner.value()[idx as int].inner.paddr());
            assert(old(self).new_item_relate(
                __cursor.rec_put_guard_from_path(__forgot_guards, __cursor.guard_level),
                item,
            )) by {
                let full_forgot_guard = __cursor.rec_put_guard_from_path(
                    __forgot_guards,
                    __cursor.guard_level,
                );
                assert(guard.guard->Some_0.inner@ =~= full_forgot_guard.get_guard_inner(nid)) by {
                    __cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                        __forgot_guards,
                        __cursor.guard_level,
                    );
                    __cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(__forgot_guards);
                    __cursor.lemma_put_guard_from_path_top_down_basic1(__forgot_guards);
                    assert(__cursor.g_level@ == 1);
                };
            };
            let full_forgot_guards_pre = __cursor.rec_put_guard_from_path(
                __forgot_guards,
                __cursor.guard_level,
            );
            let full_forgot_guards_post = cursor.rec_put_guard_from_path(
                forgot_guards,
                cursor.guard_level,
            );
            assert(full_forgot_guards_pre =~= full_forgot_guards_post);
        };

        (res, Tracked(forgot_guards))
    }

    //     /// Find and remove the first page in the cursor's following range.
    //     ///
    //     /// The range to be found in is the current virtual address with the
    //     /// provided length.
    //     ///
    //     /// The function stops and yields the page if it has actually removed a
    //     /// page, no matter if the following pages are also required to be unmapped.
    //     /// The returned page is the virtual page that existed before the removal
    //     /// but having just been unmapped.
    //     ///
    //     /// It also makes the cursor moves forward to the next page after the
    //     /// removed one, when an actual page is removed. If no mapped pages exist
    //     /// in the following range, the cursor will stop at the end of the range
    //     /// and return [`PageTableItem::NotMapped`].
    //     ///
    //     /// # Safety
    //     ///
    //     /// The caller should ensure that the range being unmapped does not affect
    //     /// kernel's memory safety.
    //     ///
    //     /// # Panics
    //     ///
    //     /// This function will panic if the end range covers a part of a huge page
    //     /// and the next page is that huge page.
    #[verifier::spinoff_prover]
    pub unsafe fn take_next(
        &mut self,
        len: usize,
        forgot_guards: Tracked<SubTreeForgotGuard<C>>,
        Tracked(m): Tracked<&LockProtocolModel<C>>,
    ) -> (res: (PageTableItem<C>, Tracked<SubTreeForgotGuard<C>>))
        requires
            old(self).0.wf(),
            old(self).0.g_level@ == old(self).0.level,
            old(self).0.va as int + len as int <= old(self).0.barrier_va.end as int,
            len > 0 && len % page_size::<C>(1) == 0,
            forgot_guards@.wf(),
            old(self).0.wf_with_forgot_guards(forgot_guards@),
            m.inv(),
            m.inst_id() == old(self).0.inst@.id(),
            m.state() is Locked,
            m.sub_tree_rt() == old(self).0.get_guard_level_unwrap(old(self).0.guard_level).nid(),
        ensures
            self.0.wf(),
            self.0.g_level@ == self.0.level,
            self.0.constant_fields_unchanged(&old(self).0),
            res.1@.wf(),
            self.0.wf_with_forgot_guards(res.1@),
    {
        let tracked forgot_guards = forgot_guards.get();

        let preempt_guard = self.0.preempt_guard;

        let start = self.0.va;
        assert(start % page_size::<C>(1) == 0);
        assert(len % page_size::<C>(1) == 0);
        let end = start + len;
        assert(end % page_size::<C>(1) == 0) by {
            admit();  // TODO
        };
        assert(end <= self.0.barrier_va.end);

        while self.0.va < end
            invariant
                self.0.wf(),
                self.0.g_level@ == self.0.level,
                self.0.constant_fields_unchanged(&old(self).0),
                self.0.get_guard_level_unwrap(self.0.guard_level).nid() =~= old(
                    self,
                ).0.get_guard_level_unwrap(self.0.guard_level).nid(),
                forgot_guards.wf(),
                self.0.wf_with_forgot_guards(forgot_guards),
                start <= self.0.va <= end <= self.0.barrier_va.end,
                end % page_size::<C>(1) == 0,
                m.inv(),
                m.inst_id() == old(self).0.inst@.id(),
                m.state() is Locked,
                m.sub_tree_rt() == old(self).0.get_guard_level_unwrap(
                    old(self).0.guard_level,
                ).nid(),
            ensures
                self.0.va == end,
            decreases
                    end - self.0.va,
                    // for push_level, only level decreases
                    self.0.level,
        {
            assert(C::NR_LEVELS() == 4) by {
                admit();  // TODO
            };

            let cur_va = self.0.va;
            let cur_level = self.0.level;
            let mut cur_entry = self.0.cur_entry();

            assert(self.0.va + page_size::<C>(self.0.level) < MAX_USERSPACE_VADDR) by {
                admit();  // TODO
            };

            // Skip if it is already absent.
            if cur_entry.is_none() {
                if self.0.va + page_size::<C>(self.0.level) > end {
                    let ghost _cursor = self.0;
                    self.0.va = end;
                    proof {
                        take_next_change_va_hold_wf(_cursor, self.0, forgot_guards);
                    }
                    break ;
                }
                assert(self.0.va + page_size::<C>(self.0.level) <= end);
                let ghost _cursor = self.0;
                let res = self.0.move_forward(Tracked(forgot_guards));
                proof {
                    forgot_guards = res.get();
                }
                let ghost pg_size = page_size::<C>(_cursor.level);
                assert(self.0.va == align_down(_cursor.va, pg_size) + pg_size);
                assert(_cursor.va <= self.0.va <= end) by {
                    assert(align_down(_cursor.va, pg_size) <= _cursor.va) by {
                        lemma_align_down_basic(_cursor.va, pg_size);
                    };
                };
                continue ;
            }
            // Go down if not applicable.

            assert(!cur_entry.is_none_spec());

            if cur_va % page_size::<C>(cur_level) != 0 || cur_va + page_size::<C>(cur_level) > end {
                assert(cur_va % page_size::<C>(1) == 0);
                proof {
                    if cur_level == 1 {
                        assert(cur_va % page_size::<C>(cur_level) == 0);
                        assert(cur_va + page_size::<C>(cur_level) <= end) by {
                            assert(cur_va < end);
                            let k = page_size::<C>(1);
                            assert(cur_va % k == 0);
                            assert(end % k == 0);
                            if cur_va + k > end {
                                assert(cur_va >= end) by {
                                    let t1 = cur_va / k;
                                    assert(cur_va == t1 * k) by {
                                        admit();  // TODO
                                    };
                                    let t2 = end / k;
                                    assert(end == t2 * k) by {
                                        admit();  // TODO
                                    };
                                    assert(t1 + 1 > t2) by {
                                        admit();  // TODO
                                    };
                                    assert(t1 >= t2);
                                    assert(cur_va >= end) by {
                                        admit();  // TODO
                                    };
                                }
                            }
                        }
                    }
                }

                assert(cur_level > 1);

                let cur_node = self.0.path[(self.0.level - 1) as usize].as_ref().unwrap();
                let child = cur_entry.to_ref(cur_node);
                match child {
                    ChildRef::PageTable(pt) => {
                        let ghost _forgot_guards = forgot_guards;
                        let ghost nid = pt.nid@;
                        let ghost spin_lock = forgot_guards.get_lock(nid);
                        assert(forgot_guards.is_sub_root_and_contained(nid)) by {
                            C::lemma_consts_properties();
                            C::lemma_nr_subpage_per_huge_is_512();
                            self.0.lemma_wf_with_forgot_guards_sound(forgot_guards);
                            self.0.lemma_rec_put_guard_from_path_basic(forgot_guards);
                            let pa_guard = self.0.get_guard_level_unwrap(self.0.level);
                            let pa_inner = pa_guard.guard->Some_0.inner@;
                            let pa_spin_lock = pa_guard.meta_spec().lock;
                            let pa_nid = pa_guard.nid();
                            let idx = pte_index::<C>(self.0.va, self.0.level);
                            assert(node_helper::is_child::<C>(pa_nid, nid)) by {
                                assert(nid == node_helper::get_child::<C>(pa_nid, idx as nat));
                                node_helper::lemma_level_dep_relation::<C>(pa_nid);
                                node_helper::lemma_get_child_sound::<C>(pa_nid, idx as nat);
                            };
                            assert(pa_inner.pte_token->Some_0.value().is_alive(idx as nat));
                            let __forgot_guards = self.0.rec_put_guard_from_path(
                                forgot_guards,
                                self.0.level,
                            );
                            assert(__forgot_guards.wf()) by {
                                if self.0.level < self.0.guard_level {
                                    assert(self.0.guards_in_path_wf_with_forgot_guards_singleton(
                                        forgot_guards,
                                        (self.0.level + 1) as PagingLevel,
                                    ));
                                }
                            };
                            assert(__forgot_guards.is_sub_root_and_contained(pa_nid)) by {
                                assert(self.0.guards_in_path_wf_with_forgot_guards_singleton(
                                    forgot_guards,
                                    self.0.level,
                                ));
                            };
                            assert(__forgot_guards =~= forgot_guards.put_spec(
                                pa_nid,
                                pa_inner,
                                pa_spin_lock,
                            ));
                            assert(forgot_guards.is_sub_root(nid)) by {
                                assert forall|_nid: NodeId| #[trigger]
                                    forgot_guards.inner.dom().contains(_nid) && _nid
                                        != nid implies {
                                    !node_helper::in_subtree_range::<C>(_nid, nid)
                                } by {
                                    assert(__forgot_guards.inner.dom().contains(_nid));
                                    assert(__forgot_guards.inner.dom().contains(nid));
                                    assert(__forgot_guards.is_sub_root(pa_nid));
                                    assert(!forgot_guards.inner.dom().contains(pa_nid));
                                    assert(_nid != pa_nid);
                                    assert(!node_helper::in_subtree_range::<C>(_nid, pa_nid));
                                    if node_helper::in_subtree_range::<C>(_nid, nid) {
                                        assert(node_helper::in_subtree_range::<C>(_nid, pa_nid))
                                            by {
                                            node_helper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range::<
                                                C,
                                            >(_nid, pa_nid, nid);
                                        };
                                    }
                                };
                            };
                        };
                        let tracked forgot_guard = forgot_guards.tracked_take(nid);
                        // Admitted due to the same reason as PageTableNode::from_raw.
                        assert(pt.deref().meta_spec().lock =~= spin_lock) by {
                            admit();
                        };
                        let pt = pt.make_guard_unchecked(
                            preempt_guard,
                            Tracked(forgot_guard),
                            Ghost(spin_lock),
                        );
                        assert(node_helper::is_child::<C>(cur_node.nid(), pt.nid())) by {
                            node_helper::lemma_level_dep_relation::<C>(cur_node.nid());
                            let idx = pte_index::<C>(self.0.va, self.0.level);
                            assert(pt.nid() == node_helper::get_child::<C>(
                                cur_node.nid(),
                                idx as nat,
                            ));
                            node_helper::lemma_get_child_sound::<C>(cur_node.nid(), idx as nat);
                        };
                        // If there's no mapped PTEs in the next level, we can
                        // skip to save time.
                        if pt.nr_children() != 0 {
                            let ghost _cursor = self.0;
                            self.0.push_level(pt);
                            assert(self.0.wf_with_forgot_guards(forgot_guards)) by {
                                let _nid = pt.nid();
                                let _inner = pt.guard->Some_0.inner@;
                                let _spin_lock = pt.inner.deref().meta_spec().lock;
                                assert(_nid == nid);
                                assert(_spin_lock =~= spin_lock);
                                assert(_inner =~= _forgot_guards.get_guard_inner(nid)) by {
                                    assert(_inner =~= forgot_guard);
                                };
                                assert(_forgot_guards =~= forgot_guards.put_spec(
                                    _nid,
                                    _inner,
                                    _spin_lock,
                                )) by {
                                    assert(forgot_guards =~= _forgot_guards.take_spec(_nid));
                                    _forgot_guards.lemma_take_put(_nid);
                                };
                                Cursor::lemma_push_level_sustains_wf_with_forgot_guards(
                                    _cursor,
                                    self.0,
                                    pt,
                                    forgot_guards,
                                );
                            };
                        } else {
                            let ghost nid = pt.nid();
                            let ghost spin_lock = pt.inner.deref().meta_spec().lock;
                            let tracked guard = pt.guard.tracked_unwrap().inner.get();
                            proof {
                                forgot_guards.tracked_put(nid, guard, spin_lock);
                            }
                            assert(self.0.wf_with_forgot_guards(forgot_guards)) by {
                                assert(forgot_guards.inner =~= _forgot_guards.inner);
                            };
                            if self.0.va + page_size::<C>(self.0.level) > end {
                                let ghost _cursor = self.0;
                                self.0.va = end;
                                proof {
                                    take_next_change_va_hold_wf(_cursor, self.0, forgot_guards);
                                }
                                break ;
                            }
                            assert(self.0.va + page_size::<C>(self.0.level) <= end);
                            assert(align_down(self.0.va, page_size::<C>(self.0.level)) <= self.0.va)
                                by {
                                lemma_align_down_basic(self.0.va, page_size::<C>(self.0.level));
                            };
                            let res = self.0.move_forward(Tracked(forgot_guards));
                            proof {
                                forgot_guards = res.get();
                            }
                        }
                    },
                    ChildRef::None => {
                        // unreachable!("Already checked");
                        assert(false);
                    },
                    ChildRef::Frame(_, _, _) => {
                        // panic!("Removing part of a huge page");
                        assume(false);  // FIXME: implement split if huge page
                    },
                }

                continue ;
            }
            // Unmap the current page and return it.

            assert(!cur_entry.is_none_spec());
            let old_pte_paddr = cur_entry.pte.inner.pte_paddr();
            assert(old_pte_paddr == cur_entry.pte.inner.pte_paddr());

            let ghost _cursor = self.0;
            let ghost _forgot_guards = forgot_guards;

            let mut cur_node = self.0.take((self.0.level - 1) as usize).unwrap();
            let ghost _cur_node = cur_node;
            let old = cur_entry.replace(Child::None, &mut cur_node);
            // assert(cur_node.wf());
            assert(cur_node.inst_id() == self.0.inst@.id());
            assert(cur_node.guard->Some_0.stray_perm().value() == false);
            assert(cur_node.guard->Some_0.in_protocol() == true);

            let item = match old {
                Child::Frame(page, level, prop) => {
                    self.0.path[(self.0.level - 1) as usize] = Some(cur_node);
                    self.0.g_level = Ghost((self.0.g_level@ - 1) as PagingLevel);

                    PageTableItem::Mapped { va: self.0.va, page, prop }
                },
                Child::PageTable(pt) => {
                    assert(cur_node.guard->Some_0.view_pte_token().value()
                        =~= _cur_node.guard->Some_0.view_pte_token().value());

                    // SAFETY: We must have locked this node.
                    let ghost nid = pt.deref().nid@;
                    assert(forgot_guards.is_sub_root_and_contained(nid)) by {
                        C::lemma_consts_properties();
                        C::lemma_nr_subpage_per_huge_is_512();
                        _cursor.lemma_wf_with_forgot_guards_sound(forgot_guards);
                        _cursor.lemma_rec_put_guard_from_path_basic(forgot_guards);
                        let pa_guard = _cursor.get_guard_level_unwrap(_cursor.level);
                        let pa_inner = pa_guard.guard->Some_0.inner@;
                        let pa_spin_lock = pa_guard.meta_spec().lock;
                        let pa_nid = pa_guard.nid();
                        let idx = pte_index::<C>(_cursor.va, _cursor.level);
                        assert(node_helper::is_child::<C>(pa_nid, nid)) by {
                            assert(nid == node_helper::get_child::<C>(pa_nid, idx as nat));
                            node_helper::lemma_level_dep_relation::<C>(pa_nid);
                            node_helper::lemma_get_child_sound::<C>(pa_nid, idx as nat);
                        };
                        assert(pa_inner.pte_token->Some_0.value().is_alive(idx as nat));
                        let __forgot_guards = _cursor.rec_put_guard_from_path(
                            forgot_guards,
                            _cursor.level,
                        );
                        assert(__forgot_guards.wf()) by {
                            if _cursor.level < _cursor.guard_level {
                                assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                    forgot_guards,
                                    (_cursor.level + 1) as PagingLevel,
                                ));
                            }
                        };
                        assert(__forgot_guards.is_sub_root_and_contained(pa_nid)) by {
                            assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                forgot_guards,
                                _cursor.level,
                            ));
                        };
                        assert(__forgot_guards =~= forgot_guards.put_spec(
                            pa_nid,
                            pa_inner,
                            pa_spin_lock,
                        ));
                        assert(forgot_guards.is_sub_root(nid)) by {
                            assert forall|_nid: NodeId| #[trigger]
                                forgot_guards.inner.dom().contains(_nid) && _nid != nid implies {
                                !node_helper::in_subtree_range::<C>(_nid, nid)
                            } by {
                                assert(__forgot_guards.inner.dom().contains(_nid));
                                assert(__forgot_guards.inner.dom().contains(nid));
                                assert(__forgot_guards.is_sub_root(pa_nid));
                                assert(!forgot_guards.inner.dom().contains(pa_nid));
                                assert(_nid != pa_nid);
                                assert(!node_helper::in_subtree_range::<C>(_nid, pa_nid));
                                if node_helper::in_subtree_range::<C>(_nid, nid) {
                                    assert(node_helper::in_subtree_range::<C>(_nid, pa_nid)) by {
                                        node_helper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range::<
                                            C,
                                        >(_nid, pa_nid, nid);
                                    };
                                }
                            };
                        };
                    };
                    let tracked sub_forgot_guards = forgot_guards.tracked_take_sub_tree(nid);

                    let ghost spin_lock = sub_forgot_guards.get_lock(nid);
                    let tracked forgot_guard = sub_forgot_guards.tracked_take(nid);
                    // Admitted due to the same reason as PageTableNode::from_raw.
                    assert(pt.meta_spec().lock =~= spin_lock) by {
                        admit();
                    };
                    let locked_pt = pt.deref().borrow().make_guard_unchecked(
                        preempt_guard,
                        Tracked(forgot_guard),
                        Ghost(spin_lock),
                    );

                    let mut pa_node = cur_node;
                    let mut pa_guard = pa_node.guard.unwrap();
                    let tracked mut pa_inner = pa_guard.inner.get();
                    let tracked pa_node_token = pa_inner.node_token.tracked_borrow();
                    let tracked mut pa_pte_array_token = pa_inner.pte_token.tracked_unwrap();
                    let mut ch_node = locked_pt;
                    let mut ch_guard = ch_node.guard.unwrap();
                    let tracked mut ch_inner = ch_guard.inner.get();
                    let tracked ch_node_token = ch_inner.node_token.tracked_unwrap();
                    let tracked ch_pte_array_token = ch_inner.pte_token.tracked_unwrap();
                    let tracked mut ch_stray_perm = ch_inner.stray_perm;
                    let tracked mut ch_stray_token = ch_stray_perm.token;
                    proof {
                        let idx = pte_index::<C>(self.0.va, self.0.level);
                        assert(0 <= idx < 512) by {
                            admit();
                        };  // TODO
                        assert(node_helper::is_child::<C>(pa_node.nid(), ch_node.nid()));
                        assert(node_helper::get_offset::<C>(ch_node.nid()) == idx) by {
                            assert(node_helper::is_not_leaf::<C>(pa_node.nid())) by {
                                node_helper::lemma_nid_to_dep_up_bound::<C>(ch_node.nid());
                                node_helper::lemma_level_dep_relation::<C>(ch_node.nid());
                                node_helper::lemma_is_child_level_relation::<C>(
                                    pa_node.nid(),
                                    ch_node.nid(),
                                );
                                node_helper::lemma_level_dep_relation::<C>(pa_node.nid());
                            };
                            node_helper::lemma_get_child_sound::<C>(pa_node.nid(), idx as nat);
                        };
                        assert(ch_node.level_spec() >= 1) by {
                            assert(node_helper::valid_nid::<C>(ch_node.nid()));
                            node_helper::lemma_nid_to_dep_up_bound::<C>(ch_node.nid());
                            node_helper::lemma_level_dep_relation::<C>(ch_node.nid());
                        };
                        assert(pa_node.level_spec() > 1) by {
                            node_helper::lemma_is_child_level_relation::<C>(
                                pa_node.nid(),
                                ch_node.nid(),
                            );
                        };
                        node_helper::lemma_level_dep_relation::<C>(pa_node.nid());
                        node_helper::lemma_get_child_sound::<C>(pa_node.nid(), idx as nat);
                        assert(ch_node.nid() != node_helper::root_id::<C>()) by {
                            node_helper::lemma_is_child_nid_increasing::<C>(
                                pa_node.nid(),
                                ch_node.nid(),
                            );
                        };

                        assert(node_helper::in_subtree_range::<C>(
                            _cursor.get_guard_level_unwrap(_cursor.guard_level).nid(),
                            pa_node.nid(),
                        )) by {
                            assert(pa_node.nid() == _cursor.get_guard_level_unwrap(
                                _cursor.level,
                            ).nid());
                            assert(_cursor.guards_in_path_relation());
                            _cursor.lemma_guards_in_path_relation(_cursor.guard_level);
                            if _cursor.level == _cursor.guard_level {
                                node_helper::lemma_tree_size_spec_table::<C>();
                            }
                        };

                        assert(ch_pte_array_token.value() =~= PteArrayState::empty()) by {
                            admit();
                        };

                        assert(pa_pte_array_token.value().get_paddr(idx as nat)
                            == ch_stray_token.key().1) by {
                            admit();
                        };

                        let _pa_pte_array_token = pa_pte_array_token;
                        let tracked res = self.0.inst.borrow().clone().protocol_deallocate(
                            m.cpu,
                            ch_node.nid(),
                            ch_node_token,
                            pa_node_token,
                            pa_pte_array_token,
                            ch_pte_array_token,
                            &m.token,
                            ch_stray_token,
                        );
                        pa_pte_array_token = res.0.get();
                        ch_stray_token = res.1.get();

                        assert(pa_pte_array_token.value().inner
                            =~= _pa_pte_array_token.value().inner.update(
                            idx as int,
                            PteState::None,
                        ));

                        ch_stray_perm.token = ch_stray_token;
                        ch_inner.node_token = None;
                        ch_inner.pte_token = None;
                        ch_inner.stray_perm = ch_stray_perm;

                        pa_inner.pte_token = Some(pa_pte_array_token);
                    }
                    ch_guard.inner = Tracked(ch_inner);
                    ch_node.guard = Some(ch_guard);
                    pa_guard.inner = Tracked(pa_inner);
                    pa_node.guard = Some(pa_guard);
                    cur_node = pa_node;
                    self.0.path[(self.0.level - 1) as usize] = Some(cur_node);
                    self.0.g_level = Ghost((self.0.g_level@ - 1) as PagingLevel);

                    assert(cur_node.wf());

                    PageTableItem::StrayPageTable {
                        pt,
                        va: self.0.va,
                        len: page_size::<C>(self.0.level),
                    }
                },
                Child::None => {
                    self.0.path[(self.0.level - 1) as usize] = Some(cur_node);
                    self.0.g_level = Ghost((self.0.g_level@ - 1) as PagingLevel);

                    PageTableItem::NotMapped { va: 0, len: 0 }
                },
            };

            let ghost idx = pte_index::<C>(_cursor.va, _cursor.level);
            assert(cur_node.guard->Some_0.view_pte_token().value()
                =~= _cur_node.guard->Some_0.view_pte_token().value().update(
                idx as nat,
                PteState::None,
            )) by {
                assert(0 <= idx < 512) by {
                    admit();
                };  // TODO
                if old !is PageTable {
                    assert(cur_node.guard->Some_0.view_pte_token().value()
                        =~= _cur_node.guard->Some_0.view_pte_token().value());
                    let seq = _cur_node.guard->Some_0.view_pte_token().value().inner;
                    assert(seq[idx as int] is None);
                    assert(seq.update(idx as int, PteState::None) =~= seq);
                }
            };

            proof {
                assert(cur_node.guard->Some_0.view_pte_token().value().is_void(idx as nat)) by {
                    assert(0 <= idx < 512) by {
                        admit();
                    };  // TODO
                };
                take_next_inner_proof_cursor_wf_final_1(
                    _cursor,
                    self.0,
                    _forgot_guards,
                    forgot_guards,
                );
                take_next_inner_proof_cursor_wf_final_2_1(
                    _cursor,
                    self.0,
                    _forgot_guards,
                    forgot_guards,
                );
                take_next_inner_proof_cursor_wf_final_2_2(
                    _cursor,
                    self.0,
                    _forgot_guards,
                    forgot_guards,
                );
            }
            let res = self.0.move_forward(Tracked(forgot_guards));
            proof {
                forgot_guards = res.get();
            }

            return (item, Tracked(forgot_guards));
        }

        // If the loop exits, we did not find any mapped pages in the range.
        (PageTableItem::NotMapped { va: start, len }, Tracked(forgot_guards))
    }
}

proof fn take_next_change_va_hold_wf<C: PageTableConfig>(
    pre_cursor: Cursor<C>,
    post_cursor: Cursor<C>,
    forgot_guards: SubTreeForgotGuard<C>,
)
    requires
        pre_cursor.wf(),
        pre_cursor.g_level@ == pre_cursor.level,
        forgot_guards.wf(),
        pre_cursor.wf_with_forgot_guards(forgot_guards),
        post_cursor.constant_fields_unchanged(&pre_cursor),
        post_cursor.level == pre_cursor.level,
        post_cursor.g_level == pre_cursor.g_level,
        forall|level: PagingLevel|
            #![trigger post_cursor.get_guard_level(level)]
            #![trigger post_cursor.get_guard_level_unwrap(level)]
            1 <= level <= C::NR_LEVELS_SPEC() ==> {
                post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level)
            },
        post_cursor.wf_va(),
    ensures
        post_cursor.wf(),
        post_cursor.wf_with_forgot_guards(forgot_guards),
{
    let _cursor = pre_cursor;
    let cursor = post_cursor;

    assert(cursor.wf()) by {
        assert(cursor.wf_path()) by {
            assert forall|level: PagingLevel|
                #![trigger cursor.get_guard_level(level)]
                #![trigger cursor.get_guard_level_unwrap(level)]
                1 <= level <= C::NR_LEVELS_SPEC() implies {
                if level > cursor.guard_level {
                    cursor.get_guard_level(level) is None
                } else if level >= cursor.g_level@ {
                    &&& cursor.get_guard_level(level) is Some
                    &&& cursor.get_guard_level_unwrap(level).wf()
                    &&& cursor.get_guard_level_unwrap(level).inst_id() == cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        cursor.get_guard_level_unwrap(level).nid(),
                    )
                    &&& cursor.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value()
                        == false
                    &&& cursor.get_guard_level_unwrap(level).guard->Some_0.in_protocol() == true
                    &&& va_level_to_nid::<C>(cursor.va, level) == cursor.get_guard_level_unwrap(
                        level,
                    ).nid()
                } else {
                    cursor.get_guard_level(level) is None
                }
            } by {
                assert(cursor.guard_level == _cursor.guard_level);
                assert(cursor.g_level@ == _cursor.g_level@);
                if level > cursor.guard_level {
                    assert(cursor.path[level - 1] =~= _cursor.path[level - 1]);
                    assert(_cursor.get_guard_level(level) is None);
                } else if level >= cursor.g_level@ {
                    assert(cursor.path[level - 1] =~= _cursor.path[level - 1]);
                    assert(va_level_to_nid::<C>(cursor.va, level) == cursor.get_guard_level_unwrap(
                        level,
                    ).nid()) by { admit() }  // TODO
                } else {
                    assert(cursor.path[level - 1] =~= _cursor.path[level - 1]);
                    assert(_cursor.get_guard_level(level) is None);
                }
            };
        };
        assert(cursor.guards_in_path_relation()) by {
            assert(_cursor.guards_in_path_relation());
            assert forall|level: PagingLevel|
                cursor.g_level@ < level <= cursor.guard_level implies {
                cursor.adjacent_guard_is_child(level)
            } by {
                assert(_cursor.adjacent_guard_is_child(level));
            };
        };
    };
    assert(cursor.wf_with_forgot_guards(forgot_guards)) by {
        let full_forgot_guards_pre = _cursor.rec_put_guard_from_path(
            forgot_guards,
            _cursor.guard_level,
        );
        let full_forgot_guards_post = cursor.rec_put_guard_from_path(
            forgot_guards,
            cursor.guard_level,
        );
        assert(cursor.wf_with_forgot_guards_nid_not_contained(forgot_guards)) by {
            assert forall|level: PagingLevel|
                #![trigger cursor.get_guard_level_unwrap(level)]
                cursor.g_level@ <= level <= cursor.guard_level implies {
                !forgot_guards.inner.dom().contains(cursor.get_guard_level_unwrap(level).nid())
            } by {
                assert(!forgot_guards.inner.dom().contains(
                    _cursor.get_guard_level_unwrap(level).nid(),
                ));
            };
        };
        assert(full_forgot_guards_pre.inner =~= full_forgot_guards_post.inner) by {
            _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                forgot_guards,
                _cursor.guard_level,
            );
            cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                forgot_guards,
                cursor.guard_level,
            );
            assert forall|nid: NodeId| #[trigger]
                full_forgot_guards_pre.inner.dom().contains(nid) implies {
                &&& full_forgot_guards_post.inner.dom().contains(nid)
                &&& full_forgot_guards_post.inner[nid] =~= full_forgot_guards_pre.inner[nid]
            } by {
                if forgot_guards.inner.dom().contains(nid) {
                } else {
                    assert(exists|level: PagingLevel|
                        _cursor.g_level@ <= level <= _cursor.guard_level
                            && #[trigger] _cursor.get_guard_level_unwrap(level).nid() == nid);
                    let level = choose|level: PagingLevel|
                        _cursor.g_level@ <= level <= _cursor.guard_level
                            && #[trigger] _cursor.get_guard_level_unwrap(level).nid() == nid;
                    assert(cursor.get_guard_level_unwrap(level).nid() == nid);
                }
            };
            assert forall|nid: NodeId| #[trigger]
                full_forgot_guards_post.inner.dom().contains(nid) implies {
                &&& full_forgot_guards_pre.inner.dom().contains(nid)
                &&& full_forgot_guards_pre.inner[nid] =~= full_forgot_guards_post.inner[nid]
            } by {
                if forgot_guards.inner.dom().contains(nid) {
                } else {
                    assert(exists|level: PagingLevel|
                        cursor.g_level@ <= level <= cursor.guard_level
                            && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid);
                    let level = choose|level: PagingLevel|
                        cursor.g_level@ <= level <= cursor.guard_level
                            && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid;
                    assert(_cursor.get_guard_level_unwrap(level).nid() == nid);
                }
            };
        };
    };
}

proof fn take_next_inner_proof_cursor_wf_final_1<C: PageTableConfig>(
    pre_cursor: Cursor<C>,
    post_cursor: Cursor<C>,
    pre_forgot_guards: SubTreeForgotGuard<C>,
    post_forgot_guards: SubTreeForgotGuard<C>,
)
    requires
        pre_cursor.wf(),
        pre_cursor.g_level@ == pre_cursor.level,
        pre_forgot_guards.wf(),
        pre_cursor.wf_with_forgot_guards(pre_forgot_guards),
        post_cursor.g_level@ == post_cursor.level,
        post_cursor.constant_fields_unchanged(&pre_cursor),
        post_cursor.level == pre_cursor.level,
        post_cursor.va == pre_cursor.va,
        forall|level: PagingLevel|
            #![trigger post_cursor.get_guard_level(level)]
            #![trigger post_cursor.get_guard_level_unwrap(level)]
            1 <= level <= C::NR_LEVELS_SPEC() && level != post_cursor.level ==> {
                post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level)
            },
        post_cursor.get_guard_level(post_cursor.level) is Some,
        post_cursor.get_guard_level_unwrap(post_cursor.level).wf(),
        post_cursor.get_guard_level_unwrap(post_cursor.level).inst_id() == post_cursor.inst@.id(),
        post_cursor.level == node_helper::nid_to_level::<C>(
            post_cursor.get_guard_level_unwrap(post_cursor.level).nid(),
        ),
        post_cursor.get_guard_level_unwrap(post_cursor.level).guard->Some_0.stray_perm().value()
            == false,
        post_cursor.get_guard_level_unwrap(post_cursor.level).guard->Some_0.in_protocol() == true,
        ({
            let level = post_cursor.level;
            let pre_guard = pre_cursor.get_guard_level_unwrap(level);
            let post_guard = post_cursor.get_guard_level_unwrap(level);
            let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
            let pte = pre_guard.guard->Some_0.perms().inner.value()[idx as int];
            {
                &&& post_guard.nid() == pre_guard.nid()
                &&& post_guard.meta_spec().lock =~= pre_guard.meta_spec().lock
                &&& post_guard.guard->Some_0.view_pte_token().value().wf()
                &&& post_guard.guard->Some_0.view_pte_token().value().is_void(idx as nat)
                &&& if pte.is_pt(pre_cursor.level) {
                    &&& node_helper::is_not_leaf::<C>(pre_guard.nid())
                    &&& post_guard.guard->Some_0.view_pte_token().value()
                        =~= pre_guard.guard->Some_0.view_pte_token().value().update(
                        idx as nat,
                        PteState::None,
                    )
                    &&& pre_guard.guard->Some_0.view_pte_token().value().is_alive(idx as nat)
                } else {
                    post_guard.guard->Some_0.view_pte_token().value()
                        =~= pre_guard.guard->Some_0.view_pte_token().value()
                }
            }
        }),
        post_forgot_guards.wf(),
        ({
            let _cur_node = pre_cursor.get_guard_level_unwrap(pre_cursor.level);
            let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
            let pte = _cur_node.guard->Some_0.perms().inner.value()[idx as int];
            if pte.is_pt(pre_cursor.level) {
                post_forgot_guards.inner =~= pre_forgot_guards.inner.remove_keys(
                    {
                        let pa = pre_cursor.get_guard_level_unwrap(pre_cursor.level).nid();
                        let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
                        let ch = node_helper::get_child::<C>(pa, idx as nat);
                        pre_forgot_guards.get_sub_tree_dom(ch)
                    },
                )
            } else {
                post_forgot_guards =~= pre_forgot_guards
            }
        }),
    ensures
        post_cursor.wf(),
{
    let _cursor = pre_cursor;
    let cursor = post_cursor;
    let _forgot_guards = pre_forgot_guards;
    let forgot_guards = post_forgot_guards;
    let _cur_node = pre_cursor.get_guard_level_unwrap(pre_cursor.level);
    let cur_node = post_cursor.get_guard_level_unwrap(post_cursor.level);
    let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
    let pte = _cur_node.guard->Some_0.perms().inner.value()[idx as int];
    assert(cursor.wf()) by {
        assert(cursor.wf_path()) by {
            assert forall|level: PagingLevel|
                #![trigger cursor.get_guard_level(level)]
                #![trigger cursor.get_guard_level_unwrap(level)]
                1 <= level <= C::NR_LEVELS_SPEC() implies {
                if level > cursor.guard_level {
                    cursor.get_guard_level(level) is None
                } else if level >= cursor.g_level@ {
                    &&& cursor.get_guard_level(level) is Some
                    &&& cursor.get_guard_level_unwrap(level).wf()
                    &&& cursor.get_guard_level_unwrap(level).inst_id() == cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        cursor.get_guard_level_unwrap(level).nid(),
                    )
                    &&& cursor.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value()
                        == false
                    &&& cursor.get_guard_level_unwrap(level).guard->Some_0.in_protocol() == true
                    &&& va_level_to_nid::<C>(cursor.va, level) == cursor.get_guard_level_unwrap(
                        level,
                    ).nid()
                } else {
                    cursor.get_guard_level(level) is None
                }
            } by {
                assert(cursor.guard_level == _cursor.guard_level);
                assert(cursor.g_level@ == _cursor.g_level@);
                if level > cursor.guard_level {
                    assert(cursor.path[level - 1] =~= _cursor.path[level - 1]) by {
                        assert(cursor.get_guard_level(level) is None);
                        assert(_cursor.get_guard_level(level) is None);
                    };
                } else if level >= cursor.g_level@ {
                    if level == cursor.g_level@ {
                        assert(cursor.get_guard_level(level) is Some);
                        assert(cursor.get_guard_level_unwrap(level) =~= cur_node);
                    } else {
                        assert(cursor.path[level - 1] =~= _cursor.path[level - 1]);
                    }
                } else {
                    assert(cursor.path[level - 1] =~= _cursor.path[level - 1]);
                    assert(_cursor.get_guard_level(level) is None);
                }
            };
        };
        assert(cursor.guards_in_path_relation()) by {
            assert forall|level: PagingLevel|
                #![trigger cursor.adjacent_guard_is_child(level)]
                cursor.g_level@ < level <= cursor.guard_level implies {
                cursor.adjacent_guard_is_child(level)
            } by {
                assert(_cursor.adjacent_guard_is_child(level));
            }
        }
    };
}

proof fn take_next_inner_proof_cursor_wf_final_2_1<C: PageTableConfig>(
    pre_cursor: Cursor<C>,
    post_cursor: Cursor<C>,
    pre_forgot_guards: SubTreeForgotGuard<C>,
    post_forgot_guards: SubTreeForgotGuard<C>,
)
    requires
        pre_cursor.wf(),
        pre_cursor.g_level@ == pre_cursor.level,
        pre_forgot_guards.wf(),
        pre_cursor.wf_with_forgot_guards(pre_forgot_guards),
        post_cursor.wf(),
        post_cursor.g_level@ == post_cursor.level,
        post_cursor.constant_fields_unchanged(&pre_cursor),
        post_cursor.level == pre_cursor.level,
        post_cursor.va == pre_cursor.va,
        forall|level: PagingLevel|
            #![trigger post_cursor.get_guard_level(level)]
            #![trigger post_cursor.get_guard_level_unwrap(level)]
            1 <= level <= C::NR_LEVELS_SPEC() && level != post_cursor.level ==> {
                post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level)
            },
        post_cursor.get_guard_level(post_cursor.level) is Some,
        post_cursor.get_guard_level_unwrap(post_cursor.level).wf(),
        post_cursor.get_guard_level_unwrap(post_cursor.level).inst_id() == post_cursor.inst@.id(),
        post_cursor.level == node_helper::nid_to_level::<C>(
            post_cursor.get_guard_level_unwrap(post_cursor.level).nid(),
        ),
        post_cursor.get_guard_level_unwrap(post_cursor.level).guard->Some_0.stray_perm().value()
            == false,
        post_cursor.get_guard_level_unwrap(post_cursor.level).guard->Some_0.in_protocol() == true,
        ({
            let level = post_cursor.level;
            let pre_guard = pre_cursor.get_guard_level_unwrap(level);
            let post_guard = post_cursor.get_guard_level_unwrap(level);
            let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
            let pte = pre_guard.guard->Some_0.perms().inner.value()[idx as int];
            {
                &&& post_guard.nid() == pre_guard.nid()
                &&& post_guard.meta_spec().lock =~= pre_guard.meta_spec().lock
                &&& post_guard.guard->Some_0.view_pte_token().value().wf()
                &&& post_guard.guard->Some_0.view_pte_token().value().is_void(idx as nat)
                &&& if pte.is_pt(pre_cursor.level) {
                    &&& node_helper::is_not_leaf::<C>(pre_guard.nid())
                    &&& post_guard.guard->Some_0.view_pte_token().value()
                        =~= pre_guard.guard->Some_0.view_pte_token().value().update(
                        idx as nat,
                        PteState::None,
                    )
                    &&& pre_guard.guard->Some_0.view_pte_token().value().is_alive(idx as nat)
                } else {
                    post_guard.guard->Some_0.view_pte_token().value()
                        =~= pre_guard.guard->Some_0.view_pte_token().value()
                }
            }
        }),
        post_forgot_guards.wf(),
        ({
            let _cur_node = pre_cursor.get_guard_level_unwrap(pre_cursor.level);
            let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
            let pte = _cur_node.guard->Some_0.perms().inner.value()[idx as int];
            if pte.is_pt(pre_cursor.level) {
                post_forgot_guards.inner =~= pre_forgot_guards.inner.remove_keys(
                    {
                        let pa = pre_cursor.get_guard_level_unwrap(pre_cursor.level).nid();
                        let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
                        let ch = node_helper::get_child::<C>(pa, idx as nat);
                        pre_forgot_guards.get_sub_tree_dom(ch)
                    },
                )
            } else {
                post_forgot_guards =~= pre_forgot_guards
            }
        }),
    ensures
        ({
            let level = post_cursor.level;
            let pre_guard = pre_cursor.get_guard_level_unwrap(level);
            let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
            let pte = pre_guard.guard->Some_0.perms().inner.value()[idx as int];
            let full_forgot_guards = post_cursor.rec_put_guard_from_path(
                post_forgot_guards,
                post_cursor.guard_level,
            );
            pte.is_pt(pre_cursor.level) ==> full_forgot_guards.wf()
        }),
{
    let _cursor = pre_cursor;
    let cursor = post_cursor;
    let _forgot_guards = pre_forgot_guards;
    let forgot_guards = post_forgot_guards;
    let _cur_node = pre_cursor.get_guard_level_unwrap(pre_cursor.level);
    let cur_node = post_cursor.get_guard_level_unwrap(post_cursor.level);
    let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
    let pte = _cur_node.guard->Some_0.perms().inner.value()[idx as int];
    if pte.is_pt(_cursor.level) {
        let full_forgot_guards = cursor.rec_put_guard_from_path(forgot_guards, cursor.guard_level);
        cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(forgot_guards, cursor.guard_level);
        cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(forgot_guards);
        assert(full_forgot_guards.wf()) by {
            assert forall|nid: NodeId| #[trigger]
                full_forgot_guards.inner.dom().contains(nid) implies {
                full_forgot_guards.children_are_contained(
                    nid,
                    full_forgot_guards.get_guard_inner(nid).pte_token->Some_0.value(),
                )
            } by {
                let pte_array = full_forgot_guards.get_guard_inner(nid).pte_token->Some_0.value();
                if forgot_guards.inner.dom().contains(nid) {
                    if node_helper::is_not_leaf::<C>(nid) {
                        assert forall|i: nat| 0 <= i < nr_subpage_per_huge::<C>() implies {
                            #[trigger] pte_array.is_alive(i)
                                <==> full_forgot_guards.inner.dom().contains(
                                node_helper::get_child::<C>(nid, i),
                            )
                        } by {
                            let ch = node_helper::get_child::<C>(nid, i);
                            if pte_array.is_alive(i) {
                                assert(full_forgot_guards.inner.dom().contains(ch));
                            }
                            if full_forgot_guards.inner.dom().contains(ch) {
                                assert(pte_array.is_alive(i)) by {
                                    assert(forgot_guards.inner.dom().contains(ch)) by {
                                        if !forgot_guards.inner.dom().contains(ch) {
                                            assert(exists|level: PagingLevel|
                                                cursor.g_level@ <= level <= cursor.guard_level
                                                    && #[trigger] cursor.get_guard_level_unwrap(
                                                    level,
                                                ).nid() == ch);
                                            let level = choose|level: PagingLevel|
                                                cursor.g_level@ <= level <= cursor.guard_level
                                                    && #[trigger] cursor.get_guard_level_unwrap(
                                                    level,
                                                ).nid() == ch;
                                            if level != cursor.guard_level {
                                                let pa = cursor.get_guard_level_unwrap(
                                                    (level + 1) as PagingLevel,
                                                ).nid();
                                                assert(node_helper::is_child::<C>(pa, ch)) by {
                                                    assert(cursor.adjacent_guard_is_child(
                                                        (level + 1) as PagingLevel,
                                                    ));
                                                };
                                                assert(pa == nid) by {
                                                    assert(node_helper::is_child::<C>(nid, ch)) by {
                                                        node_helper::lemma_get_child_sound::<C>(
                                                            nid,
                                                            i,
                                                        );
                                                    };
                                                    node_helper::lemma_is_child_implies_same_pa::<
                                                        C,
                                                    >(pa, nid, ch);
                                                };
                                            } else {
                                                let _full_forgot_guards =
                                                    _cursor.rec_put_guard_from_path(
                                                    _forgot_guards,
                                                    _cursor.guard_level,
                                                );
                                                assert(_full_forgot_guards.is_root_and_contained(
                                                    ch,
                                                ));
                                                assert(_full_forgot_guards.inner.dom().contains(
                                                    nid,
                                                )) by {
                                                    _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                                                    _forgot_guards, _cursor.guard_level);
                                                    _cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(
                                                    _forgot_guards);
                                                };
                                                assert(!node_helper::in_subtree_range::<C>(ch, nid))
                                                    by {
                                                    node_helper::lemma_get_child_sound::<C>(nid, i);
                                                    node_helper::lemma_is_child_nid_increasing::<C>(
                                                        nid,
                                                        ch,
                                                    );
                                                };
                                            }
                                        }
                                    };
                                    assert(forgot_guards.wf());
                                };
                            }
                        };
                        assert forall|i: nat| 0 <= i < nr_subpage_per_huge::<C>() implies {
                            #[trigger] pte_array.is_void(i)
                                ==> full_forgot_guards.sub_tree_not_contained(
                                node_helper::get_child::<C>(nid, i),
                            )
                        } by {
                            let ch = node_helper::get_child::<C>(nid, i);
                            if pte_array.is_void(i) {
                                assert forall|_nid: NodeId| #[trigger]
                                    full_forgot_guards.inner.dom().contains(_nid) implies {
                                    !node_helper::in_subtree_range::<C>(ch, _nid)
                                } by {
                                    if forgot_guards.inner.dom().contains(_nid) {
                                    } else {
                                        assert(exists|level: PagingLevel|
                                            cursor.g_level@ <= level <= cursor.guard_level
                                                && #[trigger] cursor.get_guard_level_unwrap(
                                                level,
                                            ).nid() == _nid);
                                        let level = choose|level: PagingLevel|
                                            cursor.g_level@ <= level <= cursor.guard_level
                                                && #[trigger] cursor.get_guard_level_unwrap(
                                                level,
                                            ).nid() == _nid;
                                        if node_helper::in_subtree_range::<C>(ch, _nid) {
                                            assert(node_helper::in_subtree_range::<C>(nid, _nid))
                                                by {
                                                assert(node_helper::in_subtree_range::<C>(nid, ch))
                                                    by {
                                                    node_helper::lemma_get_child_sound::<C>(nid, i);
                                                    node_helper::lemma_is_child_implies_in_subtree::<
                                                        C,
                                                    >(nid, ch);
                                                    node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                        C,
                                                    >(nid, ch);
                                                };
                                                node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                    C,
                                                >(nid, ch);
                                                node_helper::lemma_in_subtree_bounded::<C>(nid, ch);
                                            };
                                            assert(_forgot_guards.inner.dom().contains(nid));
                                            assert(_cursor.get_guard_level_unwrap(level).nid()
                                                == _nid);
                                            _cursor.lemma_wf_with_forgot_guards_sound(
                                                _forgot_guards,
                                            );
                                            assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                            _forgot_guards, level));
                                            _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                                                _forgot_guards,
                                                (level - 1) as PagingLevel,
                                            );
                                            let _full_forgot_guards =
                                                _cursor.rec_put_guard_from_path(
                                                _forgot_guards,
                                                (level - 1) as PagingLevel,
                                            );
                                            assert(_full_forgot_guards.is_sub_root(_nid));
                                            assert(_full_forgot_guards.inner.dom().contains(nid));
                                            assert(!node_helper::in_subtree_range::<C>(nid, _nid));
                                        }
                                    }
                                };
                            }
                        }
                    }
                } else {
                    assert(exists|level: PagingLevel|
                        cursor.g_level@ <= level <= cursor.guard_level
                            && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid);
                    let level = choose|level: PagingLevel|
                        cursor.g_level@ <= level <= cursor.guard_level
                            && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid;
                    if node_helper::is_not_leaf::<C>(nid) {
                        assert forall|i: nat| 0 <= i < nr_subpage_per_huge::<C>() implies {
                            #[trigger] pte_array.is_alive(i)
                                <==> full_forgot_guards.inner.dom().contains(
                                node_helper::get_child::<C>(nid, i),
                            )
                        } by {
                            let ch = node_helper::get_child::<C>(nid, i);
                            if pte_array.is_alive(i) {
                                assert(full_forgot_guards.inner.dom().contains(ch)) by {
                                    if level == cursor.level {
                                        assert(nid == cur_node.nid());
                                        assert(pte_array =~= cursor.get_guard_level_unwrap(
                                            cursor.level,
                                        ).guard->Some_0.view_pte_token().value());
                                        let _idx = pte_index::<C>(_cursor.va, _cursor.level);
                                        assert(0 <= _idx < 512) by {
                                            admit();
                                        };  // TODO
                                        let _ch = node_helper::get_child::<C>(nid, _idx as nat);
                                        assert(i != _idx) by {
                                            assert(pte_array.is_void(_idx as nat));
                                        };
                                        assert(forgot_guards.inner
                                            =~= _forgot_guards.inner.remove_keys(
                                            _forgot_guards.get_sub_tree_dom(_ch),
                                        ));
                                        assert forall|_nid: NodeId| #[trigger]
                                            _forgot_guards.inner.dom().contains(_nid)
                                                && !node_helper::in_subtree_range::<C>(
                                                _ch,
                                                _nid,
                                            ) implies { forgot_guards.inner.dom().contains(_nid)
                                        } by {};
                                        _cursor.lemma_wf_with_forgot_guards_sound(_forgot_guards);
                                        assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                        _forgot_guards, _cursor.level));
                                        _cursor.lemma_rec_put_guard_from_path_basic(_forgot_guards);
                                        assert(_forgot_guards.inner.dom().contains(ch)) by {
                                            let _pte_array = _cursor.get_guard_level_unwrap(
                                                _cursor.level,
                                            ).guard->Some_0.view_pte_token().value();
                                            assert(_pte_array.is_alive(i)) by {
                                                assert(0 <= i < 512) by {
                                                    admit();
                                                };  // TODO
                                            };
                                            assert(_forgot_guards.children_are_contained(
                                                nid,
                                                _pte_array,
                                            ));
                                        };
                                        assert(!node_helper::in_subtree_range::<C>(_ch, ch)) by {
                                            assert(!node_helper::in_subtree_range::<C>(_ch, nid))
                                                by {
                                                assert(0 <= _idx < nr_subpage_per_huge::<C>()) by {
                                                    admit();
                                                };  // TODO
                                                node_helper::lemma_get_child_sound::<C>(
                                                    nid,
                                                    _idx as nat,
                                                );
                                                node_helper::lemma_is_child_nid_increasing::<C>(
                                                    nid,
                                                    _ch,
                                                );
                                            };
                                            assert(_ch != ch) by {
                                                assert(0 <= i < 512) by {
                                                    admit();
                                                };  // TODO
                                                assert(0 <= idx < 512) by {
                                                    admit();
                                                };  // TODO
                                                if i < idx {
                                                    node_helper::lemma_brother_nid_increasing::<C>(
                                                        nid,
                                                        i,
                                                        idx as nat,
                                                    );
                                                } else {
                                                    node_helper::lemma_brother_nid_increasing::<C>(
                                                        nid,
                                                        idx as nat,
                                                        i,
                                                    );
                                                }
                                            };
                                            node_helper::lemma_get_child_sound::<C>(nid, i);
                                            node_helper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range::<
                                                C,
                                            >(_ch, nid, ch);
                                        };
                                    } else {
                                        let __ch = cursor.get_guard_level_unwrap(
                                            (level - 1) as PagingLevel,
                                        ).nid();
                                        if ch == __ch {
                                        } else {
                                            let _idx = pte_index::<C>(_cursor.va, _cursor.level);
                                            let _ch = node_helper::get_child::<C>(
                                                cur_node.nid(),
                                                _idx as nat,
                                            );
                                            assert forall|_nid: NodeId| #[trigger]
                                                _forgot_guards.inner.dom().contains(_nid)
                                                    && !node_helper::in_subtree_range::<C>(
                                                    _ch,
                                                    _nid,
                                                ) implies { forgot_guards.inner.dom().contains(_nid)
                                            } by {};
                                            _cursor.lemma_wf_with_forgot_guards_sound(
                                                _forgot_guards,
                                            );
                                            assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                            _forgot_guards, level));
                                            let _full_forgot_guards =
                                                _cursor.rec_put_guard_from_path(
                                                _forgot_guards,
                                                (level - 1) as PagingLevel,
                                            );
                                            assert(_full_forgot_guards.inner.dom().contains(ch))
                                                by {
                                                let _pte_array = _cursor.get_guard_level_unwrap(
                                                    level,
                                                ).guard->Some_0.view_pte_token().value();
                                                assert(_pte_array.is_alive(i)) by {
                                                    assert(0 <= i < 512) by {
                                                        admit();
                                                    };  // TODO
                                                };
                                                assert(_full_forgot_guards.children_are_contained(
                                                    nid,
                                                    _pte_array,
                                                ));
                                            };
                                            assert(_forgot_guards.inner.dom().contains(ch)) by {
                                                _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                                                _forgot_guards, (level - 1) as PagingLevel);
                                                assert forall|_level: PagingLevel|
                                                    _cursor.g_level@ <= _level < level implies {
                                                    #[trigger] _cursor.get_guard_level_unwrap(
                                                        _level,
                                                    ).nid() != ch
                                                } by {
                                                    if _level != level - 1 {
                                                        assert(node_helper::nid_to_level::<C>(ch)
                                                            == level - 1) by {
                                                            node_helper::lemma_get_child_sound::<C>(
                                                                nid,
                                                                i,
                                                            );
                                                            node_helper::lemma_is_child_level_relation::<
                                                                C,
                                                            >(nid, ch);
                                                        };
                                                    }
                                                };
                                            };
                                            assert(!node_helper::in_subtree_range::<C>(_ch, ch))
                                                by {
                                                assert(node_helper::in_subtree_range::<C>(
                                                    __ch,
                                                    cur_node.nid(),
                                                )) by {
                                                    _cursor.lemma_guards_in_path_relation(
                                                        (level - 1) as PagingLevel,
                                                    );
                                                };
                                                assert(node_helper::in_subtree_range::<C>(
                                                    __ch,
                                                    _ch,
                                                )) by {
                                                    node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                        C,
                                                    >(__ch, cur_node.nid());
                                                    assert(node_helper::is_not_leaf::<C>(
                                                        cur_node.nid(),
                                                    ));
                                                    assert(0 <= _idx < nr_subpage_per_huge::<C>())
                                                        by {
                                                        admit();
                                                    };  // TODO
                                                    node_helper::lemma_get_child_sound::<C>(
                                                        cur_node.nid(),
                                                        _idx as nat,
                                                    );
                                                    node_helper::lemma_in_subtree_is_child_in_subtree::<
                                                        C,
                                                    >(__ch, cur_node.nid(), _ch);
                                                    node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                        C,
                                                    >(__ch, _ch);
                                                };
                                                assert(!node_helper::in_subtree_range::<C>(
                                                    __ch,
                                                    ch,
                                                )) by {
                                                    assert(!node_helper::in_subtree_range::<C>(
                                                        __ch,
                                                        nid,
                                                    )) by {
                                                        assert(cursor.adjacent_guard_is_child(
                                                            level,
                                                        ));
                                                        node_helper::lemma_is_child_nid_increasing::<
                                                            C,
                                                        >(nid, __ch);
                                                    };
                                                    assert(__ch != ch);
                                                    node_helper::lemma_get_child_sound::<C>(nid, i);
                                                    node_helper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range::<
                                                        C,
                                                    >(__ch, nid, ch);
                                                };
                                                if node_helper::in_subtree_range::<C>(_ch, ch) {
                                                    assert(node_helper::in_subtree_range::<C>(
                                                        __ch,
                                                        ch,
                                                    )) by {
                                                        node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                            C,
                                                        >(__ch, _ch);
                                                        node_helper::lemma_in_subtree_bounded::<C>(
                                                            __ch,
                                                            _ch,
                                                        );
                                                    };
                                                }
                                            }
                                        }
                                    }
                                };
                            }
                            if full_forgot_guards.inner.dom().contains(ch) {
                                assert(pte_array.is_alive(i)) by {
                                    if level == cursor.level {
                                        assert(nid == cur_node.nid());
                                        assert(pte_array
                                            =~= cur_node.guard->Some_0.view_pte_token().value());
                                        let _idx = pte_index::<C>(_cursor.va, _cursor.level);
                                        let _ch = node_helper::get_child::<C>(nid, _idx as nat);
                                        assert(i != _idx) by {
                                            assert(!full_forgot_guards.inner.dom().contains(_ch))
                                                by {
                                                assert(!forgot_guards.inner.dom().contains(_ch))
                                                    by {
                                                    assert(_forgot_guards.inner.dom().contains(_ch))
                                                        by {
                                                        assert(_cur_node.guard->Some_0.view_pte_token().value().is_alive(
                                                        _idx as nat));
                                                        _cursor.lemma_wf_with_forgot_guards_sound(
                                                            _forgot_guards,
                                                        );
                                                        assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                                        _forgot_guards, _cursor.level));
                                                        _cursor.lemma_rec_put_guard_from_path_basic(
                                                            _forgot_guards,
                                                        );
                                                        assert(_forgot_guards.children_are_contained(

                                                            _cur_node.nid(),
                                                            _cur_node.guard->Some_0.view_pte_token().value(),
                                                        ));
                                                        assert(_cur_node.nid() == nid);
                                                        assert(node_helper::is_not_leaf::<C>(nid));
                                                        assert(_ch == node_helper::get_child::<C>(
                                                            _cur_node.nid(),
                                                            _idx as nat,
                                                        ));
                                                        assert(0 <= _idx < nr_subpage_per_huge::<
                                                            C,
                                                        >()) by {
                                                            admit();
                                                        };  // TODO
                                                    };
                                                    assert(forgot_guards.inner
                                                        =~= _forgot_guards.inner.remove_keys(
                                                        _forgot_guards.get_sub_tree_dom(_ch),
                                                    ));
                                                    assert(node_helper::in_subtree_range::<C>(
                                                        _ch,
                                                        _ch,
                                                    )) by {
                                                        assert(node_helper::valid_nid::<C>(_ch));
                                                        node_helper::lemma_sub_tree_size_lower_bound::<
                                                            C,
                                                        >(_ch);
                                                    };
                                                };
                                                assert forall|_level: PagingLevel|
                                                    cursor.g_level@ <= _level
                                                        <= cursor.guard_level implies {
                                                    #[trigger] cursor.get_guard_level_unwrap(
                                                        _level,
                                                    ).nid() != _ch
                                                } by {
                                                    cursor.lemma_guards_in_path_relation(_level);
                                                    assert(0 <= _idx < nr_subpage_per_huge::<C>())
                                                        by {
                                                        admit();
                                                    };  // TODO
                                                    node_helper::lemma_get_child_sound::<C>(
                                                        cur_node.nid(),
                                                        _idx as nat,
                                                    );
                                                    node_helper::lemma_is_child_nid_increasing::<C>(
                                                        cur_node.nid(),
                                                        _ch,
                                                    );
                                                };
                                            };
                                        };
                                        assert(forgot_guards.inner.dom().contains(ch)) by {
                                            assert forall|_level: PagingLevel|
                                                cursor.g_level@ <= _level
                                                    <= cursor.guard_level implies {
                                                #[trigger] cursor.get_guard_level_unwrap(_level).nid
                                                    != ch
                                            } by {
                                                node_helper::lemma_get_child_sound::<C>(nid, i);
                                                node_helper::lemma_is_child_level_relation::<C>(
                                                    nid,
                                                    ch,
                                                );
                                            };
                                        };
                                        assert(_forgot_guards.inner.dom().contains(ch));
                                        let _pte_array = _cursor.get_guard_level_unwrap(
                                            _cursor.level,
                                        ).guard->Some_0.view_pte_token().value();
                                        assert(_pte_array
                                            =~= _cur_node.guard->Some_0.view_pte_token().value());
                                        assert(_forgot_guards.children_are_contained(
                                            nid,
                                            _pte_array,
                                        )) by {
                                            _cursor.lemma_wf_with_forgot_guards_sound(
                                                _forgot_guards,
                                            );
                                            assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                            _forgot_guards, level));
                                            _cursor.lemma_rec_put_guard_from_path_basic(
                                                _forgot_guards,
                                            );
                                        };
                                        assert(_pte_array.is_alive(i));
                                        assert(pte_array.inner[i as int]
                                            =~= _pte_array.inner[i as int]) by {
                                            assert(0 <= i < 512) by {
                                                admit();
                                            };  // TODO
                                            assert(0 <= _idx < 512) by {
                                                admit();
                                            };  // TODO
                                            axiom_seq_update_different(
                                                _pte_array.inner,
                                                i as int,
                                                _idx as int,
                                                PteState::None,
                                            );
                                        };
                                    } else {
                                        let __ch = cursor.get_guard_level_unwrap(
                                            (level - 1) as PagingLevel,
                                        ).nid();
                                        if ch == __ch {
                                            let _full_forgot_guards =
                                                _cursor.rec_put_guard_from_path(
                                                _forgot_guards,
                                                (level - 1) as PagingLevel,
                                            );
                                            _cursor.lemma_wf_with_forgot_guards_sound(
                                                _forgot_guards,
                                            );
                                            assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                            _forgot_guards, level));
                                            assert(_full_forgot_guards.children_are_contained(
                                                nid,
                                                pte_array,
                                            ));
                                        } else {
                                            assert(forgot_guards.inner.dom().contains(ch)) by {
                                                assert forall|_level: PagingLevel|
                                                    cursor.g_level@ <= _level
                                                        <= cursor.guard_level implies {
                                                    #[trigger] cursor.get_guard_level_unwrap(
                                                        _level,
                                                    ).nid != ch
                                                } by {
                                                    node_helper::lemma_get_child_sound::<C>(nid, i);
                                                    node_helper::lemma_is_child_level_relation::<C>(
                                                        nid,
                                                        ch,
                                                    );
                                                };
                                            };
                                            assert(_forgot_guards.inner.dom().contains(ch));
                                            let _full_forgot_guards =
                                                _cursor.rec_put_guard_from_path(
                                                _forgot_guards,
                                                (level - 1) as PagingLevel,
                                            );
                                            _cursor.lemma_wf_with_forgot_guards_sound(
                                                _forgot_guards,
                                            );
                                            assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                            _forgot_guards, level));
                                            assert(_full_forgot_guards.children_are_contained(
                                                nid,
                                                pte_array,
                                            ));
                                            assert(_full_forgot_guards.inner.dom().contains(ch))
                                                by {
                                                _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                                                _forgot_guards, (level - 1) as PagingLevel);
                                            };
                                        }
                                    }
                                };
                            }
                        };
                        assert forall|i: nat| 0 <= i < nr_subpage_per_huge::<C>() implies {
                            #[trigger] pte_array.is_void(i)
                                ==> full_forgot_guards.sub_tree_not_contained(
                                node_helper::get_child::<C>(nid, i),
                            )
                        } by {
                            let ch = node_helper::get_child::<C>(nid, i);
                            if pte_array.is_void(i) {
                                assert forall|_nid: NodeId| #[trigger]
                                    full_forgot_guards.inner.dom().contains(_nid) implies {
                                    !node_helper::in_subtree_range::<C>(ch, _nid)
                                } by {
                                    if forgot_guards.inner.dom().contains(_nid) {
                                        if node_helper::in_subtree_range::<C>(ch, _nid) {
                                            if level != cursor.level {
                                                assert(_forgot_guards.inner.dom().contains(_nid));
                                                _cursor.lemma_wf_with_forgot_guards_sound(
                                                    _forgot_guards,
                                                );
                                                assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                                _forgot_guards, level));
                                                _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                                                _forgot_guards, (level - 1) as PagingLevel);
                                                let _full_forgot_guards =
                                                    _cursor.rec_put_guard_from_path(
                                                    _forgot_guards,
                                                    (level - 1) as PagingLevel,
                                                );
                                                assert(_full_forgot_guards.children_are_contained(
                                                    nid,
                                                    pte_array,
                                                ));
                                                assert(_full_forgot_guards.sub_tree_not_contained(
                                                    ch,
                                                ));
                                                assert(_full_forgot_guards.inner.dom().contains(
                                                    _nid,
                                                ));
                                                assert(!node_helper::in_subtree_range::<C>(
                                                    ch,
                                                    _nid,
                                                ));
                                            } else {
                                                assert(_forgot_guards.inner.dom().contains(_nid));
                                                let idx = pte_index::<C>(_cursor.va, _cursor.level);
                                                if i == idx {
                                                } else {
                                                    _cursor.lemma_wf_with_forgot_guards_sound(
                                                        _forgot_guards,
                                                    );
                                                    assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                                    _forgot_guards, level));
                                                    _cursor.lemma_rec_put_guard_from_path_basic(
                                                        _forgot_guards,
                                                    );
                                                    let _pte_array = _cursor.get_guard_level_unwrap(
                                                        level,
                                                    ).guard->Some_0.view_pte_token().value();
                                                    assert(_pte_array.is_void(i)) by {
                                                        assert(0 <= i < 512) by {
                                                            admit();
                                                        };  // TODO
                                                        assert(0 <= idx < 512) by {
                                                            admit();
                                                        };  // TODO
                                                        assert(pte_array.inner
                                                            =~= _pte_array.inner.update(
                                                            idx as int,
                                                            PteState::None,
                                                        ));
                                                        assert(pte_array.inner[i as int]
                                                            =~= _pte_array.inner[i as int]) by {
                                                            assert(_pte_array.wf());
                                                            axiom_seq_update_different(
                                                                _pte_array.inner,
                                                                i as int,
                                                                idx as int,
                                                                PteState::None,
                                                            );
                                                        };
                                                    };
                                                    assert(_forgot_guards.children_are_contained(
                                                        nid,
                                                        _pte_array,
                                                    ));
                                                    assert(_forgot_guards.sub_tree_not_contained(
                                                        ch,
                                                    ));
                                                }
                                            }
                                        }
                                    } else {
                                        assert(exists|_level: PagingLevel|
                                            cursor.g_level@ <= _level <= cursor.guard_level
                                                && #[trigger] cursor.get_guard_level_unwrap(
                                                _level,
                                            ).nid() == _nid);
                                        let _level = choose|_level: PagingLevel|
                                            cursor.g_level@ <= _level <= cursor.guard_level
                                                && #[trigger] cursor.get_guard_level_unwrap(
                                                _level,
                                            ).nid() == _nid;
                                        assert(_cursor.get_guard_level_unwrap(_level).nid()
                                            == _nid);
                                        if nid == _nid {
                                            node_helper::lemma_get_child_sound::<C>(nid, i);
                                            node_helper::lemma_is_child_nid_increasing::<C>(
                                                nid,
                                                ch,
                                            );
                                        } else {
                                            if level == cursor.level {
                                                assert(level != _level);
                                                assert(_level > cursor.g_level@);
                                                cursor.lemma_guards_in_path_relation(_level);
                                                assert(node_helper::in_subtree_range::<C>(
                                                    _nid,
                                                    nid,
                                                ));
                                                assert(node_helper::in_subtree_range::<C>(_nid, ch))
                                                    by {
                                                    node_helper::lemma_get_child_sound::<C>(nid, i);
                                                    node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                        C,
                                                    >(_nid, nid);
                                                    node_helper::lemma_in_subtree_is_child_in_subtree::<
                                                        C,
                                                    >(_nid, nid, ch);
                                                    node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                        C,
                                                    >(_nid, ch);
                                                };
                                                assert(!node_helper::in_subtree_range::<C>(
                                                    ch,
                                                    _nid,
                                                )) by {
                                                    assert(ch != _nid) by {
                                                        node_helper::lemma_get_child_sound::<C>(
                                                            nid,
                                                            i,
                                                        );
                                                        node_helper::lemma_is_child_nid_increasing::<
                                                            C,
                                                        >(nid, ch);
                                                    };
                                                };
                                            } else {
                                                if _level <= level {
                                                    _cursor.lemma_wf_with_forgot_guards_sound(
                                                        _forgot_guards,
                                                    );
                                                    assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(
                                                    _forgot_guards, level));
                                                    let _full_forgot_guards =
                                                        _cursor.rec_put_guard_from_path(
                                                        _forgot_guards,
                                                        (level - 1) as PagingLevel,
                                                    );
                                                    assert(_full_forgot_guards.children_are_contained(
                                                    nid, pte_array));
                                                    assert(_full_forgot_guards.sub_tree_not_contained(
                                                    ch));
                                                    _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                                                    _forgot_guards, (level - 1) as PagingLevel);
                                                    assert(_full_forgot_guards.inner.dom().contains(
                                                        _nid,
                                                    ));
                                                } else {
                                                    let _full_forgot_guards =
                                                        _cursor.rec_put_guard_from_path(
                                                        _forgot_guards,
                                                        _level,
                                                    );
                                                    _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                                                    _forgot_guards, _level);
                                                    assert(_full_forgot_guards.inner.dom().contains(
                                                        _nid,
                                                    ));
                                                    assert(_full_forgot_guards.inner.dom().contains(
                                                        nid,
                                                    ));
                                                    assert(_full_forgot_guards.wf()) by {
                                                        if _level < cursor.guard_level {
                                                            _cursor.lemma_wf_with_forgot_guards_sound(
                                                            _forgot_guards);
                                                            assert(_cursor.guards_in_path_wf_with_forgot_guards_singleton(

                                                                _forgot_guards,
                                                                (_level + 1) as PagingLevel,
                                                            ));
                                                        } else {
                                                            assert(_cursor.wf_with_forgot_guards(
                                                                _forgot_guards,
                                                            ));
                                                        }
                                                    };
                                                    assert(_full_forgot_guards.sub_tree_not_contained(
                                                    ch));
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        assert(node_helper::nid_to_level::<C>(nid) == 1) by {
                            node_helper::lemma_level_dep_relation::<C>(nid);
                        };
                        assert(node_helper::nid_to_level::<C>(nid) == level);
                    }
                }
            };
        };
    }
}

proof fn take_next_inner_proof_cursor_wf_final_2_2<C: PageTableConfig>(
    pre_cursor: Cursor<C>,
    post_cursor: Cursor<C>,
    pre_forgot_guards: SubTreeForgotGuard<C>,
    post_forgot_guards: SubTreeForgotGuard<C>,
)
    requires
        pre_cursor.wf(),
        pre_cursor.g_level@ == pre_cursor.level,
        pre_forgot_guards.wf(),
        pre_cursor.wf_with_forgot_guards(pre_forgot_guards),
        post_cursor.wf(),
        post_cursor.g_level@ == post_cursor.level,
        post_cursor.constant_fields_unchanged(&pre_cursor),
        post_cursor.level == pre_cursor.level,
        post_cursor.va == pre_cursor.va,
        forall|level: PagingLevel|
            #![trigger post_cursor.get_guard_level(level)]
            #![trigger post_cursor.get_guard_level_unwrap(level)]
            1 <= level <= C::NR_LEVELS_SPEC() && level != post_cursor.level ==> {
                post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level)
            },
        post_cursor.get_guard_level(post_cursor.level) is Some,
        post_cursor.get_guard_level_unwrap(post_cursor.level).wf(),
        post_cursor.get_guard_level_unwrap(post_cursor.level).inst_id() == post_cursor.inst@.id(),
        post_cursor.level == node_helper::nid_to_level::<C>(
            post_cursor.get_guard_level_unwrap(post_cursor.level).nid(),
        ),
        post_cursor.get_guard_level_unwrap(post_cursor.level).guard->Some_0.stray_perm().value()
            == false,
        post_cursor.get_guard_level_unwrap(post_cursor.level).guard->Some_0.in_protocol() == true,
        ({
            let level = post_cursor.level;
            let pre_guard = pre_cursor.get_guard_level_unwrap(level);
            let post_guard = post_cursor.get_guard_level_unwrap(level);
            let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
            let pte = pre_guard.guard->Some_0.perms().inner.value()[idx as int];
            {
                &&& post_guard.nid() == pre_guard.nid()
                &&& post_guard.meta_spec().lock =~= pre_guard.meta_spec().lock
                &&& post_guard.guard->Some_0.view_pte_token().value().wf()
                &&& post_guard.guard->Some_0.view_pte_token().value().is_void(idx as nat)
                &&& if pte.is_pt(pre_cursor.level) {
                    &&& node_helper::is_not_leaf::<C>(pre_guard.nid())
                    &&& post_guard.guard->Some_0.view_pte_token().value()
                        =~= pre_guard.guard->Some_0.view_pte_token().value().update(
                        idx as nat,
                        PteState::None,
                    )
                    &&& pre_guard.guard->Some_0.view_pte_token().value().is_alive(idx as nat)
                } else {
                    post_guard.guard->Some_0.view_pte_token().value()
                        =~= pre_guard.guard->Some_0.view_pte_token().value()
                }
            }
        }),
        post_forgot_guards.wf(),
        ({
            let _cur_node = pre_cursor.get_guard_level_unwrap(pre_cursor.level);
            let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
            let pte = _cur_node.guard->Some_0.perms().inner.value()[idx as int];
            if pte.is_pt(pre_cursor.level) {
                post_forgot_guards.inner =~= pre_forgot_guards.inner.remove_keys(
                    {
                        let pa = pre_cursor.get_guard_level_unwrap(pre_cursor.level).nid();
                        let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
                        let ch = node_helper::get_child::<C>(pa, idx as nat);
                        pre_forgot_guards.get_sub_tree_dom(ch)
                    },
                )
            } else {
                post_forgot_guards =~= pre_forgot_guards
            }
        }),
        ({
            let level = post_cursor.level;
            let pre_guard = pre_cursor.get_guard_level_unwrap(level);
            let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
            let pte = pre_guard.guard->Some_0.perms().inner.value()[idx as int];
            let full_forgot_guards = post_cursor.rec_put_guard_from_path(
                post_forgot_guards,
                post_cursor.guard_level,
            );
            pte.is_pt(pre_cursor.level) ==> full_forgot_guards.wf()
        }),
    ensures
        post_cursor.wf_with_forgot_guards(post_forgot_guards),
{
    let _cursor = pre_cursor;
    let cursor = post_cursor;
    let _forgot_guards = pre_forgot_guards;
    let forgot_guards = post_forgot_guards;
    let _cur_node = pre_cursor.get_guard_level_unwrap(pre_cursor.level);
    let cur_node = post_cursor.get_guard_level_unwrap(post_cursor.level);
    let idx = pte_index::<C>(pre_cursor.va, pre_cursor.level);
    let pte = _cur_node.guard->Some_0.perms().inner.value()[idx as int];
    assert(cursor.wf_with_forgot_guards(forgot_guards)) by {
        assert(cursor.g_level@ == _cursor.g_level@);
        assert(cursor.guard_level == _cursor.guard_level);
        assert(cursor.wf_with_forgot_guards_nid_not_contained(forgot_guards)) by {
            assert forall|level: PagingLevel|
                #![trigger cursor.get_guard_level_unwrap(level)]
                cursor.g_level@ <= level <= cursor.guard_level implies {
                !forgot_guards.inner.dom().contains(cursor.get_guard_level_unwrap(level).nid())
            } by {
                assert(cursor.get_guard_level_unwrap(level).nid() == _cursor.get_guard_level_unwrap(
                    level,
                ).nid());
            };
        };
        if !pte.is_pt(_cursor.level) {
            let full_forgot_guards_pre = _cursor.rec_put_guard_from_path(
                _forgot_guards,
                _cursor.guard_level,
            );
            _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                _forgot_guards,
                _cursor.guard_level,
            );
            _cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(_forgot_guards);
            let full_forgot_guards_post = cursor.rec_put_guard_from_path(
                forgot_guards,
                cursor.guard_level,
            );
            cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                forgot_guards,
                cursor.guard_level,
            );
            cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(forgot_guards);
            assert(full_forgot_guards_post.wf()) by {
                assert(full_forgot_guards_post =~= full_forgot_guards_pre.put_spec(
                    cur_node.nid(),
                    cur_node.guard->Some_0.inner@,
                    cur_node.meta_spec().lock,
                )) by {
                    assert(_forgot_guards.inner =~= forgot_guards.inner);
                    let _full_forgot_guards_pre = full_forgot_guards_pre.put_spec(
                        cur_node.nid(),
                        cur_node.guard->Some_0.inner@,
                        cur_node.meta_spec().lock,
                    );
                    assert(full_forgot_guards_post.inner =~= _full_forgot_guards_pre.inner) by {
                        _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                            _forgot_guards,
                            _cursor.guard_level,
                        );
                        cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                            forgot_guards,
                            cursor.guard_level,
                        );
                        assert forall|nid: NodeId|
                            _full_forgot_guards_pre.inner.dom().contains(nid) implies {
                            full_forgot_guards_post.inner.dom().contains(nid)
                        } by {
                            if nid == cur_node.nid() {
                            } else if forgot_guards.inner.dom().contains(nid) {
                            } else {
                                assert(exists|level: PagingLevel|
                                    _cursor.g_level@ <= level <= _cursor.guard_level
                                        && #[trigger] _cursor.get_guard_level_unwrap(level).nid()
                                        == nid);
                                let level = choose|level: PagingLevel|
                                    _cursor.g_level@ <= level <= _cursor.guard_level
                                        && #[trigger] _cursor.get_guard_level_unwrap(level).nid()
                                        == nid;
                                assert(cursor.get_guard_level_unwrap(level).nid() == nid);
                            }
                        };
                        assert forall|nid: NodeId|
                            full_forgot_guards_post.inner.dom().contains(nid) implies {
                            _full_forgot_guards_pre.inner.dom().contains(nid)
                        } by {
                            if nid == cur_node.nid() {
                            } else if forgot_guards.inner.dom().contains(nid) {
                            } else {
                                assert(exists|level: PagingLevel|
                                    cursor.g_level@ <= level <= cursor.guard_level
                                        && #[trigger] cursor.get_guard_level_unwrap(level).nid()
                                        == nid);
                                let level = choose|level: PagingLevel|
                                    cursor.g_level@ <= level <= cursor.guard_level
                                        && #[trigger] cursor.get_guard_level_unwrap(level).nid()
                                        == nid;
                                assert(_cursor.get_guard_level_unwrap(level).nid() == nid);
                            }
                        };
                    };
                };

                assert(full_forgot_guards_pre.get_lock(cur_node.nid())
                    =~= _cur_node.meta_spec().lock) by {
                    _cursor.lemma_put_guard_from_path_top_down_basic1(forgot_guards);
                };

                assert(full_forgot_guards_pre.get_guard_inner(cur_node.nid())
                    =~= _cur_node.guard->Some_0.inner@);

                full_forgot_guards_pre.lemma_replace_with_equal_guard_hold_wf(
                    cur_node.nid(),
                    cur_node.guard->Some_0.inner@,
                    cur_node.meta_spec().lock,
                );
            };
            assert(full_forgot_guards_pre.inner.dom() =~= full_forgot_guards_post.inner.dom()) by {
                _cursor.lemma_put_guard_from_path_top_down_basic1(_forgot_guards);
                cursor.lemma_put_guard_from_path_top_down_basic1(forgot_guards);
                assert forall|nid: NodeId|
                    full_forgot_guards_pre.inner.dom().contains(nid) implies {
                    full_forgot_guards_post.inner.dom().contains(nid)
                } by {
                    if nid == cur_node.nid() {
                    } else if forgot_guards.inner.dom().contains(nid) {
                    } else {
                        assert(exists|level: PagingLevel|
                            _cursor.g_level@ <= level <= _cursor.guard_level
                                && #[trigger] _cursor.get_guard_level_unwrap(level).nid() == nid);
                        let level = choose|level: PagingLevel|
                            _cursor.g_level@ <= level <= _cursor.guard_level
                                && #[trigger] _cursor.get_guard_level_unwrap(level).nid() == nid;
                        assert(cursor.get_guard_level_unwrap(level).nid() == nid);
                    }
                };
                assert forall|nid: NodeId|
                    full_forgot_guards_post.inner.dom().contains(nid) implies {
                    full_forgot_guards_pre.inner.dom().contains(nid)
                } by {
                    if nid == cur_node.nid() {
                    } else if forgot_guards.inner.dom().contains(nid) {
                    } else {
                        assert(exists|level: PagingLevel|
                            cursor.g_level@ <= level <= cursor.guard_level
                                && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid);
                        let level = choose|level: PagingLevel|
                            cursor.g_level@ <= level <= cursor.guard_level
                                && #[trigger] cursor.get_guard_level_unwrap(level).nid() == nid;
                        assert(_cursor.get_guard_level_unwrap(level).nid() == nid);
                    }
                };
            };
        } else {
            let full_forgot_guards = cursor.rec_put_guard_from_path(
                forgot_guards,
                cursor.guard_level,
            );
            cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                forgot_guards,
                cursor.guard_level,
            );
            cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(forgot_guards);
            assert(full_forgot_guards.is_root_and_contained(
                cursor.get_guard_level_unwrap(cursor.guard_level).nid(),
            )) by {
                let nid = cursor.get_guard_level_unwrap(cursor.guard_level).nid();
                assert forall|_nid: NodeId| #[trigger]
                    full_forgot_guards.inner.dom().contains(_nid) implies {
                    node_helper::in_subtree_range::<C>(nid, _nid)
                } by {
                    if forgot_guards.inner.dom().contains(_nid) {
                        assert(_forgot_guards.inner.dom().contains(_nid));
                        let _full_forgot_guards = _cursor.rec_put_guard_from_path(
                            _forgot_guards,
                            _cursor.guard_level,
                        );
                        assert(_full_forgot_guards.is_sub_root_and_contained(nid));
                        assert(_full_forgot_guards.inner.dom().contains(_nid)) by {
                            _cursor.lemma_put_guard_from_path_bottom_up_eq_with_rec(
                                _forgot_guards,
                                _cursor.guard_level,
                            );
                            _cursor.lemma_put_guard_from_path_bottom_up_eq_with_top_down(
                                _forgot_guards,
                            );
                        };
                    } else {
                        assert(exists|level: PagingLevel|
                            cursor.g_level@ <= level <= cursor.guard_level
                                && #[trigger] cursor.get_guard_level_unwrap(level).nid() == _nid);
                        let level = choose|level: PagingLevel|
                            cursor.g_level@ <= level <= cursor.guard_level
                                && #[trigger] cursor.get_guard_level_unwrap(level).nid() == _nid;
                        assert(_cursor.get_guard_level_unwrap(level).nid() == _nid);
                        _cursor.lemma_guard_in_path_relation_implies_in_subtree_range();
                    }
                };
            };
        }
    };
}

} // verus!
