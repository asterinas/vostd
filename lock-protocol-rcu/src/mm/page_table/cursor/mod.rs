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
    arithmetic::{div_mod::*, power::*, power2::*},
    calc,
    layout::is_power_2,
    invariant,
    pervasive::VecAdditionalExecFns,
    prelude::*,
    raw_ptr::MemContents,
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
    utils::{NodeHelper, group_node_helper_lemmas},
    rcu::{SpecInstance, NodeToken, PteArrayToken, FreePaddrToken, PteArrayState},
};

use super::{
    lemma_addr_aligned_propagate, lemma_carry_ends_at_nonzero_result_bits,
    lemma_pte_index_alternative_spec, pte_index, pte_index_mask, PageTable, PageTableConfig,
    PageTableEntryTrait, PageTableError, PagingConsts, PagingConstsTrait, PagingLevel,
};

use crate::mm::NR_ENTRIES;

verus! {

pub open spec fn va_range_wf(va: Range<Vaddr>) -> bool {
    &&& valid_va_range(va)
    &&& va.start < va.end
    &&& vaddr_is_aligned(va.start)
    &&& vaddr_is_aligned(va.end)
}

pub open spec fn va_range_get_guard_level_rec(va: Range<Vaddr>, level: PagingLevel) -> PagingLevel
    recommends
        va_range_wf(va),
        1 <= level <= 4,
    decreases level,
    when 1 <= level <= 4
{
    if level == 1 {
        1
    } else {
        let st = va.start;
        let en = (va.end - 1) as usize;

        if va_level_to_offset(st, level) == va_level_to_offset(en, level) {
            va_range_get_guard_level_rec(va, (level - 1) as PagingLevel)
        } else {
            level
        }
    }
}

pub open spec fn va_range_get_guard_level(va: Range<Vaddr>) -> PagingLevel
    recommends
        va_range_wf(va),
{
    va_range_get_guard_level_rec(va, 4)
}

pub proof fn lemma_va_range_get_guard_level_rec(va: Range<Vaddr>, level: PagingLevel)
    requires
        va_range_wf(va),
        1 <= level <= 4,
    ensures
        1 <= va_range_get_guard_level_rec(va, level) <= level,
    decreases level,
{
    if level > 1 {
        let st = va.start;
        let en = (va.end - 1) as usize;
        if va_level_to_offset(st, level) == va_level_to_offset(en, level) {
            lemma_va_range_get_guard_level_rec(va, (level - 1) as PagingLevel);
        }
    }
}

pub proof fn lemma_va_range_get_guard_level(va: Range<Vaddr>)
    requires
        va_range_wf(va),
    ensures
        1 <= va_range_get_guard_level(va) <= 4,
{
    lemma_va_range_get_guard_level_rec(va, 4);
}

pub open spec fn va_range_get_tree_path(va: Range<Vaddr>) -> Seq<NodeId>
    recommends
        va_range_wf(va),
{
    let guard_level = va_range_get_guard_level(va);
    let trace = va_level_to_trace(va.start, guard_level);
    NodeHelper::trace_to_tree_path(trace)
}

pub proof fn lemma_va_range_get_tree_path(va: Range<Vaddr>)
    requires
        va_range_wf(va),
    ensures
        forall|i|
            #![auto]
            0 <= i < va_range_get_tree_path(va).len() ==> NodeHelper::valid_nid(
                va_range_get_tree_path(va)[i],
            ),
        va_range_get_tree_path(va).len() == 5 - va_range_get_guard_level(va),
{
    broadcast use group_node_helper_lemmas;

    let guard_level = va_range_get_guard_level(va);
    let trace = va_level_to_trace(va.start, guard_level);
    lemma_va_range_get_guard_level(va);
    let path = va_range_get_tree_path(va);
    assert forall|i| 0 <= i < path.len() implies #[trigger] NodeHelper::valid_nid(path[i]) by {
        let nid = path[i];
        if i == 0 {
            assert(nid == NodeHelper::root_id());
            NodeHelper::lemma_root_id();
        } else {
            let sub_trace = trace.subrange(0, i);
            assert(nid == NodeHelper::trace_to_nid(sub_trace));
            lemma_va_level_to_trace_valid(va.start, guard_level);
        }
    }
}

pub open spec fn va_range_get_guard_nid(va: Range<Vaddr>) -> NodeId {
    let path = va_range_get_tree_path(va);
    let level = va_range_get_guard_level(va);
    let idx = 4 - level;
    path[idx]
}

} // verus!
verus! {

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
    pub inst: Tracked<SpecInstance>,
    pub g_level: Ghost<PagingLevel>,  // Ghost level, used in 'unlock_range'
}

/// The maximum value of `PagingConstsTrait::NR_LEVELS`.
pub const MAX_NR_LEVELS: usize = 4;

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
        NodeHelper::is_child(nid1, nid2)
    }

    pub open spec fn guards_in_path_relation(&self) -> bool
        recommends
            self.wf_path(),
    {
        &&& forall|level: PagingLevel|
            #![trigger self.adjacent_guard_is_child(level)]
            self.g_level@ < level <= self.guard_level ==> self.adjacent_guard_is_child(level)
    }

    pub open spec fn wf_path(&self) -> bool {
        &&& self.path.len() == 4
        &&& forall|level: PagingLevel|
            #![trigger self.get_guard_level(level)]
            #![trigger self.get_guard_level_unwrap(level)]
            1 <= level <= 4 ==> {
                if level > self.guard_level {
                    self.get_guard_level(level) is None
                } else if level >= self.g_level@ {
                    &&& self.get_guard_level(level) is Some
                    &&& self.get_guard_level_unwrap(level).wf()
                    &&& self.get_guard_level_unwrap(level).inst_id() == self.inst@.id()
                    &&& self.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value()
                        == false
                    &&& self.get_guard_level_unwrap(level).guard->Some_0.in_protocol() == true
                } else {
                    self.get_guard_level(level) is None
                }
            }
    }

    // TODO
    /// Well-formedness of the cursor's virtual address.
    pub open spec fn wf_va(&self) -> bool {
        // &&& self.va < MAX_USERSPACE_VADDR
        &&& self.barrier_va.start < self.barrier_va.end
            < MAX_USERSPACE_VADDR//
        // We allow the cursor to be at the end of the range.
        &&& self.barrier_va.start <= self.va
            <= self.barrier_va.end//
        // The barrier range should be contained in the range of the frame at
        // // the guard level.
        // &&& align_down(self.barrier_va.start, page_size::<C>((self.guard_level + 1) as u8))
        //     == align_down(
        //     (self.barrier_va.end - 1) as usize,
        //     page_size::<C>((self.guard_level + 1) as u8),
        // )

    }

    /// Well-formedness of the cursor's level and guard level.
    pub open spec fn wf_level(&self) -> bool {
        &&& 1 <= self.level <= self.guard_level <= 4
        &&& self.level <= self.g_level@ <= self.guard_level + 1
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
        admit();
    }

    pub proof fn lemma_guard_in_path_relation_implies_in_subtree_range(&self)
        requires
            self.wf(),
        ensures
            forall|level: PagingLevel|
                self.g_level@ <= level <= self.guard_level
                    ==> #[trigger] NodeHelper::in_subtree_range(
                    self.get_guard_level_unwrap(self.guard_level).nid(),
                    self.get_guard_level_unwrap(level).nid(),
                ),
    {
        admit();
    }

    pub open spec fn rec_put_guard_from_path(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
        cur_level: PagingLevel,
    ) -> SubTreeForgotGuard<C>
        recommends
            self.g_level@ <= cur_level <= self.guard_level,
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

    pub proof fn lemma_rec_put_guard_from_path_basic(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
    )
        requires
            self.wf(),
            forgot_guards.wf(),
            self.wf_with_forgot_guards(forgot_guards),
        ensures
            self.rec_put_guard_from_path(forgot_guards, (self.g_level@ - 1) as PagingLevel) =~= forgot_guards,
    {}

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

    pub open spec fn wf_with_forgot_guards(&self, forgot_guards: SubTreeForgotGuard<C>) -> bool {
        &&& {
            let res = self.rec_put_guard_from_path(forgot_guards, self.guard_level);
            {
                &&& res.wf()
                &&& res.is_root_and_contained(self.get_guard_level_unwrap(self.guard_level).nid())
            }
        }
        &&& forall|level: PagingLevel|
            #![trigger self.get_guard_level_unwrap(level)]
            self.g_level@ <= level <= self.guard_level ==> {
                !forgot_guards.inner.dom().contains(self.get_guard_level_unwrap(level).nid())
            }
    }

    pub open spec fn guards_in_path_wf_with_forgot_guards(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
    ) -> bool {
        forall|level: PagingLevel|
            #![trigger self.rec_put_guard_from_path(forgot_guards, (level - 1) as PagingLevel)]
            self.g_level@ <= level <= self.guard_level ==> {
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
        //             !NodeHelper::in_subtree_range(_nid, nid)
        //         } by {
        //             if NodeHelper::in_subtree_range(_nid, nid) {
        //                 let sub_rt_nid = self.get_guard_level_unwrap(self.guard_level).nid();
        //                 if NodeHelper::in_subtree_range(sub_rt_nid, _nid) {
        //                     assert(
        //                         exists |level: PagingLevel| 
        //                             old(self).level < level <= old(self).guard_level &&
        //                             _nid == #[trigger] old(self).get_guard_level_unwrap(level).nid()
        //                     ) by { admit(); };
        //                 } else {
        //                     assert forall |__nid: NodeId|
        //                         #[trigger] forgot_guards.inner.dom().contains(__nid)
        //                     implies {
        //                         NodeHelper::in_subtree_range(sub_rt_nid, __nid)
        //                     } by {
        //                         assert(forgot_guards.is_root(sub_rt_nid));
        //                     };
        //                 }
        //             }
        //         };
        admit();
    }

    // pub proof fn lemma_push_level_sustains_wf_with_forgot_guards(
    //     pre: Self,
    //     post: Self,
    // )
    //     requires
    //     ensures
    // {
    //     admit();
    // }
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
            0 <= i < old(self).path.len(),
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
            // self.path.len() == old(self).path.len(),
            forall|_i|
                #![trigger self.path[_i]]
                0 <= _i < self.path.len() && _i != i ==> self.path[_i] =~= old(self).path[_i],
    {
        self.g_level = Ghost((self.g_level@ + 1) as PagingLevel);
        self.path[i].take()
    }

    // Trusted
    // #[verifier::external_body]
    // pub fn put(&mut self, i: usize, guard: PageTableGuard<'a, C>)
    //     requires
    //         old(self).wf_path(),
    //         0 <= i < old(self).path.len(),
    //         old(self).level <= i + 1 <= old(self).guard_level,
    //         i + 1 == old(self).g_level@ - 1,
    //         old(self).path[i as int] is None,
    //     ensures
    //         self.wf_path(),
    //         self.g_level@ == old(self).g_level@ - 1,
    //         self.constant_fields_unchanged(old(self)),
    //         self.level == old(self).level,
    //         self.va == old(self).va,
    //         self.path[i as int] =~= Some(guard),
    //         forall |_i|
    //             #![trigger self.path[_i]]
    //             0 <= _i < self.path.len() && _i != i ==> self.path[_i] =~= old(self).path[_i],
    // {
    //     unimplemented!()
    // }

    fn no_op() {}
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
        m: Tracked<LockProtocolModel>,
    ) -> (res: (Self, Tracked<SubTreeForgotGuard<C>>, Tracked<LockProtocolModel>))
        requires
            pt.wf(),
            va_range_wf(*va),
            m@.inv(),
            m@.inst_id() == pt.inst@.id(),
            m@.state() is Void,
        ensures
            res.0.wf(),
            res.0.wf_with_forgot_guards(res.1@),
            res.1@.wf(),
            res.1@.is_root_and_contained(va_range_get_guard_nid(*va)),
            res.2@.inv(),
            res.2@.inst_id() == pt.inst@.id(),
            res.2@.state() is Locked,
            res.2@.sub_tree_rt() == va_range_get_guard_nid(*va),
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
    #[verifier::external_body]
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
    // TODO
    // match res.0 {
    //     Ok(Some(item)) => {
    //         exists|pte_pa: Paddr|
    //             {
    //                 &&& #[trigger] spt.ptes.value().contains_key(pte_pa as int)
    //                 &&& #[trigger] spt.ptes.value()[pte_pa as int].map_to_pa == item.0
    //             }
    //     },
    //     Ok(None) => true,  // Maybe && forall spt.ptes.value()[pte_pa as int].va != self.va
    //     Err(err) => {
    //         &&& old(self).va >= self.barrier_va.end
    //         &&& err == PageTableError::InvalidVaddr(old(self).va)
    //     },
    // },

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
            let level = self.level;
            let ghost cur_level = self.level;

            let cur_entry = self.cur_entry();
            let cur_node = self.path[(self.level - 1) as usize].as_ref().unwrap();
            let child = cur_entry.to_ref(cur_node);
            match child {
                ChildRef::PageTable(pt) => {
                    let ghost nid = pt.nid@;
                    let ghost spin_lock = forgot_guards.get_lock(nid);
                    assert(forgot_guards.wf()) by {
                        admit();
                    };
                    assert(NodeHelper::valid_nid(nid)) by {
                        admit();
                    };
                    assert(forgot_guards.is_sub_root_and_contained(nid)) by {
                        admit();
                    };
                    let tracked forgot_guard = forgot_guards.tracked_take(nid);
                    assert(pt.wf()) by {
                        admit();
                    };
                    assert(pt.deref().meta_spec().lock =~= spin_lock) by {
                        admit();
                    };
                    let guard = pt.make_guard_unchecked(
                        rcu_guard,
                        Tracked(forgot_guard),
                        Ghost(spin_lock),
                    );
                    assert(guard.va() == align_down(cur_va, page_size::<C>(cur_level))) by {
                        admit();
                    };
                    self.push_level(guard);
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
            self.va > old(self).va,
            self.level >= old(self).level,
            res@.wf(),
            self.wf_with_forgot_guards(res@),
            forall|level: PagingLevel|
                #![trigger self.get_guard_level(level)]
                self.level <= level <= self.guard_level ==> self.get_guard_level(level) =~= old(
                    self,
                ).get_guard_level(level),
    {
        let tracked forgot_guards = forgot_guards.get();

        assert(1 <= self.level <= C::NR_LEVELS()) by {
            admit();
        };  // We only target x86.
        let cur_page_size = page_size::<C>(self.level);
        assert(align_down(self.va, cur_page_size) <= self.va) by {
            admit();
        };  // Strange bug.
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
                assert(1 <= self.level <= C::NR_LEVELS()) by {
                    admit();
                };  // We only target x86.
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
        // Have no idea how to remove the redundant proofs.
        assert(self.wf()) by {
            assert(self.wf_path()) by {
                assert forall|level: PagingLevel|
                    #![trigger self.get_guard_level(level)]
                    #![trigger self.get_guard_level_unwrap(level)]
                    1 <= level <= 4 implies {
                    if level > self.guard_level {
                        self.get_guard_level(level) is None
                    } else if level >= self.g_level@ {
                        &&& self.get_guard_level(level) is Some
                        &&& self.get_guard_level_unwrap(level).wf()
                        &&& self.get_guard_level_unwrap(level).inst_id() == self.inst@.id()
                        &&& self.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value()
                            == false
                        &&& self.get_guard_level_unwrap(level).guard->Some_0.in_protocol() == true
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
                            &&& _cursor.get_guard_level_unwrap(
                                level,
                            ).guard->Some_0.stray_perm().value() == false
                            &&& _cursor.get_guard_level_unwrap(level).guard->Some_0.in_protocol()
                                == true
                        });
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
    {
        let ghost init_forgot_guards = forgot_guards@;
        let tracked mut forgot_guards = forgot_guards.get();

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
            assert(forgot_guard =~= old(self).get_guard_level_unwrap(old(self).level).guard->Some_0.inner@);
            assert(!forgot_guards.inner.dom().contains(nid));
            assert(forgot_guard.stray_perm.value() == false);
            assert(forgot_guard.in_protocol == true);
            assert(forgot_guards.is_sub_root(nid)) by {
                old(self).lemma_wf_with_forgot_guards_sound(forgot_guards);
                old(self).lemma_rec_put_guard_from_path_basic(forgot_guards);
            };
            assert(forgot_guards.children_are_contained(nid, forgot_guard.pte_token->Some_0.value())) by {
                old(self).lemma_wf_with_forgot_guards_sound(forgot_guards);
                old(self).lemma_rec_put_guard_from_path_basic(forgot_guards);
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
                    1 <= level <= 4 implies {
                    if level > self.guard_level {
                        self.get_guard_level(level) is None
                    } else if level >= self.g_level@ {
                        &&& self.get_guard_level(level) is Some
                        &&& self.get_guard_level_unwrap(level).wf()
                        &&& self.get_guard_level_unwrap(level).inst_id() == self.inst@.id()
                        &&& self.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value()
                            == false
                        &&& self.get_guard_level_unwrap(level).guard->Some_0.in_protocol() == true
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

        Tracked(forgot_guards)
    }

    pub open spec fn wf_push_level(self, post: Self, child_pt: PageTableGuard<'a, C>) -> bool {
        &&& post.level == self.level - 1
        &&& post.g_level@ == self.g_level@ - 1
        &&& forall |level: PagingLevel|
            #![trigger self.get_guard_level(level)]
            #![trigger self.get_guard_level_unwrap(level)]
            1 <= level <= post.guard_level && level != post.level ==> {
                self.get_guard_level(level) =~= post.get_guard_level(level)
            }
        &&& self.get_guard_level(post.level) is None
        &&& post.get_guard_level(post.level) =~= Some(child_pt)
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
            NodeHelper::is_child(
                old(self).get_guard_level_unwrap(old(self).level).nid(),
                child_pt.nid(),
            )
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
                assert(self.wf_path()) by {
                    assert forall |level: PagingLevel|
                        #![trigger self.get_guard_level(level)]
                        #![trigger self.get_guard_level_unwrap(level)]
                        1 <= level <= 4 
                    implies {
                        if level > self.guard_level {
                            self.get_guard_level(level) is None
                        } else if level >= self.g_level@ {
                            &&& self.get_guard_level(level) is Some
                            &&& self.get_guard_level_unwrap(level).wf()
                            &&& self.get_guard_level_unwrap(level).inst_id() == self.inst@.id()
                            &&& self.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value() == false
                            &&& self.get_guard_level_unwrap(level).guard->Some_0.in_protocol() == true
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
                            } else {
                                assert(self.path[level - 1] =~= old(self).path[level - 1]);
                            }
                        } else {
                            assert(self.path[level - 1] =~= old(self).path[level - 1]);
                            assert(old(self).get_guard_level(level) is None);
                        }
                    };
                };
            };
            assert(self.guards_in_path_relation()) by {
                assert forall |level: PagingLevel|
                    #![trigger self.adjacent_guard_is_child(level)]
                    self.g_level@ < level <= self.guard_level
                implies {
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
                #[trigger] forgot_guards.inner.dom().contains(va_level_to_nid(self.0.va, level))
            }
    }

    pub open spec fn new_item_relate(
        &self,
        forgot_guards: SubTreeForgotGuard<C>,
        item: C::Item,
    ) -> bool {
        let nid = va_level_to_nid(self.0.va, 1);
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
    #[verifier::external_body]
    pub fn map(
        &mut self,
        item: C::Item,
        forgot_guards: Tracked<SubTreeForgotGuard<C>>,
        Tracked(m): Tracked<&LockProtocolModel>,
    ) -> (res: (PageTableItem<C>, Tracked<SubTreeForgotGuard<C>>))
        requires
            old(self).0.wf(),
            old(self).0.g_level@ == old(self).0.level,
            // old(self).0.va % page_size::<C>(1) == 0,
            C::item_into_raw_spec(item).1 == 1,
            // old(self).0.va + page_size::<C>(C::item_into_raw_spec(item).1) <= old(
            //     self,
            // ).0.barrier_va.end,
            forgot_guards@.wf(),
            old(self).0.wf_with_forgot_guards(forgot_guards@),
            m.inv(),
            m.inst_id() == old(self).0.inst@.id(),
            m.state() is Locked,
            m.sub_tree_rt() == va_level_to_nid(old(self).0.va, old(self).0.guard_level),
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

        // #[verifier::loop_isolation(false)]
        // // Go up if not applicable.
        // while self.0.level < level
        //     invariant
        //         spt.wf(),
        //         self.0.wf_local(spt),
        //         self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
        //         // VA should be unchanged in the loop.
        //         self.0.va == old(self).0.va,
        //     decreases level - self.0.level,
        // {
        //     self.0.pop_level(Tracked(spt));
        // }

        assert(self.0.level >= level);

        // Go down if not applicable.
        while self.0.level != level
            invariant
                self.0.wf(),
                self.0.g_level@ == self.0.level,
                self.0.constant_fields_unchanged(&old(self).0),
                // VA should be unchanged in the loop.
                self.0.va == old(self).0.va,
                self.0.level >= level && level == 1,
                self.0.va < self.0.barrier_va.end,
                forgot_guards.wf(),
                self.0.wf_with_forgot_guards(forgot_guards),
            decreases self.0.level,
        {
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
                    assert(forgot_guards.wf()) by {
                        admit();
                    };
                    assert(NodeHelper::valid_nid(nid)) by {
                        admit();
                    };
                    assert(forgot_guards.is_sub_root_and_contained(nid)) by {
                        admit();
                    };
                    let tracked forgot_guard = forgot_guards.tracked_take(nid);
                    assert(pt.wf()) by {
                        admit();
                    };
                    assert(pt.deref().meta_spec().lock =~= spin_lock) by {
                        admit();
                    };
                    let child_pt = pt.make_guard_unchecked(
                        preempt_guard,
                        Tracked(forgot_guard),
                        Ghost(spin_lock),
                    );
                    assert(child_pt.va() == align_down(cur_va, page_size::<C>(cur_level))) by {
                        admit();
                    };
                    self.0.push_level(child_pt);
                },
                ChildRef::None => {
                    assert(self.0.cur_node_unwrap().level_spec() == cur_level);
                    let mut cur_node = self.0.take((self.0.level - 1) as usize).unwrap();
                    let res = cur_entry.alloc_if_none(preempt_guard, &mut cur_node, Tracked(m));
                    let child_pt = res.unwrap();
                    // self.0.put((self.0.level - 1) as usize, cur_node);
                    self.0.path[(self.0.level - 1) as usize] = Some(cur_node);

                    // assert(self.0.wf_local(spt)) by {
                    //     assert forall|i: PagingLevel|
                    //         #![trigger self.0.path[path_index_at_level_local_spec(i)]]
                    //         self.0.level <= i <= self.0.guard_level implies {
                    //         let guard = path_index!(self.0.path[i]).unwrap();
                    //         guard.wf_local(&spt.alloc_model)
                    //     } by {
                    //         // From self.wf() before calling alloc_if_none
                    //         assert(forall|i: PagingLevel|
                    //             #![trigger self.0.path[path_index_at_level_local_spec(i)]]
                    //             self.0.level <= i <= self.0.guard_level ==> {
                    //                 let guard_option = path_index!(self.0.path[i]);
                    //                 &&& guard_option.unwrap().wf_local(&old_alloc_model)
                    //             });
                    //         // From post condition of alloc_if_none's alloc_model_do_not_change_except_add_frame
                    //         assert(forall|i: int| #[trigger]
                    //             old_alloc_model.meta_map.contains_key(i) ==> {
                    //                 &&& spt.alloc_model.meta_map.contains_key(i)
                    //                 &&& spt.alloc_model.meta_map[i].pptr()
                    //                     == old_alloc_model.meta_map[i].pptr()
                    //                 &&& spt.alloc_model.meta_map[i].value()
                    //                     == old_alloc_model.meta_map[i].value()
                    //             });
                    //         let guard = path_index!(self.0.path[i]).unwrap();
                    //         assert(level_is_in_range::<C>(
                    //             guard.level_local_spec(&old_alloc_model) as int,
                    //         ));
                    //         assert(old_alloc_model.meta_map.contains_key(
                    //             guard.paddr_local() as int,
                    //         ));
                    //         assert(spt.alloc_model.meta_map.contains_key(
                    //             guard.paddr_local() as int,
                    //         ));
                    //         assert(guard.inner.meta_local_spec(&old_alloc_model)
                    //             == guard.inner.meta_local_spec(&spt.alloc_model));
                    //         assert(guard.level_local_spec(&old_alloc_model)
                    //             == guard.level_local_spec(&spt.alloc_model));
                    //     }
                    // }
                    // assert(child_pt.va() == align_down(self.0.va, page_size::<C>(self.0.level)))
                    //     by {
                    //     calc! {
                    //         (==)
                    //         child_pt.va(); {}
                    //         cur_entry.va@; {}
                    //         align_down(self.0.va, page_size::<C>(self.0.level));
                    //     }
                    // }
                    self.0.push_level(child_pt);
                },
                ChildRef::Frame(_, _, _) => {
                    assume(false);  // FIXME: implement split if huge page
                },
            }
            continue ;
        }
        assert(self.0.level == level);

        let mut cur_entry = self.0.cur_entry();
        let mut cur_node = self.0.take((self.0.level - 1) as usize).unwrap();
        let old_entry = cur_entry.replace(Child::Frame(pa, level, prop), &mut cur_node);
        // self.0.put((self.0.level - 1) as usize, cur_node);
        self.0.path[(self.0.level - 1) as usize] = Some(cur_node);

        // assert(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);
        // assert(self.0.path_wf(spt));

        let old_va = self.0.va;
        let old_len = page_size::<C>(self.0.level);

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
    #[verifier::external_body]
    pub unsafe fn take_next(
        &mut self,
        len: usize,
        forgot_guards: Tracked<SubTreeForgotGuard<C>>,
    ) -> (res: (PageTableItem<C>, Tracked<SubTreeForgotGuard<C>>))
        requires
            old(self).0.wf(),
            old(self).0.g_level@ == old(self).0.level,
            old(self).0.va as int + len as int <= old(self).0.barrier_va.end as int,
            len % page_size::<C>(1) == 0,
            len > page_size::<C>(old(self).0.level),
            forgot_guards@.wf(),
            old(self).0.wf_with_forgot_guards(forgot_guards@),
        ensures
            self.0.wf(),
            self.0.g_level@ == self.0.level,
            self.0.constant_fields_unchanged(&old(self).0),
            res.1@.wf(),
            self.0.wf_with_forgot_guards(
                res.1@,
            ),
    // TODO: Post condition of res.0

    {
        let tracked forgot_guards = forgot_guards.get();

        let preempt_guard = self.0.preempt_guard;

        let start = self.0.va;
        assert(len % page_size::<C>(1) == 0);
        let end = start + len;
        assert(end <= self.0.barrier_va.end);

        while self.0.va < end && self.0.level > 1
            invariant
                self.0.wf(),
                self.0.g_level@ == self.0.level,
                self.0.constant_fields_unchanged(&old(self).0),
                forgot_guards.wf(),
                self.0.wf_with_forgot_guards(
                    forgot_guards,
                ),
        // self.0.va + page_size::<C>(self.0.level) < end,
        // self.0.va + len < MAX_USERSPACE_VADDR,
        // end <= self.0.barrier_va.end,

            decreases
                    end - self.0.va,
                    // for push_level, only level decreases
                    self.0.level,
        {
            let cur_va = self.0.va;
            let cur_level = self.0.level;
            let mut cur_entry = self.0.cur_entry();

            // Skip if it is already absent.
            if cur_entry.is_none() {
                if self.0.va + page_size::<C>(self.0.level) > end {
                    self.0.va = end;
                    break ;
                }
                assert(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);
                let res = self.0.move_forward(Tracked(forgot_guards));
                proof {
                    forgot_guards = res.get();
                }
                // assert(self.0.path_wf(spt));

                // assume(self.0.va + page_size::<C>(self.0.level) < end);
                // assume(self.0.va + len < MAX_USERSPACE_VADDR);
                continue ;
            }
            // Go down if not applicable.

            if cur_va % page_size::<C>(cur_level) != 0 || cur_va + page_size::<C>(cur_level) > end {
                assert(!cur_entry.is_none_spec());
                let cur_node = self.0.path[(self.0.level - 1) as usize].as_ref().unwrap();
                let child = cur_entry.to_ref(cur_node);
                match child {
                    ChildRef::PageTable(pt) => {
                        let ghost nid = pt.nid@;
                        let ghost spin_lock = forgot_guards.get_lock(nid);
                        assert(forgot_guards.wf()) by {
                            admit();
                        };
                        assert(NodeHelper::valid_nid(nid)) by {
                            admit();
                        };
                        assert(forgot_guards.is_sub_root_and_contained(nid)) by {
                            admit();
                        };
                        let tracked forgot_guard = forgot_guards.tracked_take(nid);
                        assert(pt.wf()) by {
                            admit();
                        };
                        assert(pt.deref().meta_spec().lock =~= spin_lock) by {
                            admit();
                        };
                        let pt = pt.make_guard_unchecked(
                            preempt_guard,
                            Tracked(forgot_guard),
                            Ghost(spin_lock),
                        );
                        assert(pt.va() == align_down(cur_va, page_size::<C>(cur_level))) by {
                            admit();
                        };
                        // If there's no mapped PTEs in the next level, we can
                        // skip to save time.
                        if pt.nr_children() != 0 {
                            self.0.push_level(pt);
                        } else {
                            if self.0.va + page_size::<C>(self.0.level) > end {
                                self.0.va = end;
                                break ;
                            }
                            assert(self.0.va + page_size::<C>(self.0.level)
                                <= self.0.barrier_va.end);
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

                // assume(self.0.va + page_size::<C>(self.0.level) < end);
                // assume(self.0.va + len < MAX_USERSPACE_VADDR);
                continue ;
            }
            // Unmap the current page and return it.

            assert(!cur_entry.is_none_spec());
            let old_pte_paddr = cur_entry.pte.inner.pte_paddr();
            assert(old_pte_paddr == cur_entry.pte.inner.pte_paddr());

            // proof {
            //     let child_frame_addr = spt.i_ptes.value()[index_pte_paddr(
            //         cur_entry.node.paddr_local() as int,
            //         cur_entry.idx as int,
            //     ) as int].map_to_pa;
            //     let child_frame_level = spt.frames.value()[child_frame_addr].level as int;
            //     // TODO: enhance path_wf or spt_wf
            //     assume(forall|i: int| #[trigger]
            //         self.0.path[i].is_some() ==> #[trigger] self.0.path[i].unwrap().paddr_local()
            //             != child_frame_addr);
            // }
            // TODO: prove the last level entry...
            let mut cur_node = self.0.take((self.0.level - 1) as usize).unwrap();
            let old = cur_entry.replace(Child::None, &mut cur_node);
            // self.0.put((self.0.level - 1) as usize, cur_node);
            self.0.path[(self.0.level - 1) as usize] = Some(cur_node);

            let item = match old {
                Child::Frame(page, level, prop) => PageTableItem::Mapped {
                    va: self.0.va,
                    page,
                    prop,
                },
                Child::PageTable(pt) => {
                    // SAFETY: We must have locked this node.
                    let ghost nid = pt.deref().nid@;
                    let ghost spin_lock = forgot_guards.get_lock(nid);
                    let tracked forgot_guard = forgot_guards.tracked_take(nid);
                    let locked_pt = pt.deref().borrow().make_guard_unchecked(
                        preempt_guard,
                        Tracked(forgot_guard),
                        Ghost(spin_lock),
                    );
                    assert(locked_pt.va() == align_down(self.0.va, page_size::<C>(self.0.level)))
                        by {
                        admit();
                    };
                    // assert!(
                    //     !(TypeId::of::<M>() == TypeId::of::<KernelMode>()
                    //         && self.0.level == C::NR_LEVELS()),
                    //     "Unmapping shared kernel page table nodes"
                    // ); // TODO
                    // SAFETY:
                    //  - We checked that we are not unmapping shared kernel page table nodes.
                    //  - We must have locked the entire sub-tree since the range is locked.
                    // let unlocked_pt = locking::dfs_mark_astray(locked_pt);
                    // See `locking.rs` for why we need this. // TODO
                    // let drop_after_grace = unlocked_pt.clone();
                    // crate::sync::after_grace_period(|| {
                    //     drop(drop_after_grace);
                    // });
                    PageTableItem::StrayPageTable {
                        pt,
                        va: self.0.va,
                        len: page_size::<C>(self.0.level),
                    }
                },
                Child::None => { PageTableItem::NotMapped { va: 0, len: 0 } },
            };

            // assume(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);  // TODO
            // assert(self.0.path_wf(spt)) by {
            //     admit();
            // };
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

} // verus!
