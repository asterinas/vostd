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
        lemma_va_level_to_trace_valid,
    },
    utils::{NodeHelper, group_node_helper_lemmas},
    rcu::{SpecInstance, NodeToken, PteArrayToken, FreePaddrToken, PteArrayState},
};

use super::{
    lemma_addr_aligned_propagate, lemma_carry_ends_at_nonzero_result_bits,
    lemma_pte_index_alternative_spec, pte_index, pte_index_mask, PageTable, PageTableConfig,
    PageTableEntryTrait, PageTableError, PagingConsts, PagingConstsTrait, PagingLevel,
};

// use crate::exec;
use crate::mm::NR_ENTRIES;

/// A handy ghost mode macro to get the guard at a certain level in the path.
// macro_rules! path_index {
//     ($self: ident . path [$i:expr]) => {
//         $self.path.view().index(path_index_at_level_local_spec($i))
//     };
//     ($self: ident . 0 . path [$i:expr]) => {
//         $self
//             .0
//             .path
//             .view()
//             .index(path_index_at_level_local_spec($i))
//     };
//     (old($self: ident) . path [$i:expr]) => {
//         old($self)
//             .path
//             .view()
//             .index(path_index_at_level_local_spec($i))
//     };
//     (old($self: ident) . 0 . path [$i:expr]) => {
//         old($self)
//             .0
//             .path
//             .view()
//             .index(path_index_at_level_local_spec($i))
//     };
// }

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
            self.g_level@ < level <= self.guard_level ==> 
                self.adjacent_guard_is_child(level)
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
                    &&& self.get_guard_level_unwrap(level).guard->Some_0.stray_perm().value() == false
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
        // &&& self.barrier_va.start < self.barrier_va.end
        //     < MAX_USERSPACE_VADDR
        // // We allow the cursor to be at the end of the range.
        // &&& self.barrier_va.start <= self.va
        //     <= self.barrier_va.end
        // // The barrier range should be contained in the range of the frame at
        // // the guard level.
        // &&& align_down(self.barrier_va.start, page_size::<C>((self.guard_level + 1) as u8))
        //     == align_down(
        //     (self.barrier_va.end - 1) as usize,
        //     page_size::<C>((self.guard_level + 1) as u8),
        // )
        true
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

}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    pub open spec fn guard_in_path_nid_diff(
        &self,
        level1: PagingLevel,
        level2: PagingLevel,
    ) -> bool {
        self.get_guard_level_unwrap(level1).nid() != 
        self.get_guard_level_unwrap(level2).nid()
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
                    &&& _forgot_guards.childs_are_contained(
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
        admit();
    }    
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    // Trusted
    #[verifier::external_body]
    pub fn take(&mut self, i: usize) -> (res: Option<PageTableGuard<'a, C>>)
        requires
            0 <= i < old(self).path.len(),
            old(self).level <= i + 1 <= old(self).guard_level,
            i + 1 == old(self).g_level@,
        ensures
            res =~= old(self).path[i as int],
            self.path[i as int] is None,
            self.path.len() == old(self).path.len(),
            forall|_i|
                #![trigger self.path[_i]]
                0 <= _i < self.path.len() && _i != i ==> self.path[_i] =~= old(self).path[_i],
            self.preempt_guard =~= old(self).preempt_guard,
            self.level == old(self).level,
            self.guard_level == old(self).guard_level,
            self.va == old(self).va,
            self.barrier_va == old(self).barrier_va,
            self.inst =~= old(self).inst,
            self.g_level@ == old(self).g_level@ + 1,
            self.wf_path(),
    {
        self.g_level = Ghost((self.g_level@ + 1) as PagingLevel);
        self.path[i].take()
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
        m: Tracked<LockProtocolModel>,
    ) -> (res: (
        Self,
        Tracked<SubTreeForgotGuard<C>>,
        Tracked<LockProtocolModel>,
    ))
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
    // #[verifier::external_body]
    // pub fn query(
    //     &mut self,
    //     forgot_guards: Tracked<SubTreeForgotGuard<C>>,
    // ) -> (res: (
    //     Result<Option<(Paddr, PagingLevel, PageProperty)>, PageTableError>,
    //     Tracked<SubTreeForgotGuard<C>>,
    // ))
    //     requires
    //         old(self).wf_local(spt),
    //         spt.wf(),
    //         spt.wf_with_forgot_guards(forgot_guards@),
    //     ensures
    //         self.wf_local(spt),
    //         match res.0 {
    //             Ok(Some(item)) => {
    //                 exists|pte_pa: Paddr|
    //                     {
    //                         &&& #[trigger] spt.ptes.value().contains_key(pte_pa as int)
    //                         &&& #[trigger] spt.ptes.value()[pte_pa as int].map_to_pa == item.0
    //                     }
    //             },
    //             Ok(None) => true,  // Maybe && forall spt.ptes.value()[pte_pa as int].va != self.va
    //             Err(err) => {
    //                 &&& old(self).va >= self.barrier_va.end
    //                 &&& err == PageTableError::InvalidVaddr(old(self).va)
    //             },
    //         },
    // {
    //     // if self.va >= self.barrier_va.end {
    //     //     return (Err(PageTableError::InvalidVaddr(self.va)), forgot_guards);
    //     // }
    //     // let tracked forgot_guards = forgot_guards.get();

    //     // let ghost cur_va = self.va;

    //     // let rcu_guard = self.preempt_guard;

    //     // loop
    //     //     invariant
    //     //         self.wf_local(spt),
    //     //         self.constant_fields_unchanged(old(self), spt, spt),
    //     //         cur_va == self.va == old(self).va < self.barrier_va.end,
    //     //     decreases self.level,
    //     // {
    //     //     let level = self.level;
    //     //     let ghost cur_level = self.level;

    //     //     let cur_entry = self.cur_entry(Tracked(spt));
    //     //     match cur_entry.to_ref_local(Tracked(spt)) {
    //     //         ChildRefLocal::PageTable(pt) => {
    //     //             let ghost nid = pt.nid@;
    //     //             let ghost spin_lock = forgot_guards.get_lock(nid);
    //     //             assert(forgot_guards.wf()) by {
    //     //                 admit();
    //     //             };
    //     //             assert(NodeHelper::valid_nid(nid)) by {
    //     //                 admit();
    //     //             };
    //     //             assert(forgot_guards.is_sub_root_and_contained(nid)) by {
    //     //                 admit();
    //     //             };
    //     //             let tracked forgot_guard = forgot_guards.tracked_take(nid);
    //     //             assert(pt.wf()) by {
    //     //                 admit();
    //     //             };
    //     //             assert(pt.deref().meta_spec().lock =~= spin_lock) by {
    //     //                 admit();
    //     //             };
    //     //             let guard = pt.make_guard_unchecked(
    //     //                 rcu_guard,
    //     //                 Tracked(forgot_guard),
    //     //                 Ghost(spin_lock),
    //     //             );
    //     //             assert(guard.va() == align_down(cur_va, page_size::<C>(cur_level))) by {
    //     //                 admit();
    //     //             };
    //     //             self.push_level(guard, Tracked(spt));
    //     //             continue ;
    //     //         },
    //     //         ChildRefLocal::None => return (Ok(None), Tracked(forgot_guards)),
    //     //         ChildRefLocal::Frame(pa, ch_level, prop) => {
    //     //             // debug_assert_eq!(ch_level, level);
    //     //             // SAFETY:
    //     //             // This is part of (if `split_huge` happens) a page table item mapped
    //     //             // with a previous call to `C::item_into_raw`, where:
    //     //             //  - The physical address and the paging level match it;
    //     //             //  - The item part is still mapped so we don't take its ownership.
    //     //             //
    //     //             // For page table configs that require the `AVAIL1` flag to be kept
    //     //             // (currently, only kernel page tables), the callers of the unsafe
    //     //             // `protect_next` method uphold this invariant.
    //     //             // let item = core::mem::ManuallyDrop::new(
    //     //             //     unsafe { C::item_from_raw(pa, level, prop, Tracked(&spt.alloc_model)) },
    //     //             // );
    //     //             // TODO: Provide a `PageTableItemRef` to reduce copies.
    //     //             return (Ok(Some((pa, ch_level, prop))), Tracked(forgot_guards));
    //     //         },
    //     //     };
    //     // }
    //     unimplemented!()
    // }

    /// Traverses forward in the current level to the next PTE.
    ///
    /// If reached the end of a page table node, it leads itself up to the next page of the parent
    /// page if possible.
    // #[verifier::external_body]
    // pub(in crate::mm) fn move_forward(&mut self, Tracked(spt): Tracked<&SubPageTable<C>>)
    //     requires
    //         old(self).wf_local(spt),
    //         old(self).va + page_size::<C>(old(self).level) <= old(self).barrier_va.end,
    //     ensures
    //         self.wf_local(spt),
    //         self.constant_fields_unchanged(old(self), spt, spt),
    //         self.va > old(self).va,
    //         self.level >= old(self).level,
    // {
    //     // let cur_page_size = page_size::<C>(self.level);
    //     // let next_va = align_down(self.va, cur_page_size) + cur_page_size;
    //     // assert(self.va < next_va <= self.va + cur_page_size) by {
    //     //     let aligned_va = align_down(self.va, cur_page_size) as int;
    //     //     lemma_page_size_spec_properties::<C>(self.level);
    //     //     assert(0 <= self.va % cur_page_size <= self.va && 0 <= self.va % cur_page_size
    //     //         < cur_page_size) by (nonlinear_arith)
    //     //         requires
    //     //             self.va >= 0,
    //     //             cur_page_size > 0,
    //     //     ;
    //     //     assert(aligned_va as int == self.va as int - self.va as int % cur_page_size as int);
    //     //     assert(next_va - self.va == cur_page_size - self.va % cur_page_size);
    //     //     assert(0 < cur_page_size - self.va % cur_page_size <= cur_page_size);
    //     // }
    //     // let ghost old_path = self.path;
    //     // assert(next_va % page_size::<C>(self.level) == 0) by (nonlinear_arith)
    //     //     requires
    //     //         next_va == align_down(self.va, cur_page_size) + cur_page_size,
    //     //         cur_page_size == page_size::<C>(self.level),
    //     //         align_down(self.va, cur_page_size) % cur_page_size == 0,
    //     // ;
    //     // while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0
    //     //     invariant
    //     //         old(self).wf_local(spt),
    //     //         self.wf_local(spt),
    //     //         self.constant_fields_unchanged(old(self), spt, spt),
    //     //         self.level >= old(self).level,
    //     //         self.va == old(self).va,
    //     //         next_va % page_size::<C>(self.level) == 0,
    //     //         forall|i: PagingLevel|
    //     //             self.level <= i <= self.guard_level ==> path_index!(self.path[i])
    //     //                 == #[trigger] old_path[path_index_at_level_local_spec(i)],
    //     //     decreases self.guard_level - self.level,
    //     // {
    //     //     self.pop_level(Tracked(&spt));
    //     //     proof {
    //     //         // Only thing we need to prove is next_va % page_size(self.level) == 0
    //     //         assert(next_va % page_size::<C>((self.level - 1) as u8) == 0);
    //     //         assert(pte_index::<C>(next_va, (self.level - 1) as u8) == 0);
    //     //         lemma_addr_aligned_propagate::<C>(next_va, self.level);
    //     //     }
    //     // }
    //     // self.va = next_va;
    //     // proof {
    //     //     // We prove self.wf(spt) by considering two cases
    //     //     if (self.level == self.guard_level) {
    //     //         assert forall|i: PagingLevel|
    //     //             #![trigger align_down(self.va, page_size::<C>((i + 1) as u8))]
    //     //             self.level <= i <= self.guard_level && self.va
    //     //                 < self.barrier_va.end implies path_index!(self.path[i]).unwrap().va()
    //     //             == align_down(self.va, page_size::<C>((i + 1) as u8)) by {
    //     //             assert(i == self.guard_level);
    //     //             let guard_va = old_path[path_index_at_level_local_spec(i)].unwrap().va();
    //     //             let pg_size = page_size::<C>((i + 1) as u8);
    //     //             lemma_page_size_spec_properties::<C>((i + 1) as u8);
    //     //             calc! {
    //     //                 (==)
    //     //                 path_index!(self.path[i]).unwrap().va(); {}
    //     //                 guard_va@; {}
    //     //                 align_down(old(self).va, page_size::<C>((i + 1) as u8)); {
    //     //                     lemma_align_down_squeeze(
    //     //                         self.barrier_va.start,
    //     //                         old(self).va,
    //     //                         (self.barrier_va.end - 1) as usize,
    //     //                         page_size::<C>((i + 1) as u8),
    //     //                     );
    //     //                 }
    //     //                 align_down(self.barrier_va.start, page_size::<C>((i + 1) as u8)); {
    //     //                     lemma_align_down_squeeze(
    //     //                         self.barrier_va.start,
    //     //                         self.va,
    //     //                         (self.barrier_va.end - 1) as usize,
    //     //                         page_size::<C>((i + 1) as u8),
    //     //                     );
    //     //                 }
    //     //                 align_down(self.va, page_size::<C>((i + 1) as u8));
    //     //             }
    //     //         }
    //     //         assert(self.wf_local(spt));
    //     //     } else {
    //     //         let old_level = old(self).level;
    //     //         let old_page_size = cur_page_size;
    //     //         let aligned_va = align_down(old(self).va, old_page_size);
    //     //         // Information from the loop termination
    //     //         assert(old_level <= self.level < self.guard_level);
    //     //         assert(pte_index::<C>(next_va, self.level) != 0);

    //     //         // No overflow.
    //     //         assert(aligned_va + old_page_size < usize::MAX) by {
    //     //             assert(aligned_va + old_page_size <= old(self).barrier_va.end);
    //     //             assert(old(self).barrier_va.end < usize::MAX);
    //     //         }
    //     //         assert(self.va == next_va == aligned_va + old_page_size);

    //     //         // The page size of the "next" level, i.e., self.level + 1.
    //     //         let next_pg_size = page_size::<C>((self.level + 1) as u8) as nat;
    //     //         // Apply the main lemma here to show that old(self).va and self.va are the
    //     //         // same when aligned to next_pg_size.
    //     //         assert(old(self).va as nat / next_pg_size == self.va as nat / next_pg_size) by {
    //     //             assert(old(self).va < self.va <= old(self).va + old_page_size);
    //     //             // These are the arguments to lemma_carry_ends_at_nonzero_result_bits
    //     //             let p = (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2()
    //     //                 - C::PTE_SIZE().ilog2()) * self.level) as nat;
    //     //             assert(pow2(p) == next_pg_size) by {
    //     //                 lemma_page_size_spec_properties::<C>((self.level + 1) as PagingLevel);
    //     //             }
    //     //             let q = (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2()
    //     //                 - C::PTE_SIZE().ilog2()) * (self.level - 1)) as nat;
    //     //             assert(pow2(q) == page_size::<C>(self.level) as nat) by {
    //     //                 lemma_page_size_spec_properties::<C>(self.level);
    //     //             }
    //     //             // Preconditions
    //     //             C::lemma_consts_properties();
    //     //             // q <= p
    //     //             assert(q <= p) by (nonlinear_arith)
    //     //                 requires
    //     //                     p == (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2()
    //     //                         - C::PTE_SIZE().ilog2()) * self.level) as nat,
    //     //                     q == (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2()
    //     //                         - C::PTE_SIZE().ilog2()) * (self.level - 1)) as nat,
    //     //                     C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2() >= 0,
    //     //             ;
    //     //             // old_page_size is not too large
    //     //             assert(old_page_size <= pow2(q)) by {
    //     //                 lemma_page_size_increases::<C>(old(self).level, self.level);
    //     //             }
    //     //             // The middle part of the result is not zero
    //     //             assert(next_va as nat % pow2(p) / pow2(q) != 0) by {
    //     //                 lemma_pte_index_alternative_spec::<C>(next_va, self.level);
    //     //                 // Use this to activate the second alternative spec
    //     //                 assert(self.level < self.guard_level <= C::NR_LEVELS());
    //     //                 // Then, use this to help the verifier know where the !=0 came from
    //     //                 assert(pte_index::<C>(next_va, self.level) != 0);
    //     //             }
    //     //             // Now we are finally ready to apply the main lemma
    //     //             lemma_carry_ends_at_nonzero_result_bits(
    //     //                 next_va as nat,
    //     //                 old(self).va as nat,
    //     //                 p,
    //     //                 q,
    //     //             );
    //     //             // Let's restate the result of the lemma here.
    //     //             assert(next_va as nat / pow2(p) == old(self).va as nat / pow2(p));
    //     //         }

    //     //         assert forall|i: PagingLevel|
    //     //             #![trigger page_size::<C>(i)]
    //     //             self.level < i <= self.guard_level + 1 implies old(self).va as nat
    //     //             / page_size::<C>(i) as nat == self.va as nat / page_size::<C>(i) as nat by {
    //     //             assert(self.level + 1 <= i);
    //     //             assert(next_pg_size > 0) by {
    //     //                 lemma_page_size_spec_properties::<C>((self.level + 1) as u8);
    //     //             }
    //     //             // Ratio of page_size::<C>(i) / next_pg_size
    //     //             let ratio = pow(
    //     //                 nr_subpage_per_huge::<C>() as int,
    //     //                 (i - (self.level + 1)) as nat,
    //     //             ) as nat;
    //     //             assert(page_size::<C>(i) as nat == next_pg_size * ratio) by {
    //     //                 lemma_page_size_geometric::<C>((self.level + 1) as u8, i);
    //     //             }
    //     //             assert(ratio > 0) by {
    //     //                 C::lemma_consts_properties();
    //     //                 assert(nr_subpage_per_huge::<C>() > 0);
    //     //                 lemma_pow_positive(
    //     //                     nr_subpage_per_huge::<C>() as int,
    //     //                     (i - (self.level + 1)) as nat,
    //     //                 );
    //     //             }
    //     //             calc! {
    //     //                 (==)
    //     //                 old(self).va as nat / page_size::<C>(i) as nat; {
    //     //                     // Already proven: page_size(i) == next_pg_size * ratio
    //     //                 }
    //     //                 old(self).va as nat / (next_pg_size * ratio) as nat; {
    //     //                     lemma_div_denominator(
    //     //                         old(self).va as int,
    //     //                         next_pg_size as int,
    //     //                         ratio as int,
    //     //                     );
    //     //                 }
    //     //                 old(self).va as nat / next_pg_size / ratio as nat; {
    //     //                     // Already proven
    //     //                 }
    //     //                 self.va as nat / next_pg_size / ratio as nat; {
    //     //                     lemma_div_denominator(
    //     //                         self.va as int,
    //     //                         next_pg_size as int,
    //     //                         ratio as int,
    //     //                     );
    //     //                 }
    //     //                 self.va as nat / (next_pg_size * ratio) as nat; {
    //     //                     // Already proven: page_size(i) == next_pg_size * ratio
    //     //                 }
    //     //                 self.va as nat / page_size::<C>(i) as nat;
    //     //             }
    //     //         }

    //     //         assert forall|i: PagingLevel|
    //     //             #![trigger align_down(self.va, page_size::<C>((i + 1) as u8))]
    //     //             self.level <= i <= self.guard_level && self.va
    //     //                 < self.barrier_va.end implies path_index!(self.path[i]).unwrap().va()
    //     //             == align_down(self.va, page_size::<C>((i + 1) as u8)) by {
    //     //             lemma_page_size_spec_properties::<C>((i + 1) as u8);
    //     //             calc! {
    //     //                 (==)
    //     //                 path_index!(self.path[i]).unwrap().va() as nat; {}
    //     //                 old_path[path_index_at_level_local_spec(i)].unwrap().va() as nat; {}
    //     //                 align_down(old(self).va, page_size::<C>((i + 1) as u8)) as nat; {
    //     //                     lemma_align_down_properties(
    //     //                         old(self).va,
    //     //                         page_size::<C>((i + 1) as u8),
    //     //                     );
    //     //                 }
    //     //                 old(self).va as nat / page_size::<C>((i + 1) as u8) as nat * page_size::<C>(
    //     //                     (i + 1) as u8,
    //     //                 ) as nat; {}
    //     //                 self.va as nat / page_size::<C>((i + 1) as u8) as nat * page_size::<C>(
    //     //                     (i + 1) as u8,
    //     //                 ) as nat; {
    //     //                     lemma_align_down_properties(self.va, page_size::<C>((i + 1) as u8));
    //     //                 }
    //     //                 align_down(self.va, page_size::<C>((i + 1) as u8)) as nat;
    //     //             }
    //     //         }

    //     //         assert forall|i: u8| self.level < i <= self.guard_level implies pte_index::<C>(
    //     //             self.va,
    //     //             i,
    //     //         ) == pte_index::<C>(old(self).va, i) by {
    //     //             assert(self.level + 1 <= i);

    //     //             assert(next_pg_size > 0) by {
    //     //                 lemma_page_size_spec_properties::<C>((self.level + 1) as u8);
    //     //             }
    //     //             // Ratio of page_size::<C>(i) / next_pg_size
    //     //             let ratio = pow(
    //     //                 nr_subpage_per_huge::<C>() as int,
    //     //                 (i - (self.level + 1)) as nat,
    //     //             ) as nat;
    //     //             assert(page_size::<C>(i) as nat == next_pg_size * ratio) by {
    //     //                 lemma_page_size_geometric::<C>((self.level + 1) as u8, i);
    //     //             }
    //     //             assert(ratio > 0) by {
    //     //                 C::lemma_consts_properties();
    //     //                 assert(nr_subpage_per_huge::<C>() > 0);
    //     //                 lemma_pow_positive(
    //     //                     nr_subpage_per_huge::<C>() as int,
    //     //                     (i - (self.level + 1)) as nat,
    //     //                 );
    //     //             }

    //     //             calc! {
    //     //                 (==)
    //     //                 pte_index::<C>(self.va, i) as nat; {
    //     //                     lemma_pte_index_alternative_spec::<C>(self.va, i);
    //     //                 }
    //     //                 self.va as nat / page_size_spec::<C>(i) as nat % nr_subpage_per_huge::<
    //     //                     C,
    //     //                 >() as nat; {}
    //     //                 old(self).va as nat / page_size_spec::<C>(i) as nat % nr_subpage_per_huge::<
    //     //                     C,
    //     //                 >() as nat; {
    //     //                     lemma_pte_index_alternative_spec::<C>(old(self).va, i);
    //     //                 }
    //     //                 pte_index::<C>(old(self).va, i) as nat;
    //     //             }
    //     //         }
    //     //         assert(self.wf_local(spt));
    //     //     }
    //     // }

    //     unimplemented!()
    // }

    pub fn virt_addr(&self) -> Vaddr 
        returns self.va,
    {
        self.va
    }

    /// Goes up a level.
    // #[verifier::external_body]
    // fn pop_level(&mut self, Tracked(spt): Tracked<&SubPageTable<C>>)
    //     requires
    //         old(self).wf_local(spt),
    //         old(self).level < old(self).guard_level,
    //     ensures
    //         self.wf_local(spt),
    //         self.level == old(self).level + 1,
    //         // Other fields remain unchanged.
    //         self.constant_fields_unchanged(old(self), spt, spt),
    //         self.va == old(self).va,
    //         forall|i: PagingLevel|
    //             #![trigger self.path[path_index_at_level_local_spec(i)]]
    //             self.level <= i <= self.guard_level ==> {
    //                 path_index!(self.path[i]) == path_index!(old(self).path[i])
    //             },
    // {
    //     // proof {
    //     //     let taken = &path_index!(self.path[self.level]);
    //     //     // self.path[path_index_at_level(self.level)].take() // Verus does not support this currently
    //     //     assert(taken == path_index!(self.path[self.level]));
    //     //     assert(taken.is_some());
    //     // }
    //     // self.path[path_index_at_level(self.level)] = None;

    //     // self.level = self.level + 1;

    //     unimplemented!()
    // }

    /// Goes down a level to a child page table.
    // #[verifier::external_body]
    // fn push_level(
    //     &mut self,
    //     child_pt: PageTableGuard<'a, C>,
    //     Tracked(spt): Tracked<&SubPageTable<C>>,
    // )
    //     requires
    //         old(self).wf_local(spt),
    //         old(self).level > 1,
    //         child_pt.wf_local(&spt.alloc_model),
    //         child_pt.level_local_spec(&spt.alloc_model) == old(self).level - 1,
    //         spt.frames.value().contains_key(child_pt.paddr_local() as int),
    //         old(self).ancestors_match_path(spt, child_pt),
    //         old(self).va < old(self).barrier_va.end,
    //         // The guard is to be inserted at level `old(self).level - 1`, so its
    //         // virtual address should be aligned to page_size(old(self).level).
    //         child_pt.va() == align_down(old(self).va, page_size::<C>(old(self).level)),
    //     ensures
    //         self.wf_local(spt),
    //         self.constant_fields_unchanged(old(self), spt, spt),
    //         self.level == old(self).level - 1,
    //         path_index!(self.path[self.level]) == Some(child_pt),
    //         // Other fields remain unchanged.
    //         self.va == old(self).va,
    //         // Path remains unchanged except the one being set
    //         forall|i: PagingLevel|
    //             #![auto]
    //             old(self).level <= i <= old(self).guard_level ==> {
    //                 #[trigger] path_index!(self.path[i]) == path_index!(old(self).path[i])
    //             },
    // {
    //     // self.level = self.level - 1;

    //     // self.path[path_index_at_level(self.level)] = Some(child_pt);

    //     unimplemented!()
    // }

    // Note that mut types are not supported in Verus.
    // fn cur_entry(&mut self) -> Entry<'_, C> {
    fn cur_entry(&self) -> (res: Entry<C>)
        requires
            self.wf(),
            self.g_level@ == self.level,
            self.va < self.barrier_va.end,
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
// pub struct CursorMut<'a, C: PageTableConfig>(pub Cursor<'a, C>);

// impl<'a, C: PageTableConfig> CursorMut<'a, C> {
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
//     #[verifier::spinoff_prover]
//     #[verifier::external_body]
//     pub fn map(
//         &mut self,
//         item: C::Item,
//         Tracked(spt): Tracked<&mut SubPageTable<C>>,
//         forgot_guards: Tracked<SubTreeForgotGuard<C>>,
//     ) -> (res: (PageTableItem<C>, Tracked<SubTreeForgotGuard<C>>))
//         requires
//             old(spt).wf(),
//             old(self).0.wf_local(old(spt)),
//             old(self).0.va % page_size::<C>(1) == 0,
//             1 <= C::item_into_raw_spec(item).1 <= old(self).0.guard_level,
//             old(self).0.va + page_size::<C>(C::item_into_raw_spec(item).1) <= old(
//                 self,
//             ).0.barrier_va.end,
//         ensures
//             spt.wf(),
//             self.0.wf_local(spt),
//             self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
//             self.0.va > old(self).0.va,
//             // The map succeeds.
//             exists|pte_pa: Paddr|
//                 {
//                     &&& #[trigger] spt.ptes.value().contains_key(
//                         pte_pa as int,
//                     )
//                     // &&& #[trigger] spt.ptes.value()[pte_pa as int].map_va == old(self).0.va
//                     &&& #[trigger] spt.ptes.value()[pte_pa as int].map_to_pa
//                         == C::item_into_raw_spec(item).0
//                 },
//     {
//         // let tracked mut forgot_guards = forgot_guards.get();

//         // let preempt_guard = self.0.preempt_guard;

//         // let (pa, level, prop) = C::item_into_raw(item);
//         // assert(1 <= level <= self.0.guard_level);

//         // let end = self.0.va + page_size::<C>(level);

//         // #[verifier::loop_isolation(false)]
//         // // Go up if not applicable.
//         // while self.0.level < level
//         //     invariant
//         //         spt.wf(),
//         //         self.0.wf_local(spt),
//         //         self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
//         //         // VA should be unchanged in the loop.
//         //         self.0.va == old(self).0.va,
//         //     decreases level - self.0.level,
//         // {
//         //     self.0.pop_level(Tracked(spt));
//         // }

//         // assert(self.0.level >= level);

//         // // Go down if not applicable.
//         // while self.0.level != level
//         //     invariant
//         //         spt.wf(),
//         //         self.0.wf_local(spt),
//         //         self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
//         //         // VA should be unchanged in the loop.
//         //         self.0.va == old(self).0.va,
//         //         self.0.level >= level >= 1,
//         //         self.0.va < self.0.barrier_va.end,
//         //     decreases self.0.level,
//         // {
//         //     let cur_level = self.0.level;
//         //     let ghost cur_va = self.0.va;
//         //     let mut cur_entry = self.0.cur_entry(Tracked(spt));
//         //     match cur_entry.to_ref_local(Tracked(spt)) {
//         //         ChildRefLocal::PageTable(pt) => {
//         //             assert(spt.i_ptes.value().contains_key(cur_entry.pte.pte_paddr() as int));
//         //             assert(cur_level == cur_entry.node.level_local_spec(&spt.alloc_model));
//         //             assert(cur_level - 1 == pt.level_local_spec(&spt.alloc_model));
//         //             let ghost nid = pt.nid@;
//         //             let ghost spin_lock = forgot_guards.get_lock(nid);
//         //             assert(forgot_guards.wf()) by {
//         //                 admit();
//         //             };
//         //             assert(NodeHelper::valid_nid(nid)) by {
//         //                 admit();
//         //             };
//         //             assert(forgot_guards.is_sub_root_and_contained(nid)) by {
//         //                 admit();
//         //             };
//         //             let tracked forgot_guard = forgot_guards.tracked_take(nid);
//         //             assert(pt.wf()) by {
//         //                 admit();
//         //             };
//         //             assert(pt.deref().meta_spec().lock =~= spin_lock) by {
//         //                 admit();
//         //             };
//         //             let child_pt = pt.make_guard_unchecked(
//         //                 preempt_guard,
//         //                 Tracked(forgot_guard),
//         //                 Ghost(spin_lock),
//         //             );
//         //             assert(child_pt.va() == align_down(cur_va, page_size::<C>(cur_level))) by {
//         //                 admit();
//         //             };
//         //             assert(self.0.ancestors_match_path(spt, child_pt));
//         //             self.0.push_level(child_pt, Tracked(spt));
//         //         },
//         //         ChildRefLocal::None => {
//         //             assert(!spt.ptes.value().contains_key(cur_entry.pte.pte_paddr() as int));
//         //             assert(cur_entry.node.level_local_spec(&spt.alloc_model) == cur_level);
//         //             let ghost old_alloc_model = spt.alloc_model;
//         //             let res = cur_entry.alloc_if_none_local(
//         //                 preempt_guard,
//         //                 Tracked(spt),
//         //                 Tracked(forgot_guards),
//         //             );
//         //             let child_pt = res.0.unwrap();
//         //             proof {
//         //                 forgot_guards = res.1.get();
//         //             }

//         //             assert(self.0.wf_local(spt)) by {
//         //                 assert forall|i: PagingLevel|
//         //                     #![trigger self.0.path[path_index_at_level_local_spec(i)]]
//         //                     self.0.level <= i <= self.0.guard_level implies {
//         //                     let guard = path_index!(self.0.path[i]).unwrap();
//         //                     guard.wf_local(&spt.alloc_model)
//         //                 } by {
//         //                     // From self.wf() before calling alloc_if_none
//         //                     assert(forall|i: PagingLevel|
//         //                         #![trigger self.0.path[path_index_at_level_local_spec(i)]]
//         //                         self.0.level <= i <= self.0.guard_level ==> {
//         //                             let guard_option = path_index!(self.0.path[i]);
//         //                             &&& guard_option.unwrap().wf_local(&old_alloc_model)
//         //                         });
//         //                     // From post condition of alloc_if_none's alloc_model_do_not_change_except_add_frame
//         //                     assert(forall|i: int| #[trigger]
//         //                         old_alloc_model.meta_map.contains_key(i) ==> {
//         //                             &&& spt.alloc_model.meta_map.contains_key(i)
//         //                             &&& spt.alloc_model.meta_map[i].pptr()
//         //                                 == old_alloc_model.meta_map[i].pptr()
//         //                             &&& spt.alloc_model.meta_map[i].value()
//         //                                 == old_alloc_model.meta_map[i].value()
//         //                         });
//         //                     let guard = path_index!(self.0.path[i]).unwrap();
//         //                     assert(level_is_in_range::<C>(
//         //                         guard.level_local_spec(&old_alloc_model) as int,
//         //                     ));
//         //                     assert(old_alloc_model.meta_map.contains_key(
//         //                         guard.paddr_local() as int,
//         //                     ));
//         //                     assert(spt.alloc_model.meta_map.contains_key(
//         //                         guard.paddr_local() as int,
//         //                     ));
//         //                     assert(guard.inner.meta_local_spec(&old_alloc_model)
//         //                         == guard.inner.meta_local_spec(&spt.alloc_model));
//         //                     assert(guard.level_local_spec(&old_alloc_model)
//         //                         == guard.level_local_spec(&spt.alloc_model));
//         //                 }
//         //             }
//         //             assert(child_pt.va() == align_down(self.0.va, page_size::<C>(self.0.level)))
//         //                 by {
//         //                 calc! {
//         //                     (==)
//         //                     child_pt.va(); {}
//         //                     cur_entry.va@; {}
//         //                     align_down(self.0.va, page_size::<C>(self.0.level));
//         //                 }
//         //             }
//         //             self.0.push_level(child_pt, Tracked(spt));
//         //         },
//         //         ChildRefLocal::Frame(_, _, _) => {
//         //             assume(false);  // FIXME: implement split if huge page
//         //         },
//         //     }
//         //     continue ;
//         // }
//         // assert(self.0.level == level);

//         // let mut cur_entry = self.0.cur_entry(Tracked(spt));

//         // let old_entry = cur_entry.replace_local(ChildLocal::Frame(pa, level, prop), Tracked(spt));

//         // assert(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);
//         // assert(self.0.path_wf(spt));

//         // let old_va = self.0.va;
//         // let old_len = page_size::<C>(self.0.level);

//         // self.0.move_forward(Tracked(spt));

//         // let res = match old_entry {
//         //     ChildLocal::Frame(pa, level, prop) => PageTableItem::Mapped {
//         //         va: old_va,
//         //         page: pa,
//         //         prop: prop,
//         //     },
//         //     ChildLocal::None => PageTableItem::NotMapped { va: old_va, len: old_len },
//         //     ChildLocal::PageTable(pt) => PageTableItem::StrayPageTable {
//         //         pt,
//         //         va: old_va,
//         //         len: old_len,
//         //     },
//         // };
//         // (res, Tracked(forgot_guards))

//         unimplemented!()
//     }

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
//     #[verifier::spinoff_prover]
//     #[verifier::external_body]
//     pub unsafe fn take_next(
//         &mut self,
//         len: usize,
//         Tracked(spt): Tracked<&mut SubPageTable<C>>,
//         forgot_guards: Tracked<SubTreeForgotGuard<C>>,
//     ) -> (res: PageTableItem<C>)
//         requires
//             old(spt).wf(),
//             old(self).0.wf_local(old(spt)),
//             old(self).0.va as int + len as int <= old(self).0.barrier_va.end as int,
//             len % page_size::<C>(1) == 0,
//             len > page_size::<C>(old(self).0.level),
//         ensures
//             spt.wf(),
//             self.0.wf_local(spt),
//             self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
//     {
//         // let tracked forgot_guards = forgot_guards.get();

//         // let preempt_guard = self.0.preempt_guard;

//         // let start = self.0.va;
//         // assert(len % page_size::<C>(1) == 0);
//         // let end = start + len;
//         // assert(end <= self.0.barrier_va.end);

//         // while self.0.va < end && self.0.level > 1
//         //     invariant
//         //         spt.wf(),
//         //         self.0.wf_local(spt),
//         //         self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
//         //         self.0.va + page_size::<C>(self.0.level) < end,
//         //         self.0.va + len < MAX_USERSPACE_VADDR,
//         //         end <= self.0.barrier_va.end,
//         //     decreases
//         //             end - self.0.va,
//         //             // for push_level, only level decreases
//         //             self.0.level,
//         // {
//         //     let cur_va = self.0.va;
//         //     let cur_level = self.0.level;
//         //     let mut cur_entry = self.0.cur_entry(Tracked(spt));

//         //     // Skip if it is already absent.
//         //     if cur_entry.is_none_local(Tracked(spt)) {
//         //         if self.0.va + page_size::<C>(self.0.level) > end {
//         //             self.0.va = end;
//         //             break ;
//         //         }
//         //         assert(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);
//         //         self.0.move_forward(Tracked(spt));
//         //         assert(self.0.path_wf(spt));

//         //         assume(self.0.va + page_size::<C>(self.0.level) < end);
//         //         assume(self.0.va + len < MAX_USERSPACE_VADDR);
//         //         continue ;
//         //     }
//         //     // Go down if not applicable.

//         //     if cur_va % page_size::<C>(cur_level) != 0 || cur_va + page_size::<C>(cur_level) > end {
//         //         assert(!cur_entry.is_none_local_spec(spt));
//         //         let child = cur_entry.to_ref_local(Tracked(spt));
//         //         match child {
//         //             ChildRefLocal::PageTable(pt) => {
//         //                 let ghost nid = pt.nid@;
//         //                 let ghost spin_lock = forgot_guards.get_lock(nid);
//         //                 assert(forgot_guards.wf()) by {
//         //                     admit();
//         //                 };
//         //                 assert(NodeHelper::valid_nid(nid)) by {
//         //                     admit();
//         //                 };
//         //                 assert(forgot_guards.is_sub_root_and_contained(nid)) by {
//         //                     admit();
//         //                 };
//         //                 let tracked forgot_guard = forgot_guards.tracked_take(nid);
//         //                 assert(pt.wf()) by {
//         //                     admit();
//         //                 };
//         //                 assert(pt.deref().meta_spec().lock =~= spin_lock) by {
//         //                     admit();
//         //                 };
//         //                 let pt = pt.make_guard_unchecked(
//         //                     preempt_guard,
//         //                     Tracked(forgot_guard),
//         //                     Ghost(spin_lock),
//         //                 );
//         //                 assert(pt.va() == align_down(cur_va, page_size::<C>(cur_level))) by {
//         //                     admit();
//         //                 };
//         //                 // If there's no mapped PTEs in the next level, we can
//         //                 // skip to save time.
//         //                 if pt.nr_children() != 0 {
//         //                     self.0.push_level(pt, Tracked(spt));
//         //                 } else {
//         //                     let _ = pt.into_raw_paddr();
//         //                     if self.0.va + page_size::<C>(self.0.level) > end {
//         //                         self.0.va = end;
//         //                         break ;
//         //                     }
//         //                     assert(self.0.va + page_size::<C>(self.0.level)
//         //                         <= self.0.barrier_va.end);
//         //                     self.0.move_forward(Tracked(spt));
//         //                 }
//         //             },
//         //             ChildRefLocal::None => {
//         //                 // unreachable!("Already checked");
//         //                 assert(false);
//         //             },
//         //             ChildRefLocal::Frame(_, _, _) => {
//         //                 // panic!("Removing part of a huge page");
//         //                 assume(false);  // FIXME: implement split if huge page
//         //             },
//         //         }

//         //         assume(self.0.va + page_size::<C>(self.0.level) < end);
//         //         assume(self.0.va + len < MAX_USERSPACE_VADDR);
//         //         continue ;
//         //     }
//         //     // Unmap the current page and return it.

//         //     assert(!cur_entry.is_none_local_spec(spt));
//         //     let old_pte_paddr = cur_entry.pte.pte_paddr();
//         //     assert(old_pte_paddr == cur_entry.pte.pte_paddr());

//         //     assume(spt.i_ptes.value().contains_key(cur_entry.pte.pte_paddr() as int));
//         //     proof {
//         //         let child_frame_addr = spt.i_ptes.value()[index_pte_paddr(
//         //             cur_entry.node.paddr_local() as int,
//         //             cur_entry.idx as int,
//         //         ) as int].map_to_pa;
//         //         let child_frame_level = spt.frames.value()[child_frame_addr].level as int;
//         //         // TODO: enhance path_wf or spt_wf
//         //         assume(forall|i: int| #[trigger]
//         //             self.0.path[i].is_some() ==> #[trigger] self.0.path[i].unwrap().paddr_local()
//         //                 != child_frame_addr);
//         //     }
//         //     // TODO: prove the last level entry...
//         //     let old = cur_entry.replace_with_none_local(ChildLocal::None, Tracked(spt));

//         //     // the post condition
//         //     assert(!spt.i_ptes.value().contains_key(old_pte_paddr as int));

//         //     let item = match old {
//         //         ChildLocal::Frame(page, level, prop) => PageTableItem::Mapped {
//         //             va: self.0.va,
//         //             page,
//         //             prop,
//         //         },
//         //         ChildLocal::PageTable(pt) => {
//         //             // SAFETY: We must have locked this node.
//         //             let ghost nid = pt.deref().nid@;
//         //             let ghost spin_lock = forgot_guards.get_lock(nid);
//         //             let tracked forgot_guard = forgot_guards.tracked_take(nid);
//         //             let locked_pt = pt.deref().borrow(
//         //                 Tracked(&spt.alloc_model),
//         //             ).make_guard_unchecked(preempt_guard, Tracked(forgot_guard), Ghost(spin_lock));
//         //             assert(locked_pt.va() == align_down(self.0.va, page_size::<C>(self.0.level)))
//         //                 by {
//         //                 admit();
//         //             };
//         //             // assert!(
//         //             //     !(TypeId::of::<M>() == TypeId::of::<KernelMode>()
//         //             //         && self.0.level == C::NR_LEVELS()),
//         //             //     "Unmapping shared kernel page table nodes"
//         //             // ); // TODO
//         //             // SAFETY:
//         //             //  - We checked that we are not unmapping shared kernel page table nodes.
//         //             //  - We must have locked the entire sub-tree since the range is locked.
//         //             // let unlocked_pt = locking::dfs_mark_astray(locked_pt);
//         //             // See `locking.rs` for why we need this. // TODO
//         //             // let drop_after_grace = unlocked_pt.clone();
//         //             // crate::sync::after_grace_period(|| {
//         //             //     drop(drop_after_grace);
//         //             // });
//         //             PageTableItem::StrayPageTable {
//         //                 pt,
//         //                 va: self.0.va,
//         //                 len: page_size::<C>(self.0.level),
//         //             }
//         //         },
//         //         ChildLocal::None => { PageTableItem::NotMapped { va: 0, len: 0 } },
//         //     };

//         //     assume(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);  // TODO
//         //     assert(self.0.path_wf(spt)) by {
//         //         admit();
//         //     };
//         //     self.0.move_forward(Tracked(spt));

//         //     return item;
//         // }

//         // // If the loop exits, we did not find any mapped pages in the range.
//         // PageTableItem::NotMapped { va: start, len }

//         unimplemented!()
//     }
// }

pub fn no_op() {}

} // verus!
