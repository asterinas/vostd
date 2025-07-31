use core::mem::ManuallyDrop;
use core::ops::Deref;
use std::ops::Range;

use vstd::prelude::*;

use vstd_extra::manually_drop::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::super::{common::*, types::*, cpu::*};
use super::super::{frame::meta::*, page_table::*};
use super::super::node::{
    PageTableNode, PageTableNodeRef, PageTableGuard,
    child::{Child, ChildRef},
    entry::Entry,
    spinlock::*,
    stray::*,
};
use super::super::pte::{Pte, page_table_entry_trait::*};
use super::super::trust_rcu::*;
use super::Cursor;
use crate::mm::page_table::cursor::MAX_NR_LEVELS;

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
            NodeHelper::lemma_trace_to_nid_sound(sub_trace);
        }
    }
}

} // verus!
verus! {

#[verifier::exec_allows_no_decreases_clause]
pub(super) fn lock_range<'rcu>(
    pt: &'rcu PageTable,
    guard: &'rcu (),  // TODO
    va: &Range<Vaddr>,
    m: Tracked<LockProtocolModel>,
) -> (res: (Cursor<'rcu>, Tracked<LockProtocolModel>))
    requires
        pt.wf(),
        va_range_wf(*va),
        m@.inv(),
        m@.inst_id() == pt.inst@.id(),
        m@.state() is Void,
    ensures
        res.1@.inv(),
        res.1@.inst_id() == pt.inst@.id(),
        res.1@.state() is Locked,
{
    let tracked mut m = m.get();

    // The re-try loop of finding the sub-tree root.
    //
    // If we locked a stray node, we need to re-try. Otherwise, although
    // there are no safety concerns, the operations of a cursor on an stray
    // sub-tree will not see the current state and will not change the current
    // state, breaking serializability.
    let mut subtree_root_opt: Option<PageTableGuard<'rcu>> = None;
    loop
        invariant_except_break
            subtree_root_opt is None,
            pt.wf(),
            va_range_wf(*va),
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            m.state() is Void,
        ensures
            subtree_root_opt is Some,
            subtree_root_opt->Some_0.wf(),
            subtree_root_opt->Some_0.inst().cpu_num() == GLOBAL_CPU_NUM,
            subtree_root_opt->Some_0.inst_id() == pt.inst@.id(),
            subtree_root_opt->Some_0.guard->Some_0.stray_perm@.value() == false,
            subtree_root_opt->Some_0.guard->Some_0.in_protocol@ == true,
            // TODO
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            m.state() is Locking,
            m.sub_tree_rt() == subtree_root_opt->Some_0.nid(),
            m.cur_node() == m.sub_tree_rt() + 1,
    {
        let res = try_traverse_and_lock_subtree_root(pt, guard, va, Tracked(m));
        proof {
            m = res.1.get();
        }
        if let Some(subtree_root) = res.0 {
            subtree_root_opt = Some(subtree_root);
            break ;
        }
    };
    let subtree_root = subtree_root_opt.unwrap();

    // Once we have locked the sub-tree that is not stray, we won't read any
    // stray nodes in the following traversal since we must lock before reading.
    let guard_level = subtree_root.deref().deref().level();
    // let cur_node_va = va.start.align_down(page_size(guard_level + 1));
    // dfs_acquire_lock(guard, &mut subtree_root, cur_node_va, va.clone());
    let res = dfs_acquire_lock(guard, &subtree_root, Tracked(m));
    proof {
        m = res.get();
        let tracked res = pt.inst.borrow().protocol_lock_end(m.cpu, m.token);
        m.token = res;
    }

    let mut path: [Option<PageTableGuard<'rcu>>; MAX_NR_LEVELS] = [None, None, None, None];
    path[guard_level as usize - 1] = Some(subtree_root);

    (
        Cursor::<'rcu> {
            path,
            rcu_guard: guard,
            level: guard_level,
            guard_level,
            va: va.start,
            barrier_va: va.start..va.end,
            inst: Tracked(pt.inst.borrow().clone()),
        },
        Tracked(m),
    )
}

pub fn unlock_range(cursor: &mut Cursor<'_>, m: Tracked<LockProtocolModel>) -> (res: Tracked<
    LockProtocolModel,
>)
    requires
        old(cursor).wf(),
        m@.inv(),
        m@.inst_id() == old(cursor).inst@.id(),
        m@.state() is Locked,
        m@.sub_tree_rt() == old(cursor).path[old(cursor).guard_level - 1]->Some_0.nid(),
    ensures
        cursor.path.len() == old(cursor).path.len(),
        forall|i| 0 <= i < cursor.path.len() ==> cursor.path[i] is None,
        res@.inv(),
        res@.inst_id() == old(cursor).inst@.id(),
        res@.state() is Void,
{
    let tracked mut m = m.get();
    proof {
        let tracked res = cursor.inst.borrow().protocol_unlock_start(m.cpu, m.token);
        m.token = res;
    }

    let mut i = cursor.guard_level - 1;
    while i > 0
        invariant
            0 <= i <= cursor.guard_level - 1,
            cursor.wf(),
            m.inst_id() == cursor.inst@.id(),
            m.sub_tree_rt() == cursor.path[cursor.guard_level - 1]->Some_0.nid(),
            forall|level: PagingLevel|
                #![trigger cursor.path[level - 1]]
                i < level <= cursor.guard_level - 1 ==> cursor.path[level - 1] is None,
        decreases i,
    {
        i -= 1;
        if let Some(guard) = cursor.take(i as usize) {
            let _ = ManuallyDrop::new(guard);
        }
    }
    let guard_level = cursor.guard_level;
    let guard_node = cursor.take(guard_level as usize - 1).unwrap();
    assert forall|i| 0 <= i < cursor.path@.len() implies { cursor.path[i] is None } by {
        assert(cursor.path[(i + 1) - 1] is None);
    }
    // let cur_node_va = cursor
    //     .barrier_va
    //     .start
    //     .align_down(page_size(cursor.guard_level + 1));

    assert(m.sub_tree_rt() == guard_node.nid());
    assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), guard_node.nid())) by {
        NodeHelper::lemma_tree_size_spec_table();
    };
    let res = dfs_release_lock(
        cursor.rcu_guard,
        guard_node,
        // cur_node_va,
        // cursor.barrier_va.clone(),
        Tracked(m),
    );
    proof {
        m = res.get();
        let tracked res = cursor.inst.borrow().protocol_unlock_end(m.cpu, m.token);
        m.token = res;
    }

    Tracked(m)
}

/// Finds and locks an intermediate page table node that covers the range.
///
/// If that node (or any of its ancestors) does not exist, we need to lock
/// the parent and create it. After the creation the lock of the parent will
/// be released and the new node will be locked.
///
/// If this function founds that a locked node is stray (because of racing with
/// page table recycling), it will return `None`. The caller should retry in
/// this case to lock the proper node.
fn try_traverse_and_lock_subtree_root<'rcu>(
    pt: &PageTable,
    guard: &'rcu (),  // TODO
    va: &Range<Vaddr>,
    m: Tracked<LockProtocolModel>,
) -> (res: (Option<PageTableGuard<'rcu>>, Tracked<LockProtocolModel>))
    requires
        pt.wf(),
        va_range_wf(*va),
        m@.inv(),
        m@.inst_id() == pt.inst@.id(),
        m@.state() is Void,
    ensures
        res.0 is None ==> {
            &&& res.1@.inv()
            &&& res.1@.inst_id() == pt.inst@.id()
            &&& res.1@.state() is Void
        },
        res.0 is Some ==> {
            &&& res.0->Some_0.wf()
            &&& res.0->Some_0.inst().cpu_num() == GLOBAL_CPU_NUM
            &&& res.0->Some_0.inst_id() == pt.inst@.id()
            &&& res.0->Some_0.guard->Some_0.stray_perm@.value() == false
            &&& res.0->Some_0.guard->Some_0.in_protocol@ == true
            &&& res.1@.inv()
            &&& res.1@.inst_id() == pt.inst@.id()
            &&& res.1@.state() is Locking
            &&& res.1@.sub_tree_rt() == res.0->Some_0.nid()
            &&& res.1@.cur_node() == res.1@.sub_tree_rt() + 1
        },
{
    let tracked mut m = m.get();

    let mut cur_node_guard: Option<PageTableGuard> = None;
    let mut cur_pt_addr = pt.root.start_paddr();
    let ghost mut cur_nid: NodeId = NodeHelper::root_id();
    let mut cur_level: PagingLevel = MAX_NR_LEVELS as PagingLevel;
    while cur_level >= 1
        invariant_except_break
            1 <= cur_level <= MAX_NR_LEVELS,
            NodeHelper::valid_nid(cur_nid),
            cur_level == NodeHelper::nid_to_level(cur_nid),
            pt.wf(),
            va_range_wf(*va),
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            m.state() is Void,
            cur_node_guard is Some ==> {
                &&& cur_node_guard->Some_0.wf()
                &&& cur_node_guard->Some_0.inst_id() == pt.inst@.id()
                &&& cur_node_guard->Some_0.nid() == cur_nid
                &&& cur_node_guard->Some_0.inner.deref().level_spec() == cur_level
                &&& cur_node_guard->Some_0.guard->Some_0.in_protocol@ == false
            },
        ensures
            1 <= cur_level <= MAX_NR_LEVELS,
            NodeHelper::valid_nid(cur_nid),
            cur_level == NodeHelper::nid_to_level(cur_nid),
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            m.state() is Void,
            cur_node_guard is Some ==> {
                &&& cur_node_guard->Some_0.wf()
                &&& cur_node_guard->Some_0.inst_id() == pt.inst@.id()
                &&& cur_node_guard->Some_0.nid() == cur_nid
                &&& cur_node_guard->Some_0.inner.deref().level_spec() == cur_level
                &&& cur_node_guard->Some_0.guard->Some_0.in_protocol@ == false
            },
        decreases cur_level,
    {
        let start_idx = pte_index(va.start, cur_level);
        let level_too_high = {
            let end_idx = pte_index(va.end - 1, cur_level);
            cur_level > 1 && start_idx == end_idx
        };
        assert(cur_level == 1 ==> level_too_high == false);
        if !level_too_high {
            break ;
        }
        let va = paddr_to_vaddr(cur_pt_addr);
        // let ptr = (va + start_idx * 64) as *const Pte;
        let cur_pte = rcu_load_pte(
            va,
            start_idx,
            Ghost(PageTableNode::from_raw_spec(cur_pt_addr)),
            Ghost(start_idx as nat),
        );

        if cur_pte.inner.is_present() {
            if cur_pte.inner.is_last(cur_level) {
                unreached::<()>();
            }
            cur_pt_addr = cur_pte.inner.paddr();
            if cur_node_guard.is_some() {
                let mut pt_guard = cur_node_guard.take().unwrap();
                pt_guard.normal_drop();
            }
            cur_node_guard = None;
        } else {
            let cur_node_guard_inner = cur_node_guard.take();
            let mut pt_guard = if cur_node_guard_inner.is_some() {
                cur_node_guard_inner.unwrap()
            } else {
                let node_ref = PageTableNodeRef::<'rcu>::borrow_paddr(
                    cur_pt_addr,
                    Ghost(cur_nid),
                    Ghost(pt.inst@.id()),
                    Ghost(cur_level),
                );
                node_ref.normal_lock(guard)
            };
            if pt_guard.read_stray() {
                // Manually drop the guard.
                pt_guard.normal_drop();
                return (None, Tracked(m));
            }
            let mut cur_entry = pt_guard.entry(start_idx);
            if cur_entry.is_none() {
                assert(NodeHelper::is_not_leaf(pt_guard.nid())) by {
                    NodeHelper::lemma_level_dep_relation(pt_guard.nid());
                };
                let allocated_guard = cur_entry.normal_alloc_if_none(guard, &mut pt_guard).unwrap();
                cur_pt_addr = allocated_guard.deref().deref().start_paddr();
                cur_node_guard = Some(allocated_guard);
            } else if cur_entry.is_node(&pt_guard) {
                let ChildRef::PageTable(pt) = cur_entry.to_ref(&pt_guard) else { unreached() };
                cur_pt_addr = pt.start_paddr();
                cur_node_guard = None;
            } else {
                // let guard = cur_entry.split_if_mapped_huge(guard).unwrap();
                cur_pt_addr = pt_guard.deref().deref().start_paddr();
                cur_node_guard = None;
            }
            pt_guard.normal_drop();
        }

        cur_level -= 1;
        let ghost nxt_nid = NodeHelper::get_child(cur_nid, start_idx as nat);
        proof {
            NodeHelper::lemma_level_dep_relation(cur_nid);
            NodeHelper::lemma_get_child_sound(cur_nid, start_idx as nat);
            NodeHelper::lemma_is_child_level_relation(cur_nid, nxt_nid);
            cur_nid = nxt_nid;
        }
    }

    let mut pt_guard = if cur_node_guard.is_some() {
        cur_node_guard.unwrap()
    } else {
        let node_ref = PageTableNodeRef::<'rcu>::borrow_paddr(
            cur_pt_addr,
            Ghost(cur_nid),
            Ghost(pt.inst@.id()),
            Ghost(cur_level),
        );
        node_ref.normal_lock(guard)
    };
    if pt_guard.read_stray() {
        // Manually drop the guard.
        pt_guard.normal_drop();
        return (None, Tracked(m));
    } else {
        proof {
            m.token = pt.inst.borrow().protocol_lock_start(m.cpu, pt_guard.nid(), m.token);
            assert(m.state() is Locking);
        }
        assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), pt_guard.nid())) by {
            assert(m.sub_tree_rt() == pt_guard.nid());
            assert(NodeHelper::next_outside_subtree(m.sub_tree_rt()) > m.sub_tree_rt()) by {
                NodeHelper::lemma_tree_size_spec_table()
            };
        };
        let res = pt_guard.trans_lock_protocol(Tracked(m));
        proof {
            m = res.get();
        }
    }
    (Some(pt_guard), Tracked(m))
}

/// Acquires the locks for the given range in the sub-tree rooted at the node.
///
/// `cur_node_va` must be the virtual address of the `cur_node`. The `va_range`
/// must be within the range of the `cur_node`. The range must not be empty.
///
/// The function will forget all the [`PageTableGuard`] objects in the sub-tree.
#[verifier::loop_isolation(false)]
fn dfs_acquire_lock(
    guard: &(),
    cur_node: &PageTableGuard<'_>,
    // cur_node_va: Vaddr,
    // va_range: Range<Vaddr>,
    m: Tracked<LockProtocolModel>,
) -> (res: Tracked<LockProtocolModel>)
    requires
        cur_node.wf(),
        cur_node.guard->Some_0.stray_perm@.value() == false,
        cur_node.guard->Some_0.in_protocol@ == true,
        m@.inv(),
        m@.inst_id() == cur_node.inst_id(),
        m@.state() is Locking,
        m@.cur_node() == cur_node.nid() + 1,
        m@.node_is_locked(cur_node.nid()),
    ensures
        res@.inv(),
        res@.inst_id() == cur_node.inst_id(),
        res@.state() is Locking,
        res@.sub_tree_rt() == m@.sub_tree_rt(),
        res@.cur_node() == NodeHelper::next_outside_subtree(cur_node.nid()),
    decreases cur_node.deref().deref().level_spec(),
{
    let cur_level = cur_node.deref().deref().level();
    if cur_level == 1 {
        assert(m@.cur_node() == NodeHelper::next_outside_subtree(cur_node.nid())) by {
            assert(NodeHelper::nid_to_level(cur_node.nid()) == 1);
            assert(NodeHelper::next_outside_subtree(cur_node.nid()) == cur_node.nid() + 1) by {
                NodeHelper::lemma_tree_size_spec_table();
            };
        }
        return m;
    }
    let tracked mut m = m.get();
    let ghost sub_tree_rt = m.sub_tree_rt();

    assert(NodeHelper::is_not_leaf(cur_node.nid())) by {
        assert(NodeHelper::nid_to_level(cur_node.nid()) > 1);
        NodeHelper::lemma_level_dep_relation(cur_node.nid());
    }
    assert(NodeHelper::get_child(cur_node.nid(), 0) == cur_node.nid() + 1) by {
        NodeHelper::lemma_parent_child_algebraic_relation(cur_node.nid(), 0);
    };

    // let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let mut i = 0;
    while i < 512
        invariant
            0 <= i <= 512,
            cur_node.wf(),
            cur_node.guard->Some_0.stray_perm@.value() == false,
            cur_node.guard->Some_0.in_protocol@ == true,
            cur_node.deref().deref().level_spec() > 1,
            NodeHelper::is_not_leaf(cur_node.nid()),
            m.inv(),
            m.inst_id() == cur_node.inst_id(),
            m.state() is Locking,
            m.sub_tree_rt() == sub_tree_rt,
            m.cur_node() == if i < 512 {
                NodeHelper::get_child(cur_node.nid(), i as nat)
            } else {
                NodeHelper::next_outside_subtree(cur_node.nid())
            },
            m.node_is_locked(cur_node.nid()),
        decreases 512 - i,
    {
        assert(0 <= i < 512);
        let entry = cur_node.entry(i);
        let child = entry.to_ref(cur_node);
        assert(!(child is Frame)) by {
            child.axiom_no_huge_page();
        };
        match child {
            ChildRef::PageTable(pt) => {
                assert(pt.nid@ == NodeHelper::get_child(cur_node.nid(), entry.idx as nat));
                assert(cur_node.nid() == NodeHelper::get_parent(pt.nid@)) by {
                    NodeHelper::lemma_get_child_sound(cur_node.nid(), entry.idx as nat);
                };
                assert(entry.idx as nat == NodeHelper::get_offset(pt.nid@)) by {
                    NodeHelper::lemma_get_child_sound(cur_node.nid(), entry.idx as nat);
                };
                let tracked pa_pte_array_token =
                    cur_node.tracked_borrow_guard().tracked_borrow_pte_token();
                assert(pa_pte_array_token.value().is_alive(entry.idx as nat));
                assert(pa_pte_array_token.value().get_paddr(entry.idx as nat)
                    == cur_node.guard->Some_0.perms@.inner.value()[entry.idx as int].inner.paddr());
                assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), pt.nid@)) by {
                    NodeHelper::lemma_get_child_sound(cur_node.nid(), entry.idx as nat);
                    assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), cur_node.nid()));
                    NodeHelper::lemma_in_subtree_iff_in_subtree_range(
                        m.sub_tree_rt(),
                        cur_node.nid(),
                    );
                    NodeHelper::lemma_in_subtree_iff_in_subtree_range(m.sub_tree_rt(), pt.nid@);
                    NodeHelper::lemma_in_subtree_is_child_in_subtree(
                        m.sub_tree_rt(),
                        cur_node.nid(),
                        pt.nid@,
                    );
                }
                let res = pt.lock(guard, Tracked(m), Tracked(pa_pte_array_token));
                let pt_guard = res.0;
                proof {
                    m = res.1.get();
                }
                // let child_node_va = cur_node_va + i * page_size(cur_level);
                // let child_node_va_end = child_node_va + page_size(cur_level);
                // let va_start = va_range.start.max(child_node_va);
                // let va_end = va_range.end.min(child_node_va_end);
                // dfs_acquire_lock(guard, &mut pt_guard, child_node_va, va_start..va_end);
                assert(pt_guard.guard->Some_0.stray_perm@.value() == false);
                let res = dfs_acquire_lock(guard, &pt_guard, Tracked(m));
                proof {
                    m = res.get();
                }
                let _ = ManuallyDrop::new(pt_guard);

            },
            ChildRef::Frame(_, _, _) => unreached(),
            ChildRef::None => {
                let tracked_inst = cur_node.tracked_pt_inst();
                let tracked inst = tracked_inst.get();
                proof {
                    let ghost nid = NodeHelper::get_child(cur_node.nid(), i as nat);
                    NodeHelper::lemma_get_child_sound(cur_node.nid(), i as nat);
                    let tracked pte_token: &PteArrayToken =
                        cur_node.guard.tracked_borrow().pte_token.borrow().tracked_borrow();
                    assert(pte_token.value().is_void(i as nat));
                    assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), nid)) by {
                        NodeHelper::lemma_in_subtree_iff_in_subtree_range(
                            m.sub_tree_rt(),
                            cur_node.nid(),
                        );
                        NodeHelper::lemma_in_subtree_iff_in_subtree_range(m.sub_tree_rt(), nid);
                        NodeHelper::lemma_in_subtree_is_child_in_subtree(
                            m.sub_tree_rt(),
                            cur_node.nid(),
                            nid,
                        );
                    };
                    let tracked res = inst.clone().protocol_lock_skip(
                        m.cpu,
                        nid,
                        pte_token,
                        m.token,
                    );
                    m.token = res;

                    assert(m.cur_node() <= NodeHelper::next_outside_subtree(m.sub_tree_rt())) by {
                        assert(NodeHelper::in_subtree(m.sub_tree_rt(), cur_node.nid())) by {
                            assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), cur_node.nid()));
                            NodeHelper::lemma_in_subtree_iff_in_subtree_range(
                                m.sub_tree_rt(),
                                cur_node.nid(),
                            );
                        }
                        if i + 1 < 512 {
                            assert(m.cur_node() == NodeHelper::get_child(
                                cur_node.nid(),
                                (i + 1) as nat,
                            )) by {
                                assert(m.cur_node() == NodeHelper::next_outside_subtree(nid));
                                NodeHelper::lemma_brother_algebraic_relation(
                                    cur_node.nid(),
                                    i as nat,
                                );
                            };
                            NodeHelper::lemma_get_child_sound(cur_node.nid(), (i + 1) as nat);
                            NodeHelper::lemma_in_subtree_is_child_in_subtree(
                                m.sub_tree_rt(),
                                cur_node.nid(),
                                m.cur_node(),
                            );
                            assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), m.cur_node())) by {
                                assert(NodeHelper::in_subtree(m.sub_tree_rt(), m.cur_node()));
                                NodeHelper::lemma_in_subtree_iff_in_subtree_range(
                                    m.sub_tree_rt(),
                                    m.cur_node(),
                                );
                            };
                        } else {
                            assert(i + 1 == 512);
                            assert(m.cur_node() == NodeHelper::next_outside_subtree(cur_node.nid()))
                                by {
                                assert(m.cur_node() == NodeHelper::next_outside_subtree(nid));
                                NodeHelper::lemma_last_child_next_outside_subtree(cur_node.nid())
                            };
                            NodeHelper::lemma_in_subtree_bounded(m.sub_tree_rt(), cur_node.nid());
                        }
                    };
                }
            },
        }

        if i + 1 < 512 {
            assert(m.cur_node() == NodeHelper::get_child(cur_node.nid(), (i + 1) as nat)) by {
                assert(m.cur_node() == NodeHelper::next_outside_subtree(
                    NodeHelper::get_child(cur_node.nid(), i as nat),
                ));
                NodeHelper::lemma_brother_algebraic_relation(cur_node.nid(), i as nat);
            }
            assert(m.node_is_locked(cur_node.nid())) by {
                assert(m.cur_node() == NodeHelper::get_child(cur_node.nid(), (i + 1) as nat));
                NodeHelper::lemma_get_child_sound(cur_node.nid(), (i + 1) as nat);
                NodeHelper::lemma_is_child_nid_increasing(cur_node.nid(), m.cur_node());
            }
        } else {
            assert(m.cur_node() == NodeHelper::next_outside_subtree(cur_node.nid())) by {
                NodeHelper::lemma_last_child_next_outside_subtree(cur_node.nid());
            }
        }

        i += 1;
    }

    Tracked(m)
}

/// Releases the locks for the given range in the sub-tree rooted at the node.
///
/// # Safety
///
/// The caller must ensure that the nodes in the specified sub-tree are locked
/// and all guards are forgotten.
#[verifier::loop_isolation(false)]
fn dfs_release_lock<'rcu>(
    guard: &'rcu (),  // TODO
    mut cur_node: PageTableGuard<'rcu>,
    // cur_node_va: Vaddr,
    // va_range: Range<Vaddr>,
    m: Tracked<LockProtocolModel>,
) -> (res: Tracked<LockProtocolModel>)
    requires
        cur_node.wf(),
        cur_node.guard->Some_0.stray_perm@.value() == false,
        cur_node.guard->Some_0.in_protocol@ == true,
        m@.inv(),
        m@.inst_id() == cur_node.inst_id(),
        m@.state() is Locking,
        m@.cur_node() == NodeHelper::next_outside_subtree(cur_node.nid()),
        m@.node_is_locked(cur_node.nid()),
    ensures
        res@.inv(),
        res@.inst_id() == cur_node.inst_id(),
        res@.state() is Locking,
        res@.sub_tree_rt() == m@.sub_tree_rt(),
        res@.cur_node() == cur_node.nid(),
    decreases cur_node.deref().deref().level_spec(),
{
    let tracked mut m = m.get();

    let cur_level = cur_node.deref().deref().level();
    if cur_level == 1 {
        assert(m.cur_node() == cur_node.nid() + 1) by {
            assert(NodeHelper::nid_to_level(cur_node.nid()) == 1);
            assert(NodeHelper::next_outside_subtree(cur_node.nid()) == cur_node.nid() + 1) by {
                NodeHelper::lemma_tree_size_spec_table();
            };
        };

        // Manually drop the guard
        let res = cur_node.drop(Tracked(m));
        proof {
            m = res.get();
        }
        return Tracked(m);
    }
    let ghost sub_tree_rt = m.sub_tree_rt();

    assert(NodeHelper::is_not_leaf(cur_node.nid())) by {
        assert(NodeHelper::nid_to_level(cur_node.nid()) > 1);
        NodeHelper::lemma_level_dep_relation(cur_node.nid());
    }

    // let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let mut i = 512;
    while i >= 1
        invariant
            0 <= i <= 512,
            cur_node.wf(),
            cur_node.guard->Some_0.stray_perm@.value() == false,
            cur_node.guard->Some_0.in_protocol@ == true,
            m.inv(),
            m.inst_id() == cur_node.inst_id(),
            m.state() is Locking,
            m.sub_tree_rt() == sub_tree_rt,
            m.cur_node() == if i < 512 {
                NodeHelper::get_child(cur_node.nid(), i as nat)
            } else {
                NodeHelper::next_outside_subtree(cur_node.nid())
            },
            m.node_is_locked(cur_node.nid()),
        decreases i,
    {
        i -= 1;
        let entry = cur_node.entry(i);
        let child = entry.to_ref(&cur_node);
        match child {
            ChildRef::PageTable(pt) => {
                assert(m.node_is_locked(pt.deref().nid@)) by {
                    assert(pt.deref().nid@ == NodeHelper::get_child(cur_node.nid(), i as nat));
                    assert(m.sub_tree_rt() <= pt.deref().nid@) by {
                        NodeHelper::lemma_get_child_sound(cur_node.nid(), i as nat);
                        NodeHelper::lemma_is_child_nid_increasing(cur_node.nid(), pt.deref().nid@);
                    };
                    if i + 1 < 512 {
                        assert(m.cur_node() == NodeHelper::get_child(
                            cur_node.nid(),
                            (i + 1) as nat,
                        ));
                        NodeHelper::lemma_brother_nid_increasing(
                            cur_node.nid(),
                            i as nat,
                            (i + 1) as nat,
                        );
                    } else {
                        assert(m.cur_node() == NodeHelper::next_outside_subtree(cur_node.nid()));
                        assert(NodeHelper::in_subtree_range(cur_node.nid(), pt.deref().nid@)) by {
                            NodeHelper::lemma_get_child_sound(cur_node.nid(), i as nat);
                            NodeHelper::lemma_is_child_implies_in_subtree(
                                cur_node.nid(),
                                pt.deref().nid@,
                            );
                            NodeHelper::lemma_in_subtree_iff_in_subtree_range(
                                cur_node.nid(),
                                pt.deref().nid@,
                            );
                        };
                    }
                };
                assert(pt.nid@ == NodeHelper::get_child(cur_node.nid(), entry.idx as nat));
                assert(cur_node.nid() == NodeHelper::get_parent(pt.nid@)) by {
                    NodeHelper::lemma_get_child_sound(cur_node.nid(), entry.idx as nat);
                };
                assert(entry.idx as nat == NodeHelper::get_offset(pt.nid@)) by {
                    NodeHelper::lemma_get_child_sound(cur_node.nid(), entry.idx as nat);
                };
                let tracked pa_pte_array_token =
                    cur_node.tracked_borrow_guard().tracked_borrow_pte_token();
                assert(pa_pte_array_token.value().is_alive(i as nat));
                let child_node = pt.make_guard_unchecked(
                    guard,
                    Tracked(&m),
                    Tracked(pa_pte_array_token),
                );
                // let child_node_va = cur_node_va + i * page_size::<C>(cur_level);
                // let child_node_va_end = child_node_va + page_size::<C>(cur_level);
                // let va_start = va_range.start.max(child_node_va);
                // let va_end = va_range.end.min(child_node_va_end);
                // SAFETY: The caller ensures that all the nodes in the sub-tree are locked and all
                // guards are forgotten.
                // unsafe { dfs_release_lock(guard, child_node, child_node_va, va_start..va_end) };
                assert(m.cur_node() == NodeHelper::next_outside_subtree(child_node.nid())) by {
                    if i + 1 < 512 {
                        assert(m.cur_node() == NodeHelper::get_child(
                            cur_node.nid(),
                            (i + 1) as nat,
                        ));
                        NodeHelper::lemma_brother_algebraic_relation(cur_node.nid(), i as nat);
                    } else {
                        assert(m.cur_node() == NodeHelper::next_outside_subtree(cur_node.nid()));
                        NodeHelper::lemma_last_child_next_outside_subtree(cur_node.nid());
                    }
                };
                let res = dfs_release_lock(guard, child_node, Tracked(m));
                proof {
                    m = res.get();
                }
            },
            ChildRef::Frame(_, _, _) => unreached(),
            ChildRef::None => {
                let tracked_inst = cur_node.tracked_pt_inst();
                let tracked inst = tracked_inst.get();
                proof {
                    let ghost nid = NodeHelper::get_child(cur_node.nid(), i as nat);
                    NodeHelper::lemma_get_child_sound(cur_node.nid(), i as nat);
                    let tracked pte_token: &PteArrayToken =
                        cur_node.guard.tracked_borrow().pte_token.borrow().tracked_borrow();
                    assert(m.cur_node() == NodeHelper::next_outside_subtree(nid)) by {
                        if i + 1 < 512 {
                            assert(m.cur_node() == NodeHelper::get_child(
                                cur_node.nid(),
                                (i + 1) as nat,
                            ));
                            NodeHelper::lemma_brother_algebraic_relation(cur_node.nid(), i as nat);
                        } else {
                            assert(m.cur_node() == NodeHelper::next_outside_subtree(
                                cur_node.nid(),
                            ));
                            NodeHelper::lemma_last_child_next_outside_subtree(cur_node.nid());
                        }
                    };
                    assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), nid)) by {
                        NodeHelper::lemma_in_subtree_iff_in_subtree_range(
                            m.sub_tree_rt(),
                            cur_node.nid(),
                        );
                        NodeHelper::lemma_in_subtree_iff_in_subtree_range(m.sub_tree_rt(), nid);
                        NodeHelper::lemma_in_subtree_is_child_in_subtree(
                            m.sub_tree_rt(),
                            cur_node.nid(),
                            nid,
                        );
                    };
                    let tracked res = inst.clone().protocol_unlock_skip(
                        m.cpu,
                        nid,
                        pte_token,
                        m.token,
                    );
                    m.token = res;

                    assert(m.cur_node() == nid);
                    assert(m.sub_tree_rt() <= m.cur_node()) by {
                        assert(m.sub_tree_rt() <= cur_node.nid());
                        NodeHelper::lemma_get_child_sound(cur_node.nid(), i as nat);
                        NodeHelper::lemma_is_child_nid_increasing(cur_node.nid(), nid);
                    };
                    assert(m.cur_node() <= NodeHelper::next_outside_subtree(m.sub_tree_rt()));
                }
            },
        }
        assert(m.node_is_locked(cur_node.nid())) by {
            assert(m.cur_node() == NodeHelper::get_child(cur_node.nid(), i as nat));
            NodeHelper::lemma_get_child_sound(cur_node.nid(), i as nat);
            NodeHelper::lemma_is_child_nid_increasing(cur_node.nid(), m.cur_node());
        }
    }

    // Manually drop the guard
    assert(m.cur_node() == cur_node.nid() + 1) by {
        assert(m.cur_node() == NodeHelper::get_child(cur_node.nid(), 0));
        assert(NodeHelper::get_child(cur_node.nid(), 0) == cur_node.nid() + 1) by {
            NodeHelper::lemma_parent_child_algebraic_relation(cur_node.nid(), 0);
        };
    }
    let res = cur_node.drop(Tracked(m));
    proof {
        m = res.get();
    }

    Tracked(m)
}

} // verus!
