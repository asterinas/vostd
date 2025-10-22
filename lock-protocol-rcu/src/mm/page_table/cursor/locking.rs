use core::mem::ManuallyDrop;
use core::ops::Deref;
use std::ops::Range;

use vstd::prelude::*;

use vstd_extra::ghost_tree::Node;
use vstd_extra::manually_drop::*;

use crate::mm::frame::meta::*;
use crate::mm::page_table::{
    PageTable, PageTableConfig, PageTableEntryTrait, Paddr, Vaddr, PagingLevel, pte_index,
};
use crate::mm::page_table::cursor::MAX_NR_LEVELS;
use crate::mm::page_table::node::{
    PageTableNode, PageTableNodeRef, PageTableGuard,
    child::{Child, ChildRef},
    entry::Entry,
    stray::{StrayFlag, StrayPerm},
};
use crate::mm::page_table::pte::Pte;
use crate::sync::rcu::rcu_load_pte;
use crate::sync::spinlock::{PageTablePageSpinLock, SpinGuard};
use crate::sync::spinlock::guard_forget::SubTreeForgotGuard;
use crate::task::DisabledPreemptGuard;
use crate::x86_64::kspace::paddr_to_vaddr;

use crate::configs::{PTE_NUM, GLOBAL_CPU_NUM};
use crate::spec::{
    lock_protocol::LockProtocolModel,
    common::{
        NodeId, valid_va_range, vaddr_is_aligned, va_level_to_trace, va_level_to_offset,
        lemma_va_level_to_trace_valid,
    },
    utils::{NodeHelper, group_node_helper_lemmas},
    rcu::{SpecInstance, NodeToken, PteArrayToken, FreePaddrToken},
    rcu::{PteArrayState},
};

use super::{Cursor, va_range_wf};

verus! {


} // verus!
verus! {

#[verifier::exec_allows_no_decreases_clause]
pub(super) fn lock_range<'rcu, C: PageTableConfig>(
    pt: &'rcu PageTable<C>,
    guard: &'rcu DisabledPreemptGuard,
    va: &Range<Vaddr>,
    m: Tracked<LockProtocolModel>,
) -> (res: (Cursor<'rcu, C>, Tracked<LockProtocolModel>, Tracked<SubTreeForgotGuard<C>>))
    requires
        pt.wf(),
        va_range_wf(*va),
        m@.inv(),
        m@.inst_id() == pt.inst@.id(),
        m@.state() is Void,
    ensures
        res.0.wf(),
        res.0.wf_with_forgot_guards(res.2@),
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
    let mut subtree_root_opt: Option<PageTableGuard<'rcu, C>> = None;
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
            subtree_root_opt->Some_0.guard->Some_0.stray_perm().value() == false,
            subtree_root_opt->Some_0.guard->Some_0.in_protocol() == true,
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
    let tracked forgot_guards;
    proof {
        m = res.0.get();
        forgot_guards = res.1.get();
        let tracked res = pt.inst.borrow().protocol_lock_end(m.cpu, m.token);
        m.token = res;
    }

    let mut path: [Option<PageTableGuard<'rcu, C>>; MAX_NR_LEVELS] = [None, None, None, None];
    path[guard_level as usize - 1] = Some(subtree_root);

    let result = Cursor::<'rcu> {
        path,
        preempt_guard: guard,
        level: guard_level,
        guard_level,
        va: va.start,
        barrier_va: va.start..va.end,
        inst: Tracked(pt.inst.borrow().clone()),
        g_level: Ghost(guard_level),
    };
    assert(result.wf_with_forgot_guards(forgot_guards)) by { admit(); };

    (result, Tracked(m), Tracked(forgot_guards))
}

pub fn unlock_range<C: PageTableConfig>(
    cursor: &mut Cursor<'_, C>,
    m: Tracked<LockProtocolModel>,
    forgot_guards: Tracked<SubTreeForgotGuard<C>>,
) -> (res: Tracked<LockProtocolModel>)
    requires
        old(cursor).wf(),
        old(cursor).g_level@ == old(cursor).level,
        m@.inv(),
        m@.inst_id() == old(cursor).inst@.id(),
        m@.state() is Locked,
        m@.sub_tree_rt() == old(cursor).get_guard_level_unwrap(old(cursor).guard_level).nid(),
        old(cursor).wf_with_forgot_guards(forgot_guards@),
        forgot_guards@.wf(),
        forgot_guards@.is_root(old(cursor).get_guard_level_unwrap(old(cursor).guard_level).nid()),
    ensures
        cursor.path.len() == old(cursor).path.len(),
        forall|i| 0 <= i < cursor.path.len() ==> cursor.path[i] is None,
        res@.inv(),
        res@.inst_id() == old(cursor).inst@.id(),
        res@.state() is Void,
{
    broadcast use group_node_helper_lemmas;

    let tracked mut m = m.get();
    proof {
        let tracked res = cursor.inst.borrow().protocol_unlock_start(m.cpu, m.token);
        m.token = res;
    }

    let tracked mut forgot_guards = forgot_guards.get();

    let mut i = cursor.level - 1;
    while i < cursor.guard_level - 1
        invariant
            cursor.level - 1 <= i <= cursor.guard_level - 1,
            cursor.wf(),
            cursor.g_level@ == i + 1,
            m.inst_id() == cursor.inst@.id(),
            m.sub_tree_rt() == cursor.path[cursor.guard_level - 1]->Some_0.nid(),
            cursor.level == old(cursor).level,
            cursor.guard_level == old(cursor).guard_level,
            forall|level: PagingLevel|
                #![trigger cursor.path[level - 1]]
                i + 1 <= level <= 4 ==> cursor.path[level - 1] =~= old(cursor).path[level - 1],
            forall|level: PagingLevel|
                #![trigger cursor.get_guard_level(level)]
                1 <= level < i + 1 ==> cursor.get_guard_level(level) is None,
            cursor.inst =~= old(cursor).inst,
            cursor.wf_with_forgot_guards(forgot_guards),
            forgot_guards.wf(),
            forgot_guards.is_root(old(cursor).get_guard_level_unwrap(old(cursor).guard_level).nid()),
        decreases 4 - i,
    {
        assert(cursor.path[i as int] is Some) by {
            let level = (i + 1) as PagingLevel;
            assert(cursor.get_guard_level(level) is Some);
        };
        let ghost _cursor = *cursor;
        let ghost _forgot_guards = forgot_guards;
        if let Some(mut guard) = cursor.take(i as usize) {
            let ghost nid = guard.nid();
            let ghost spin_lock = guard.deref().deref().meta_spec().lock;
            let tracked _guard = guard.guard.tracked_unwrap();
            guard.guard = None;
            let tracked forgot_guard = _guard.inner.get();
            proof {
                assert(forgot_guards.is_sub_root(nid)) by {
                    _cursor.lemma_wf_with_forgot_guards_sound(forgot_guards);
                    assert(nid == _cursor.get_guard_level_unwrap(_cursor.g_level@).nid());
                    assert(forgot_guards =~= _cursor.rec_put_guard_from_path(
                        forgot_guards,
                        (_cursor.g_level@ - 1) as PagingLevel,
                    ));
                };
                assert(forgot_guards.childs_are_contained(
                    nid,
                    forgot_guard.pte_token->Some_0.value(),
                )) by {
                    _cursor.lemma_wf_with_forgot_guards_sound(forgot_guards);
                    assert(nid == _cursor.get_guard_level_unwrap(_cursor.g_level@).nid());
                    assert(forgot_guards =~= _cursor.rec_put_guard_from_path(
                        forgot_guards,
                        (_cursor.g_level@ - 1) as PagingLevel,
                    ));
                };
                forgot_guards.tracked_put(nid, forgot_guard, spin_lock);
                let root_nid = old(cursor).path[old(cursor).guard_level - 1]->Some_0.nid();
                assert(forgot_guards.is_root(root_nid)) by {
                    assert(NodeHelper::in_subtree_range(root_nid, nid)) by {
                        _cursor.lemma_guard_in_path_relation_implies_in_subtree_range();
                    };
                };
                assert(cursor.wf_with_forgot_guards(forgot_guards)) by {
                    assert(cursor.guard_level == _cursor.guard_level);
                    let merged_forgot_guards1 = cursor.rec_put_guard_from_path(
                        forgot_guards,
                        cursor.guard_level,
                    );
                    let merged_forgot_guards2 = _cursor.rec_put_guard_from_path(
                        _forgot_guards,
                        _cursor.guard_level,
                    );
                    assert(merged_forgot_guards1 =~= merged_forgot_guards2) by {
                        admit();
                    };  // Need induction
                    assert(merged_forgot_guards1.wf());
                    assert(merged_forgot_guards1.is_root_and_contained(
                        cursor.get_guard_level_unwrap(cursor.guard_level).nid(),
                    ));
                    _cursor.lemma_guard_in_path_relation_implies_nid_diff();
                    assert forall|level: PagingLevel|
                        #![trigger cursor.path[level - 1]]
                        cursor.g_level@ <= level <= cursor.guard_level implies {
                        !forgot_guards.inner.dom().contains(cursor.get_guard_level_unwrap(level).nid())
                    } by {
                        assert(
                            cursor.get_guard_level_unwrap(level) =~= 
                            _cursor.get_guard_level_unwrap(level)
                        );
                        assert(!_forgot_guards.inner.dom().contains(
                            _cursor.get_guard_level_unwrap(level).nid(),
                        ));
                        assert(forgot_guards.inner.dom() =~= _forgot_guards.inner.dom().insert(
                            nid,
                        ));
                        assert(_cursor.guard_in_path_nid_diff(_cursor.g_level@, level));
                    }
                };
                assert(cursor.guards_in_path_relation()) by {
                    assert forall |level: PagingLevel| 
                        cursor.g_level@ < level <= cursor.guard_level
                    implies {
                        cursor.adjacent_guard_is_child(level)
                    } by {
                        assert(_cursor.adjacent_guard_is_child(level));
                    };
                };
            }
            let _ = ManuallyDrop::new(guard);
        } else {
            unreached()
        }
        i += 1;
    }
    let guard_level = cursor.guard_level;
    let guard_node = cursor.take(guard_level as usize - 1).unwrap();
    assert forall|i| 0 <= i < cursor.path@.len() implies { cursor.path[i] is None } by {
        let level = (i + 1) as PagingLevel;
        assert(cursor.get_guard_level(level) is None);
    }

    assert(!forgot_guards.inner.dom().contains(guard_node.nid()));
    let res = dfs_release_lock(
        cursor.preempt_guard,
        guard_node,
        Tracked(m),
        Tracked(forgot_guards),
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
fn try_traverse_and_lock_subtree_root<'rcu, C: PageTableConfig>(
    pt: &PageTable<C>,
    guard: &'rcu DisabledPreemptGuard,
    va: &Range<Vaddr>,
    m: Tracked<LockProtocolModel>,
) -> (res: (Option<PageTableGuard<'rcu, C>>, Tracked<LockProtocolModel>))
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
            &&& res.0->Some_0.guard->Some_0.stray_perm().value() == false
            &&& res.0->Some_0.guard->Some_0.in_protocol() == true
            &&& res.1@.inv()
            &&& res.1@.inst_id() == pt.inst@.id()
            &&& res.1@.state() is Locking
            &&& res.1@.sub_tree_rt() == res.0->Some_0.nid()
            &&& res.1@.cur_node() == res.1@.sub_tree_rt() + 1
        },
{
    broadcast use group_node_helper_lemmas;

    let tracked mut m = m.get();

    let mut cur_node_guard: Option<PageTableGuard<C>> = None;
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
                &&& cur_node_guard->Some_0.guard->Some_0.in_protocol() == false
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
                &&& cur_node_guard->Some_0.guard->Some_0.in_protocol() == false
            },
        decreases cur_level,
    {
        let start_idx = pte_index::<C>(va.start, cur_level);
        let level_too_high = {
            let end_idx = pte_index::<C>(va.end - 1, cur_level);
            cur_level > 1 && start_idx == end_idx
        };
        assert(cur_level == 1 ==> level_too_high == false);
        if !level_too_high {
            break ;
        }
        let va = paddr_to_vaddr(cur_pt_addr);
        // let ptr = (va + start_idx * 64) as *const Pte;
        let cur_pte: Pte<C> = rcu_load_pte(
            va,
            start_idx,
            Ghost(PageTableNode::from_raw_spec(cur_pt_addr)),
            Ghost(start_idx as nat),
        );

        if cur_pte.inner.is_present() {
            if cur_pte.inner.is_last(cur_level) {
                assert(cur_level == 1) by {
                    admit();
                };  // TODO: Have no idea how to handle this.
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
        let node_token = pt_guard.take_node_token();
        let tracked new_node_token;
        proof {
            let tracked new_token = pt.inst.borrow().protocol_lock_start(
                m.cpu,
                pt_guard.nid(),
                node_token.get(),
                m.token,
            );
            new_node_token = new_token.0.get();
            m.token = new_token.1.get();
        }
        pt_guard.put_node_token(Tracked(new_node_token));
        pt_guard.update_in_protocol(Tracked(true));
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
fn dfs_acquire_lock<C: PageTableConfig>(
    guard: &DisabledPreemptGuard,
    cur_node: &PageTableGuard<'_, C>,
    // cur_node_va: Vaddr,
    // va_range: Range<Vaddr>,
    m: Tracked<LockProtocolModel>,
) -> (res: (Tracked<LockProtocolModel>, Tracked<SubTreeForgotGuard<C>>))
    requires
        cur_node.wf(),
        cur_node.guard->Some_0.stray_perm().value() == false,
        cur_node.guard->Some_0.in_protocol() == true,
        m@.inv(),
        m@.inst_id() == cur_node.inst_id(),
        m@.state() is Locking,
        m@.cur_node() == cur_node.nid() + 1,
        m@.node_is_locked(cur_node.nid()),
    ensures
        res.0@.inv(),
        res.0@.inst_id() == cur_node.inst_id(),
        res.0@.state() is Locking,
        res.0@.sub_tree_rt() == m@.sub_tree_rt(),
        res.0@.cur_node() == NodeHelper::next_outside_subtree(cur_node.nid()),
        res.1@.wf(),
        !res.1@.inner.dom().contains(cur_node.nid()),
        res.1@.is_root(cur_node.nid()),
        res.1@.childs_are_contained(
            cur_node.nid(),
            cur_node.guard->Some_0.view_pte_token().value(),
        ),
    decreases cur_node.deref().deref().level_spec(),
{
    broadcast use crate::spec::utils::group_node_helper_lemmas;

    let tracked mut forgot_guards = SubTreeForgotGuard::empty();

    let cur_level = cur_node.deref().deref().level();
    if cur_level == 1 {
        assert(m@.cur_node() == NodeHelper::next_outside_subtree(cur_node.nid())) by {
            NodeHelper::lemma_tree_size_spec_table();
        }
        assert(cur_node.guard->Some_0.view_pte_token().value() =~= PteArrayState::empty()) by {
            admit();
        };
        return (m, Tracked(forgot_guards));
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

    let mut i = 0;
    while i < 512
        invariant
            0 <= i <= 512,
            cur_node.wf(),
            cur_node.guard->Some_0.stray_perm().value() == false,
            cur_node.guard->Some_0.in_protocol() == true,
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
            forgot_guards.wf(),
            !forgot_guards.inner.dom().contains(cur_node.nid()),
            forgot_guards.is_root(cur_node.nid()),
            forgot_guards.childs_are_contained_constrained(
                cur_node.nid(),
                cur_node.guard->Some_0.view_pte_token().value(),
                i as nat,
            ),
            forall|_i: nat|
                i <= _i < 512 ==> #[trigger] forgot_guards.sub_tree_not_contained(
                    NodeHelper::get_child(cur_node.nid(), _i),
                ),
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
                let tracked pa_pte_array_token =
                    cur_node.tracked_borrow_guard().tracked_borrow_pte_token();
                assert(pa_pte_array_token.value().is_alive(entry.idx as nat));
                assert(pa_pte_array_token.value().get_paddr(entry.idx as nat)
                    == cur_node.guard->Some_0.perms().inner.value()[entry.idx as int].inner.paddr());
                assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), pt.nid@)) by {
                    assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), cur_node.nid()));
                }
                let res = pt.lock(guard, Tracked(m), Tracked(pa_pte_array_token));
                let mut pt_guard = res.0;
                proof {
                    m = res.1.get();
                }
                // let child_node_va = cur_node_va + i * page_size(cur_level);
                // let child_node_va_end = child_node_va + page_size(cur_level);
                // let va_start = va_range.start.max(child_node_va);
                // let va_end = va_range.end.min(child_node_va_end);
                // dfs_acquire_lock(guard, &mut pt_guard, child_node_va, va_start..va_end);
                assert(pt_guard.guard->Some_0.stray_perm().value() == false);
                let res = dfs_acquire_lock(guard, &pt_guard, Tracked(m));
                let tracked mut sub_forgot_guards;
                proof {
                    m = res.0.get();
                    sub_forgot_guards = res.1.get();
                }
                // Forget the page table guard.
                assert(pt_guard.guard is Some);
                let ghost spin_lock = pt_guard.deref().deref().meta_spec().lock;
                let tracked guard = pt_guard.guard.tracked_unwrap();
                let tracked forgot_guard = guard.inner.get();
                proof {
                    sub_forgot_guards.tracked_put(pt.nid@, forgot_guard, spin_lock);
                }
                pt_guard.guard = None;
                let _ = ManuallyDrop::new(pt_guard);
                // Merge forgot guards.
                proof {
                    assert(forgot_guards.inner.dom().disjoint(sub_forgot_guards.inner.dom())) by {
                        let child_nid = NodeHelper::get_child(cur_node.nid(), i as nat);
                        assert(sub_forgot_guards.is_root(child_nid));
                        assert(forgot_guards.sub_tree_not_contained(child_nid));
                    };
                    assert forall|_i: nat| i < _i < 512 implies {
                        #[trigger] forgot_guards.union_spec(
                            sub_forgot_guards,
                        ).sub_tree_not_contained(NodeHelper::get_child(cur_node.nid(), _i))
                    } by {
                        let child_nid = NodeHelper::get_child(cur_node.nid(), _i as nat);
                        assert(sub_forgot_guards.is_root(
                            NodeHelper::get_child(cur_node.nid(), i as nat),
                        ));
                        assert forall|nid: NodeId| #[trigger]
                            forgot_guards.union_spec(sub_forgot_guards).inner.dom().contains(
                                nid,
                            ) implies { !NodeHelper::in_subtree_range(child_nid, nid) } by {
                            if forgot_guards.inner.dom().contains(nid) {
                                assert(forgot_guards.sub_tree_not_contained(
                                    NodeHelper::get_child(cur_node.nid(), _i),
                                ));
                            }
                        };
                    };
                    forgot_guards.tracked_union(sub_forgot_guards);
                }
            },
            ChildRef::Frame(_, _, _) => unreached(),
            ChildRef::None => {
                let tracked_inst = cur_node.tracked_pt_inst();
                let tracked inst = tracked_inst.get();
                proof {
                    let ghost nid = NodeHelper::get_child(cur_node.nid(), i as nat);
                    let tracked pte_token: &PteArrayToken =
                        cur_node.guard.tracked_borrow().tracked_borrow_pte_token();
                    assert(pte_token.value().is_void(i as nat));
                    assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), nid)) by {
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
                            NodeHelper::lemma_in_subtree_is_child_in_subtree(
                                m.sub_tree_rt(),
                                cur_node.nid(),
                                m.cur_node(),
                            );
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
                NodeHelper::lemma_is_child_nid_increasing(cur_node.nid(), m.cur_node());
            }
        } else {
            assert(m.cur_node() == NodeHelper::next_outside_subtree(cur_node.nid())) by {
                NodeHelper::lemma_last_child_next_outside_subtree(cur_node.nid());
            }
        }

        i += 1;
    }

    (Tracked(m), Tracked(forgot_guards))
}

/// Releases the locks for the given range in the sub-tree rooted at the node.
///
/// # Safety
///
/// The caller must ensure that the nodes in the specified sub-tree are locked
/// and all guards are forgotten.
#[verifier::loop_isolation(false)]
fn dfs_release_lock<'rcu, C: PageTableConfig>(
    guard: &'rcu DisabledPreemptGuard,
    mut cur_node: PageTableGuard<'rcu, C>,
    // cur_node_va: Vaddr,
    // va_range: Range<Vaddr>,
    m: Tracked<LockProtocolModel>,
    forgot_guards: Tracked<SubTreeForgotGuard<C>>,
) -> (res: Tracked<LockProtocolModel>)
    requires
        cur_node.wf(),
        cur_node.guard->Some_0.stray_perm().value() == false,
        cur_node.guard->Some_0.in_protocol() == true,
        m@.inv(),
        m@.inst_id() == cur_node.inst_id(),
        m@.state() is Locking,
        m@.cur_node() == NodeHelper::next_outside_subtree(cur_node.nid()),
        m@.node_is_locked(cur_node.nid()),
        forgot_guards@.wf(),
        forgot_guards@.is_root(cur_node.nid()),
        !forgot_guards@.inner.dom().contains(cur_node.nid()),
        forgot_guards@.childs_are_contained(
            cur_node.nid(),
            cur_node.guard->Some_0.view_pte_token().value(),
        ),
    ensures
        res@.inv(),
        res@.inst_id() == cur_node.inst_id(),
        res@.state() is Locking,
        res@.sub_tree_rt() == m@.sub_tree_rt(),
        res@.cur_node() == cur_node.nid(),
    decreases cur_node.deref().deref().level_spec(),
{
    broadcast use crate::spec::utils::group_node_helper_lemmas;

    let tracked mut forgot_guards = forgot_guards.get();

    let tracked mut m = m.get();

    let cur_level = cur_node.deref().deref().level();
    if cur_level == 1 {
        assert(m.cur_node() == cur_node.nid() + 1) by {
            NodeHelper::lemma_tree_size_spec_table();
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
            cur_node.guard->Some_0.stray_perm().value() == false,
            cur_node.guard->Some_0.in_protocol() == true,
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
            forgot_guards.wf(),
            forgot_guards.is_root(cur_node.nid()),
            !forgot_guards.inner.dom().contains(cur_node.nid()),
            forgot_guards.childs_are_contained_constrained(
                cur_node.nid(),
                cur_node.guard->Some_0.view_pte_token().value(),
                i as nat,
            ),
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
                            NodeHelper::lemma_is_child_implies_in_subtree(
                                cur_node.nid(),
                                pt.deref().nid@,
                            );
                        };
                    }
                };
                let tracked pa_pte_array_token =
                    cur_node.tracked_borrow_guard().tracked_borrow_pte_token();
                assert(pa_pte_array_token.value().is_alive(i as nat));
                let tracked mut sub_forgot_guards;
                let tracked child_guard;
                let ghost mut child_spin_lock;
                proof {
                    let child_nid = NodeHelper::get_child(cur_node.nid(), i as nat);
                    assert(forgot_guards.is_sub_root_and_contained(child_nid)) by {
                        assert(forgot_guards.inner.dom().contains(child_nid));
                        assert(forgot_guards.is_root(cur_node.nid()));
                        assert forall|_nid: NodeId| #[trigger]
                            forgot_guards.inner.dom().contains(_nid) && _nid != child_nid implies {
                            !NodeHelper::in_subtree_range(_nid, child_nid)
                        } by {
                            assert(NodeHelper::in_subtree_range(cur_node.nid(), _nid));
                            assert(_nid != cur_node.nid());
                            if NodeHelper::in_subtree_range(_nid, child_nid) {
                                assert(NodeHelper::in_subtree_range(_nid, cur_node.nid())) by {
                                    NodeHelper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range(
                                    _nid, cur_node.nid(), child_nid);
                                };
                            }
                        };
                    };
                    sub_forgot_guards = forgot_guards.tracked_take_sub_tree(child_nid);
                    child_spin_lock = sub_forgot_guards.get_lock(child_nid);
                    child_guard = sub_forgot_guards.tracked_take(child_nid);
                }
                assert(pt.deref().meta_spec().lock =~= child_spin_lock) by {
                    admit();
                };  // Should be guaranteed by 'from_raw'.
                let child_node = pt.make_guard_unchecked(
                    guard,
                    Tracked(child_guard),
                    Ghost(child_spin_lock),
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
                let res = dfs_release_lock(
                    guard,
                    child_node,
                    Tracked(m),
                    Tracked(sub_forgot_guards),
                );
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
                    let tracked pte_token: &PteArrayToken =
                        cur_node.guard.tracked_borrow().tracked_borrow_pte_token();
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
                        NodeHelper::lemma_is_child_nid_increasing(cur_node.nid(), nid);
                    };
                    assert(m.cur_node() <= NodeHelper::next_outside_subtree(m.sub_tree_rt()));
                }
            },
        }
        assert(m.node_is_locked(cur_node.nid())) by {
            assert(m.cur_node() == NodeHelper::get_child(cur_node.nid(), i as nat));
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
