use std::mem::ManuallyDrop;
use core::ops::Deref;
use std::ops::Range;

use vstd::invariant;
use vstd::prelude::*;
use vstd::atomic_with_ghost;
use vstd::bits::*;
use vstd::rwlock::{ReadHandle, WriteHandle};
use vstd::vpanic;
use vstd::pervasive::allow_panic;
use vstd::pervasive::unreached;

use vstd_extra::manually_drop::*;

use crate::spec::{common::*, utils::*, rw::*};
use crate::task::guard;
use super::{GuardInPath, Cursor};
use super::va_range::*;
use super::super::{common::*, types::*, cpu::*, frame::*, page_table::*};
use super::super::node::*;
use super::super::node::child::{Child, ChildRef};
use super::super::node::entry::Entry;
use super::super::node::rwlock::*;
use crate::mm::page_table::cursor::MAX_NR_LEVELS;

verus! {

// TODO: Notice that we don't support huge pages yet.
#[verifier::exec_allows_no_decreases_clause]
pub fn lock_range<'a>(
    pt: &'a PageTable,
    guard: &'a (),
    va: &Range<Vaddr>,
    m: Tracked<LockProtocolModel>,
) -> (res: (Cursor<'a>, Tracked<LockProtocolModel>))
    requires
        pt.wf(),
        va_range_wf(*va),
        m@.inv(),
        m@.inst_id() == pt.inst@.id(),
        m@.state() is Void,
    ensures
        res.0.wf(),
        res.0.wf_init(*va),
        res.0.inst@.id() == pt.inst@.id(),
        res.1@.inv(),
        res.1@.inst_id() == pt.inst@.id(),
        res.1@.state() is WriteLocked,
        res.1@.path() =~= va_range_get_tree_path(*va),
        res.0.wf_with_lock_protocol_model(res.1@),
{
    let mut path: [GuardInPath; MAX_NR_LEVELS] = [
        GuardInPath::Unlocked,
        GuardInPath::Unlocked,
        GuardInPath::Unlocked,
        GuardInPath::Unlocked,
    ];

    let ghost mut cur_nid: NodeId = 0;
    assert(NodeHelper::valid_nid(cur_nid)) by {
        NodeHelper::lemma_root_id();
    };

    let mut cur_pt = pt.root.borrow();

    let tracked mut m = m.get();
    proof {
        m.token = pt.inst.borrow().locking_start(m.cpu, m.token);
        assert(m.state() is ReadLocking);
    }
    proof {
        assert(cur_nid == va_level_to_nid(va.start, cur_pt.deref().level_spec())) by {
            reveal(NodeHelper::trace_to_nid_rec);
        };
        lemma_va_range_get_guard_level(*va);
        lemma_va_range_get_tree_path(*va);
    }
    let mut cur_wlock_opt: Option<PageTableWriteLock> = None;
    while cur_pt.deref().level() > 1
        invariant_except_break
            cur_wlock_opt is None,
            pt.wf(),
            va_range_wf(*va),
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            m.state() is ReadLocking,
            m.path().len() > 0 ==> NodeHelper::is_child(m.cur_node(), cur_nid),
            m.path() =~= Seq::new(
                (4 - cur_pt.deref().level_spec()) as nat,
                |i| va_level_to_nid(va.start, (4 - i) as PagingLevel),
            ),
            cur_pt.wf(),
            cur_pt.deref().inst@.id() == pt.inst@.id(),
            cur_nid == cur_pt.deref().nid@,
            cur_nid == va_level_to_nid(va.start, cur_pt.deref().level_spec()),
            cur_pt.deref().level_spec() >= va_range_get_guard_level(*va),
            forall|l: PagingLevel|
                cur_pt.deref().level_spec() < l <= 4 ==> {
                    #[trigger] va_level_to_offset(va.start, l) == va_level_to_offset(
                        (va.end - 1) as usize,
                        l,
                    )
                },
            1 <= va_range_get_guard_level(*va) <= 4,
            forall|i: int|
                #![trigger path@[i - 1]]
                cur_pt.deref().level_spec() < i <= 4 ==> {
                    &&& path@[i - 1] is Read
                    &&& path@[i - 1]->Read_0.wf()
                    &&& path@[i - 1]->Read_0.inst_id() == pt.inst@.id()
                    &&& m.path()[4 - i] == path@[i - 1]->Read_0.nid()
                },
            forall|i: int|
                #![trigger path@[i - 1]]
                1 <= i <= cur_pt.deref().level_spec() ==> path@[i - 1] is Unlocked,
        ensures
            cur_wlock_opt is None,
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            m.path().len() == 4 - cur_pt.deref().level_spec(),
            m.state() is ReadLocking,
            m.path().len() > 0 ==> NodeHelper::is_child(m.cur_node(), cur_nid),
            m.path() == Seq::new(
                (4 - cur_pt.deref().level_spec()) as nat,
                |i| va_level_to_nid(va.start, (4 - i) as PagingLevel),
            ),
            cur_pt.wf(),
            cur_pt.deref().inst@.id() == pt.inst@.id(),
            cur_nid == cur_pt.deref().nid@,
            cur_nid == va_level_to_nid(va.start, cur_pt.deref().level_spec()),
            cur_pt.deref().level_spec() == va_range_get_guard_level(*va),
            forall|i: int|
                #![trigger path@[i - 1]]
                cur_pt.deref().level_spec() < i <= 4 ==> {
                    &&& path@[i - 1] is Read
                    &&& path@[i - 1]->Read_0.wf()
                    &&& path@[i - 1]->Read_0.inst_id() == pt.inst@.id()
                    &&& m.path()[4 - i] == path@[i - 1]->Read_0.nid()
                },
            forall|i: int|
                #![trigger path@[i - 1]]
                1 <= i <= cur_pt.deref().level_spec() ==> path@[i - 1] is Unlocked,
        decreases cur_pt.deref().level_spec(),
    {
        let cur_level = cur_pt.deref().level();

        let start_idx = pte_index(va.start, cur_level);
        let level_too_high = {
            let end_idx = pte_index(va.end - 1, cur_level);
            cur_level > 1 && start_idx == end_idx
        };
        if !level_too_high {
            assert(cur_level == va_range_get_guard_level(*va)) by {
                lemma_va_range_get_guard_level_implied_by_offsets_equal(*va, cur_level);
            };
            break ;
        }
        assert(cur_level != va_range_get_guard_level(*va)) by {
            lemma_va_range_get_guard_level_implies_offsets_equal(*va);
        };

        proof {
            assert(m.path().len() == 0 ==> cur_pt.nid@ == NodeHelper::root_id()) by {
                reveal(NodeHelper::trace_to_nid_rec);
            };
        }
        let res = cur_pt.clone_ref().lock_read(guard, Tracked(m));
        let mut cur_pt_rlockguard = res.0;
        proof {
            m = res.1.get();
        }

        let entry = cur_pt_rlockguard.entry(start_idx);
        let child_ref = entry.to_ref_read(&cur_pt_rlockguard);
        assert(child_ref !is Frame) by {
            child_ref.axiom_no_huge_page();
        };
        let ghost nxt_nid = NodeHelper::get_child(cur_nid, start_idx as nat);
        proof {
            NodeHelper::lemma_nid_to_dep_le_3(cur_nid);
            NodeHelper::lemma_get_child_sound(cur_nid, start_idx as nat);
            lemma_va_level_to_nid_inc(
                va.start,
                (cur_level - 1) as PagingLevel,
                cur_nid,
                start_idx as nat,
            );
            NodeHelper::lemma_is_child_level_relation(cur_nid, nxt_nid);
        }
        match child_ref {
            ChildRef::PageTable(pt) => {
                path[cur_level as usize - 1] = GuardInPath::Read(cur_pt_rlockguard);
                cur_pt = pt;
                proof {
                    cur_nid = nxt_nid;
                }
            },
            ChildRef::Frame(_, _, _) => unreached(),
            ChildRef::None => {
                // Upgrade to write lock.
                let res = cur_pt_rlockguard.drop(Tracked(m));
                proof {
                    m = res.get();
                }
                let res = cur_pt.clone_ref().lock_write(guard, Tracked(m));
                let mut cur_pt_wlockguard = res.0;
                proof {
                    m = res.1.get();
                }

                let mut entry = cur_pt_wlockguard.entry(start_idx);
                let child_ref = entry.to_ref_write(&cur_pt_wlockguard);
                assert(!(child_ref is Frame)) by {
                    child_ref.axiom_no_huge_page();
                };
                match child_ref {
                    ChildRef::PageTable(pt) => {
                        // Downgrade to read lock.
                        let res = cur_pt_wlockguard.drop(Tracked(m));
                        proof {
                            m = res.get();
                        }
                        let res = cur_pt.clone_ref().lock_read(guard, Tracked(m));
                        let cur_pt_rlockguard = res.0;
                        proof {
                            m = res.1.get();
                        }
                        path[cur_level as usize - 1] = GuardInPath::Read(cur_pt_rlockguard);
                        cur_pt = pt;
                        proof {
                            cur_nid = nxt_nid;
                        }
                    },
                    ChildRef::Frame(_, _, _) => unreached(),
                    ChildRef::None => {
                        // We need to allocate a new page table node.
                        let wguard = entry.alloc_if_none(
                            guard,
                            &mut cur_pt_wlockguard,
                            Tracked(&m),
                        ).unwrap();
                        let nxt_pt = wguard.as_ref();
                        // This is implicitly write locked. Don't drop (unlock) it.
                        let _ = ManuallyDrop::new(wguard);
                        // Downgrade to read lock.
                        let res = cur_pt_wlockguard.drop(Tracked(m));
                        proof {
                            m = res.get();
                        }
                        let res = cur_pt.clone_ref().lock_read(guard, Tracked(m));
                        let cur_pt_rlockguard = res.0;
                        proof {
                            m = res.1.get();
                        }
                        path[cur_level as usize - 1] = GuardInPath::Read(cur_pt_rlockguard);
                        cur_pt = nxt_pt;
                        proof {
                            cur_nid = nxt_nid;
                        }
                    },
                }
            },
        }
    };

    // Get write lock of the current page table node.
    let cur_level = cur_pt.deref().level();
    assert(cur_wlock_opt is None);
    let cur_pt_wlockguard = if cur_wlock_opt.is_some() {
        cur_wlock_opt.unwrap()
    } else {
        proof {
            lemma_wf_tree_path_inc(m.path(), cur_pt.nid@);
        }
        let res = cur_pt.lock_write(guard, Tracked(m));
        proof {
            m = res.1.get();
        }
        assert(m.path().is_prefix_of(va_range_get_tree_path(*va)));
        res.0
    };
    path[cur_level as usize - 1] = GuardInPath::Write(cur_pt_wlockguard);

    let tracked inst = pt.inst.borrow().clone();
    let cursor = Cursor::<'a> {
        path,
        rcu_guard: guard,
        level: cur_level,
        guard_level: cur_level,
        va: va.start,
        barrier_va: va.start..va.end,
        inst: Tracked(inst),
        unlock_level: Ghost(cur_level),
    };

    (cursor, Tracked(m))
}

pub fn unlock_range(cursor: &mut Cursor, m: Tracked<LockProtocolModel>) -> (res: Tracked<
    LockProtocolModel,
>)
    requires
        old(cursor).wf(),
        old(cursor).wf_with_lock_protocol_model(m@),
        m@.inv(),
        m@.state() is WriteLocked,
    ensures
        cursor.wf_unlock(),
        res@.inv(),
        res@.state() is Void,
{
    let tracked mut m = m.get();

    let mut i = cursor.level;
    let ghost level = cursor.level;
    let ghost guard_level = cursor.guard_level;
    while i < cursor.guard_level
        invariant
            cursor.level <= i <= cursor.guard_level,
            m.inv(),
            m.inst_id() == cursor.inst@.id(),
            m.state() is WriteLocked,
            cursor.wf_unlocking(),
            cursor.wf_with_lock_protocol_model(m),
            cursor.unlock_level@ == i,
            cursor.level == level,
            cursor.guard_level == guard_level,
        decreases cursor.guard_level - i,
    {
        let GuardInPath::ImplicitWrite(guard) = cursor.take_guard(i as usize - 1) else { unreached()
        };
        // This is implicitly write locked. Don't drop (unlock) it.
        let _ = ManuallyDrop::new(guard);
        i += 1;
        cursor.unlock_level = Ghost(i);
    }

    let guard_level = cursor.guard_level;
    let GuardInPath::Write(mut guard_node) = cursor.take_guard(guard_level as usize - 1) else {
        unreached()
    };
    let res = guard_node.drop(Tracked(m));
    proof {
        m = res.get();
    }
    cursor.unlock_level = Ghost((cursor.unlock_level@ + 1) as PagingLevel);

    let mut i = guard_level + 1;
    while i <= 4
        invariant
            guard_level + 1 <= i <= 5,
            i == cursor.unlock_level@,
            m.inv(),
            m.state() is ReadLocking,
            cursor.wf_unlocking(),
            cursor.wf_with_lock_protocol_model(m),
            cursor.level == level,
            cursor.guard_level == guard_level,
            forall|level: int|
                #![trigger cursor.path@[level - 1] is Read]
                i <= level <= 4 ==> {
                    &&& cursor.path@[level - 1] is Read
                    &&& cursor.path@[level - 1]->Read_0.wf()
                    &&& cursor.path@[level - 1]->Read_0.inst_id() == cursor.inst@.id()
                },
            forall|level: int|
                #![trigger cursor.path@[level - 1]]
                1 <= level < i ==> cursor.path@[level - 1] is Unlocked,
        decreases 5 - i,
    {
        match cursor.take_guard(i as usize - 1) {
            GuardInPath::Unlocked => unreached(),
            GuardInPath::Read(mut rguard) => {
                let res = rguard.drop(Tracked(m));
                proof {
                    m = res.get();
                }
            },
            GuardInPath::Write(_) => unreached(),
            GuardInPath::ImplicitWrite(_) => unreached(),
        }
        i += 1;
        cursor.unlock_level = Ghost(i);
    }

    proof {
        let tracked token = cursor.inst.borrow().unlocking_end(m.cpu, m.token);
        m.token = token;
    }

    Tracked(m)
}

} // verus!
