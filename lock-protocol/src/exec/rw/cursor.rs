use std::mem::ManuallyDrop;
use core::ops::Deref;
use std::ops::Range;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::atomic_with_ghost;
use vstd::rwlock::{ReadHandle, WriteHandle};
use vstd::vpanic;
use vstd::pervasive::allow_panic;
use vstd::pervasive::unreached;

use vstd_extra::manually_drop::*;

use crate::spec::{common::*, utils::*, tree::*};
use super::{
    common::*, utils::*, types::*, 
    mem_content::*, cpu::*, frame::*, page_table::*
};
use super::node::{
    PageTableNode, PageTableReadLock, PageTableWriteLock,
    child::Child, entry::Entry,
    rwlock::*,
};

verus! {

#[is_variant]
pub enum GuardInPath {
    ReadLocked(PageTableReadLock),
    WriteLocked(PageTableWriteLock),
    None,
}

struct_with_invariants!{

pub struct Cursor {
    pub path: Vec<GuardInPath>,
    pub level: PagingLevel,
    pub guard_level: PagingLevel,
    pub va: Vaddr,
}

pub open spec fn wf(&self, mem: &MemContent) -> bool {
    predicate {
        &&& self.path@.len() == 4

        &&& 1 <= self.level <= self.guard_level <= 4

        &&& forall |level: PagingLevel| #![trigger self.path[level - 1]]
            1 <= level <= 4 ==> {
                if level < self.guard_level {
                    self.path[level - 1] is None
                } else if level == self.guard_level {
                    &&& self.path[level - 1] is WriteLocked
                    &&& self.path[level - 1]->WriteLocked_0.wf(mem)
                } else {
                    &&& self.path[level - 1] is ReadLocked
                    &&& self.path[level - 1]->ReadLocked_0.wf(mem)
                }
            }

        // &&& valid_vaddr(self.va)
        // &&& vaddr_is_aligned(self.va)
    }
}

}

impl Cursor {
    pub open spec fn wf_init(&self, va: Range<Vaddr>) -> bool
        recommends
            va_range_wf(va),
    {
        &&& self.level == self.guard_level
        &&& self.va == va.start
        &&& self.level == va_range_get_guard_level(va)
    }
}

} // verus!

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
{
    if 1 <= level <= 4 {
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
    } else {
        arbitrary()
    }
}

pub open spec fn va_range_get_guard_level(va: Range<Vaddr>) -> PagingLevel
    recommends
        va_range_wf(va),
{
    va_range_get_guard_level_rec(va, 4)
}

pub proof fn lemma_va_range_get_guard_level(va: Range<Vaddr>)
    requires
        va_range_wf(va),
    ensures
        1 <= va_range_get_guard_level(va) <= 4,
{
    admit(); // TODO
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
    admit(); //TODO
}

// pub proof fn lemma_va_range_get_tree_path_inc(
//     va: Range<Vaddr>, path: Seq<NodeId>,
// )

// TODO: Notice that we don't support huge pages yet.
#[verifier::exec_allows_no_decreases_clause]
pub fn lock_range(
    pt: &PageTable,
    va: &Range<Vaddr>,
    // new_pt_is_tracked: MapTrackingStatus,
    m: Tracked<LockProtocolModel>,
    mem: &MemContent,
) -> (res: (Cursor, Tracked<LockProtocolModel>))
    requires
        pt.wf(mem),
        va_range_wf(*va),
        m@.inv(),
        m@.inst_id() == pt.inst@.id(),
        m@.state() is Void,
    ensures
        res.0.wf(mem),
        res.0.wf_init(*va),
        res.1@.inv(),
        res.1@.inst_id() == pt.inst@.id(),
        res.1@.state() is WriteLocked,
        res.1@.path() =~= va_range_get_tree_path(*va),
{
    let mut path: Vec<GuardInPath> = Vec::with_capacity(4);
    let mut i: usize = 0;
    while i < 4
        invariant
            0 <= i <= 4,
            path@.len() == i,
            forall|_i| 0 <= _i < i ==> path@[_i] is None,
    {
        path.push(GuardInPath::None);
        i += 1;
    }
    assert(path.len() == 4);
    assert(forall|i| 0 <= i < 4 ==> path@[i] is None);

    let ghost mut cur_nid: NodeId = 0;
    let mut level: PagingLevel = 4;

    assert(cur_nid == NodeHelper::root_id());
    assert(NodeHelper::valid_nid(cur_nid)) by {
        NodeHelper::lemma_root_id();
    };

    let mut cur_pt_paddr = pt.root.start_paddr(mem);

    let tracked mut m = m.get();
    proof {
        m.token = pt.inst.borrow().locking_start(m.cpu, m.token);
        assert(m.state() is ReadLocking);
    }

    // Prologue lemmas
    proof {
        assert(va_level_to_nid(va.start, 4) == NodeHelper::root_id()) by {
            admit();
        };
        assert(NodeHelper::nid_to_level(NodeHelper::root_id()) == 4) by {
            admit();
        };

        lemma_va_range_get_guard_level(*va);
        lemma_va_range_get_tree_path(*va);
    }

    let mut cur_wlock_opt: Option<PageTableWriteLock> = None;
    while level > 1
        invariant_except_break
            valid_paddr(cur_pt_paddr),
            pt.wf(mem),
            va_range_wf(*va),
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            NodeHelper::valid_nid(cur_nid),
            cur_nid == va_level_to_nid(va.start, level),
            1 <= level <= 4,
            level as nat == NodeHelper::nid_to_level(cur_nid),
            level >= va_range_get_guard_level(*va),
            1 <= va_range_get_guard_level(*va) <= 4,
            path.len() == 4,
            forall|i| #![auto] level <= i < 4 ==> {
                &&& path@[i] is ReadLocked
                &&& path@[i]->ReadLocked_0.wf(mem)
            },
            forall|i| 0 <= i < level ==> path@[i] is None,
            m.path().len() == 4 - level,
            m.path().is_prefix_of(va_range_get_tree_path(*va)),
            m.state() is ReadLocking,
            cur_wlock_opt is None,
            m.path().len() > 0 ==> 
                NodeHelper::is_child(m.path().last(), cur_nid),
        ensures
            valid_paddr(cur_pt_paddr),
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            NodeHelper::valid_nid(cur_nid),
            cur_nid == va_level_to_nid(va.start, level),
            1 <= level <= 4,
            level as nat == NodeHelper::nid_to_level(cur_nid),
            level == va_range_get_guard_level(*va),
            path.len() == 4,
            forall|i| #![auto] level <= i < 4 ==> {
                &&& path@[i] is ReadLocked
                &&& path@[i]->ReadLocked_0.wf(mem)
            },
            forall|i| 0 <= i < level ==> path@[i] is None,
            m.path().len() == 4 - level,
            m.path().is_prefix_of(va_range_get_tree_path(*va)),
            m.state() is ReadLocking,
            cur_wlock_opt is None,
            m.path().len() > 0 ==> 
                NodeHelper::is_child(m.path().last(), cur_nid),
        decreases level,
    {
        let start_idx = pte_index(va.start, level);
        let level_too_high = {
            let end_idx = pte_index(va.end - 1, level);
            level > 1 && start_idx == end_idx
        };
        if !level_too_high {
            assert(level == va_range_get_guard_level(*va)) by {
                admit();
            };
            break;
        }
        assert(level != va_range_get_guard_level(*va)) by {
            admit();
        };
        assert(level > 1);

        // SAFETY: It's OK to get a reference to the page table node since
        // the PT is alive. We will forget the reference later.
        let cur_pt: PageTableNode = PageTableNode::from_raw(
            cur_pt_paddr, 
            mem, 
            Ghost(cur_nid), 
            Ghost(pt.inst@.id()),
        );
        proof { lemma_wf_tree_path_inc(m.path(), cur_pt.nid@); }
        let res = cur_pt.lock_read(mem, Tracked(m));
        let mut cur_pt_rlockguard = res.0;
        proof { m = res.1.get(); }

        let child = cur_pt_rlockguard.read_child_ref(start_idx, mem);
        assert(!(child is Frame)) by {
            child.axiom_no_huge_page();
        };
        let ghost nxt_nid = NodeHelper::get_child(cur_nid, start_idx as nat);
        proof {
            NodeHelper::lemma_get_child_sound(cur_nid, start_idx as nat);
            lemma_va_level_to_nid_inc(
                va.start, (level - 1) as PagingLevel, cur_nid, start_idx as nat,
            );
            NodeHelper::lemma_is_child_level_relation(cur_nid, nxt_nid);
        }
        match child {
            Child::PageTable(_, _, _) => unreached(),
            Child::PageTableRef(pt, _, _) => {
                path[level as usize - 1] = GuardInPath::ReadLocked(cur_pt_rlockguard);
                cur_pt_paddr = pt;
                level -= 1;
                proof { cur_nid = nxt_nid; }
            }
            Child::None | Child::Unimplemented => {
                // Upgrade to write lock.
                let res = cur_pt_rlockguard.unlock(mem, Tracked(m));
                let cur_pt = res.0;
                proof { m = res.1.get(); }
                let res = cur_pt.lock_write(mem, Tracked(m));
                let mut cur_pt_wlockguard = res.0;
                proof { m = res.1.get(); }

                let entry = cur_pt_wlockguard.entry(start_idx, mem);
                let child = entry.to_ref(&cur_pt_wlockguard, mem);
                assert(!(child is Frame)) by {
                    child.axiom_no_huge_page();
                };
                match child {
                    Child::PageTable(_, _, _) => unreached(),
                    Child::PageTableRef(pt, _, _) => {
                        // Downgrade to read lock.
                        let res = cur_pt_wlockguard.unlock(mem, Tracked(m));
                        let cur_pt = res.0;
                        proof { m = res.1.get(); }
                        let res = cur_pt.lock_read(mem, Tracked(m));
                        let cur_pt_rlockguard = res.0;
                        proof { m = res.1.get(); }

                        path[level as usize - 1] = GuardInPath::ReadLocked(cur_pt_rlockguard);
                        cur_pt_paddr = pt;
                        level -= 1;
                        proof { cur_nid = NodeHelper::get_child(cur_nid, start_idx as nat); }
                    }
                    Child::None | Child::Unimplemented => {
                        // We need to allocate a new page table node.
                        // let pt = zeroed_pt_pool::alloc::<E, C>(
                        //     &preempt_guard,
                        //     level - 1,
                        //     new_pt_is_tracked,
                        // );
                        let pt = allocate_pt(level - 1, mem);
                        let tracked pt_inst = pt.inst.borrow().clone();
                        cur_pt_paddr = pt.start_paddr(mem);
                        let new_child = Child::PageTable(
                            pt, 
                            Tracked(pt_inst),
                            Ghost(NodeHelper::get_child(cur_nid, start_idx as nat)),
                        );
                        assert(new_child.wf(mem)) by {
                            NodeHelper::lemma_get_child_sound(cur_nid, start_idx as nat);
                        };
                        entry.replace(
                            new_child, &mut cur_pt_wlockguard, mem,
                        );
                        // Downgrade to read lock.
                        let res = cur_pt_wlockguard.unlock(mem, Tracked(m));
                        let cur_pt = res.0;
                        proof { m = res.1.get(); }
                        let res = cur_pt.lock_read(mem, Tracked(m));
                        let cur_pt_rlockguard = res.0;
                        proof { m = res.1.get(); }
                        path[level as usize - 1] = GuardInPath::ReadLocked(cur_pt_rlockguard);
                        level -= 1;
                        proof { cur_nid = NodeHelper::get_child(cur_nid, start_idx as nat); }
                    }
                    _ => {
                        // cur_wlock_opt = Some(cur_pt_wlockguard);
                        // break;
                        unreached::<()>()
                    }
                }
            }
            _ => {
                // let res = cur_pt_rlockguard.unlock(mem, Tracked(m));
                // let cur_pt = res.0;
                // proof { m = res.1.get(); }
                // let _ = cur_pt.into_raw(mem);
                // cur_wlock_opt = None;

                // break;
                unreached::<()>()
            }
        }
        assert(m.path().is_prefix_of(va_range_get_tree_path(*va))) by { admit(); } // TODO
    };

    assert(cur_wlock_opt is None);
    
    let cur_pt_wlockguard = if cur_wlock_opt.is_some() {
        cur_wlock_opt.unwrap()
    } else {
        let cur_pt = PageTableNode::from_raw(
            cur_pt_paddr, 
            mem, 
            Ghost(cur_nid), 
            Ghost(pt.inst@.id()),
        );
        proof { lemma_wf_tree_path_inc(m.path(), cur_pt.nid@); }
        let res = cur_pt.lock_write(mem, Tracked(m));
        proof { m = res.1.get(); }
        assert(m.path().is_prefix_of(va_range_get_tree_path(*va))) by { admit(); };
        res.0
    };

    path[level as usize - 1] = GuardInPath::WriteLocked(cur_pt_wlockguard);

    let cursor = Cursor { path, level: level, guard_level: level, va: va.start };

    (cursor, Tracked(m))
}

pub fn unlock_range(
    cursor: &mut Cursor,
) 
{}

} // verus!
