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
use super::{common::*, types::*, mem_content::*, cpu::*, frame::*, page_table::*};
use super::node::{
    PageTableNode, PageTableReadLock, PageTableWriteLock, child::Child, entry::Entry, rwlock::*,
};
use crate::mm::page_table::cursor::MAX_NR_LEVELS;

verus! {

pub enum GuardInPath {
    Read(PageTableReadLock),
    Write(PageTableWriteLock),
    ImplicitWrite(PageTableWriteLock),
    Unlocked,
}

impl GuardInPath {
    #[verifier::external_body]  // Verus does not support replace.
    pub fn take(&mut self) -> (res: Self)
        ensures
            res =~= *old(self),
            *self is Unlocked,
    {
        core::mem::replace(self, Self::Unlocked)
    }
}

pub struct Cursor {
    pub path: [GuardInPath; MAX_NR_LEVELS],
    pub level: PagingLevel,
    pub guard_level: PagingLevel,
    pub va: Vaddr,
    pub inst: Tracked<SpecInstance>,
    pub unlock_level: Ghost<PagingLevel>  // Used for 'unlock_range'.
    ,
}

impl Cursor {
    pub open spec fn wf(&self) -> bool {
        &&& self.path@.len() == 4
        &&& 1 <= self.level <= self.guard_level <= 4
        &&& forall|level: PagingLevel|
            #![trigger self.path[level - 1]]
            1 <= level <= 4 ==> {
                if level < self.guard_level {
                    self.path[level - 1] is Unlocked
                } else if level == self.guard_level {
                    &&& self.path[level - 1] is Write
                    &&& self.path[level - 1]->Write_0.wf()
                    &&& self.path[level - 1]->Write_0.inst_id() == self.inst@.id()
                } else {
                    &&& self.path[level - 1] is Read
                    &&& self.path[level - 1]->Read_0.wf()
                    &&& self.path[level - 1]->Read_0.inst_id() == self.inst@.id()
                }
            }
            // &&& valid_vaddr(self.va)
            // &&& vaddr_is_aligned(self.va)
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
        &&& self.unlock_level@ == self.guard_level
    }

    pub open spec fn wf_init(&self, va: Range<Vaddr>) -> bool
        recommends
            va_range_wf(va),
    {
        &&& self.level == self.guard_level
        &&& self.va == va.start
        &&& self.level == va_range_get_guard_level(va)
    }

    pub open spec fn wf_unlock(&self) -> bool {
        &&& self.unlock_level@ == 5
        &&& forall|level: int|
            #![trigger self.path@[level - 1]]
            1 <= level <= 4 ==> self.path@[level - 1] is Unlocked
    }

    pub open spec fn wf_with_lock_protocol_model(&self, m: LockProtocolModel) -> bool {
        &&& m.inst_id() == self.inst@.id()
        &&& m.path().len() == 5 - self.unlock_level@
        &&& forall|level: int|
            #![trigger self.path[level - 1]]
            self.unlock_level@ <= level <= 4 ==> {
                &&& !(self.path[level - 1] is Unlocked)
                &&& match self.path[level - 1] {
                    GuardInPath::Read(rguard) => m.path()[4 - level] == rguard.nid(),
                    GuardInPath::Write(wguard) => m.path()[4 - level] == wguard.nid(),
                    GuardInPath::ImplicitWrite(wguard) => m.path()[4 - level] == wguard.nid(),
                    GuardInPath::Unlocked => true,
                }
            }
    }

    #[verifier::external_body]  // Verus does not support index for &mut.
    pub fn take_guard(&mut self, idx: usize) -> (res: GuardInPath)
        requires
            0 <= idx < old(self).path@.len(),
        ensures
            res =~= old(self).path@[idx as int],
            self.path@ =~= old(self).path@.update(idx as int, GuardInPath::Unlocked),
            self.level == old(self).level,
            self.guard_level == old(self).guard_level,
            self.va =~= old(self).va,
            self.inst@ =~= old(self).inst@,
            self.unlock_level@ == old(self).unlock_level@,
    {
        self.path[idx].take()
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

pub proof fn lemma_va_range_get_guard_level_implied_by_offsets_equal(
    va: Range<Vaddr>,
    level: PagingLevel,
)
    requires
        va_range_wf(va),
        1 <= level <= 4,
        forall|l|
            level < l <= 4 ==> va_level_to_offset(va.start, l) == va_level_to_offset(
                (va.end - 1) as usize,
                l,
            ),
        level == 1 || va_level_to_offset(va.start, level) != va_level_to_offset(
            (va.end - 1) as usize,
            level,
        ),
    ensures
        level == va_range_get_guard_level(va),
{
    lemma_va_range_get_guard_level_implied_by_offsets_equal_induction(va, level, 4);
}

proof fn lemma_va_range_get_guard_level_implied_by_offsets_equal_induction(
    va: Range<Vaddr>,
    level: PagingLevel,
    top_level: PagingLevel,
)
    requires
        va_range_wf(va),
        1 <= level <= top_level <= 4,
        forall|l|
            level < l <= top_level ==> va_level_to_offset(va.start, l) == va_level_to_offset(
                (va.end - 1) as usize,
                l,
            ),
        level == 1 || va_level_to_offset(va.start, level) != va_level_to_offset(
            (va.end - 1) as usize,
            level,
        ),
    ensures
        level == va_range_get_guard_level_rec(va, top_level),
    decreases top_level,
{
    if (top_level == 1) {
    } else {
        if va_level_to_offset(va.start, top_level) == va_level_to_offset(
            (va.end - 1) as usize,
            top_level,
        ) {
            lemma_va_range_get_guard_level_implied_by_offsets_equal_induction(
                va,
                level,
                (top_level - 1) as PagingLevel,
            );
        }
    }
}

pub proof fn lemma_va_range_get_guard_level_implies_offsets_equal(va: Range<Vaddr>)
    requires
        va_range_wf(va),
    ensures
        forall|l: PagingLevel| #[trigger]
            va_range_get_guard_level(va) < l <= 4 ==> va_level_to_offset(va.start, l)
                == va_level_to_offset((va.end - 1) as usize, l),
        va_range_get_guard_level(va) == 1 || va_level_to_offset(
            va.start,
            va_range_get_guard_level(va),
        ) != va_level_to_offset((va.end - 1) as usize, va_range_get_guard_level(va)),
{
    lemma_va_range_get_guard_level_implies_offsets_equal_induction(va, 4);
}

proof fn lemma_va_range_get_guard_level_implies_offsets_equal_induction(
    va: Range<Vaddr>,
    top_level: PagingLevel,
)
    requires
        va_range_wf(va),
        1 <= top_level <= 4,
    ensures
        forall|l: PagingLevel| #[trigger]
            va_range_get_guard_level_rec(va, top_level) < l <= top_level ==> va_level_to_offset(
                va.start,
                l,
            ) == va_level_to_offset((va.end - 1) as usize, l),
        va_range_get_guard_level_rec(va, top_level) == 1 || va_level_to_offset(
            va.start,
            va_range_get_guard_level_rec(va, top_level),
        ) != va_level_to_offset((va.end - 1) as usize, va_range_get_guard_level_rec(va, top_level)),
    decreases top_level,
{
    if top_level == 1 {
    } else {
        if va_level_to_offset(va.start, top_level) == va_level_to_offset(
            (va.end - 1) as usize,
            top_level,
        ) {
            lemma_va_range_get_guard_level_implies_offsets_equal_induction(
                va,
                (top_level - 1) as PagingLevel,
            );
        }
    }
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
    lemma_va_level_to_trace_rec_len(va.start >> 12, guard_level);
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

// pub proof fn lemma_va_range_get_tree_path_inc(
//     va: Range<Vaddr>, path: Seq<NodeId>,
// )
// TODO: Notice that we don't support huge pages yet.
#[verifier::exec_allows_no_decreases_clause]
pub fn lock_range(pt: &PageTable, va: &Range<Vaddr>, m: Tracked<LockProtocolModel>) -> (res: (
    Cursor,
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
    let mut level: PagingLevel = 4;

    assert(NodeHelper::valid_nid(cur_nid)) by {
        NodeHelper::lemma_root_id();
    };

    let mut cur_pt_paddr = pt.root.start_paddr();

    let tracked mut m = m.get();
    proof {
        m.token = pt.inst.borrow().locking_start(m.cpu, m.token);
        assert(m.state() is ReadLocking);
    }

    // Prologue lemmas
    proof {
        reveal(NodeHelper::trace_to_nid_rec);
        assert(va_level_to_nid(va.start, 4) == NodeHelper::root_id());
        assert(NodeHelper::nid_to_level(NodeHelper::root_id()) == 4);

        lemma_va_range_get_guard_level(*va);
        lemma_va_range_get_tree_path(*va);
    }

    let mut cur_wlock_opt: Option<PageTableWriteLock> = None;
    while level > 1
        invariant_except_break
            pt.wf(),
            va_range_wf(*va),
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            NodeHelper::valid_nid(cur_nid),
            cur_nid == va_level_to_nid(va.start, level),
            1 <= level <= 4,
            level as nat == NodeHelper::nid_to_level(cur_nid),
            level >= va_range_get_guard_level(*va),
            forall|l: PagingLevel|
                level < l <= 4 ==> {
                    #[trigger] va_level_to_offset(va.start, l) == va_level_to_offset(
                        (va.end - 1) as usize,
                        l,
                    )
                },
            1 <= va_range_get_guard_level(*va) <= 4,
            forall|i: int|
                #![trigger path@[i - 1]]
                level < i <= 4 ==> {
                    &&& path@[i - 1] is Read
                    &&& path@[i - 1]->Read_0.wf()
                    &&& path@[i - 1]->Read_0.inst_id() == pt.inst@.id()
                    &&& m.path()[4 - i] == path@[i - 1]->Read_0.nid()
                },
            forall|i: int| #![trigger path@[i - 1]] 1 <= i <= level ==> path@[i - 1] is Unlocked,
            m.path().len() == 4 - level,
            m.state() is ReadLocking,
            cur_wlock_opt is None,
            m.path().len() > 0 ==> NodeHelper::is_child(m.path().last(), cur_nid),
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
            forall|i: int|
                #![trigger path@[i - 1]]
                level < i <= 4 ==> {
                    &&& path@[i - 1] is Read
                    &&& path@[i - 1]->Read_0.wf()
                    &&& path@[i - 1]->Read_0.inst_id() == pt.inst@.id()
                    &&& m.path()[4 - i] == path@[i - 1]->Read_0.nid()
                },
            forall|i: int| #![trigger path@[i - 1]] 1 <= i <= level ==> path@[i - 1] is Unlocked,
            m.path().len() == 4 - level,
            m.state() is ReadLocking,
            cur_wlock_opt is None,
            m.path().len() > 0 ==> NodeHelper::is_child(m.path().last(), cur_nid),
        decreases level,
    {
        let start_idx = pte_index(va.start, level);
        let level_too_high = {
            let end_idx = pte_index(va.end - 1, level);
            level > 1 && start_idx == end_idx
        };
        if !level_too_high {
            assert(level == va_range_get_guard_level(*va)) by {
                lemma_va_range_get_guard_level_implied_by_offsets_equal(*va, level);
            };
            break ;
        }
        assert(level != va_range_get_guard_level(*va)) by {
            lemma_va_range_get_guard_level_implies_offsets_equal(*va);
        };
        // SAFETY: It's OK to get a reference to the page table node since
        // the PT is alive. We will forget the reference later.
        let cur_pt: PageTableNode = PageTableNode::from_raw(
            cur_pt_paddr,
            Ghost(cur_nid),
            Ghost(pt.inst@.id()),
        );
        proof {
            assert(m.path().len() == 0 ==> cur_pt.nid@ == NodeHelper::root_id()) by {
                reveal(NodeHelper::trace_to_nid_rec);
            };
            lemma_wf_tree_path_inc(m.path(), cur_pt.nid@);
        }
        let res = cur_pt.lock_read(Tracked(m));
        let mut cur_pt_rlockguard = res.0;
        proof {
            m = res.1.get();
        }

        let child = cur_pt_rlockguard.read_child_ref(start_idx);
        assert(!(child is Frame)) by {
            child.axiom_no_huge_page();
        };
        let ghost nxt_nid = NodeHelper::get_child(cur_nid, start_idx as nat);
        proof {
            NodeHelper::lemma_nid_to_dep_le_3(cur_nid);
            NodeHelper::lemma_get_child_sound(cur_nid, start_idx as nat);
            lemma_va_level_to_nid_inc(
                va.start,
                (level - 1) as PagingLevel,
                cur_nid,
                start_idx as nat,
            );
            NodeHelper::lemma_is_child_level_relation(cur_nid, nxt_nid);
        }
        match child {
            Child::PageTable(_, _, _) => unreached(),
            Child::PageTableRef(pt, _, _) => {
                path[level as usize - 1] = GuardInPath::Read(cur_pt_rlockguard);
                cur_pt_paddr = pt;
                level -= 1;
                proof {
                    cur_nid = nxt_nid;
                }
            },
            Child::None | Child::Unimplemented => {
                // Upgrade to write lock.
                let res = cur_pt_rlockguard.unlock(Tracked(m));
                let cur_pt = res.0;
                proof {
                    m = res.1.get();
                }
                let res = cur_pt.lock_write(Tracked(m));
                let mut cur_pt_wlockguard = res.0;
                proof {
                    m = res.1.get();
                }

                let entry = cur_pt_wlockguard.entry(start_idx);
                let child = entry.to_ref(&cur_pt_wlockguard);
                assert(!(child is Frame)) by {
                    child.axiom_no_huge_page();
                };
                match child {
                    Child::PageTable(_, _, _) => unreached(),
                    Child::PageTableRef(pt, _, _) => {
                        // Downgrade to read lock.
                        let res = cur_pt_wlockguard.unlock(Tracked(m));
                        let cur_pt = res.0;
                        proof {
                            m = res.1.get();
                        }
                        let res = cur_pt.lock_read(Tracked(m));
                        let cur_pt_rlockguard = res.0;
                        proof {
                            m = res.1.get();
                        }

                        path[level as usize - 1] = GuardInPath::Read(cur_pt_rlockguard);
                        cur_pt_paddr = pt;
                        level -= 1;
                        proof {
                            cur_nid = NodeHelper::get_child(cur_nid, start_idx as nat);
                        }
                    },
                    Child::None | Child::Unimplemented => {
                        // We need to allocate a new page table node.
                        // let pt = zeroed_pt_pool::alloc::<E, C>(
                        //     &preempt_guard,
                        //     level - 1,
                        //     new_pt_is_tracked,
                        // );
                        let pt = allocate_pt(
                            level - 1,
                            Tracked(pt.inst.borrow().clone()),
                            Ghost(nxt_nid),
                        );
                        let tracked pt_inst = pt.inst.borrow().clone();
                        cur_pt_paddr = pt.start_paddr();
                        let new_child = Child::PageTable(pt, Tracked(pt_inst), Ghost(nxt_nid));
                        assert(new_child.wf()) by {
                            NodeHelper::lemma_nid_to_dep_le_3(cur_nid);
                            NodeHelper::lemma_get_child_sound(cur_nid, start_idx as nat);
                        };
                        entry.replace(new_child, &mut cur_pt_wlockguard);
                        // Downgrade to read lock.
                        let res = cur_pt_wlockguard.unlock(Tracked(m));
                        let cur_pt = res.0;
                        proof {
                            m = res.1.get();
                        }
                        let res = cur_pt.lock_read(Tracked(m));
                        let cur_pt_rlockguard = res.0;
                        proof {
                            m = res.1.get();
                        }
                        path[level as usize - 1] = GuardInPath::Read(cur_pt_rlockguard);
                        level -= 1;
                        proof {
                            cur_nid = NodeHelper::get_child(cur_nid, start_idx as nat);
                        }
                    },
                    _ => {
                        // cur_wlock_opt = Some(cur_pt_wlockguard);
                        // break;
                        unreached::<()>()
                    },
                }
            },
            _ => {
                // let res = cur_pt_rlockguard.unlock(mem, Tracked(m));
                // let cur_pt = res.0;
                // proof { m = res.1.get(); }
                // let _ = cur_pt.into_raw(mem);
                // cur_wlock_opt = None;
                // break;
                unreached::<()>()
            },
        }
    };

    assert(cur_wlock_opt is None);

    let cur_pt_wlockguard = if cur_wlock_opt.is_some() {
        cur_wlock_opt.unwrap()
    } else {
        let cur_pt = PageTableNode::from_raw(cur_pt_paddr, Ghost(cur_nid), Ghost(pt.inst@.id()));
        proof {
            lemma_wf_tree_path_inc(m.path(), cur_pt.nid@);
        }
        let res = cur_pt.lock_write(Tracked(m));
        proof {
            m = res.1.get();
        }
        assert(m.path().is_prefix_of(va_range_get_tree_path(*va))) by {
            admit();
        };
        res.0
    };

    path[level as usize - 1] = GuardInPath::Write(cur_pt_wlockguard);

    let tracked inst = pt.inst.borrow().clone();
    let cursor = Cursor {
        path,
        level: level,
        guard_level: level,
        va: va.start,
        inst: Tracked(inst),
        unlock_level: Ghost(level),
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

    let guard_level = cursor.guard_level;
    let GuardInPath::Write(mut guard_node) = cursor.take_guard(guard_level as usize - 1) else {
        unreached()
    };
    let res = guard_node.unlock(Tracked(m));
    let pt = res.0;
    proof {
        m = res.1.get();
    }
    pt.into_raw();
    cursor.unlock_level = Ghost((cursor.unlock_level@ + 1) as PagingLevel);

    let mut i = guard_level + 1;
    while i <= 4
        invariant
            guard_level + 1 <= i <= 5,
            i == cursor.unlock_level@,
            cursor.path@.len() == 4,
            forall|level: int|
                #![trigger cursor.path@[level - 1]]
                i <= level <= 4 ==> {
                    &&& cursor.path@[level - 1] is Read
                    &&& cursor.path@[level - 1]->Read_0.wf()
                    &&& cursor.path@[level - 1]->Read_0.inst_id() == cursor.inst@.id()
                },
            forall|level: int|
                #![trigger cursor.path@[level - 1]]
                1 <= level < i ==> cursor.path@[level - 1] is Unlocked,
            cursor.wf_with_lock_protocol_model(m),
            m.inv(),
            m.state() is ReadLocking,
            cursor.inst@.cpu_num() == GLOBAL_CPU_NUM,
        decreases 5 - i,
    {
        match cursor.take_guard(i as usize - 1) {
            GuardInPath::Unlocked => unreached(),
            GuardInPath::Read(mut rguard) => {
                assert(m.path()[4 - i] == rguard.nid());
                let res = rguard.unlock(Tracked(m));
                let pt = res.0;
                proof {
                    m = res.1.get();
                }
                pt.into_raw();
                cursor.unlock_level = Ghost((cursor.unlock_level@ + 1) as PagingLevel);
            },
            GuardInPath::Write(_) => unreached(),
            GuardInPath::ImplicitWrite(_) => unreached(),
        }
        i += 1;
    }

    proof {
        let tracked token = cursor.inst.borrow().unlocking_end(m.cpu, m.token);
        m.token = token;
    }

    Tracked(m)
}

} // verus!
