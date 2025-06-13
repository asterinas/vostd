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

use vstd_extra::manually_drop::*;

use crate::spec::{common::*, utils::*, tree::*};
use super::{common::*, utils::*, types::*, cpu::*, frame::*, page_table::*};

verus! {

pub enum GuardInPath<'a> {
    ReadLocked(ReadHandle<'a, Tracked<NodeToken>, spec_fn(Tracked<NodeToken>) -> bool>),
    WriteLocked(WriteHandle<'a, Tracked<NodeToken>, spec_fn(Tracked<NodeToken>) -> bool>),
    None,
}

struct_with_invariants!{

pub struct Cursor<'a> {
    pub path: Vec<GuardInPath<'a>>,
    pub level: Level,
    pub guard_level: Level,
    pub va: Vaddr,
}

pub open spec fn wf(&self) -> bool {
    predicate {
        &&& self.path@.len() == 4

        &&& 1 <= self.level <= self.guard_level <= 4

        &&& forall |level: Level| #![trigger self.path[level - 1]]
            1 <= level <= 4 ==> {
                if level < self.guard_level {
                    self.path[level - 1] is None
                } else if level == self.guard_level {
                    self.path[level - 1] is WriteLocked
                } else {
                    self.path[level - 1] is ReadLocked
                }
            }

        // &&& valid_vaddr(self.va)
        // &&& vaddr_is_aligned(self.va)
    }
}

}

impl<'a> Cursor<'a> {
    pub open spec fn init_wf(&self, va: Range<Vaddr>) -> bool
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

pub struct TransHandler;

impl TransHandler {
    pub fn acquire_write<'a>(
        pt_frame: &'a PageTableFrame,
        m: Tracked<LockProtocolModel>,
        tree_path: Ghost<Seq<NodeId>>,
    ) -> (res: (
        Tracked<NodeToken>,
        WriteHandle<'a, Tracked<NodeToken>, spec_fn(Tracked<NodeToken>) -> bool>,
        Tracked<LockProtocolModel>,
        Ghost<Seq<NodeId>>,
    ))
        requires
            pt_frame.wf(),
            m@.inv(),
            m@.inst_id() == pt_frame.inst@.id(),
            m@.pred_cursor_ReadLocking(tree_path@),
            wf_tree_path(tree_path@.push(pt_frame.nid@)),
        ensures
            res.0@.instance_id() == pt_frame.inst@.id(),
            res.0@.key() == pt_frame.nid@,
            res.0@.value() is WriteLocked,
            res.1.rwlock() == pt_frame.rw_lock,
            res.2@.inv(),
            res.2@.inst_id() == pt_frame.inst@.id(),
            res.2@.pred_cursor_WriteLocked(res.3@),
            res.3@ =~= tree_path@.push(pt_frame.nid@),
    {
        let tracked mut m = m.get();
        let ghost mut tree_path = tree_path@;

        let (node_token, write_handle) = pt_frame.rw_lock.acquire_write();
        let tracked mut node_token = node_token.get();
        atomic_with_ghost!(
            pt_frame.rc => no_op();
            update prev -> next;
            ghost g => {
                assert(prev == 0) by { admit(); }; // How to remove this?

                let tracked res = pt_frame.inst.borrow().write_lock(
                    m.cpu,
                    pt_frame.nid@,
                    node_token,
                    &g,
                    m.token,
                );

                node_token = res.0.get();
                m.token = res.1.get();
                tree_path = tree_path.push(pt_frame.nid@);
            }
        );

        (Tracked(node_token), write_handle, Tracked(m), Ghost(tree_path))
    }

    pub fn release_write<'a>(
        pt_frame: &PageTableFrame,
        token: Tracked<NodeToken>,
        write_handle: WriteHandle<'a, Tracked<NodeToken>, spec_fn(Tracked<NodeToken>) -> bool>,
        m: Tracked<LockProtocolModel>,
        tree_path: Ghost<Seq<NodeId>>,
    ) -> (res: (Tracked<LockProtocolModel>, Ghost<Seq<NodeId>>))
        requires
            pt_frame.wf(),
            token@.instance_id() == pt_frame.inst@.id(),
            token@.key() == pt_frame.nid@,
            token@.value() is WriteLocked,
            write_handle.rwlock() == pt_frame.rw_lock,
            m@.inv(),
            m@.inst_id() == pt_frame.inst@.id(),
            m@.pred_cursor_WriteLocked(tree_path@),
            wf_tree_path(tree_path@),
            tree_path@.len() > 0 && tree_path@.last() == pt_frame.nid@,
        ensures
            res.0@.inv(),
            res.0@.inst_id() == pt_frame.inst@.id(),
            res.0@.pred_cursor_ReadLocking(res.1@),
            res.1@ =~= tree_path@.drop_last(),
    {
        let tracked mut m = m.get();
        let ghost mut tree_path = tree_path@;
        let tracked mut token = token.get();
        proof {
            let tracked res = pt_frame.inst.borrow().write_unlock(
                m.cpu,
                pt_frame.nid@,
                token,
                m.token,
            );
            token = res.0.get();
            m.token = res.1.get();
            tree_path = tree_path.drop_last();
        }

        // Exec-mode: release write lock
        write_handle.release_write(Tracked(token));

        (Tracked(m), Ghost(tree_path))
    }

    pub fn acquire_read<'a>(
        pt_frame: &'a PageTableFrame,
        m: Tracked<LockProtocolModel>,
        tree_path: Ghost<Seq<NodeId>>,
    ) -> (res: (
        ReadHandle<'a, Tracked<NodeToken>, spec_fn(Tracked<NodeToken>) -> bool>,
        Tracked<LockProtocolModel>,
        Ghost<Seq<NodeId>>,
    ))
        requires
            pt_frame.wf(),
            m@.inv(),
            m@.inst_id() == pt_frame.inst@.id(),
            m@.pred_cursor_ReadLocking(tree_path@),
            wf_tree_path(tree_path@.push(pt_frame.nid@)),
        ensures
            pt_frame.rw_lock.inv(res.0.view()),
            res.0.rwlock() == pt_frame.rw_lock,
            res.1@.inv(),
            res.1@.inst_id() == pt_frame.inst@.id(),
            res.1@.pred_cursor_ReadLocking(res.2@),
            res.2@ =~= tree_path@.push(pt_frame.nid@),
    {
        let tracked mut m = m.get();
        let ghost mut tree_path = tree_path@;

        let read_handle = pt_frame.rw_lock.acquire_read();

        let tracked_node_token = read_handle.borrow();
        let tracked node_token = tracked_node_token.borrow();
        atomic_with_ghost!{
            pt_frame.rc => fetch_add(1);
            update prev -> next;
            ghost g => {
                assert(next <= MAX_RC()) by { admit(); }; // How to remove this?

                assert(tree_path.len() < 3) by { admit(); };
                let tracked res = pt_frame.inst.borrow().read_lock(
                    m.cpu,
                    pt_frame.nid@,
                    node_token,
                    g,
                    m.token,
                );
                g = res.0.get();
                m.token = res.1.get();
                tree_path = tree_path.push(pt_frame.nid@);
            }
        };

        (read_handle, Tracked(m), Ghost(tree_path))
    }

    pub fn release_read<'a>(
        pt_frame: &PageTableFrame,
        read_handle: ReadHandle<'a, Tracked<NodeToken>, spec_fn(Tracked<NodeToken>) -> bool>,
        m: Tracked<LockProtocolModel>,
        tree_path: Ghost<Seq<NodeId>>,
    ) -> (res: (Tracked<LockProtocolModel>, Ghost<Seq<NodeId>>))
        requires
            pt_frame.wf(),
            read_handle.rwlock() == pt_frame.rw_lock,
            m@.inv(),
            m@.inst_id() == pt_frame.inst@.id(),
            m@.pred_cursor_ReadLocking(tree_path@),
            wf_tree_path(tree_path@),
            tree_path@.len() > 0 && tree_path@.last() == pt_frame.nid@,
        ensures
            res.0@.inv(),
            res.0@.inst_id() == pt_frame.inst@.id(),
            res.0@.pred_cursor_ReadLocking(res.1@),
            res.1@ =~= tree_path@.drop_last(),
    {
        let tracked mut m = m.get();
        let ghost mut tree_path = tree_path@;
        atomic_with_ghost!(
            pt_frame.rc => fetch_sub(1);
            update prev -> next;
            ghost g => {
                assert(prev > 0) by { admit(); } // How to remove this?

                let tracked res = pt_frame.inst.borrow().read_unlock(
                    m.cpu,
                    pt_frame.nid@,
                    g,
                    m.token,
                );
                g = res.0.get();
                m.token = res.1.get();
                tree_path = tree_path.drop_last();
            }
        );

        (Tracked(m), Ghost(tree_path))
    }

    #[verifier::external_body]
    pub fn allocate(
        pt: &PageTable,
        // allocator: &mut FrameAllocator,
        allocator: &FrameAllocator,
        nid: u64,
        m: Tracked<&LockProtocolModel>,
        tree_path: Ghost<&Seq<NodeId>>,
    )
        requires
            pt.wf(*allocator),
            allocator.wf(),
            NodeHelper::valid_nid(nid as NodeId),
            nid as NodeId != NodeHelper::root_id(),
            m@.inv(),
            m@.inst_id() == pt.inst@.id(),
            m@.pred_cursor_WriteLocked(*tree_path@),
            tree_path@.len() > 0,
            NodeHelper::in_subtree(tree_path@.last(), nid as NodeId),
        ensures
    // allocator.wf(),

    {
        let tracked m = m.borrow();
        let ghost tree_path = *tree_path@;

        let pa: Paddr = allocator.find_void_frame_pa();
        assert(valid_paddr(pa) && paddr_is_aligned(pa));
        // TODO: Here we need something to guarantee the exclusive access
        let tracked mut node_token;
        let tracked mut rc_token;
        atomic_with_ghost!{
            pt.nodes[nid as usize] => store(pa);
            update prev -> next;
            ghost g => {
                assert(prev == INVALID_PADDR) by { admit(); }; // How to remove this?
                assert(g.tokens is Some);
                let tracked tokens = g.tokens.tracked_unwrap();
                assert(tokens.0.value() is UnAllocated);

                let tracked res = pt.inst.borrow().allocate(
                    m.cpu,
                    nid as NodeId,
                    tokens.0,
                    &m.token,
                );

                node_token = res;
                rc_token = tokens.1;
                g.tokens = None;
            }
        };
        allocator.allocate_pt_frame(
            pa,
            Ghost(nid as NodeId),
            Tracked(pt.inst.borrow().clone()),
            Tracked(node_token),
            Tracked(rc_token),
        );
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

pub open spec fn va_range_get_guard_level_rec(va: Range<Vaddr>, cur_level: Level) -> Level
    recommends
        va_range_wf(va),
        1 <= cur_level <= 4,
    decreases cur_level,
{
    if 1 <= cur_level <= 4 {
        if cur_level == 1 {
            1
        } else {
            let st = va.start;
            let en = (va.end - 1) as u64;

            if va_level_to_offset(st, cur_level) == va_level_to_offset(en, cur_level) {
                va_range_get_guard_level_rec(va, (cur_level - 1) as Level)
            } else {
                cur_level
            }
        }
    } else {
        arbitrary()
    }
}

pub open spec fn va_range_get_guard_level(va: Range<Vaddr>) -> Level
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
    admit();
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
    admit();
}

#[verifier::exec_allows_no_decreases_clause]
#[verifier::external_body]
pub fn lock_range<'a>(
    pt: &PageTable,
    allocator: &'a FrameAllocator,
    va: &Range<Vaddr>,
    m: Tracked<LockProtocolModel>,
) -> (res: (Cursor<'a>, Tracked<LockProtocolModel>))
    requires
        pt.wf(*allocator),
        allocator.wf(),
        va_range_wf(*va),
        m@.inv(),
        m@.inst_id() == pt.inst@.id(),
        m@.pred_cursor_Void(),
    ensures
        res.0.wf(),
        res.0.init_wf(*va),
        res.1@.inv(),
        res.1@.inst_id() == pt.inst@.id(),
        res.1@.pred_cursor_WriteLocked(va_range_get_tree_path(*va)),
{
    let mut path: Vec<GuardInPath<'a>> = Vec::with_capacity(4);
    for i in 0..4
        invariant
            0 <= i <= 4,
            path@.len() == i,
            forall|_i| 0 <= _i < i ==> path@[_i] is None,
    {
        path.push(GuardInPath::None);
    }
    assert(path.len() == 4);
    assert(forall|i| 0 <= i < 4 ==> path@[i] is None);

    let mut cur_nid: u64 = 0;
    let mut cur_level: Level = 4;

    assert(cur_nid as NodeId == NodeHelper::root_id());
    assert(NodeHelper::valid_nid(cur_nid as NodeId)) by {
        NodeHelper::lemma_root_id();
    };

    let tracked mut m = m.get();
    let ghost mut tree_path: Seq<NodeId> = Seq::empty();
    proof {
        m.token = pt.inst.borrow().locking_start(m.cpu, m.token);
        assert(m.pred_cursor_ReadLocking(tree_path));
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

    while cur_level > 1
        invariant_except_break
            pt.wf(*allocator),
            allocator.wf(),
            va_range_wf(*va),
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            NodeHelper::valid_nid(cur_nid as NodeId),
            cur_nid as NodeId == va_level_to_nid(va.start, cur_level),
            1 <= cur_level <= 4,
            cur_level as nat == NodeHelper::nid_to_level(cur_nid as NodeId),
            cur_level >= va_range_get_guard_level(*va),
            1 <= va_range_get_guard_level(*va) <= 4,
            path.len() == 4,
            forall|i| cur_level <= i < 4 ==> path@[i] is ReadLocked,
            forall|i| 0 <= i < cur_level ==> path@[i] is None,
            tree_path.len() == 4 - cur_level,
            tree_path.is_prefix_of(va_range_get_tree_path(*va)),
            m.pred_cursor_ReadLocking(tree_path),
        ensures
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            NodeHelper::valid_nid(cur_nid as NodeId),
            cur_nid as NodeId == va_level_to_nid(va.start, cur_level),
            1 <= cur_level <= 4,
            cur_level as nat == NodeHelper::nid_to_level(cur_nid as NodeId),
            cur_level == va_range_get_guard_level(*va),
            path.len() == 4,
            forall|i| cur_level <= i < 4 ==> path@[i] is ReadLocked,
            forall|i| 0 <= i < cur_level ==> path@[i] is None,
            tree_path.len() == 4 - cur_level,
            tree_path.is_prefix_of(va_range_get_tree_path(*va)),
            m.pred_cursor_ReadLocking(tree_path),
        decreases cur_level,
    {
        let start_idx = pte_index(va.start, cur_level);
        let level_too_high = {
            let end_idx = pte_index(va.end - 1, cur_level);
            cur_level > 1 && start_idx == end_idx
        };
        if !level_too_high {
            assert(cur_level == va_range_get_guard_level(*va)) by {
                admit();
            };
            break ;
        }
        assert(cur_level != va_range_get_guard_level(*va)) by {
            admit();
        };

        let pa: Paddr =
            atomic_with_ghost!{
            pt.nodes[cur_nid as usize] => load();
            returning res;
            ghost g => {
                assert(g.nid == cur_nid as NodeId);
                if res != INVALID_PADDR {
                    assert(g.tokens is None);
                }
            }
        };

        // TODO: fix this.
        assert(pa != INVALID_PADDR) by {
            admit();
        };
        assert(valid_paddr(pa));
        assert(paddr_is_aligned(pa));

        assert(allocator.usages@[pa_to_fid(pa) as int] is PageTable) by {
            admit();
        };
        let frame: &Frame = allocator.get_pt_frame_from_pa(pa);
        let pt_frame: &PageTableFrame = unsafe { frame.page_table_frame.deref() };
        // How to remove these?
        assert(pt_frame.nid == cur_nid as NodeId) by {
            admit();
        }
        assert(pt_frame.inst@.id() == pt.inst@.id()) by {
            admit();
        }
        assert(pt_frame =~= &manually_drop_unwrap(
            get_union_field::<Frame, ManuallyDrop<PageTableFrame>>(*frame, "page_table_frame"),
        )) by {
            admit();
        };
        assert(pt_frame.wf());

        assert(wf_tree_path(tree_path.push(cur_nid as NodeId))) by {
            admit();
        };
        let res = TransHandler::acquire_read(pt_frame, Tracked(m), Ghost(tree_path));
        let read_handle = res.0;
        proof {
            m = res.1.get();
            tree_path = res.2@;
        }

        let pte_offset: u64 = pte_index(va.start, cur_level);
        assert(NodeHelper::is_not_leaf(cur_nid as NodeId)) by {
            assert(cur_level as nat == NodeHelper::nid_to_level(cur_nid as NodeId));
            assert(cur_level > 1);
            NodeHelper::lemma_level_dep_relation(cur_nid as NodeId);
        };
        let nxt_nid = NodeHelperExec::get_child_exec(cur_nid, pte_offset);
        assert(NodeHelper::valid_nid(nxt_nid as NodeId));

        // Check if the pte exisis
        let res =
            atomic_with_ghost!{
            pt.nodes[nxt_nid as usize] => load();
            ghost g => {}
        };
        if res == INVALID_PADDR {
            // Lock upgrades
            let res = TransHandler::release_read(
                pt_frame,
                read_handle,
                Tracked(m),
                Ghost(tree_path),
            );
            proof {
                m = res.0.get();
                tree_path = res.1@;
            }

            assert(wf_tree_path(tree_path.push(cur_nid as NodeId))) by {
                admit();
            };
            let res = TransHandler::acquire_write(pt_frame, Tracked(m), Ghost(tree_path));
            let node_token = res.0;
            let write_handle = res.1;
            proof {
                m = res.2.get();
                tree_path = res.3@;
            }

            // Check again
            let res =
                atomic_with_ghost!{
                pt.nodes[nxt_nid as usize] => load();
                ghost g => {}
            };
            if res == INVALID_PADDR {
                // Allocate new page table node
                TransHandler::allocate(pt, allocator, nxt_nid, Tracked(&m), Ghost(&tree_path));
            }
            let res = TransHandler::release_write(
                pt_frame,
                node_token,
                write_handle,
                Tracked(m),
                Ghost(tree_path),
            );
            proof {
                m = res.0.get();
                tree_path = res.1@;
            }

            // Downgrade to read lock.
            assert(wf_tree_path(tree_path.push(cur_nid as NodeId))) by {
                admit();
            };
            let res = TransHandler::acquire_read(pt_frame, Tracked(m), Ghost(tree_path));
            let read_handle = res.0;
            proof {
                m = res.1.get();
                tree_path = res.2@;
            }

            path[(cur_level - 1) as usize] = GuardInPath::ReadLocked(read_handle);
            cur_nid = nxt_nid;
            cur_level = cur_level - 1;

            assert(cur_nid as NodeId == va_level_to_nid(va.start, cur_level)) by {
                admit();
            };
            assert(cur_level as nat == NodeHelper::nid_to_level(cur_nid as nat)) by {
                admit();
            };
            assert(tree_path.is_prefix_of(va_range_get_tree_path(*va))) by {
                admit();
            };
        } else {
            path[(cur_level - 1) as usize] = GuardInPath::ReadLocked(read_handle);
            cur_nid = nxt_nid;
            cur_level = cur_level - 1;

            assert(cur_nid as NodeId == va_level_to_nid(va.start, cur_level)) by {
                admit();
            };
            assert(cur_level as nat == NodeHelper::nid_to_level(cur_nid as nat)) by {
                admit();
            };
            assert(tree_path.is_prefix_of(va_range_get_tree_path(*va))) by {
                admit();
            };
        }
    }

    loop
        invariant_except_break
            pt.wf(*allocator),
            allocator.wf(),
            va_range_wf(*va),
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            NodeHelper::valid_nid(cur_nid as NodeId),
            cur_nid as NodeId == va_level_to_nid(va.start, cur_level),
            1 <= cur_level <= 4,
            cur_level == va_range_get_guard_level(*va),
            path.len() == 4,
            forall|i| cur_level <= i < 4 ==> path@[i] is ReadLocked,
            forall|i| 0 <= i < cur_level ==> path@[i] is None,
            tree_path.len() == 4 - cur_level,
            tree_path.is_prefix_of(va_range_get_tree_path(*va)),
            va_range_get_tree_path(*va).len() == 5 - va_range_get_guard_level(*va),
            m.pred_cursor_ReadLocking(tree_path),
        ensures
            m.inv(),
            m.inst_id() == pt.inst@.id(),
            NodeHelper::valid_nid(cur_nid as NodeId),
            cur_nid as NodeId == va_level_to_nid(va.start, cur_level),
            1 <= cur_level <= 4,
            cur_level == va_range_get_guard_level(*va),
            path.len() == 4,
            forall|i| cur_level <= i < 4 ==> path@[i] is ReadLocked,
            path@[cur_level - 1] is WriteLocked,
            forall|i| 0 <= i < cur_level - 1 ==> path@[i] is None,
            tree_path.len() == 5 - cur_level,
            tree_path =~= va_range_get_tree_path(*va),
            m.pred_cursor_WriteLocked(tree_path),
    {
        let pa: Paddr =
            atomic_with_ghost!{
            pt.nodes[cur_nid as usize] => load();
            returning res;
            ghost g => {
                assert(g.nid == cur_nid as NodeId);
                if res != INVALID_PADDR {
                    assert(g.tokens is None);
                }
            }
        };

        // TODO: fix this.
        if pa == INVALID_PADDR {
            continue ;
        }
        assert(valid_paddr(pa));
        assert(paddr_is_aligned(pa));

        assert(allocator.usages@[pa_to_fid(pa) as int] is PageTable) by {
            admit();
        };
        let frame: &Frame = allocator.get_pt_frame_from_pa(pa);
        let pt_frame: &PageTableFrame = unsafe { frame.page_table_frame.deref() };
        // How to remove these?
        assert(pt_frame.nid == cur_nid as NodeId) by {
            admit();
        }
        assert(pt_frame.inst@.id() == pt.inst@.id()) by {
            admit();
        }
        assert(pt_frame =~= &manually_drop_unwrap(
            get_union_field::<Frame, ManuallyDrop<PageTableFrame>>(*frame, "page_table_frame"),
        )) by {
            admit();
        };
        assert(pt_frame.wf());

        assert(wf_tree_path(tree_path.push(cur_nid as NodeId))) by {
            admit();
        };
        let res = TransHandler::acquire_write(pt_frame, Tracked(m), Ghost(tree_path));
        let node_token = res.0;
        let write_handle = res.1;
        proof {
            m = res.2.get();
            tree_path = res.3@;
        }
        let (node_token, write_handle) = pt_frame.rw_lock.acquire_write();
        let tracked mut node_token = node_token.get();

        assert(cur_level >= 1);
        path[(cur_level - 1) as usize] = GuardInPath::WriteLocked(write_handle);

        assert(tree_path.is_prefix_of(va_range_get_tree_path(*va))) by {
            admit();
        };

        break ;
    }

    let cursor = Cursor::<'a> { path, level: cur_level, guard_level: cur_level, va: va.start };

    (cursor, Tracked(m))
}

} // verus!
