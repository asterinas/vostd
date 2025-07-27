use vstd::prelude::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::super::{common::*, types::*, cpu::*};
use super::PageTableGuard;

verus! {

/// Trusted properties of stray flag.
/// We can't prove this by Verus since the logical complexity.
/// This is correct by following reasons:
/// 1. The stray flag will be changed from false to true
///     iff. the node is deleted from the page table.
/// 2. The delete operation should be done through a Cursor.
/// 3. The sub tree root of a Cursor cannot be deleted.
/// 4. Guarded nodes in a Cursor are exclusively owned.
#[verifier::external_body]
pub proof fn lemma_in_protocol_guarded_parent_implies_child_is_pt_node(
    parent_guard: PageTableGuard,
    child_guard: PageTableGuard,
    m: LockProtocolModel,
)
    requires
        parent_guard.wf(),
        parent_guard.guard->Some_0.stray_perm@.value() == false,
        child_guard.wf(),
        NodeHelper::is_child(parent_guard.nid(), child_guard.nid()),
        parent_guard.inst_id() == child_guard.inst_id(),
        m.inv(),
        m.inst_id() == parent_guard.inst_id(),
        // The creation of the cursor has not been completed yet.
        m.state() is Locking,
        m.node_is_locked(child_guard.nid()),
    ensures
        child_guard.guard->Some_0.stray_perm@.value() == false,
{
}

/// Trusted properties of stray flag.
/// We can't prove this by Verus since the logical complexity.
/// This is correct by following reasons:
/// The child is exclusively owned, since the parent is guarded.
#[verifier::external_body]
pub proof fn lemma_guarded_parent_implies_allocated_child_is_pt_node(
    parent_guard: PageTableGuard,
    new_allocated_child_guard: PageTableGuard,
)
    requires
        parent_guard.wf(),
        parent_guard.guard->Some_0.stray_perm@.value() == false,
        new_allocated_child_guard.wf(),
        NodeHelper::is_child(parent_guard.nid(), new_allocated_child_guard.nid()),
    ensures
        new_allocated_child_guard.guard->Some_0.stray_perm@.value() == false,
{
}

} // verus!
