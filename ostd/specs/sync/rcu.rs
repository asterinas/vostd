//! Specification skeleton for RCU traversal safety.
//!
//! This module models the shape of the traversal specification from the RCU
//! relaxed-memory paper:
//!
//! - the base layer provides read-side guards, protected pointers, and retire
//!   permissions;
//! - the traversal layer reasons about link histories (`RcuPointsTo`) and
//!   incoming-link histories (`RcuPointedBy`);
//! - concrete data structures instantiate the traversal trait.
//!
//! The module is intentionally proof-only for now. The executable RCU
//! implementation should later connect its real guard/token state to these
//! abstract ghost tokens.
use super::weak_memory::{History, Msg, WeakAtomicInvariantPredicate, WmView};
use vstd::prelude::*;
use vstd::resource::Loc;

verus! {

pub type LinkIndex = nat;

pub type LinkEdge<T> = (*mut T, LinkIndex);

/// Proof summary for a type-erased RCU callback.
///
/// The executable callback may close over any sized Rust value, but the RCU
/// proof only needs to know which logical object it will reclaim and which
/// grace-period generation retired that object. `domain` identifies the RCU
/// protection domain, and `obj` identifies the reclaimed allocation/object
/// inside that domain.
pub ghost struct RcuCallbackSummary {
    /// The RCU protection domain whose grace period governs this callback.
    pub domain: Loc,
    /// Logical identity of the retired object inside `domain`.
    pub obj: Loc,
    /// The domain-local epoch in which `obj` was retired.
    pub retire_epoch: nat,
}

/// The weak-memory invariant for the root pointer stored in an executable RCU
/// cell.
///
/// The key is the cell's nullability: `true` for `RcuOption`, `false` for
/// `Rcu`.  At this layer we only connect the atomic message history to the
/// public nullability contract. Ownership, read tokens, and reclamation are
/// deliberately modeled by the traversal/reclaim tokens below and will be wired
/// into this predicate in later steps.
pub struct RcuWeakAtomicInv;

pub open spec fn rcu_history_inv<T>(nullable: bool, history: History<*mut T>) -> bool {
    &&& history.len() >= 1
    &&& !nullable ==> forall|i: int|
        0 <= i < history.len() ==> #[trigger] history[i].value.addr() != 0
}

impl<T> WeakAtomicInvariantPredicate<bool, *mut T, ()> for RcuWeakAtomicInv {
    open spec fn atomic_inv(nullable: bool, history: History<*mut T>, _g: ()) -> bool {
        rcu_history_inv(nullable, history)
    }
}

/// Ghost summary paired with the RCU monitor's `is_monitoring` flag.
///
/// `pending[i]` summarizes whether the monitor state represented at flag
/// message `i` has queued callbacks or an active grace period that must still be
/// observed. This is intentionally a summary: the concrete callback vectors
/// live in the monitor state protected by its lock.
pub ghost struct RcuMonitorFlagGhost {
    pub pending: Seq<bool>,
}

impl RcuMonitorFlagGhost {
    pub open spec fn initial() -> Self {
        RcuMonitorFlagGhost { pending: seq![false] }
    }

    pub open spec fn push(self, pending: bool) -> Self {
        RcuMonitorFlagGhost { pending: self.pending.push(pending) }
    }
}

/// Weak-memory invariant for the monitor's fast-path flag.
///
/// The invariant is deliberately one-way: a `false` flag message certifies no
/// pending monitor work for that message's ghost summary. A `true` flag is
/// conservative and may over-approximate pending work.
pub open spec fn rcu_monitor_flag_history_inv(
    history: History<bool>,
    ghost: RcuMonitorFlagGhost,
) -> bool {
    &&& history.len() >= 1
    &&& ghost.pending.len() == history.len()
    &&& forall|i: int|
        0 <= i < history.len() ==> {
            &&& !#[trigger] history[i].value ==> !ghost.pending[i]
        }
}

pub struct RcuMonitorFlagInv;

impl WeakAtomicInvariantPredicate<(), bool, RcuMonitorFlagGhost> for RcuMonitorFlagInv {
    open spec fn atomic_inv(
        _k: (),
        history: History<bool>,
        ghost: RcuMonitorFlagGhost,
    ) -> bool {
        rcu_monitor_flag_history_inv(history, ghost)
    }
}

pub proof fn rcu_monitor_flag_initial_inv()
    ensures
        RcuMonitorFlagInv::atomic_inv(
            (),
            seq![Msg { value: false, view: WmView::empty() }],
            RcuMonitorFlagGhost::initial(),
        ),
{
}

pub proof fn preserve_rcu_monitor_flag_inv_on_push(
    prev: History<bool>,
    next: History<bool>,
    msg: Msg<bool>,
    prev_ghost: RcuMonitorFlagGhost,
    next_ghost: RcuMonitorFlagGhost,
    pending: bool,
)
    requires
        rcu_monitor_flag_history_inv(prev, prev_ghost),
        next == prev.push(msg),
        next_ghost == prev_ghost.push(pending),
        !msg.value ==> !pending,
    ensures
        rcu_monitor_flag_history_inv(next, next_ghost),
{
    assert(next.len() >= 1);
    assert(next_ghost.pending.len() == next.len());
    assert forall|i: int| 0 <= i < next.len() implies {
        &&& !#[trigger] next[i].value ==> !next_ghost.pending[i]
    } by {
        if i == prev.len() {
            assert(next[i] == msg);
            assert(next_ghost.pending[i] == pending);
        } else {
            assert(i < prev.len());
            assert(next[i] == prev[i]);
            assert(next_ghost.pending[i] == prev_ghost.pending[i]);
        }
    };
}

pub proof fn rcu_monitor_flag_false_has_no_pending(
    history: History<bool>,
    ghost: RcuMonitorFlagGhost,
    ts: nat,
)
    requires
        rcu_monitor_flag_history_inv(history, ghost),
        ts < history.len(),
        !history[ts as int].value,
    ensures
        !ghost.pending[ts as int],
{
}

pub proof fn preserve_rcu_history_inv_on_push<T>(
    nullable: bool,
    prev: History<*mut T>,
    next: History<*mut T>,
    msg: Msg<*mut T>,
)
    requires
        rcu_history_inv(nullable, prev),
        next == prev.push(msg),
        nullable || msg.value.addr() != 0,
    ensures
        rcu_history_inv(nullable, next),
{
    assert(next.len() >= 1);
    if !nullable {
        assert forall|i: int| 0 <= i < next.len() implies #[trigger] next[i].value.addr() != 0 by {
            if i == prev.len() {
                assert(next[i] == msg);
            } else {
                assert(i < prev.len());
            }
        };
    }
}

pub proof fn rcu_history_inv_read_nonnull<T>(history: History<*mut T>, ts: nat)
    requires
        rcu_history_inv(false, history),
        ts < history.len(),
    ensures
        history[ts as int].value.addr() != 0,
        !history[ts as int].value.is_null(),
{
    assert(history[ts as int].value.addr() != 0);
}

/// Link view carried by an RCU read-side guard.
///
/// `seen_at(p) = n` means the guard has observed link-history events for source
/// node `p` up to at least `n`. Following a loaded link at index `k` is allowed
/// only when `seen_at(p) <= k`; otherwise the pointer may be too stale.
#[verifier::reject_recursive_types(T)]
pub ghost struct RcuLinkView<T> {
    pub seen: Map<*mut T, LinkIndex>,
}

impl<T> RcuLinkView<T> {
    pub open spec fn empty() -> Self {
        RcuLinkView { seen: Map::empty() }
    }

    pub open spec fn seen_at(self, p: *mut T) -> LinkIndex {
        if self.seen.contains_key(p) {
            self.seen[p]
        } else {
            0nat
        }
    }

    pub open spec fn observe(self, p: *mut T, n: LinkIndex) -> Self {
        RcuLinkView {
            seen: self.seen.insert(
                p,
                if self.seen_at(p) <= n {
                    n
                } else {
                    self.seen_at(p)
                },
            ),
        }
    }
}

/// Paper-style `SeenRemoved(D, LV)`.
///
/// `removed` is the set `D` observed by the guard; `link_view` is `LV`.
/// A dead incoming edge is either from a removed predecessor or overwritten by a
/// later observed link event.
#[verifier::reject_recursive_types(T)]
pub ghost struct RcuSeenRemoved<T> {
    pub removed: Set<*mut T>,
    pub link_view: RcuLinkView<T>,
}

impl<T> RcuSeenRemoved<T> {
    pub open spec fn empty() -> Self {
        RcuSeenRemoved { removed: Set::empty(), link_view: RcuLinkView::empty() }
    }

    pub open spec fn seen_at(self, p: *mut T) -> LinkIndex {
        self.link_view.seen_at(p)
    }

    pub open spec fn dead_edge(self, edge: LinkEdge<T>) -> bool {
        self.removed.contains(edge.0) || self.seen_at(edge.0) > edge.1
    }
}

/// Authoritative ghost handle for one RCU protection domain.
///
/// The concrete implementation owns this token in its invariant. We keep the
/// fields private so clients cannot manufacture domain authority.
pub tracked struct RcuDomainAuth {
    ghost id: Loc,
}

impl RcuDomainAuth {
    pub closed spec fn id(self) -> Loc {
        self.id
    }
}

/// Logical identity of one RCU-managed object.
///
/// Traversal proofs are typed and pointer-based (`*mut T`), while the callback
/// monitor stores type-erased callbacks. This token bridges the two worlds: it
/// says that `obj` is the logical identity of `ptr` inside `domain`.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuObjectId<T> {
    ghost domain: Loc,
    ghost obj: Loc,
    ghost ptr: *mut T,
}

impl<T> RcuObjectId<T> {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn obj(self) -> Loc {
        self.obj
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.ptr
    }
}

/// Low-level base retire permission.
///
/// This is the paper's `BaseRetirePerm`. By itself it is not enough to reclaim;
/// it must be combined with a `SeenRemoved` observation for the retired object.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuBaseRetirePerm<T> {
    ghost domain: Loc,
    ghost ptr: *mut T,
}

impl<T> RcuBaseRetirePerm<T> {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.ptr
    }
}

/// High-level retire permission.
///
/// This corresponds to `RetirePerm(l, a) = BaseRetirePerm(l, a) *
/// exists D LV. SeenRemoved(D, LV) * a in D`.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRetirePerm<T> {
    ghost domain: Loc,
    ghost ptr: *mut T,
    ghost seen_removed: RcuSeenRemoved<T>,
}

impl<T> RcuRetirePerm<T> {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.ptr
    }

    pub closed spec fn seen_removed(self) -> RcuSeenRemoved<T> {
        self.seen_removed
    }

    pub open spec fn ready_to_reclaim(self) -> bool {
        self.seen_removed().removed.contains(self.ptr())
    }
}

/// Lift a base retire permission once the caller has observed the object in the
/// removed set.
pub proof fn lift_retire_perm<T>(
    tracked base: RcuBaseRetirePerm<T>,
    seen_removed: RcuSeenRemoved<T>,
) -> (tracked perm: RcuRetirePerm<T>)
    requires
        seen_removed.removed.contains(base.ptr()),
    ensures
        perm.domain() == base.domain(),
        perm.ptr() == base.ptr(),
        perm.seen_removed() == seen_removed,
        perm.ready_to_reclaim(),
{
    RcuRetirePerm { domain: base.domain(), ptr: base.ptr(), seen_removed }
}

/// Non-generic proof certificate carried across the type-erasure boundary.
///
/// A certificate can only be produced from a typed traversal retire permission,
/// but after that point the monitor only needs the erased callback summary.
pub tracked struct RcuCallbackSafety {
    ghost summary: RcuCallbackSummary,
}

impl View for RcuCallbackSafety {
    type V = RcuCallbackSummary;

    closed spec fn view(&self) -> RcuCallbackSummary {
        self.summary
    }
}

pub open spec fn callback_safety_from_traversal<T>(
    cert: RcuCallbackSafety,
    object: RcuObjectId<T>,
    retire_epoch: nat,
) -> bool {
    &&& cert@.domain == object.domain()
    &&& cert@.obj == object.obj()
    &&& cert@.retire_epoch == retire_epoch
}

/// Consume a typed traversal retire permission and compress it into the
/// non-generic summary needed by the type-erased callback monitor.
pub proof fn certify_callback_from_retire_perm<T>(
    tracked object: &RcuObjectId<T>,
    tracked retire: RcuRetirePerm<T>,
    retire_epoch: nat,
) -> (tracked cert: RcuCallbackSafety)
    requires
        object.domain() == retire.domain(),
        object.ptr() == retire.ptr(),
        retire.ready_to_reclaim(),
    ensures
        cert@ == (RcuCallbackSummary {
            domain: retire.domain(),
            obj: object.obj(),
            retire_epoch,
        }),
        callback_safety_from_traversal(cert, *object, retire_epoch),
{
    RcuCallbackSafety {
        summary: RcuCallbackSummary {
            domain: retire.domain(),
            obj: object.obj(),
            retire_epoch,
        },
    }
}

/// Read-side guard token for one critical section.
///
/// This is the traversal-level guard: it includes the base guard protection and
/// the `SeenRemoved(D, LV)` observation used to rule out stale links.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuReadGuardToken<T> {
    ghost domain: Loc,
    ghost seen_removed: RcuSeenRemoved<T>,
}

impl<T> RcuReadGuardToken<T> {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn seen_removed(self) -> RcuSeenRemoved<T> {
        self.seen_removed
    }

    pub closed spec fn link_view(self) -> RcuLinkView<T> {
        self.seen_removed().link_view
    }

    pub open spec fn seen_at(self, p: *mut T) -> LinkIndex {
        self.seen_removed().seen_at(p)
    }

    pub open spec fn is_for(self, domain: RcuDomainAuth) -> bool {
        self.domain() == domain.id()
    }

    pub open spec fn can_protect(self, p: *mut T) -> bool {
        !self.seen_removed().removed.contains(p)
    }
}

/// A pointer protected by a live read-side guard.
///
/// It records the same `SeenRemoved` snapshot as the guard. This lets traversal
/// proofs preserve the fact that the protected pointer is not in the guard's
/// removed set.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuProtectedPtr<T> {
    ghost domain: Loc,
    ghost ptr: *mut T,
    ghost seen_removed: RcuSeenRemoved<T>,
}

impl<T> RcuProtectedPtr<T> {
    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn ptr(self) -> *mut T {
        self.ptr
    }

    pub closed spec fn seen_removed(self) -> RcuSeenRemoved<T> {
        self.seen_removed
    }

    pub open spec fn protected_by(self, guard: RcuReadGuardToken<T>) -> bool {
        &&& self.domain() == guard.domain()
        &&& self.seen_removed() == guard.seen_removed()
        &&& !self.seen_removed().removed.contains(self.ptr())
    }
}

/// Traversal specification for an RCU-protected data structure.
///
/// `link_inv(from, n, to, g)` is the client-facing analogue of a
/// `RcuPointsTo(from, ...)` snapshot containing the `n`th link event from
/// `from` to `to`. `seen_removed_sound` is the client-facing analogue of the
/// `RcuPointedBy`/`SeenRemoved` invariant for partially ordered link histories.
pub trait RcuTraversalSafety: Sized {
    type Node;

    type Ghost;

    spec fn root_inv(p: *mut Self::Node, g: Self::Ghost) -> bool;

    spec fn node_inv(p: *mut Self::Node, g: Self::Ghost) -> bool;

    spec fn link_inv(
        from: *mut Self::Node,
        n: LinkIndex,
        to: *mut Self::Node,
        g: Self::Ghost,
    ) -> bool;

    spec fn seen_removed_sound(seen_removed: RcuSeenRemoved<Self::Node>, g: Self::Ghost) -> bool;

    proof fn root_is_node_inv(p: *mut Self::Node, g: Self::Ghost)
        requires
            Self::root_inv(p, g),
        ensures
            Self::node_inv(p, g),
    ;

    proof fn link_preserves_protection(
        from: *mut Self::Node,
        n: LinkIndex,
        to: *mut Self::Node,
        seen_removed: RcuSeenRemoved<Self::Node>,
        g: Self::Ghost,
    )
        requires
            Self::node_inv(from, g),
            Self::link_inv(from, n, to, g),
            Self::seen_removed_sound(seen_removed, g),
            !seen_removed.removed.contains(from),
            seen_removed.seen_at(from) <= n,
        ensures
            Self::node_inv(to, g),
            !seen_removed.removed.contains(to),
    ;
}

/// Protect a freshly acquired root pointer.
pub proof fn protect_root<S: RcuTraversalSafety>(
    tracked domain: &RcuDomainAuth,
    tracked guard: &RcuReadGuardToken<S::Node>,
    p: *mut S::Node,
    g: S::Ghost,
) -> (tracked root: RcuProtectedPtr<S::Node>)
    requires
        guard.is_for(*domain),
        guard.can_protect(p),
        S::root_inv(p, g),
    ensures
        root.ptr() == p,
        root.domain() == domain.id(),
        root.protected_by(*guard),
        S::node_inv(p, g),
{
    S::root_is_node_inv(p, g);
    RcuProtectedPtr { domain: domain.id(), ptr: p, seen_removed: guard.seen_removed() }
}

/// Protect a child reached by following a non-stale link-history event.
pub proof fn protect_link<S: RcuTraversalSafety>(
    tracked guard: &RcuReadGuardToken<S::Node>,
    tracked from: &RcuProtectedPtr<S::Node>,
    n: LinkIndex,
    to: *mut S::Node,
    g: S::Ghost,
) -> (tracked to_protected: RcuProtectedPtr<S::Node>)
    requires
        from.protected_by(*guard),
        S::node_inv(from.ptr(), g),
        S::link_inv(from.ptr(), n, to, g),
        S::seen_removed_sound(guard.seen_removed(), g),
        guard.seen_at(from.ptr()) <= n,
    ensures
        to_protected.ptr() == to,
        to_protected.domain() == from.domain(),
        to_protected.protected_by(*guard),
        S::node_inv(to, g),
{
    S::link_preserves_protection(from.ptr(), n, to, guard.seen_removed(), g);
    RcuProtectedPtr { domain: from.domain(), ptr: to, seen_removed: guard.seen_removed() }
}

/// Minimal ghost-only node used to demonstrate the traversal contract.
pub struct LinkedListNode;

/// Paper-style ghost state for a linked list.
///
/// `successors[p]` is the successor history for `p`, corresponding to
/// `RcuPointsTo(p, s)`.
///
/// `incoming_all[p]` is the set of all incoming edges that have ever pointed to
/// `p`, corresponding to the authoritative incoming set in `RcuPointedBy(p, B)`.
///
/// `current_incoming[p]` is the current incoming set `B`. It is not required for
/// the simple one-step traversal proof below, but keeping it in the ghost state
/// makes the example match the paper's predicate shape.
pub ghost struct LinkedListGhost {
    pub root: *mut LinkedListNode,
    pub successors: Map<*mut LinkedListNode, Seq<Option<*mut LinkedListNode>>>,
    pub incoming_all: Map<*mut LinkedListNode, Set<LinkEdge<LinkedListNode>>>,
    pub current_incoming: Map<*mut LinkedListNode, Set<LinkEdge<LinkedListNode>>>,
}

pub struct LinkedListTraversalSpec;

impl RcuTraversalSafety for LinkedListTraversalSpec {
    type Node = LinkedListNode;

    type Ghost = LinkedListGhost;

    open spec fn root_inv(p: *mut LinkedListNode, g: LinkedListGhost) -> bool {
        &&& p == g.root
        &&& g.successors.contains_key(p)
        &&& g.incoming_all.contains_key(p)
    }

    open spec fn node_inv(p: *mut LinkedListNode, g: LinkedListGhost) -> bool {
        &&& g.successors.contains_key(p)
        &&& g.incoming_all.contains_key(p)
    }

    open spec fn link_inv(
        from: *mut LinkedListNode,
        n: LinkIndex,
        to: *mut LinkedListNode,
        g: LinkedListGhost,
    ) -> bool {
        &&& g.successors.contains_key(from)
        &&& n < g.successors[from].len()
        &&& g.successors[from][n as int] == Some(to)
        &&& g.successors.contains_key(to)
        &&& g.incoming_all.contains_key(to)
        &&& g.incoming_all[to].contains((from, n))
    }

    open spec fn seen_removed_sound(
        seen_removed: RcuSeenRemoved<LinkedListNode>,
        g: LinkedListGhost,
    ) -> bool {
        forall|to: *mut LinkedListNode| #[trigger]
            seen_removed.removed.contains(to) ==> {
                &&& g.incoming_all.contains_key(to)
                &&& forall|edge: LinkEdge<LinkedListNode>| #[trigger]
                    g.incoming_all[to].contains(edge) ==> seen_removed.dead_edge(edge)
            }
    }

    proof fn root_is_node_inv(p: *mut LinkedListNode, g: LinkedListGhost) {
    }

    proof fn link_preserves_protection(
        from: *mut LinkedListNode,
        n: LinkIndex,
        to: *mut LinkedListNode,
        seen_removed: RcuSeenRemoved<LinkedListNode>,
        g: LinkedListGhost,
    ) {
        if seen_removed.removed.contains(to) {
            assert(g.incoming_all[to].contains((from, n)));
            assert(seen_removed.dead_edge((from, n)));
            assert(false);
        }
    }
}

/// Example: after protecting the root, following a non-stale successor-history
/// event protects the next node under the same guard.
pub proof fn linked_list_protect_next_example(
    tracked domain: &RcuDomainAuth,
    tracked guard: &RcuReadGuardToken<LinkedListNode>,
    root: *mut LinkedListNode,
    n: LinkIndex,
    next: *mut LinkedListNode,
    g: LinkedListGhost,
) -> (tracked next_protected: RcuProtectedPtr<LinkedListNode>)
    requires
        guard.is_for(*domain),
        guard.can_protect(root),
        LinkedListTraversalSpec::root_inv(root, g),
        LinkedListTraversalSpec::link_inv(root, n, next, g),
        LinkedListTraversalSpec::seen_removed_sound(guard.seen_removed(), g),
        guard.seen_at(root) <= n,
    ensures
        next_protected.ptr() == next,
        next_protected.domain() == domain.id(),
        next_protected.protected_by(*guard),
        LinkedListTraversalSpec::node_inv(next, g),
{
    let tracked root_protected = protect_root::<LinkedListTraversalSpec>(domain, guard, root, g);
    protect_link::<LinkedListTraversalSpec>(guard, &root_protected, n, next, g)
}

} // verus!
