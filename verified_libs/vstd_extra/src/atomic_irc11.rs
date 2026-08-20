//! Thin adapters for Verus' native IRC11 weak-memory model.
//!
//! This module exposes native subjective thread views, per-location histories,
//! and points-to resources without introducing a second weak-memory model.
pub use vstd::atomic_weak::{
    AtomicHistory, AtomicPointsTo, LoadData, PAtomicWeakBool, PAtomicWeakI8, PAtomicWeakI16,
    PAtomicWeakI32, PAtomicWeakIsize, PAtomicWeakU8, PAtomicWeakU16, PAtomicWeakU32,
    PAtomicWeakUsize, StoreData, UpdateData, fence_acquire, fence_release,
    history_get_contains_timestamp, load_acquire, load_reads_from_history, load_relaxed,
    load_timestamp_in_view, load_view_nondecreasing, store_insert_history, store_relaxed,
    store_release, store_timestamp_in_view, store_view_increasing,
};
#[cfg(target_has_atomic = "64")]
pub use vstd::atomic_weak::{PAtomicWeakI64, PAtomicWeakU64};
pub use vstd::cell::CellId as AtomicId;
use vstd::prelude::*;
pub use vstd::thread_view::{
    AcquireViewSeen, Objective, ReleaseViewSeen, ThreadView, ViewAt, ViewSeen,
};

verus! {

/// Logical timestamp used by one native atomic history.
pub type Timestamp = nat;

/// Compatibility vocabulary for ordering native subjective views.
///
/// `old.spec_le(new)` is notation for the native relation
/// `new.contains(old)` and does not introduce a second view model.
pub trait ThreadViewOrder {
    spec fn spec_le(self, newer: Self) -> bool;

    spec fn view_join(self, other: Self) -> Self;

    proof fn lemma_spec_le_transitive(self, middle: Self, newer: Self)
        requires
            self.spec_le(middle),
            middle.spec_le(newer),
        ensures
            self.spec_le(newer),
    ;

    proof fn lemma_join_left(self, other: Self)
        ensures
            self.spec_le(self.view_join(other)),
    ;

    proof fn lemma_join_right(self, other: Self)
        ensures
            other.spec_le(self.view_join(other)),
    ;
}

impl ThreadViewOrder for ThreadView {
    open spec fn spec_le(self, newer: Self) -> bool {
        newer.contains(self)
    }

    open spec fn view_join(self, other: Self) -> Self {
        self.join(other)
    }

    proof fn lemma_spec_le_transitive(self, middle: Self, newer: Self) {
        ThreadView::contains_trans(newer, middle, self);
    }

    proof fn lemma_join_left(self, other: Self) {
        ThreadView::join_contains(self, other);
    }

    proof fn lemma_join_right(self, other: Self) {
        ThreadView::join_comm(self, other);
        ThreadView::join_contains(other, self);
    }
}

/// Scheduler-owned native subjective view.
///
/// OSTD creates one token for each execution participant, moves it through
/// schedule-in and schedule-out, and borrows it for native weak atomic
/// operations. The wrapper cannot manufacture an arbitrary non-empty view.
pub tracked struct ThreadViewToken {
    view_seen: ViewSeen,
}

impl View for ThreadViewToken {
    type V = ThreadView;

    closed spec fn view(&self) -> ThreadView {
        self.view_seen@
    }
}

impl ThreadViewToken {
    /// Creates the empty view used when registering a task or CPU.
    pub proof fn new() -> (tracked res: Self)
        ensures
            res@ == ThreadView::empty(),
    {
        let tracked view_seen = ViewSeen::new();
        ThreadViewToken { view_seen }
    }

    /// Wraps a native view returned by atomic or synchronization setup.
    pub proof fn from_view_seen(tracked view_seen: ViewSeen) -> (tracked res: Self)
        ensures
            res@ == view_seen@,
    {
        ThreadViewToken { view_seen }
    }

    /// Removes the scheduler wrapper without changing the represented view.
    pub proof fn into_view_seen(tracked self) -> (tracked res: ViewSeen)
        ensures
            res@ == self@,
    {
        self.view_seen
    }

    /// Borrows the native token for one atomic operation.
    pub proof fn tracked_borrow_mut(tracked &mut self) -> (tracked res: &mut ViewSeen)
        ensures
            (*res)@ == old(self)@,
            final(self)@ == (*final(res))@,
    {
        &mut self.view_seen
    }

    /// Imports observations held by another execution participant.
    pub proof fn tracked_join(tracked &mut self, tracked other: &Self)
        ensures
            final(self)@ == old(self)@.join(other@),
    {
        let tracked other_view = other.view_seen;
        let tracked old_view = self.view_seen;
        self.view_seen = old_view.join(other_view);
    }

    /// Imports this stored lower bound into an executing thread's native view.
    pub proof fn tracked_join_into_view_seen(tracked &self, tracked target: &mut ViewSeen)
        ensures
            final(target)@ == old(target)@.join(self@),
    {
        let tracked source = self.view_seen;
        let tracked old_target = *target;
        *target = old_target.join(source);
    }

    /// Publishes an executing thread's current native view into this token.
    pub proof fn tracked_join_view_seen(tracked &mut self, tracked source: &ViewSeen)
        ensures
            final(self)@ == old(self)@.join(source@),
    {
        let tracked source = *source;
        let tracked old_view = self.view_seen;
        self.view_seen = old_view.join(source);
    }

    /// Returns a joined token without mutating the stored source token.
    pub proof fn tracked_joined_view_seen(tracked &self, tracked source: &ViewSeen) -> (tracked res:
        Self)
        ensures
            res@ == self@.join(source@),
    {
        let tracked source = *source;
        let tracked stored = self.view_seen;
        let tracked view_seen = stored.join(source);
        ThreadViewToken { view_seen }
    }
}

} // verus!
