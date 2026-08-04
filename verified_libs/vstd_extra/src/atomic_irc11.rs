//! Adapters for Verus' native IRC11 weak-memory model.
//!
//! This module is intentionally thin. It exposes the native subjective thread
//! views, per-location histories, and points-to resources without translating
//! them into the older `atomic_weak` model. In particular, native histories are
//! finite maps with abstract natural-number timestamps rather than contiguous
//! sequences.
//!
//! Verus does not yet provide a weak-memory `AtomicPtr`. This module therefore
//! supplies only that executable wrapper, specified directly in terms of
//! [`AtomicPointsTo`] and the native load/store/update relations.
use core::sync::atomic::{AtomicPtr, Ordering};

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
/// `old.spec_le(new)` is only notation for the native relation
/// `new.contains(old)`; it introduces no second view model.
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
/// OSTD should create one token when it registers an execution participant,
/// move that token through schedule-in/schedule-out, and borrow it for native
/// weak atomic operations. The wrapper deliberately exposes no operation that
/// can manufacture an arbitrary non-empty view.
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
    ///
    /// `ViewSeen` is persistent knowledge, so Verus' native model permits
    /// copying it before the join. The source token consequently remains
    /// available to its CPU or task owner.
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

/// IRC11 wrapper around Rust's sized-pointer atomic.
///
/// The permission describes only the atomic location's modification history;
/// ownership of the pointee remains in the client invariant.
#[repr(transparent)]
#[verifier::accept_recursive_types(T)]
#[verifier::external_body]
pub struct PAtomicWeakPtr<T> {
    value: AtomicPtr<T>,
}

impl<T> PAtomicWeakPtr<T> {
    pub uninterp spec fn loc(&self) -> AtomicId;

    #[inline(always)]
    #[verifier::external_body]
    pub const fn new(value: *mut T) -> ((atomic, points_to, view, timestamp): (
        Self,
        Tracked<AtomicPointsTo<*mut T>>,
        Tracked<ViewSeen>,
        Ghost<nat>,
    ))
        ensures
            atomic.loc() == points_to@.loc(),
            points_to@.hist().is_singleton(timestamp@, (value, view@@)),
            points_to@.get_timestamp(view@@) == Some(timestamp@),
    {
        (
            Self { value: AtomicPtr::new(value) },
            Tracked::assume_new(),
            Tracked::assume_new(),
            Ghost::assume_new(),
        )
    }

    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load(
        &self,
        order: Ordering,
        Tracked(view): Tracked<&mut ViewSeen>,
        Tracked(points_to): Tracked<&AtomicPointsTo<*mut T>>,
    ) -> ((value, acquire_view, load): (*mut T, Tracked<AcquireViewSeen>, Ghost<LoadData>))
        requires
            self.loc() == points_to.loc(),
            order matches Ordering::Acquire
            || order matches Ordering::Relaxed,
        ensures
            match order {
                Ordering::Acquire => load_acquire(
                    *points_to,
                    old(view)@,
                    final(view)@,
                    value,
                    load@.timestamp,
                    load@.message_view,
                ),
                Ordering::Relaxed => load_relaxed(
                    *points_to,
                    old(view)@,
                    final(view)@,
                    acquire_view@@,
                    value,
                    load@.timestamp,
                    load@.message_view,
                ),
            },
        opens_invariants none
        no_unwind
    {
        (self.value.load(order), Tracked::assume_new(), Ghost::assume_new())
    }

    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store(
        &self,
        value: *mut T,
        order: Ordering,
        Tracked(view): Tracked<&mut ViewSeen>,
        Tracked(release_view): Tracked<ReleaseViewSeen>,
        Tracked(points_to): Tracked<&mut AtomicPointsTo<*mut T>>,
    ) -> (store: Ghost<StoreData>)
        requires
            self.loc() == old(points_to).loc(),
            order matches Ordering::Release
            || order matches Ordering::Relaxed,
        ensures
            forall|observed_view: ThreadView| #[trigger]
                old(points_to).get_timestamp(observed_view) == final(points_to).get_timestamp(
                    observed_view,
                ),
            match order {
                Ordering::Release => store_release(
                    *old(points_to),
                    *final(points_to),
                    old(view)@,
                    final(view)@,
                    value,
                    store@.timestamp,
                    store@.message_view,
                ),
                Ordering::Relaxed => store_relaxed(
                    *old(points_to),
                    *final(points_to),
                    old(view)@,
                    final(view)@,
                    release_view@,
                    value,
                    store@.timestamp,
                    store@.message_view,
                ),
            },
        opens_invariants none
        no_unwind
    {
        self.value.store(value, order);
        Ghost::assume_new()
    }

    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn compare_exchange(
        &self,
        current: *mut T,
        new: *mut T,
        success: Ordering,
        failure: Ordering,
        Tracked(view): Tracked<&mut ViewSeen>,
        Tracked(release_view): Tracked<ReleaseViewSeen>,
        Tracked(points_to): Tracked<&mut AtomicPointsTo<*mut T>>,
    ) -> ((result, acquire_view, update): (
        Result<*mut T, *mut T>,
        Tracked<AcquireViewSeen>,
        Ghost<UpdateData>,
    ))
        requires
            self.loc() == old(points_to).loc(),
            success matches Ordering::AcqRel
            || success matches Ordering::Acquire
            || success matches Ordering::Release
            || success matches Ordering::Relaxed,
            failure matches Ordering::Acquire
            || failure matches Ordering::Relaxed,
        ensures
            result is Ok ==> old(points_to).hist().is_max_timestamp(update@.load_timestamp),
            forall|observed_view: ThreadView| #[trigger]
                old(points_to).get_timestamp(observed_view) == final(points_to).get_timestamp(
                    observed_view,
                ),
            match result {
                Ok(value) => {
                    &&& current.addr() == value.addr()
                    &&& update@.store_message_view.contains_strict(update@.load_message_view)
                    &&& match success {
                        Ordering::AcqRel => {
                            &&& load_acquire(
                                *old(points_to),
                                old(view)@,
                                update@.intermediate_thread_view,
                                value,
                                update@.load_timestamp,
                                update@.load_message_view,
                            )
                            &&& store_release(
                                *old(points_to),
                                *final(points_to),
                                update@.intermediate_thread_view,
                                final(view)@,
                                new,
                                update@.load_timestamp + 1,
                                update@.store_message_view,
                            )
                        },
                        Ordering::Acquire => {
                            &&& load_acquire(
                                *old(points_to),
                                old(view)@,
                                update@.intermediate_thread_view,
                                value,
                                update@.load_timestamp,
                                update@.load_message_view,
                            )
                            &&& store_relaxed(
                                *old(points_to),
                                *final(points_to),
                                update@.intermediate_thread_view,
                                final(view)@,
                                release_view@,
                                new,
                                update@.load_timestamp + 1,
                                update@.store_message_view,
                            )
                        },
                        Ordering::Release => {
                            &&& load_relaxed(
                                *old(points_to),
                                old(view)@,
                                update@.intermediate_thread_view,
                                acquire_view@@,
                                value,
                                update@.load_timestamp,
                                update@.load_message_view,
                            )
                            &&& store_release(
                                *old(points_to),
                                *final(points_to),
                                update@.intermediate_thread_view,
                                final(view)@,
                                new,
                                update@.load_timestamp + 1,
                                update@.store_message_view,
                            )
                        },
                        Ordering::Relaxed => {
                            &&& load_relaxed(
                                *old(points_to),
                                old(view)@,
                                update@.intermediate_thread_view,
                                acquire_view@@,
                                value,
                                update@.load_timestamp,
                                update@.load_message_view,
                            )
                            &&& store_relaxed(
                                *old(points_to),
                                *final(points_to),
                                update@.intermediate_thread_view,
                                final(view)@,
                                release_view@,
                                new,
                                update@.load_timestamp + 1,
                                update@.store_message_view,
                            )
                        },
                    }
                },
                Err(value) => {
                    &&& current.addr() != value.addr()
                    &&& *final(points_to) == *old(points_to)
                    &&& match failure {
                        Ordering::Acquire => load_acquire(
                            *old(points_to),
                            old(view)@,
                            final(view)@,
                            value,
                            update@.load_timestamp,
                            update@.load_message_view,
                        ),
                        Ordering::Relaxed => load_relaxed(
                            *old(points_to),
                            old(view)@,
                            final(view)@,
                            acquire_view@@,
                            value,
                            update@.load_timestamp,
                            update@.load_message_view,
                        ),
                    }
                },
            },
        opens_invariants none
        no_unwind
    {
        (
            self.value.compare_exchange(current, new, success, failure),
            Tracked::assume_new(),
            Ghost::assume_new(),
        )
    }

    /// Release swap reads the latest modification and immediately appends its
    /// replacement in the same modification order.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn swap_release(
        &self,
        value: *mut T,
        Tracked(view): Tracked<&mut ViewSeen>,
        Tracked(points_to): Tracked<&mut AtomicPointsTo<*mut T>>,
    ) -> ((old_value, acquire_view, swap): (*mut T, Tracked<AcquireViewSeen>, Ghost<UpdateData>))
        requires
            self.loc() == old(points_to).loc(),
        ensures
            old(points_to).hist().is_max_timestamp(swap@.load_timestamp),
            forall|observed_view: ThreadView| #[trigger]
                old(points_to).get_timestamp(observed_view) == final(points_to).get_timestamp(
                    observed_view,
                ),
            load_relaxed(
                *old(points_to),
                old(view)@,
                swap@.intermediate_thread_view,
                acquire_view@@,
                old_value,
                swap@.load_timestamp,
                swap@.load_message_view,
            ),
            store_release(
                *old(points_to),
                *final(points_to),
                swap@.intermediate_thread_view,
                final(view)@,
                value,
                swap@.load_timestamp + 1,
                swap@.store_message_view,
            ),
        opens_invariants none
        no_unwind
    {
        (self.value.swap(value, Ordering::Release), Tracked::assume_new(), Ghost::assume_new())
    }
}

/// The partial order used for weak-memory views, written from old to new.
pub open spec fn view_le(old_view: ThreadView, new_view: ThreadView) -> bool {
    new_view.contains(old_view)
}

/// View joins monotonically include both operands.
pub proof fn lemma_join_upper_bound(left: ThreadView, right: ThreadView)
    ensures
        view_le(left, left.join(right)),
        view_le(right, left.join(right)),
{
    ThreadView::join_contains(left, right);
    ThreadView::join_comm(left, right);
    ThreadView::join_contains(right, left);
}

// These executable examples are part of verification. They ensure that the
// native tokens can be threaded through the operation shapes needed by OSTD.
fn test_native_acquire_load() {
    let (atomic, Tracked(pt), Tracked(mut view), Ghost(initial_ts)) = PAtomicWeakUsize::new(7);
    let ghost old_view = view@;
    assert(pt.hist().is_singleton(initial_ts, (7, old_view)));
    let (value, Tracked(_acquire_view), Ghost(load)) = atomic.load(
        Ordering::Acquire,
        Tracked(&mut view),
        Tracked(&pt),
    );

    proof {
        assert(pt.hist().get(load.timestamp) == Some((value, load.message_view)));
        history_get_contains_timestamp(pt.hist(), load.timestamp);
        assert(pt.hist().contains_timestamp(load.timestamp));
        assert(load.timestamp == initial_ts);
        assert(pt.hist().get(load.timestamp) == Some((7, old_view)));
        assert(value == 7);
        assert(view@.contains(old_view));
        assert(pt.get_timestamp(view@) == Some(load.timestamp));
    }
}

fn test_native_release_store() {
    let (atomic, Tracked(mut pt), Tracked(mut view), Ghost(_initial_ts)) = PAtomicWeakBool::new(
        false,
    );
    proof_decl! {
        let tracked release_view = ReleaseViewSeen::new();
    }
    let ghost old_history = pt.hist();
    let Ghost(store) = atomic.store(
        true,
        Ordering::Release,
        Tracked(&mut view),
        Tracked(release_view),
        Tracked(&mut pt),
    );

    proof {
        assert(pt.hist() == old_history.insert(store.timestamp, true, store.message_view));
        assert(pt.get_timestamp(view@) == Some(store.timestamp));
        assert(store.message_view == view@);
    }
}

fn test_native_compare_exchange() {
    let (atomic, Tracked(mut pt), Tracked(mut view), Ghost(_initial_ts)) = PAtomicWeakUsize::new(0);
    proof_decl! {
        let tracked release_view = ReleaseViewSeen::new();
    }
    let (result, Tracked(_acquire_view), Ghost(update)) = atomic.compare_exchange(
        0,
        1,
        Ordering::AcqRel,
        Ordering::Acquire,
        Tracked(&mut view),
        Tracked(release_view),
        Tracked(&mut pt),
    );

    proof {
        match result {
            Ok(value) => {
                assert(value == 0);
                assert(pt.hist().get_value(update.load_timestamp + 1) == Some(1));
            },
            Err(value) => {
                assert(value != 0);
            },
        }
    }
}

fn test_native_pointer_operations() {
    let first = core::ptr::null_mut::<usize>();
    let second = core::ptr::null_mut::<usize>();
    let (atomic, Tracked(mut points_to), Tracked(mut view), Ghost(_initial_ts)) =
        PAtomicWeakPtr::new(first);

    let (_loaded, Tracked(_acquire_view), Ghost(_load)) = atomic.load(
        Ordering::Acquire,
        Tracked(&mut view),
        Tracked(&points_to),
    );

    proof_decl! {
        let tracked release_view = ReleaseViewSeen::new();
    }
    let Ghost(_store) = atomic.store(
        second,
        Ordering::Release,
        Tracked(&mut view),
        Tracked(release_view),
        Tracked(&mut points_to),
    );

    proof_decl! {
        let tracked release_view = ReleaseViewSeen::new();
    }
    let (_result, Tracked(_acquire_view), Ghost(_update)) = atomic.compare_exchange(
        second,
        first,
        Ordering::AcqRel,
        Ordering::Acquire,
        Tracked(&mut view),
        Tracked(release_view),
        Tracked(&mut points_to),
    );

    let (_old, Tracked(_acquire_view), Ghost(swap)) = atomic.swap_release(
        second,
        Tracked(&mut view),
        Tracked(&mut points_to),
    );
    proof {
        assert(points_to.get_timestamp(view@) == Some(swap.load_timestamp + 1));
    }
}

fn test_scheduler_owned_view_token() {
    let (atomic, Tracked(mut points_to), Tracked(view_seen), Ghost(initial_ts)) =
        PAtomicWeakUsize::new(0);
    proof_decl! {
        let tracked mut token = ThreadViewToken::from_view_seen(view_seen);
    }
    let ghost initial_view = token@;
    proof {
        assert(points_to.hist().is_singleton(initial_ts, (0, initial_view)));
    }

    let (value, Tracked(_acquire_view), Ghost(load)) = atomic.load(
        Ordering::Acquire,
        Tracked(token.tracked_borrow_mut()),
        Tracked(&points_to),
    );
    proof {
        assert(points_to.get_timestamp(token@) == Some(load.timestamp));
        assert(points_to.hist().get(load.timestamp) == Some((value, load.message_view)));
        history_get_contains_timestamp(points_to.hist(), load.timestamp);
        assert(load.timestamp == initial_ts);
        assert(points_to.hist().get(load.timestamp) == Some((0, initial_view)));
        assert(value == 0);
    }

    proof_decl! {
        let tracked release_view = ReleaseViewSeen::new();
    }
    let Ghost(store) = atomic.store(
        1,
        Ordering::Release,
        Tracked(token.tracked_borrow_mut()),
        Tracked(release_view),
        Tracked(&mut points_to),
    );
    proof {
        assert(points_to.get_timestamp(token@) == Some(store.timestamp));
        assert(points_to.hist().get_value(store.timestamp) == Some(1));
    }

    proof_decl! {
        let tracked cpu_token = ThreadViewToken::new();
    }
    proof {
        let ghost before = token@;
        token.tracked_join(&cpu_token);
        assert(token@ == before.join(cpu_token@));
        ThreadView::join_contains(before, cpu_token@);
        assert(token@.contains(before));
    }
}

} // verus!
