// SPDX-License-Identifier: MPL-2.0
//! Native release/acquire handoff for the RCU monitor's objective resources.
//!
//! # Verified Properties
//! Successful CAS imports the last unlock's native message view before exposing
//! protected resources. Unlock requires the caller's actual view to cover their
//! publication obligations. No subjective token is stored inside the invariant.
//! The guard is linear and must be explicitly released; this is not IRQ masking.
use vstd::{
    invariant::{AtomicInvariant, InvariantPredicate},
    modes::tracked_static_ref,
    prelude::*,
    resource::{
        Loc,
        ghost_var::{GhostVar, GhostVarAuth},
    },
};
use vstd_extra::{
    atomic_irc11::{
        AtomicId, AtomicPointsTo, Objective, PAtomicWeakPtr, ReleaseViewSeen, ThreadView, ViewSeen,
    },
    external::NonNullAdditionalFns,
};

use core::{marker::PhantomData, sync::atomic::Ordering};

verus! {

broadcast use {
    vstd::atomic_weak::group_view_history,
    vstd_extra::external::nonnull::group_nonull_axioms,
};

/// Interpretation and observations required by the resource protected by a lock.
pub trait WeakLockPredicate<R> {
    type Key;

    /// Interprets the protected resource under this lock's fixed client key.
    spec fn inv(key: Self::Key, resource: R) -> bool;

    /// Observations that must be imported before exposing this resource.
    spec fn required_view(resource: R) -> ThreadView;
}

tracked struct LockState<R> {
    points_to: AtomicPointsTo<*mut u8>,
    owner: GhostVarAuth<(nat, ThreadView)>,
    available: Option<(R, GhostVar<(nat, ThreadView)>)>,
}

// SAFETY: native atomic ownership, objective RA tokens, and R: Objective only.
// ThreadView is an inert snapshot; no ViewSeen is stored or fabricated.
unsafe impl<R: Objective> Objective for LockState<R> {

}

ghost struct LockPredicate<P> {
    marker: PhantomData<P>,
}

impl<R: Objective, P: WeakLockPredicate<R>> InvariantPredicate<
    (AtomicId, Loc, P::Key),
    LockState<R>,
> for LockPredicate<P> {
    closed spec fn inv(key: (AtomicId, Loc, P::Key), state: LockState<R>) -> bool {
        &&& state.points_to.loc() == key.0
        &&& state.owner.id() == key.1
        &&& state.points_to.hist().is_max_timestamp(state.owner@.0)
        &&& state.points_to.get_timestamp(state.owner@.1) == Some(state.owner@.0)
        &&& match state.available {
            Some((resource, token)) => {
                &&& state.points_to.hist().value(state.owner@.0).addr() == 0
                &&& token.id() == key.1
                &&& P::inv(key.2, resource)
                &&& state.points_to.hist().thread_view(state.owner@.0).contains(
                    P::required_view(resource),
                )
            },
            None => state.points_to.hist().value(state.owner@.0).addr() != 0,
        }
    }
}

type LockInvariant<R, P> = AtomicInvariant<
    (AtomicId, Loc, <P as WeakLockPredicate<R>>::Key),
    LockState<R>,
    LockPredicate<P>,
>;

/// Protected resource checked out by a successful native acquire operation.
pub tracked struct WeakLockGuard<R> {
    resource: R,
    token: GhostVar<(nat, ThreadView)>,
}

impl<R> WeakLockGuard<R> {
    /// Logical protected resource currently checked out.
    pub closed spec fn resource(self) -> R {
        self.resource
    }

    /// Identity of the paired ownership authority.
    pub closed spec fn lock(self) -> Loc {
        self.token.id()
    }

    /// Native view obtained when this guard acquired the lock.
    pub closed spec fn acquired_view(self) -> ThreadView {
        self.token@.1
    }

    /// Borrows the checked-out resource without transferring its ownership.
    pub proof fn tracked_resource(tracked &self) -> (tracked res: &R)
        ensures
            *res == self.resource(),
    {
        &self.resource
    }

    /// Mutably borrows the resource while preserving the lock identity and acquired view.
    pub proof fn tracked_resource_mut(tracked &mut self) -> (tracked res: &mut R)
        ensures
            *res == old(self).resource(),
            *final(res) == final(self).resource(),
            final(self).lock() == old(self).lock(),
            final(self).acquired_view() == old(self).acquired_view(),
    {
        &mut self.resource
    }
}

/* A pointer-sized null/non-null flag reuses the repository's native CAS
 * adapter (whose successful RMW reads the maximum history timestamp). Neither
 * flag value is dereferenced. This new explicit lock does not replace SpinLock.
 * Origin Rust: <none; new executable code>
 */

pub struct RcuWeakLock<R: Objective + 'static, P: WeakLockPredicate<R> + 'static> {
    atomic: PAtomicWeakPtr<u8>,
    tracked_state: Tracked<&'static LockInvariant<R, P>>,
}

impl<R: Objective + 'static, P: WeakLockPredicate<R> + 'static> RcuWeakLock<R, P> {
    /// The native flag and retained invariant always refer to the same atomic location.
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.atomic.loc() == self.tracked_state@.constant().0
    }
}

impl<R: Objective + 'static, P: WeakLockPredicate<R> + 'static> RcuWeakLock<R, P> {
    /// Identity used to match this lock with its unique checked-out guard.
    pub closed spec fn id(&self) -> Loc {
        self.tracked_state@.constant().1
    }

    /// Fixed client interpretation key stored in the invariant.
    pub closed spec fn key(&self) -> P::Key {
        self.tracked_state@.constant().2
    }

    /// Publishes initial protected observations with an actual native release.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Stores only objective resources; no subjective view token enters the invariant.
    /// ## Functional Correctness
    /// - Release-publishes the initial resource's required observations.
    /// ## Preconditions
    /// - The resource satisfies its interpretation and the actual caller view covers its required view.
    /// ## Postconditions
    /// - The returned lock has the requested key and the caller's view is preserved monotonically.
    /* New explicit publication adapter; the initial native store must carry the protected observations.
     * Origin Rust: <none; new executable code>
     */
    pub fn new(
        Tracked(resource): Tracked<R>,
        Ghost(key): Ghost<P::Key>,
        Tracked(view): Tracked<&mut ViewSeen>,
    ) -> (res: Self)
        requires
            P::inv(key, resource),
            old(view)@.contains(P::required_view(resource)),
        ensures
            res.key() == key,
            final(view)@.contains(old(view)@),
    {
        let (atomic, Tracked(mut points_to), Tracked(initial), Ghost(initial_ts)) =
            PAtomicWeakPtr::<u8>::new(core::ptr::null_mut());
        proof {
            let ghost before = view@;
            let tracked previous = *view;
            *view = previous.join(initial);
            ThreadView::join_contains(before, initial@);
            ThreadView::join_comm(before, initial@);
            assert(view@.contains(before));
            assert(view@.contains(initial@));
            points_to.get_timestamp_monotonic(view@, initial@);
        }
        let Ghost(stored) = atomic.store(
            core::ptr::null_mut(),
            Ordering::Release,
            Tracked(view),
            Tracked(ReleaseViewSeen::new()),
            Tracked(&mut points_to),
        );
        let tracked (owner, token) = GhostVarAuth::new((stored.timestamp, view@));
        let tracked state = LockState { points_to, owner, available: Some((resource, token)) };
        proof {
            assert(stored.timestamp > initial_ts);
            assert(state.points_to.hist().is_max_timestamp(stored.timestamp));
            assert(view@.contains(old(view)@));
            assert(view@.contains(P::required_view(resource)));
        }
        let tracked invariant = AtomicInvariant::new(
            (atomic.loc(), state.owner.id(), key),
            state,
            0,
        );
        Self { atomic, tracked_state: Tracked(tracked_static_ref(invariant)) }
    }

    /* This accessor lets invariant blocks contain exactly one native atomic instruction.
     * Origin Rust: <none; new executable code>
     */
    fn raw_atomic(&self) -> (res: &PAtomicWeakPtr<u8>)
        ensures
            res.loc() == self.atomic.loc(),
        opens_invariants none
        no_unwind
    {
        &self.atomic
    }

    /// Attempts acquire once. Failure imports no protected state or certificate.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Successful native acquire is required before exposing the protected resource.
    /// ## Functional Correctness
    /// - Attempts CAS once; success returns exactly one checked-out guard, failure returns none.
    /// ## Preconditions
    /// - Supply the caller's actual mutable native view.
    /// ## Postconditions
    /// - A successful guard matches this lock and its resource is valid and observed; the view only grows.
    /* New explicit native CAS handoff; it does not execute preemption or interrupt masking.
     * Origin Rust: <none; new executable code>
     */
    pub fn try_acquire(&self, Tracked(view): Tracked<&mut ViewSeen>) -> (res: (
        bool,
        Tracked<Option<WeakLockGuard<R>>>,
    ))
        ensures
            final(view)@.contains(old(view)@),
            res.0 == (res.1@ is Some),
            res.1@ matches Some(guard) ==> {
                &&& guard.lock() == self.id()
                &&& P::inv(self.key(), guard.resource())
                &&& final(view)@.contains(P::required_view(guard.resource()))
                &&& guard.acquired_view() == final(view)@
            },
    {
        proof {
            use_type_invariant(self);
        }
        let result;
        let atomic = self.raw_atomic();
        let locked = core::ptr::NonNull::<u8>::dangling().as_ptr();
        let unlocked = core::ptr::null_mut();
        vstd::invariant::open_atomic_invariant!(self.tracked_state.get() => state => {
            let ghost before = state.points_to;
            let update = atomic.compare_exchange(unlocked, locked,
                Ordering::AcqRel, Ordering::Relaxed, Tracked(view),
                Tracked(ReleaseViewSeen::new()), Tracked(&mut state.points_to));
            match update.0 { Ok(_) => {
                let tracked guard;
                proof {
                    assert(update.2@.load_timestamp == state.owner@.0);
                    let tracked (resource, mut token) = state.available.tracked_take();
                    state.owner.update(&mut token, (update.2@.load_timestamp + 1, view@));
                    guard = WeakLockGuard { resource, token };
                }
                result = (true, Tracked(Some(guard)));
            }, Err(_) => {
                result = (false, Tracked(None));
            } }
        });
        result
    }

    /// Release-publishes every observation required by the updated resource.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - The unique matching guard returns ownership before another caller can acquire it.
    /// ## Functional Correctness
    /// - Release-publishes the updated resource's required observations.
    /// ## Preconditions
    /// - The guard matches this lock, its resource is valid, and the actual view covers both acquired and required views.
    /// ## Postconditions
    /// - The caller's native view is preserved monotonically; the guard is consumed.
    /* New explicit release path pairs the native unlock with returning protected ownership.
     * Origin Rust: <none; new executable code>
     */
    pub fn release(
        &self,
        Tracked(guard): Tracked<WeakLockGuard<R>>,
        Tracked(view): Tracked<&mut ViewSeen>,
    )
        requires
            guard.lock() == self.id(),
            P::inv(self.key(), guard.resource()),
            old(view)@.contains(guard.acquired_view()),
            old(view)@.contains(P::required_view(guard.resource())),
        ensures
            final(view)@.contains(old(view)@),
    {
        proof {
            use_type_invariant(self);
        }
        let atomic = self.raw_atomic();
        let unlocked = core::ptr::null_mut();
        vstd::invariant::open_atomic_invariant!(self.tracked_state.get() => state => {
            let tracked WeakLockGuard { resource, mut token } = guard;
            proof {
                state.owner.agree(&token);
                state.points_to.get_timestamp_monotonic(view@, token@.1);
            }
            let Ghost(stored) = atomic.store(unlocked, Ordering::Release,
                Tracked(view), Tracked(ReleaseViewSeen::new()), Tracked(&mut state.points_to));
            proof {
                state.owner.update(&mut token, (stored.timestamp, view@));
                state.available = Some((resource, token));
            }
        });
    }
}

} // verus!
