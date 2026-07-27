// SPDX-License-Identifier: MPL-2.0
//! OSTD-specific adapters for the generic weak-memory atomic library.
//!
//! The reusable view, history, resource algebra, atomic wrappers, and
//! invariant-opening macro live in [`vstd_extra::atomic_weak`]. This module
//! re-exports that API for existing OSTD callers and keeps only transitions
//! coupled to the RCU root and monitor ghost state.
pub use vstd_extra::atomic_weak::*;
pub use vstd_extra::weak_atomic_with_ghost;

use super::rcu as rcu_spec;
use vstd::prelude::*;

verus! {

/// OSTD's RCU-specific specialization of the generic weak pointer atomic.
///
/// The inner atomic and its history protocol are reusable; this wrapper adds
/// transitions that manipulate `RcuRootOwnedGhost`.
#[verifier::reject_recursive_types(T)]
pub struct RcuWeakAtomicPtr<T, O, OwnPred> {
    inner: WeakAtomicPtr<
        T,
        rcu_spec::RcuRootKey,
        rcu_spec::RcuRootOwnedGhost<T, O>,
        rcu_spec::RcuOwnedWeakAtomicInv<OwnPred>,
    >,
}

impl<T, O, OwnPred> RcuWeakAtomicPtr<T, O, OwnPred> {
    pub closed spec fn constant(&self) -> rcu_spec::RcuRootKey {
        self.inner.constant()
    }

    pub closed spec fn id(&self) -> AtomicId {
        self.inner.id()
    }

    pub closed spec fn well_formed(&self) -> bool {
        self.inner.well_formed()
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(&self) -> bool {
        self.well_formed()
    }
}

impl<T, O, OwnPred> RcuWeakAtomicPtr<T, O, OwnPred> where
    OwnPred: rcu_spec::RcuRootOwnershipPredicate<T, O>,
 {
    pub const fn new(
        Ghost(k): Ghost<rcu_spec::RcuRootKey>,
        init: *mut T,
        Tracked(g): Tracked<rcu_spec::RcuRootOwnedGhost<T, O>>,
    ) -> (res: Self)
        requires
            rcu_spec::RcuOwnedWeakAtomicInv::<OwnPred>::atomic_inv(
                k,
                seq![Msg { value: init, view: WmView::empty() }],
                g,
            ),
        ensures
            res.well_formed(),
            res.constant() == k,
    {
        let inner = WeakAtomicPtr::new(Ghost(k), init, Tracked(g));
        Self { inner }
    }

    fn raw_atomic(&self) -> (res: &AtomicPtrW<T>)
        requires
            self.well_formed(),
        ensures
            res.id() == self.id(),
    {
        self.inner.raw_atomic()
    }

    proof fn tracked_atomic_inv(tracked &self) -> (tracked res: &vstd::invariant::AtomicInvariant<
        (rcu_spec::RcuRootKey, AtomicId),
        (HistAuth<*mut T>, rcu_spec::RcuRootOwnedGhost<T, O>),
        WeakAtomicPredPtr<T, rcu_spec::RcuOwnedWeakAtomicInv<OwnPred>>,
    >)
        requires
            self.well_formed(),
        ensures
            res.constant() == (self.constant(), self.id()),
    {
        self.inner.tracked_atomic_inv()
    }

    /// Acquire-load helper for RCU root pointers.
    #[inline(always)]
    pub fn load_acquire_rcu(&self, Tracked(tv): Tracked<&mut ThreadView>) -> (res: (
        *mut T,
        Ghost<Timestamp>,
        Ghost<Option<rcu_spec::RcuPublishedObject>>,
        Tracked<Option<rcu_spec::RcuBlockInfo<T>>>,
    ))
        requires
            self.well_formed(),
        ensures
            !self.constant().nullable ==> !res.0.is_null(),
            match (res.2@, res.3@) {
                (None, None) => res.0.addr() == 0,
                (Some(object), Some(info)) => {
                    &&& res.0.addr() != 0
                    &&& object.addr == res.0.addr()
                    &&& info.wf()
                    &&& info.domain() == object.domain
                    &&& info.obj() == object.obj
                    &&& info.addr() == object.addr
                    &&& equal(info.ptr(), res.0)
                },
                _ => false,
            },
    {
        let result;
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (hist, g) = pair;
            proof {
                assert(hist.id() == self.id());
                assert(raw_atomic.id() == self.id());
                assert(hist.id() == raw_atomic.id());
            }
            let loaded = raw_atomic.load_acquire(Tracked(&hist), Tracked(tv));
            proof {
                assert(hist.valid_ts(loaded.1@));
                assert(loaded.1@ < hist.history().len());
                assert(rcu_spec::rcu_owned_root_history_inv(hist.history(), g));
            }
            proof_decl! {
                let ghost published = g.published_at(loaded.1@);
                let tracked loaded_info;
            }
            proof {
                assert(rcu_spec::rcu_history_inv(self.constant().nullable, hist.history()));
                assert(rcu_spec::rcu_owned_root_history_inv(hist.history(), g));
                loaded_info = g.tracked_info_at(hist.history(), loaded.1@);
                match (published, &loaded_info) {
                    (Some(object), Some(info)) => {
                        assert(equal(hist.history()[loaded.1@ as int].value, loaded.0));
                        assert(equal(info.ptr(), loaded.0));
                    },
                    (None, None) => {
                        assert(loaded.0.addr() == 0);
                    },
                    _ => assert(false),
                };
                if !self.constant().nullable {
                    rcu_spec::rcu_history_inv_read_nonnull::<T>(hist.history(), loaded.1@);
                    assert(!loaded.0.is_null());
                }
            }
            result = (loaded.0, loaded.1, Ghost(published), Tracked(loaded_info));
            proof {
                pair = (hist, g);
            }
        });
        result
    }

    /// Acquire-load an RCU root while starting a paper read-side guard.
    ///
    /// The ghost reader transition occurs in the same invariant opening as the
    /// real acquire load. Executably this is identical to `load_acquire_rcu`.
    #[inline(always)]
    pub fn load_acquire_rcu_guarded(
        &self,
        Ghost(reader): Ghost<rcu_spec::RcuReaderContext>,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (
        *mut T,
        Ghost<Timestamp>,
        Ghost<Option<rcu_spec::RcuPublishedObject>>,
        Tracked<Option<rcu_spec::RcuBlockInfo<T>>>,
        Tracked<rcu_spec::RcuReadGuardToken<T>>,
    ))
        requires
            self.well_formed(),
        ensures
            !self.constant().nullable ==> !res.0.is_null(),
            res.4@.wf(),
            res.4@.domain() == self.constant().domain,
            res.4@.reader_registry() == self.constant().reader_registry,
            res.4@.reader() == reader,
            match (res.2@, res.3@) {
                (None, None) => res.0.addr() == 0,
                (Some(object), Some(info)) => {
                    &&& res.0.addr() != 0
                    &&& object.addr == res.0.addr()
                    &&& info.wf()
                    &&& info.domain() == object.domain
                    &&& info.domain() == res.4@.domain()
                    &&& info.obj() == object.obj
                    &&& info.addr() == object.addr
                    &&& equal(info.ptr(), res.0)
                    &&& !res.4@.expired().contains(info.obj())
                    &&& res.4@.protects(info.addr(), info.obj())
                },
                _ => false,
            },
    {
        let result;
        proof {
            use_type_invariant(self);
        }
        let ghost start_view = tv@;
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (hist, mut g) = pair;
            proof {
                assert(hist.id() == self.id());
                assert(raw_atomic.id() == self.id());
                assert(hist.id() == raw_atomic.id());
            }
            proof_decl! {
                let tracked base_guard =
                    g.tracked_start_reader(hist.history(), self.id(), start_view, reader);
            }
            let loaded = raw_atomic.load_acquire(Tracked(&hist), Tracked(tv));
            proof {
                assert(hist.valid_ts(loaded.1@));
                assert(loaded.1@ < hist.history().len());
                assert(rcu_spec::rcu_owned_root_history_inv(hist.history(), g));
            }
            proof_decl! {
                let tracked loaded_info;
            }
            proof {
                assert(rcu_spec::rcu_history_inv(
                    self.constant().nullable,
                    hist.history(),
                ));
                loaded_info = g.tracked_info_at(hist.history(), loaded.1@);
                assert(loaded.1@ < g.publications().len());
            }
            proof_decl! {
                let ghost published = g.published_at(loaded.1@);
            }
            proof {
                match (published, &loaded_info) {
                    (Some(object), Some(info)) => {
                        assert(equal(hist.history()[loaded.1@ as int].value, loaded.0));
                        assert(equal(info.ptr(), loaded.0));
                        assert(info.domain() == g.domain());
                        assert(info.domain() == base_guard.domain());
                    },
                    (None, None) => {
                        assert(loaded.0.addr() == 0);
                    },
                    _ => assert(false),
                };
                if !self.constant().nullable {
                    rcu_spec::rcu_history_inv_read_nonnull::<T>(hist.history(), loaded.1@);
                    assert(!loaded.0.is_null());
                }
                assert(base_guard.domain() == self.constant().domain);
                assert(base_guard.reader_registry() == self.constant().reader_registry);
                assert(rcu_spec::rcu_current_ownership_inv::<T, O, OwnPred>(g));
            }
            proof_decl! {
                let tracked mut guard =
                    rcu_spec::RcuReadGuardToken::tracked_from_base(base_guard);
            }
            proof {
                assert(guard.expired()
                    == g.root().domain_auth().observed_retired(self.id(), start_view));
                match &loaded_info {
                    Some(info) => {
                        if guard.expired().contains(info.obj()) {
                            assert(g.root().domain_auth().observed_retired(
                                self.id(),
                                start_view,
                            ).contains(info.obj()));
                            g.lemma_observed_retired(
                                hist.history(),
                                self.id(),
                                start_view,
                                info.obj(),
                            );
                            let ghost removal = g.removals()[info.obj()];
                            assert(removal.root == self.id());
                            assert(removal.observed_by(start_view));
                            assert(start_view.seen_at(self.id()) <= loaded.1@);
                            assert(removal.timestamp <= loaded.1@);
                            assert(g.removals_wf(hist.history()));
                            assert(removal.timestamp < hist.history().len());
                            assert(g.publications()[loaded.1@ as int] != Some(info.obj()));
                            assert(published == Some(rcu_spec::RcuPublishedObject {
                                domain: info.domain(),
                                obj: info.obj(),
                                addr: info.addr(),
                            }));
                            g.lemma_published_object_id(
                                hist.history(),
                                loaded.1@,
                                rcu_spec::RcuPublishedObject {
                                    domain: info.domain(),
                                    obj: info.obj(),
                                    addr: info.addr(),
                                },
                            );
                            assert(g.publications()[loaded.1@ as int] == Some(info.obj()));
                            assert(false);
                        }
                        assert(guard.can_protect(*info));
                        guard.tracked_protect(info);
                    },
                    None => {},
                }
            }
            result = (
                loaded.0,
                loaded.1,
                Ghost(published),
                Tracked(loaded_info),
                Tracked(guard),
            );
            proof {
                pair = (hist, g);
            }
        });
        result
    }

    /// End a paper read-side guard without executing another atomic operation.
    #[inline(always)]
    pub fn stop_rcu_reader(&self, Tracked(guard): Tracked<rcu_spec::RcuReadGuardToken<T>>)
        requires
            self.well_formed(),
            guard.wf(),
            guard.domain() == self.constant().domain,
            guard.reader_registry() == self.constant().reader_registry,
    {
        proof_decl! {
            let tracked base_guard = guard.tracked_into_base();
        }
        let credit = vstd::invariant::create_open_invariant_credit();
        proof {
            use_type_invariant(self);
            vstd::invariant::open_atomic_invariant_in_proof!(
                credit.get() => self.tracked_atomic_inv() => pair => {
                    let tracked (hist, mut g) = pair;
                    assert(g.domain() == self.constant().domain);
                    assert(g.reader_registry() == self.constant().reader_registry);
                    g.tracked_stop_reader(hist.history(), base_guard);
                    assert(rcu_spec::rcu_current_ownership_inv::<T, O, OwnPred>(g));
                    pair = (hist, g);
                }
            );
        }
    }

    /// Release-swap helper for a freshly introduced RCU root pointer.
    ///
    /// The new registration remains owned by the atomic invariant. The return
    /// value contains the previous root's retired ownership, if any. Root
    /// removal and the base retire transition happen while the same atomic
    /// invariant is open.
    #[inline(always)]
    pub fn swap_release_rcu(
        &self,
        value: *mut T,
        Tracked(ownership): Tracked<Option<O>>,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (*mut T, Tracked<Option<rcu_spec::RcuRetiredOwnedObject<T, O>>>))
        requires
            self.well_formed(),
            self.constant().nullable || !value.is_null(),
            match ownership {
                Some(ownership) => {
                    &&& !value.is_null()
                    &&& OwnPred::owns(value, ownership)
                },
                None => value.is_null(),
            },
        ensures
            (res.1@ is Some) == !res.0.is_null(),
            res.1@ is Some ==> res.1@->Some_0.object().wf(),
            res.1@ is Some ==> equal(res.1@->Some_0.ptr(), res.0),
            res.1@ is Some ==> res.1@->Some_0.retired().obj() == res.1@->Some_0.obj(),
            res.1@ is Some ==> res.1@->Some_0.retired().removal().root == self.id(),
            res.1@ is Some ==> res.1@->Some_0.retired().removal().observed_by(final(tv)@),
            res.1@ is Some ==> OwnPred::owns(res.0, res.1@->Some_0.ownership()),
    {
        let result;
        proof_decl! {
            let tracked retired_ownership;
        }
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (mut hist, mut g) = pair;
            proof {
                assert(hist.id() == self.id());
                assert(raw_atomic.id() == self.id());
                assert(hist.id() == raw_atomic.id());
            }
            let ghost prev = hist.history();
            let swap = raw_atomic.swap_release(Tracked(&mut hist), Tracked(tv), value);
            result = swap.0;
            let snap = swap.1;
            let ghost next = hist.history();
            proof {
                assert(rcu_spec::rcu_owned_root_history_inv(prev, g));
                assert(rcu_spec::rcu_current_ownership_inv::<T, O, OwnPred>(g));
                rcu_spec::lemma_current_owned_resources::<T, O, OwnPred>(prev, &g);
                if !self.constant().nullable {
                    assert(!value.is_null());
                    assert(snap@.msg().value.addr() != 0);
                }
                rcu_spec::preserve_rcu_history_inv_on_push(
                    self.constant().nullable,
                    prev,
                    next,
                    snap@.msg(),
                );
                let tracked detached = g.tracked_push_fresh::<OwnPred>(
                    prev,
                    next,
                    snap@.msg(),
                    self.id(),
                    ownership,
                );
                assert(detached is Some ==> detached->Some_0.object().wf());
                assert(detached is Some ==> equal(detached->Some_0.ptr(), result));
                assert(detached is Some ==> OwnPred::owns(
                    result,
                    detached->Some_0.ownership(),
                ));
                assert(detached is Some ==> detached->Some_0.retired().removal().root
                    == self.id());
                assert(detached is Some ==> detached->Some_0.retired().removal().timestamp
                    == prev.len());
                assert(detached is Some ==> detached->Some_0.retired().removal().observed_by(
                    tv@,
                ));
                assert(rcu_spec::rcu_current_ownership_inv::<T, O, OwnPred>(g)) by {
                    match g.current_owned() {
                        Some(owned) => {
                            assert(ownership == Some(owned.ownership()));
                            assert(equal(owned.block_info().ptr(), value));
                        },
                        None => {},
                    }
                };
                retired_ownership = detached;
                pair = (hist, g);
            }
        });
        (result, Tracked(retired_ownership))
    }

    /// Strong AcqRel/Acquire CAS helper for a freshly introduced RCU pointer.
    ///
    /// Registration occurs only in the successful CAS branch. A successful
    /// CAS returns the previous root registration; a failed CAS leaves the
    /// ownership state unchanged and returns no detached registration.
    #[inline(always)]
    pub fn compare_exchange_acqrel_acquire_rcu(
        &self,
        current: *mut T,
        new: *mut T,
        Tracked(new_ownership): Tracked<Option<O>>,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (
        Result<*mut T, *mut T>,
        Ghost<Timestamp>,
        Tracked<(Option<rcu_spec::RcuRetiredOwnedObject<T, O>>, Option<O>)>,
    ))
        requires
            self.well_formed(),
            self.constant().nullable || !new.is_null(),
            match new_ownership {
                Some(ownership) => {
                    &&& !new.is_null()
                    &&& OwnPred::owns(new, ownership)
                },
                None => new.is_null(),
            },
        ensures
            res.0 is Err ==> res.2@.0 is None,
            res.0 is Err ==> res.2@.1 == new_ownership,
            res.0 is Ok ==> res.2@.1 is None,
            res.0 is Ok ==> ((res.2@.0 is Some) == !res.0->Ok_0.is_null()),
            res.2@.0 is Some ==> res.2@.0->Some_0.object().wf(),
            res.2@.0 is Some ==> equal(res.2@.0->Some_0.ptr(), res.0->Ok_0),
            res.2@.0 is Some ==> res.2@.0->Some_0.retired().obj() == res.2@.0->Some_0.obj(),
            res.2@.0 is Some ==> res.2@.0->Some_0.retired().removal().root == self.id(),
            res.2@.0 is Some ==> res.2@.0->Some_0.retired().removal().observed_by(final(tv)@),
            res.2@.0 is Some ==> OwnPred::owns(res.0->Ok_0, res.2@.0->Some_0.ownership()),
    {
        let result;
        proof_decl! {
            let tracked retired_ownership;
        }
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (mut hist, mut g) = pair;
            proof {
                assert(hist.id() == self.id());
                assert(raw_atomic.id() == self.id());
                assert(hist.id() == raw_atomic.id());
            }
            let ghost prev = hist.history();
            let cas_result = raw_atomic.compare_exchange_acqrel_acquire(
                Tracked(&mut hist),
                Tracked(tv),
                current,
                new,
            );
            result = (cas_result.0, cas_result.1);
            let ghost next = hist.history();
            proof {
                assert(rcu_spec::rcu_owned_root_history_inv(prev, g));
                assert(rcu_spec::rcu_current_ownership_inv::<T, O, OwnPred>(g));
                rcu_spec::lemma_current_owned_resources::<T, O, OwnPred>(prev, &g);
                match cas_result.0 {
                    Result::Ok(_) => {
                        let tracked snap_opt = cas_result.2.get();
                        match snap_opt {
                            Option::Some(snap) => {
                                if !self.constant().nullable {
                                    assert(!new.is_null());
                                    assert(snap.msg().value.addr() != 0);
                                }
                                rcu_spec::preserve_rcu_history_inv_on_push(
                                    self.constant().nullable,
                                    prev,
                                    next,
                                    snap.msg(),
                                );
                                let tracked detached = g.tracked_push_fresh::<OwnPred>(
                                    prev,
                                    next,
                                    snap.msg(),
                                    self.id(),
                                    new_ownership,
                                );
                                assert(detached is Some ==> detached->Some_0.object().wf());
                                assert(detached is Some ==> equal(
                                    detached->Some_0.ptr(),
                                    cas_result.0->Ok_0,
                                ));
                                assert(detached is Some ==> OwnPred::owns(
                                    cas_result.0->Ok_0,
                                    detached->Some_0.ownership(),
                                ));
                                assert(detached is Some ==> detached->Some_0.retired().removal().root
                                    == self.id());
                                assert(detached is Some ==>
                                    detached->Some_0.retired().removal().timestamp == prev.len());
                                assert(detached is Some ==>
                                    detached->Some_0.retired().removal().observed_by(tv@));
                                assert(rcu_spec::rcu_current_ownership_inv::<T, O, OwnPred>(g)) by {
                                    match g.current_owned() {
                                        Some(owned) => {
                                            assert(new_ownership == Some(owned.ownership()));
                                            assert(equal(owned.block_info().ptr(), new));
                                        },
                                        None => {},
                                    }
                                };
                                retired_ownership = (detached, None);
                            },
                            Option::None => {
                                assert(false);
                                retired_ownership = (None, None);
                            },
                        }
                    },
                    Result::Err(_) => {
                        retired_ownership = (None, new_ownership);
                        assert(next == prev);
                        assert(rcu_spec::rcu_history_inv(self.constant().nullable, next));
                    },
                }
                pair = (hist, g);
            }
        });
        (result.0, result.1, Tracked(retired_ownership))
    }
}

/// RCU monitor specialization of the generic weak boolean atomic.
pub struct RcuMonitorWeakAtomicBool {
    inner: WeakAtomicBool<(), rcu_spec::RcuMonitorFlagGhost, rcu_spec::RcuMonitorFlagInv>,
}

impl RcuMonitorWeakAtomicBool {
    pub closed spec fn id(&self) -> AtomicId {
        self.inner.id()
    }

    pub closed spec fn well_formed(&self) -> bool {
        self.inner.well_formed()
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(&self) -> bool {
        self.well_formed()
    }

    pub const fn new(
        Ghost(k): Ghost<()>,
        init: bool,
        Tracked(g): Tracked<rcu_spec::RcuMonitorFlagGhost>,
    ) -> (res: Self)
        requires
            rcu_spec::RcuMonitorFlagInv::atomic_inv(
                k,
                seq![Msg { value: init, view: WmView::empty() }],
                g,
            ),
        ensures
            res.well_formed(),
    {
        let inner = WeakAtomicBool::new(Ghost(k), init, Tracked(g));
        Self { inner }
    }

    pub fn load_relaxed(&self, Tracked(tv): Tracked<&mut ThreadView>) -> (res: (
        bool,
        Ghost<Timestamp>,
    ))
        requires
            self.well_formed(),
    {
        self.inner.load_relaxed(Tracked(tv))
    }

    fn raw_atomic(&self) -> (res: &AtomicBoolW)
        requires
            self.well_formed(),
        ensures
            res.id() == self.id(),
    {
        self.inner.raw_atomic()
    }

    proof fn tracked_atomic_inv(tracked &self) -> (tracked res: &vstd::invariant::AtomicInvariant<
        ((), AtomicId),
        (HistAuth<bool>, rcu_spec::RcuMonitorFlagGhost),
        WeakAtomicPredBool<rcu_spec::RcuMonitorFlagInv>,
    >)
        requires
            self.well_formed(),
        ensures
            res.constant() == ((), self.id()),
    {
        self.inner.tracked_atomic_inv()
    }

    /// Relaxed-store helper for the RCU monitor flag.
    ///
    /// The executable flag remains a relaxed atomic flag, matching the old
    /// monitor protocol. The proof-side effect is stronger: each stored flag
    /// message appends the lock-protected monitor-state snapshot supplied by
    /// the writer.
    #[inline(always)]
    pub fn store_relaxed_rcu_monitor(
        &self,
        value: bool,
        Ghost(state): Ghost<rcu_spec::MonitorStateView>,
        Tracked(tv): Tracked<&mut ThreadView>,
    )
        requires
            self.well_formed(),
            state.wf(),
            !value ==> state.no_pending_work(),
    {
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (mut hist, mut g) = pair;
            proof {
                assert(hist.id() == self.id());
                assert(raw_atomic.id() == self.id());
                assert(hist.id() == raw_atomic.id());
            }
            let ghost prev = hist.history();
            let snap = raw_atomic.store_relaxed(Tracked(&mut hist), Tracked(tv), value);
            let ghost next = hist.history();
            proof {
                assert(snap@.msg().value == value);
                rcu_spec::preserve_rcu_monitor_flag_inv_on_push(
                    prev,
                    next,
                    snap@.msg(),
                    g,
                    g.push(state),
                    state,
                );
                g = g.tracked_push(state);
                pair = (hist, g);
            }
        });
    }
}

} // verus!
