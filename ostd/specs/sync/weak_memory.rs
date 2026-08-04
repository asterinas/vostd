// SPDX-License-Identifier: MPL-2.0
//! OSTD-specific adapters for Verus' native IRC11 weak-memory atomics.
//!
//! This module contains only transitions coupled to the RCU root and monitor
//! ghost state. Generic native primitives are re-exported by
//! [`vstd_extra::atomic_irc11`].

use core::sync::atomic::Ordering;

use super::{rcu as rcu_spec, rcu_cpu as rcu_cpu_spec};
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::thread_view::Objective;
use vstd_extra::atomic_irc11::{
    AtomicId as Irc11AtomicId, AtomicPointsTo, PAtomicWeakBool as Irc11AtomicBool,
    PAtomicWeakPtr, ReleaseViewSeen, ThreadView as Irc11ThreadView,
    ThreadViewOrder as Irc11ThreadViewOrder, Timestamp, ViewSeen,
};

verus! {

broadcast use {vstd::atomic_weak::group_view_history, vstd::thread_view::group_thread_view_axioms};

/// OSTD's RCU-specific specialization of the generic weak pointer atomic.
///
/// This is an RCU client of Verus' native IRC11 protocol. The only local TCB
/// component is `PAtomicWeakPtr`, needed because upstream does not yet expose
/// a native weak-memory `AtomicPtr`.
#[verifier::reject_recursive_types(T)]
pub struct RcuWeakAtomicPtr<T, O: Objective, OwnPred> {
    atomic: PAtomicWeakPtr<T>,
    tracked_atomic_inv: Tracked<
        AtomicInvariant<
            (rcu_spec::RcuRootKey, Irc11AtomicId),
            (AtomicPointsTo<*mut T>, rcu_spec::RcuRootOwnedGhost<T, O>),
            rcu_spec::RcuOwnedWeakAtomicInv<OwnPred>,
        >,
    >,
}

impl<T, O: Objective, OwnPred> RcuWeakAtomicPtr<T, O, OwnPred> {
    pub closed spec fn constant(&self) -> rcu_spec::RcuRootKey {
        self.tracked_atomic_inv@.constant().0
    }

    pub closed spec fn id(&self) -> Loc {
        self.constant().domain
    }

    pub closed spec fn native_loc(&self) -> Irc11AtomicId {
        self.atomic.loc()
    }

    pub closed spec fn well_formed(&self) -> bool {
        self.tracked_atomic_inv@.constant().1 == self.native_loc()
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(&self) -> bool {
        self.well_formed()
    }
}

impl<T, O: Objective, OwnPred> RcuWeakAtomicPtr<T, O, OwnPred> where
    OwnPred: rcu_spec::RcuRootOwnershipPredicate<T, O>,
 {
    pub const fn new(
        Ghost(nullable): Ghost<bool>,
        init: *mut T,
        Tracked(ownership): Tracked<Option<O>>,
    ) -> (res: Self)
        requires
            nullable || !init.is_null(),
            (ownership is Some) == !init.is_null(),
            ownership is Some ==> OwnPred::owns(init, ownership->Some_0),
        ensures
            res.well_formed(),
            res.constant().nullable == nullable,
    {
        let (atomic, Tracked(points_to), Tracked(initial_view), Ghost(timestamp)) =
            PAtomicWeakPtr::new(init);
        let tracked g = rcu_spec::RcuRootOwnedGhost::tracked_initial(
            init,
            ownership,
            points_to.hist(),
            timestamp,
            initial_view@,
        );
        let ghost key = rcu_spec::RcuRootKey {
            nullable,
            domain: g.domain(),
            reader_registry: g.reader_registry(),
            retire_observation_registry: g.retire_observation_registry(),
        };
        let tracked pair = (points_to, g);
        proof {
            assert(rcu_spec::rcu_history_inv(nullable, pair.0.hist())) by {
                assert(!pair.0.hist().dom().is_empty());
                if !nullable {
                    assert forall|ts: nat|
                        pair.0.hist().contains_timestamp(ts) implies #[trigger] pair.0.hist().value(
                        ts,
                    ).addr() != 0 by {
                        assert(ts == timestamp);
                        assert(equal(pair.0.hist().value(ts), init));
                    };
                }
            };
            assert(rcu_spec::rcu_current_ownership_inv::<T, O, OwnPred>(pair.1)) by {
                match pair.1.current_owned() {
                    Some(owned) => {
                        assert(ownership == Some(owned.ownership()));
                        assert(equal(owned.block_info().ptr(), init));
                    },
                    None => {},
                }
            };
            assert forall|obj: nat| pair.1.removals().contains_key(obj) implies {
                let removal = #[trigger] pair.1.removals()[obj];
                pair.0.get_timestamp(removal.message_view) == Some(removal.timestamp)
            } by {
                assert(pair.1.removals() == Map::empty());
            };
            assert(rcu_spec::RcuOwnedWeakAtomicInv::<OwnPred>::inv((key, atomic.loc()), pair));
        }
        let tracked atomic_inv = AtomicInvariant::new((key, atomic.loc()), pair, 0);
        Self { atomic, tracked_atomic_inv: Tracked(atomic_inv) }
    }

    fn raw_atomic(&self) -> (res: &PAtomicWeakPtr<T>)
        requires
            self.well_formed(),
        ensures
            res.loc() == self.native_loc(),
    {
        &self.atomic
    }

    proof fn tracked_atomic_inv(tracked &self) -> (tracked res: &vstd::invariant::AtomicInvariant<
        (rcu_spec::RcuRootKey, Irc11AtomicId),
        (AtomicPointsTo<*mut T>, rcu_spec::RcuRootOwnedGhost<T, O>),
        rcu_spec::RcuOwnedWeakAtomicInv<OwnPred>,
    >)
        requires
            self.well_formed(),
        ensures
            res.constant() == (self.constant(), self.native_loc()),
    {
        self.tracked_atomic_inv.borrow()
    }

    /// Acquire-load helper for RCU root pointers.
    #[inline(always)]
    pub fn load_acquire_rcu(&self, Tracked(tv): Tracked<&mut ViewSeen>) -> (res: (
        *mut T,
        Ghost<Timestamp>,
        Ghost<Option<rcu_spec::RcuPublishedObject>>,
        Tracked<Option<rcu_spec::RcuBlockInfo<T>>>,
    ))
        requires
            self.well_formed(),
        ensures
            old(tv)@.spec_le(final(tv)@),
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
        let ghost start_view = tv@;
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (points_to, g) = pair;
            proof {
                assert(points_to.loc() == self.native_loc());
            }
            let loaded = raw_atomic.load(
                Ordering::Acquire,
                Tracked(tv),
                Tracked(&points_to),
            );
            proof {
                assert(rcu_spec::rcu_owned_root_history_inv(points_to.hist(), g));
            }
            proof_decl! {
                let ghost timestamp = loaded.2@.timestamp;
                let ghost published = g.published_at(timestamp);
                let tracked loaded_info;
            }
            proof {
                loaded_info = g.tracked_info_at(points_to.hist(), timestamp);
                match (published, &loaded_info) {
                    (Some(object), Some(info)) => {
                        assert(equal(points_to.hist().value(timestamp), loaded.0));
                        assert(equal(info.ptr(), loaded.0));
                    },
                    (None, None) => {
                        assert(loaded.0.addr() == 0);
                    },
                    _ => assert(false),
                };
                if !self.constant().nullable {
                    rcu_spec::rcu_history_inv_read_nonnull::<T>(points_to.hist(), timestamp);
                    assert(!loaded.0.is_null());
                }
            }
            result = (loaded.0, Ghost(timestamp), Ghost(published), Tracked(loaded_info));
            proof {
                pair = (points_to, g);
            }
        });
        result
    }

    /// Acquire-load an RCU root while starting a paper read-side guard.
    ///
    /// The ghost reader transition occurs in the same invariant opening as the
    /// real acquire load. Executably this is identical to `load_acquire_rcu`.
    #[inline(always)]
    pub fn load_acquire_rcu_guarded_with_retired(
        &self,
        Ghost(reader): Ghost<rcu_spec::RcuReaderContext>,
        Tracked(retired_facts): Tracked<&rcu_spec::RcuRetiredFacts>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: (
        *mut T,
        Ghost<Timestamp>,
        Ghost<Option<rcu_spec::RcuPublishedObject>>,
        Tracked<Option<rcu_spec::RcuBlockInfo<T>>>,
        Tracked<rcu_spec::RcuReadGuardToken<T>>,
    ))
        requires
            self.well_formed(),
            retired_facts.observed_by(old(tv)@),
        ensures
            old(tv)@.spec_le(final(tv)@),
            !self.constant().nullable ==> !res.0.is_null(),
            res.4@.wf(),
            res.4@.domain() == self.constant().domain,
            res.4@.reader_registry() == self.constant().reader_registry,
            res.4@.retire_observation_registry() == self.constant().retire_observation_registry,
            res.4@.reader() == reader,
            res.4@.root() == self.id(),
            res.4@.start_view() == old(tv)@,
            forall|record: rcu_spec::RcuRetiredRecord| #[trigger]
                retired_facts.records().contains(record) && record.domain == res.4@.domain()
                    && record.retire_observation_registry == res.4@.retire_observation_registry()
                    && record.removal.root == res.4@.root() ==> res.4@.expired().contains(
                    record.obj,
                ),
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
            let tracked (points_to, mut g) = pair;
            proof {
                assert(points_to.loc() == self.native_loc());
                assert(g.retire_observation_registry()
                    == self.constant().retire_observation_registry);
            }
            proof_decl! {
                let tracked base_guard =
                    g.tracked_start_reader(points_to.hist(), self.id(), start_view, reader);
            }
            proof {
                g.lemma_retired_facts_observed(
                    points_to.hist(),
                    retired_facts,
                    self.id(),
                    start_view,
                );
            }
            let loaded = raw_atomic.load(
                Ordering::Acquire,
                Tracked(tv),
                Tracked(&points_to),
            );
            let ghost timestamp = loaded.2@.timestamp;
            proof {
                assert(rcu_spec::rcu_owned_root_history_inv(points_to.hist(), g));
            }
            proof_decl! {
                let tracked loaded_info;
            }
            proof {
                loaded_info = g.tracked_info_at(points_to.hist(), timestamp);
            }
            proof_decl! {
                let ghost published = g.published_at(timestamp);
            }
            proof {
                match (published, &loaded_info) {
                    (Some(object), Some(info)) => {
                        assert(equal(points_to.hist().value(timestamp), loaded.0));
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
                    rcu_spec::rcu_history_inv_read_nonnull::<T>(points_to.hist(), timestamp);
                    assert(!loaded.0.is_null());
                }
                assert(base_guard.domain() == self.constant().domain);
                assert(base_guard.reader_registry() == self.constant().reader_registry);
                assert(base_guard.retire_observation_registry()
                    == g.retire_observation_registry());
                assert(g.retire_observation_registry()
                    == self.constant().retire_observation_registry);
                assert(base_guard.retire_observation_registry()
                    == self.constant().retire_observation_registry);
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
                                points_to.hist(),
                                self.id(),
                                start_view,
                                info.obj(),
                            );
                            let ghost removal = g.removals()[info.obj()];
                            assert(removal.root == self.id());
                            assert(removal.observed_by(start_view));
                            assert(points_to.get_timestamp(removal.message_view)
                                == Some(removal.timestamp));
                            points_to.get_timestamp_monotonic(start_view, removal.message_view);
                            assert(points_to.get_timestamp(start_view) is Some);
                            assert(removal.timestamp
                                <= points_to.get_timestamp(start_view)->Some_0);
                            assert(points_to.get_timestamp(start_view)->Some_0 <= timestamp);
                            assert(removal.timestamp <= timestamp);
                            assert(g.removals_wf(points_to.hist()));
                            assert(g.publications()[timestamp] != Some(info.obj()));
                            assert(published == Some(rcu_spec::RcuPublishedObject {
                                domain: info.domain(),
                                obj: info.obj(),
                                addr: info.addr(),
                            }));
                            g.lemma_published_object_id(
                                points_to.hist(),
                                timestamp,
                                rcu_spec::RcuPublishedObject {
                                    domain: info.domain(),
                                    obj: info.obj(),
                                    addr: info.addr(),
                                },
                            );
                            assert(g.publications()[timestamp] == Some(info.obj()));
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
                Ghost(timestamp),
                Ghost(published),
                Tracked(loaded_info),
                Tracked(guard),
            );
            proof {
                pair = (points_to, g);
            }
        });
        result
    }

    /// Acquire-load an RCU root while starting a paper read-side guard.
    ///
    /// This compatibility entry point has no CPU-generation retirement
    /// history, so it starts the guard with only the root invariant's directly
    /// observed retirements.
    #[inline(always)]
    pub fn load_acquire_rcu_guarded(
        &self,
        Ghost(reader): Ghost<rcu_spec::RcuReaderContext>,
        Tracked(tv): Tracked<&mut ViewSeen>,
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
            old(tv)@.spec_le(final(tv)@),
            !self.constant().nullable ==> !res.0.is_null(),
            res.4@.wf(),
            res.4@.domain() == self.constant().domain,
            res.4@.reader_registry() == self.constant().reader_registry,
            res.4@.retire_observation_registry() == self.constant().retire_observation_registry,
            res.4@.reader() == reader,
            res.4@.root() == self.id(),
            res.4@.start_view() == old(tv)@,
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
        proof_decl! {
            let tracked retired_facts = rcu_spec::RcuRetiredFacts::empty();
        }
        self.load_acquire_rcu_guarded_with_retired(
            Ghost(reader),
            Tracked(&retired_facts),
            Tracked(tv),
        )
    }

    /// Acquire-load an RCU root while retaining the CPU implementation
    /// fragment in the returned guard.
    ///
    /// The caller must split `cpu_reader` after disabling preemption and before
    /// calling this method. The fragment is therefore live before the first
    /// protected load, while the participant view bound ensures that the paper
    /// guard starts no earlier than the CPU state from which it was split.
    #[inline(always)]
    pub fn load_acquire_rcu_guarded_cpu(
        &self,
        Ghost(reader): Ghost<rcu_spec::RcuReaderContext>,
        Tracked(cpu_reader): Tracked<rcu_cpu_spec::CpuRcuReaderFragment>,
        Tracked(binding): Tracked<rcu_cpu_spec::CpuRcuCoreBinding>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    ) -> (res: (
        *mut T,
        Ghost<Timestamp>,
        Ghost<Option<rcu_spec::RcuPublishedObject>>,
        Tracked<Option<rcu_spec::RcuBlockInfo<T>>>,
        Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<T>>,
    ))
        requires
            self.well_formed(),
            cpu_reader.wf(),
            reader.cpu == cpu_reader.cpu(),
            reader.generation == cpu_reader.generation(),
            binding.registry() == reader.scheduler,
            binding.cpu() == cpu_reader.cpu(),
            binding.single_local_id() == cpu_reader.participant_id(),
            cpu_reader.participant_view().spec_le(old(tv)@),
        ensures
            old(tv)@.spec_le(final(tv)@),
            !self.constant().nullable ==> !res.0.is_null(),
            res.4@.wf(),
            res.4@.participant_id() == cpu_reader.participant_id(),
            res.4@.cpu() == cpu_reader.cpu(),
            res.4@.generation() == cpu_reader.generation(),
            res.4@.participant_view() == cpu_reader.participant_view(),
            res.4@.reader_fragment() == cpu_reader,
            res.4@.scheduler() == binding.registry(),
            res.4@.domain() == self.constant().domain,
            res.4@.reader_registry() == self.constant().reader_registry,
            res.4@.retire_observation_registry() == self.constant().retire_observation_registry,
            res.4@.reader_context() == reader,
            res.4@.root() == self.id(),
            res.4@.start_view() == old(tv)@,
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
        let loaded = {
            proof_decl! {
                let tracked retired_facts =
                    cpu_reader.tracked_retired_facts_observed_by(tv@);
            }
            let loaded = self.load_acquire_rcu_guarded_with_retired(
                Ghost(reader),
                Tracked(retired_facts),
                Tracked(tv),
            );
            proof {
                assert forall|record: rcu_spec::RcuRetiredRecord| #[trigger]
                    cpu_reader.known_retired().contains(record) && record.domain
                        == loaded.4@.domain() && record.retire_observation_registry
                        == loaded.4@.retire_observation_registry() && record.removal.root
                        == loaded.4@.root() implies loaded.4@.expired().contains(record.obj) by {
                    assert(retired_facts.records().contains(record));
                };
            }
            loaded
        };
        proof {
            assert(loaded.4@.reader() == reader);
            assert(match (loaded.2@, loaded.3@) {
                (None, None) => loaded.0.addr() == 0,
                (Some(object), Some(info)) => {
                    &&& loaded.0.addr() != 0
                    &&& object.addr == loaded.0.addr()
                    &&& info.wf()
                    &&& info.domain() == object.domain
                    &&& info.domain() == loaded.4@.domain()
                    &&& info.obj() == object.obj
                    &&& info.addr() == object.addr
                    &&& equal(info.ptr(), loaded.0)
                    &&& !loaded.4@.expired().contains(info.obj())
                    &&& loaded.4@.protects(info.addr(), info.obj())
                },
                _ => false,
            });
        }
        let (ptr, timestamp, published, info, Tracked(paper_guard)) = loaded;
        proof_decl! {
            let tracked guard =
                rcu_cpu_spec::CpuRcuReadGuardToken::tracked_new(paper_guard, cpu_reader, binding);
        }
        proof {
            assert(guard.reader_context() == reader);
            assert(guard.reader_fragment() == cpu_reader);
            match (&published@, &info@) {
                (Some(object), Some(info)) => {
                    assert(info.domain() == guard.domain());
                    assert(!guard.expired().contains(info.obj()));
                    assert(guard.protects(info.addr(), info.obj()));
                },
                (None, None) => {
                    assert(ptr.addr() == 0);
                },
                _ => assert(false),
            }
        }
        (ptr, timestamp, published, info, Tracked(guard))
    }

    /// End a paper read-side guard without executing another atomic operation.
    #[inline(always)]
    pub fn stop_rcu_reader(&self, Tracked(guard): Tracked<rcu_spec::RcuReadGuardToken<T>>)
        requires
            self.well_formed(),
            guard.wf(),
            guard.domain() == self.constant().domain,
            guard.reader_registry() == self.constant().reader_registry,
            guard.retire_observation_registry() == self.constant().retire_observation_registry,
    {
        proof_decl! {
            let tracked base_guard = guard.tracked_into_base();
            let tracked _inactive = base_guard.tracked_stop();
        }
        proof {
            use_type_invariant(self);
        }
    }

    /// Ends a CPU-refined reader and returns its linear CPU fragment.
    ///
    /// The fragment is intentionally returned instead of dropped. The standard
    /// guard destruction path must join it back into the current CPU's
    /// participant before executable preemption is re-enabled.
    #[inline(always)]
    pub fn stop_cpu_rcu_reader(
        &self,
        Tracked(guard): Tracked<rcu_cpu_spec::CpuRcuReadGuardToken<T>>,
    ) -> (res: Tracked<rcu_cpu_spec::CpuRcuReaderFragment>)
        requires
            self.well_formed(),
            guard.wf(),
            guard.domain() == self.constant().domain,
            guard.root() == self.id(),
            guard.retire_observation_registry() == self.constant().retire_observation_registry,
        ensures
            res@.wf(),
            res@ == guard.reader_fragment(),
            res@.participant_id() == guard.participant_id(),
            res@.cpu() == guard.cpu(),
            res@.generation() == guard.generation(),
        opens_invariants none
        no_unwind
    {
        proof_decl! {
            let tracked (_inactive, reader) = guard.tracked_stop();
        }
        proof {
            use_type_invariant(self);
        }
        Tracked(reader)
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
        Tracked(tv): Tracked<&mut ViewSeen>,
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
            old(tv)@.spec_le(final(tv)@),
            (res.1@ is Some) == !res.0.is_null(),
            res.1@ is Some ==> res.1@->Some_0.object().wf(),
            res.1@ is Some ==> equal(res.1@->Some_0.ptr(), res.0),
            res.1@ is Some ==> res.1@->Some_0.retired().obj() == res.1@->Some_0.obj(),
            res.1@ is Some ==> res.1@->Some_0.retired().removal().root == self.id(),
            res.1@ is Some ==> res.1@->Some_0.retired().removal().observed_by(final(tv)@),
            res.1@ is Some ==> OwnPred::owns(res.0, res.1@->Some_0.ownership()),
    {
        let result;
        let ghost start_view = tv@;
        proof_decl! {
            let tracked retired_ownership;
        }
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (mut points_to, mut g) = pair;
            proof {
                assert(points_to.loc() == self.native_loc());
            }
            let ghost prev = points_to.hist();
            let ghost previous_removals = g.removals();
            let swap = raw_atomic.swap_release(value, Tracked(tv), Tracked(&mut points_to));
            result = swap.0;
            let ghost update = swap.2@;
            let ghost next = points_to.hist();
            proof {
                assert(rcu_spec::rcu_owned_root_history_inv(prev, g));
                assert(rcu_spec::rcu_current_ownership_inv::<T, O, OwnPred>(g));
                rcu_spec::lemma_current_owned_resources::<T, O, OwnPred>(prev, &g);
                if !self.constant().nullable {
                    assert(!value.is_null());
                }
                rcu_spec::preserve_rcu_history_inv_on_push(
                    self.constant().nullable,
                    prev,
                    next,
                    update.load_timestamp + 1,
                    value,
                    update.store_message_view,
                );
                let tracked detached = g.tracked_push_fresh::<OwnPred>(
                    prev,
                    next,
                    update.load_timestamp,
                    update.load_timestamp + 1,
                    value,
                    update.store_message_view,
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
                    == update.load_timestamp + 1);
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
                assert forall|obj: nat| g.removals().contains_key(obj) implies {
                    let removal = #[trigger] g.removals()[obj];
                    points_to.get_timestamp(removal.message_view) == Some(removal.timestamp)
                } by {
                    match detached {
                        Some(detached) => {
                            if obj == detached.obj() {
                                assert(g.removals()[obj] == detached.retired().removal());
                            } else {
                                assert(previous_removals.contains_key(obj));
                                assert(g.removals()[obj] == previous_removals[obj]);
                            }
                        },
                        None => {
                            assert(previous_removals.contains_key(obj));
                            assert(g.removals()[obj] == previous_removals[obj]);
                        },
                    }
                };
                retired_ownership = detached;
                pair = (points_to, g);
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
        Tracked(tv): Tracked<&mut ViewSeen>,
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
            old(tv)@.spec_le(final(tv)@),
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
        let ghost start_view = tv@;
        proof_decl! {
            let tracked retired_ownership;
        }
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (mut points_to, mut g) = pair;
            proof {
                assert(points_to.loc() == self.native_loc());
            }
            let ghost prev = points_to.hist();
            let ghost previous_removals = g.removals();
            proof_decl! {
                let tracked release_view = vstd::thread_view::ReleaseViewSeen::new();
            }
            let cas_result = raw_atomic.compare_exchange(
                current,
                new,
                Ordering::AcqRel,
                Ordering::Acquire,
                Tracked(tv),
                Tracked(release_view),
                Tracked(&mut points_to),
            );
            result = (cas_result.0, Ghost(cas_result.2@.load_timestamp));
            let ghost update = cas_result.2@;
            let ghost next = points_to.hist();
            proof {
                assert(rcu_spec::rcu_owned_root_history_inv(prev, g));
                assert(rcu_spec::rcu_current_ownership_inv::<T, O, OwnPred>(g));
                rcu_spec::lemma_current_owned_resources::<T, O, OwnPred>(prev, &g);
                match cas_result.0 {
                    Result::Ok(_) => {
                        rcu_spec::preserve_rcu_history_inv_on_push(
                            self.constant().nullable,
                            prev,
                            next,
                            update.load_timestamp + 1,
                            new,
                            update.store_message_view,
                        );
                        let tracked detached = g.tracked_push_fresh::<OwnPred>(
                            prev,
                            next,
                            update.load_timestamp,
                            update.load_timestamp + 1,
                            new,
                            update.store_message_view,
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
                        assert forall|obj: nat| g.removals().contains_key(obj) implies {
                            let removal = #[trigger] g.removals()[obj];
                            points_to.get_timestamp(removal.message_view)
                                == Some(removal.timestamp)
                        } by {
                            match detached {
                                Some(detached) => {
                                    if obj == detached.obj() {
                                        assert(g.removals()[obj] == detached.retired().removal());
                                    } else {
                                        assert(previous_removals.contains_key(obj));
                                        assert(g.removals()[obj] == previous_removals[obj]);
                                    }
                                },
                                None => {
                                    assert(previous_removals.contains_key(obj));
                                    assert(g.removals()[obj] == previous_removals[obj]);
                                },
                            }
                        };
                        retired_ownership = (detached, None);
                    },
                    Result::Err(_) => {
                        retired_ownership = (None, new_ownership);
                        assert(next == prev);
                    },
                }
                pair = (points_to, g);
            }
        });
        (result.0, result.1, Tracked(retired_ownership))
    }
}

/// Native IRC11 weak boolean atomic specialized for the RCU monitor flag.
pub struct RcuMonitorWeakAtomicBool {
    atomic: Irc11AtomicBool,
    tracked_atomic_inv: Tracked<
        AtomicInvariant<
            Irc11AtomicId,
            (AtomicPointsTo<bool>, rcu_spec::RcuMonitorFlagGhost),
            rcu_spec::RcuMonitorFlagInv,
        >,
    >,
}

impl RcuMonitorWeakAtomicBool {
    pub closed spec fn id(&self) -> Irc11AtomicId {
        self.atomic.loc()
    }

    pub closed spec fn well_formed(&self) -> bool {
        self.tracked_atomic_inv@.constant() == self.id()
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(&self) -> bool {
        self.well_formed()
    }

    pub const fn new() -> (res: Self)
        ensures
            res.well_formed(),
    {
        let (atomic, Tracked(points_to), Tracked(initial_view), Ghost(timestamp)) =
            Irc11AtomicBool::new(false);
        let tracked flag_ghost = rcu_spec::RcuMonitorFlagGhost::tracked_initial(timestamp);
        proof {
            rcu_spec::rcu_monitor_flag_initial_inv(
                points_to.hist(),
                timestamp,
                initial_view@,
            );
            assert(rcu_spec::RcuMonitorFlagInv::inv(
                atomic.loc(),
                (points_to, flag_ghost),
            ));
        }
        let tracked pair = (points_to, flag_ghost);
        let tracked atomic_inv = AtomicInvariant::new(atomic.loc(), pair, 0);
        Self { atomic, tracked_atomic_inv: Tracked(atomic_inv) }
    }

    pub fn load_relaxed(&self, Tracked(tv): Tracked<&mut ViewSeen>) -> (res: (
        bool,
        Ghost<nat>,
    ))
        requires
            self.well_formed(),
        ensures
            old(tv)@.spec_le(final(tv)@),
    {
        let result;
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (points_to, flag_ghost) = pair;
            let loaded = raw_atomic.load(
                Ordering::Relaxed,
                Tracked(tv),
                Tracked(&points_to),
            );
            result = (loaded.0, Ghost(loaded.2@.timestamp));
            proof {
                pair = (points_to, flag_ghost);
            }
        });
        result
    }

    fn raw_atomic(&self) -> (res: &Irc11AtomicBool)
        requires
            self.well_formed(),
        ensures
            res.loc() == self.id(),
    {
        &self.atomic
    }

    proof fn tracked_atomic_inv(tracked &self) -> (tracked res: &vstd::invariant::AtomicInvariant<
        Irc11AtomicId,
        (AtomicPointsTo<bool>, rcu_spec::RcuMonitorFlagGhost),
        rcu_spec::RcuMonitorFlagInv,
    >)
        requires
            self.well_formed(),
        ensures
            res.constant() == self.id(),
    {
        self.tracked_atomic_inv.borrow()
    }

    /// Relaxed-store helper for the RCU monitor flag.
    ///
    /// The executable flag remains a relaxed atomic flag, matching the old
    /// monitor protocol. The proof-side effect is stronger: each stored flag
    /// message inserts the lock-protected monitor-state snapshot supplied by
    /// the writer.
    #[inline(always)]
    pub fn store_relaxed_rcu_monitor(
        &self,
        value: bool,
        Ghost(state): Ghost<rcu_spec::MonitorStateView>,
        Tracked(tv): Tracked<&mut ViewSeen>,
    )
        requires
            self.well_formed(),
            state.wf(),
            !value ==> state.no_pending_work(),
        ensures
            old(tv)@.spec_le(final(tv)@),
    {
        proof {
            use_type_invariant(self);
        }
        let raw_atomic = self.raw_atomic();
        vstd::invariant::open_atomic_invariant!(self.tracked_atomic_inv() => pair => {
            let tracked (mut points_to, mut flag_ghost) = pair;
            proof {
                assert(points_to.loc() == self.id());
                assert(raw_atomic.loc() == self.id());
            }
            let ghost prev = points_to.hist();
            proof_decl! {
                let tracked release_view = ReleaseViewSeen::new();
            }
            let store = raw_atomic.store(
                value,
                Ordering::Relaxed,
                Tracked(tv),
                Tracked(release_view),
                Tracked(&mut points_to),
            );
            let ghost next = points_to.hist();
            proof {
                rcu_spec::preserve_rcu_monitor_flag_inv_on_insert(
                    prev,
                    next,
                    store@.timestamp,
                    value,
                    store@.message_view,
                    flag_ghost,
                    flag_ghost.insert(store@.timestamp, state),
                    state,
                );
                flag_ghost = flag_ghost.tracked_insert(store@.timestamp, state);
                pair = (points_to, flag_ghost);
            }
        });
    }
}

} // verus!
