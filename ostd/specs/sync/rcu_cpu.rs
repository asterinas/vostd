// SPDX-License-Identifier: MPL-2.0
//! CPU-local grace-period participation for preemptible RCU.
//!
//! This is the proof component used to refine the paper's abstract reader guard
//! to Asterinas's per-CPU quiescent-state implementation. A
//! [`CpuRcuParticipant`] is intended to stay in one CPU core's tracked local
//! state across task switches. Starting a reader splits a fractional
//! [`CpuRcuReaderFragment`]. Reporting a quiescent state requires the whole
//! fraction, so it cannot race with a live reader from the generation being
//! closed.
//!
//! A report also creates an idempotent [`CpuRcuClosedGeneration`] resource.
//! Resource validity gives the two facts needed by the relaxed-memory proof:
//!
//! - a closed generation is strictly older than every reader that can coexist
//!   with its report;
//! - the report's weak-memory view is included in every such later reader's
//!   participant view, which [`CpuRcuParticipant::tracked_start_reader`]
//!   requires the task's start view to include.
//!
//! # Refinement boundary
//!
//! A participant generation is not the global epoch from the paper's concrete
//! epoch-based implementation. It only names the interval between two
//! quiescent reports on one CPU. A complete grace period must separately prove
//! that every relevant CPU reported after the callback's retire point and that
//! each report view includes the callback's retire view.
//!
//! The end-to-end refinement must enforce all of the following:
//!
//! - preemption is disabled before splitting a reader fragment and remains
//!   disabled until that same fragment is returned;
//! - the fragment is created before the first protected load and is retained by
//!   the executable RCU guard until guard destruction;
//! - only the scheduler-owned CPU-local participant can issue a report;
//! - a task entering after a report imports the participant's persistent view
//!   before starting a reader.
//!
//! The current refinement treats `online_cpus()` as stable for a grace period
//! and covers only readers represented by a task `RunningTaskContext`.
//! CPU-hotplug transitions and interrupt/NMI readers need separate
//! participants before they can be included in the end-to-end theorem.
//!
//! `RunningTaskContext` owns the scheduler-checked-out canonical participant.
//! Its older task/session generation remains a distinct preemption-session
//! counter and is not an authority for this persistent CPU generation. Reader
//! contexts obtain their CPU generation from [`CpuRcuReaderFragment`].
use crate::specs::{
    mm::cpu::{CpuId, online_cpus},
    task::cpu_core::{CpuCoreLocalState, CpuCoreOwner, CpuCoreOwnerBinding, CpuCoreRegistration},
};
use vstd::{
    modes::tracked_swap,
    prelude::*,
    resource::{
        Loc,
        agree::AgreementRA,
        algebra::{Resource, ResourceAlgebra},
        frac::FractionRA,
        map::{GhostMapAuth, GhostPointsTo},
        product::ProductRA,
        relations::frame_preserving_update_opt,
    },
};

use super::rcu::{
    RcuBlockInfo, RcuInactive, RcuProtectedPtr, RcuReadGuardToken, RcuReaderContext,
    RcuRetiredFact, RcuRetiredFacts, RcuRetiredRecord, RcuSeenRemoved,
};
use vstd_extra::atomic_irc11::{ThreadView as Irc11ThreadView, ThreadViewOrder};
use vstd_extra::rcu_read_pool::{RcuTrackedReadLease, RcuTrackedReadPoolRegistry};

verus! {

broadcast use {vstd::set::group_set_lemmas, vstd::thread_view::group_thread_view_axioms};

/// One CPU quiescent report retained by the participant PCM.
pub ghost struct CpuRcuReportView {
    pub cpu: CpuId,
    pub generation: nat,
    pub view: Irc11ThreadView,
    pub known_retired: Set<RcuRetiredRecord>,
}

pub(super) ghost struct CpuRcuStateView {
    pub(super) cpu: CpuId,
    pub(super) generation: nat,
    pub(super) view: Irc11ThreadView,
    pub(super) known_retired: Set<RcuRetiredRecord>,
}

pub(super) type CpuRcuState = ProductRA<FractionRA, AgreementRA<CpuRcuStateView>>;

pub(super) ghost struct CpuRcuCarrier {
    pub(super) state: Option<CpuRcuState>,
    pub(super) closed: Set<CpuRcuReportView>,
}

impl CpuRcuCarrier {
    pub(super) open spec fn records_observed(
        records: Set<RcuRetiredRecord>,
        view: Irc11ThreadView,
    ) -> bool {
        forall|record: RcuRetiredRecord| #[trigger]
            records.contains(record) ==> record.removal.observed_by(view)
    }

    pub(super) open spec fn state(
        cpu: CpuId,
        generation: nat,
        view: Irc11ThreadView,
        known_retired: Set<RcuRetiredRecord>,
        fraction: real,
    ) -> Self {
        CpuRcuCarrier {
            state: Some(
                ProductRA {
                    left: FractionRA::Frac(fraction),
                    right: AgreementRA::Agree(
                        CpuRcuStateView { cpu, generation, view, known_retired },
                    ),
                },
            ),
            closed: Set::empty(),
        }
    }

    pub(super) open spec fn closed(report: CpuRcuReportView) -> Self {
        CpuRcuCarrier { state: None, closed: Set::empty().insert(report) }
    }

    pub(super) open spec fn reports_fit(
        state: CpuRcuStateView,
        reports: Set<CpuRcuReportView>,
    ) -> bool {
        forall|report: CpuRcuReportView| #[trigger]
            reports.contains(report) ==> {
                &&& report.cpu == state.cpu
                &&& report.generation < state.generation
                &&& report.view.spec_le(state.view)
                &&& report.known_retired.subset_of(state.known_retired)
                &&& CpuRcuCarrier::records_observed(report.known_retired, report.view)
            }
    }

    pub(super) open spec fn state_view(self) -> CpuRcuStateView {
        self.state.unwrap().right->Agree_0
    }

    pub(super) open spec fn fraction(self) -> real {
        self.state.unwrap().left->Frac_0
    }

    pub(super) open spec fn has_valid_state(self) -> bool {
        &&& self.state is Some
        &&& self.state.unwrap().left is Frac
        &&& self.state.unwrap().right is Agree
        &&& self.state.valid()
    }
}

impl ResourceAlgebra for CpuRcuCarrier {
    closed spec fn valid(self) -> bool {
        match self.state {
            Some(ProductRA { left: FractionRA::Frac(_), right: AgreementRA::Agree(state) }) => {
                &&& self.state.valid()
                &&& CpuRcuCarrier::reports_fit(state, self.closed)
                &&& CpuRcuCarrier::records_observed(state.known_retired, state.view)
            },
            None => forall|report: CpuRcuReportView| #[trigger]
                self.closed.contains(report) ==> CpuRcuCarrier::records_observed(
                    report.known_retired,
                    report.view,
                ),
            _ => false,
        }
    }

    closed spec fn op(left: Self, right: Self) -> Self {
        CpuRcuCarrier {
            state: Option::<CpuRcuState>::op(left.state, right.state),
            closed: left.closed.union(right.closed),
        }
    }

    proof fn valid_op(left: Self, right: Self) {
        Option::<CpuRcuState>::valid_op(left.state, right.state);
        match left.state {
            None => {
                let ghost combined = CpuRcuCarrier::op(left, right);
                assert(combined.valid());
                assert(combined.closed == left.closed.union(right.closed));
                assert forall|report: CpuRcuReportView| #[trigger]
                    left.closed.contains(report) implies CpuRcuCarrier::records_observed(
                    report.known_retired,
                    report.view,
                ) by {
                    assert(combined.closed.contains(report));
                    match right.state {
                        None => {
                            assert(combined.state is None);
                        },
                        Some(
                            ProductRA {
                                left: FractionRA::Frac(_),
                                right: AgreementRA::Agree(right_state),
                            },
                        ) => {
                            assert(combined.state == right.state);
                            assert(combined.state_view() == right_state);
                            assert(CpuRcuCarrier::reports_fit(right_state, combined.closed));
                        },
                        _ => {},
                    }
                };
            },
            Some(
                ProductRA { left: FractionRA::Frac(_), right: AgreementRA::Agree(left_state) },
            ) => {
                assert forall|report: CpuRcuReportView| #[trigger]
                    left.closed.contains(report) implies {
                    &&& report.cpu == left_state.cpu
                    &&& report.generation < left_state.generation
                    &&& report.view.spec_le(left_state.view)
                    &&& report.known_retired.subset_of(left_state.known_retired)
                    &&& CpuRcuCarrier::records_observed(report.known_retired, report.view)
                } by {
                    assert(left.closed.union(right.closed).contains(report));
                    match right.state {
                        None => {},
                        Some(
                            ProductRA { left: FractionRA::Frac(_), right: AgreementRA::Agree(_) },
                        ) => {},
                        _ => {},
                    }
                };
            },
            _ => {},
        }
    }

    proof fn commutative(left: Self, right: Self) {
        Option::<CpuRcuState>::commutative(left.state, right.state);
        assert(left.closed.union(right.closed) =~= right.closed.union(left.closed));
    }

    proof fn associative(left: Self, middle: Self, right: Self) {
        Option::<CpuRcuState>::associative(left.state, middle.state, right.state);
        assert(left.closed.union(middle.closed.union(right.closed)) =~= left.closed.union(
            middle.closed,
        ).union(right.closed));
    }
}

/// CPU-owned fractional authority for one RCU participation generation.
///
/// This token belongs permanently to the CPU core named by [`Self::cpu`].
/// It may cross task execution sessions, but it must never migrate to another
/// CPU's local-state aggregate.
pub tracked struct CpuRcuParticipant {
    resource: Resource<CpuRcuCarrier>,
    known_retired: RcuRetiredFacts,
}

/// Generic CPU-core registration evidence specialized to the RCU local state.
pub type CpuRcuCoreBinding = CpuCoreOwnerBinding<CpuRcuParticipant>;

/// Linear witness that one reader is live in a CPU participation generation.
pub tracked struct CpuRcuReaderFragment {
    resource: Resource<CpuRcuCarrier>,
    known_retired: RcuRetiredFacts,
}

/// Idempotent proof that one CPU generation has passed a quiescent boundary.
///
/// The resource can be split into two identical copies because its PCM element
/// is idempotent. It contains no executable state.
pub tracked struct CpuRcuClosedGeneration {
    resource: Resource<CpuRcuCarrier>,
    known_retired: RcuRetiredFacts,
    binding: CpuRcuCoreBinding,
}

/// Refinement of the paper guard with one live CPU reader fragment.
///
/// The wrapped [`RcuReadGuardToken`] remains the reusable abstract
/// `Guard(tid, X, G)`. The fragment is the Asterinas implementation witness
/// that prevents this CPU from reporting a quiescent boundary until the guard
/// is destroyed. Keeping both resources in one linear token prevents the
/// executable guard from ending only the abstract critical section while
/// silently losing its CPU participation.
#[verifier::reject_recursive_types(T)]
pub tracked struct CpuRcuReadGuardToken<T> {
    paper_guard: RcuReadGuardToken<T>,
    reader: CpuRcuReaderFragment,
    binding: CpuRcuCoreBinding,
}

/// CPU-generation witness retained beside one active physical read lease.
///
/// The executable guard keeps the other half of `reader`. The ghost snapshot
/// records which abstract guard protected the allocation without duplicating
/// that guard's linear `Guard(tid, X, G)` resource.
#[verifier::reject_recursive_types(T)]
pub tracked struct CpuRcuReadLeaseWitness<T> {
    reader: CpuRcuReaderFragment,
    ghost paper_guard: RcuReadGuardToken<T>,
    binding: CpuRcuCoreBinding,
    protected: RcuProtectedPtr<T>,
}

/// Physical-permission pools associated with one RCU root.
///
/// A pool is indexed by the allocation identity from [`RcuBlockInfo`], rather
/// than by its address. Pools therefore survive root replacement and remain
/// distinguishable when a reclaimed address is later reused. Every active
/// lease record retains the CPU-generation witness needed by the monitor to
/// rule it out after a completed grace period.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuRootPermissionState<T, O> {
    registry: RcuTrackedReadPoolRegistry<nat, O, CpuRcuReadLeaseWitness<T>>,
    active_leases: GhostMapAuth<nat, RcuActiveLeaseBinding>,
    reclaim_state: GhostMapAuth<nat, Option<*mut T>>,
    unretired_claims: Map<nat, GhostPointsTo<nat, Option<*mut T>>>,
    reclaimed: Map<nat, RcuReclaimedWitness>,
    ghost scheduler: Loc,
    ghost domain: Loc,
    ghost root: Loc,
    ghost retire_observation_registry: Loc,
}

/// Authoritative metadata for one lease currently registered at an RCU root.
///
/// The matching [`RcuRootReadLease`] owns the linear map points-to token.  Its
/// agreement with the authority lets a later invariant opening recover the
/// exact active record created by the guarded load.
pub ghost struct RcuActiveLeaseBinding {
    key: nat,
    pool_id: Loc,
    fraction: real,
    participant_id: Loc,
    reader_fraction: real,
    domain: Loc,
    root: Loc,
    reader: RcuReaderContext,
    start_view: Irc11ThreadView,
    protected_addr: usize,
}

/// Physical read lease together with proof that its active record still
/// belongs to the same RCU root.
#[verifier::reject_recursive_types(O)]
pub tracked struct RcuRootReadLease<O> {
    lease: RcuTrackedReadLease<nat, O>,
    active: GhostPointsTo<nat, RcuActiveLeaseBinding>,
}

/// Unique right to reclaim one retired allocation's physical permission.
///
/// The matching authority remains in [`RcuRootPermissionState`]. Validation
/// against that authority proves that the allocation has not already been
/// reclaimed; consuming the claim changes its authoritative state exactly
/// once.
pub tracked struct RcuReclaimClaim<T> {
    points_to: GhostPointsTo<nat, Option<*mut T>>,
}

/// Persistent grace-period evidence retained after one allocation is reclaimed.
///
/// A later weak load may still select the allocation's old atomic-history
/// message. The closed generation for its CPU proves that such a coexisting
/// reader is newer and already carries `record` in its retired set.
pub tracked struct RcuReclaimedWitness {
    ghost record: RcuRetiredRecord,
    ghost scheduler: Loc,
    retired: RcuRetiredFact,
    closed_generations: Map<CpuId, CpuRcuClosedGeneration>,
}

unsafe impl<
    T,
    O: vstd::thread_view::Objective,
> vstd::thread_view::Objective for RcuRootPermissionState<T, O> {

}

unsafe impl<T> vstd::thread_view::Objective for RcuReclaimClaim<T> {

}

unsafe impl vstd::thread_view::Objective for RcuReclaimedWitness {

}

proof fn lemma_choose_singleton_report(report: CpuRcuReportView)
    ensures
        (choose|candidate: CpuRcuReportView| Set::empty().insert(report).contains(candidate))
            == report,
{
    let ghost reports = Set::empty().insert(report);
    assert(reports.contains(report));
    let ghost chosen = choose|candidate: CpuRcuReportView| reports.contains(candidate);
    assert(reports.contains(chosen));
    assert(chosen == report);
}

impl CpuRcuParticipant {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.resource.value().has_valid_state()
        &&& self.resource.value().closed.is_empty()
        &&& self.resource.value().state_view().known_retired == self.known_retired.records()
        &&& CpuRcuCarrier::records_observed(
            self.resource.value().state_view().known_retired,
            self.resource.value().state_view().view,
        )
    }

    /// Creates generation zero for one CPU.
    pub proof fn new(cpu: CpuId, view: Irc11ThreadView) -> (tracked res: Self)
        ensures
            res.cpu() == cpu,
            res.generation() == 0,
            res.view() == view,
            res.fraction() == 1real,
            res.wf(),
    {
        let tracked known_retired = RcuRetiredFacts::empty();
        let tracked resource = Resource::alloc(
            CpuRcuCarrier::state(cpu, 0, view, known_retired.records(), 1real),
        );
        CpuRcuParticipant { resource, known_retired }
    }

    /// Stable identity of this CPU's RCU participant.
    pub closed spec fn id(self) -> Loc {
        self.resource.loc()
    }

    pub closed spec fn cpu(self) -> CpuId {
        self.resource.value().state_view().cpu
    }

    pub closed spec fn generation(self) -> nat {
        self.resource.value().state_view().generation
    }

    pub closed spec fn view(self) -> Irc11ThreadView {
        self.resource.value().state_view().view
    }

    /// Persistent retirement facts known before this CPU generation started.
    pub closed spec fn known_retired(self) -> Set<RcuRetiredRecord> {
        self.known_retired.records()
    }

    pub closed spec fn fraction(self) -> real {
        self.resource.value().fraction()
    }

    pub open spec fn wf(self) -> bool {
        0real < self.fraction() <= 1real
    }

    /// Starts a reader in the current CPU generation.
    ///
    /// `start_view` is the task view after it has imported the persistent CPU
    /// view. The caller chooses a positive rational `reader_fraction`, so this
    /// protocol imposes no fixed bound on the number of readers.
    pub proof fn tracked_start_reader(
        tracked self,
        start_view: Irc11ThreadView,
        reader_fraction: real,
    ) -> (tracked res: (CpuRcuParticipant, CpuRcuReaderFragment))
        requires
            self.wf(),
            self.view().spec_le(start_view),
            0real < reader_fraction < self.fraction(),
        ensures
            res.0.id() == self.id(),
            res.0.cpu() == self.cpu(),
            res.0.generation() == self.generation(),
            res.0.view() == self.view(),
            res.0.known_retired() == self.known_retired(),
            res.0.fraction() == self.fraction() - reader_fraction,
            res.0.wf(),
            res.1.participant_id() == self.id(),
            res.1.cpu() == self.cpu(),
            res.1.generation() == self.generation(),
            res.1.participant_view() == self.view(),
            res.1.known_retired() == self.known_retired(),
            res.1.fraction() == reader_fraction,
            res.1.wf(),
    {
        use_type_invariant(&self);
        let ghost participant = CpuRcuCarrier::state(
            self.cpu(),
            self.generation(),
            self.view(),
            self.known_retired(),
            self.fraction() - reader_fraction,
        );
        let ghost reader = CpuRcuCarrier::state(
            self.cpu(),
            self.generation(),
            self.view(),
            self.known_retired(),
            reader_fraction,
        );
        assert(self.resource.value() == CpuRcuCarrier::state(
            self.cpu(),
            self.generation(),
            self.view(),
            self.known_retired(),
            self.fraction(),
        ));
        assert(0real < self.fraction() - reader_fraction <= 1real);
        assert(0real < reader_fraction <= 1real);
        assert(FractionRA::op(
            FractionRA::Frac(self.fraction() - reader_fraction),
            FractionRA::Frac(reader_fraction),
        ) == FractionRA::Frac(self.fraction()));
        assert(AgreementRA::op(
            AgreementRA::Agree(self.resource.value().state_view()),
            AgreementRA::Agree(self.resource.value().state_view()),
        ) == AgreementRA::Agree(self.resource.value().state_view()));
        assert(Option::<CpuRcuState>::op(participant.state, reader.state)
            == self.resource.value().state);
        assert(participant.closed.union(reader.closed).is_empty());
        assert(self.resource.value() == CpuRcuCarrier::op(participant, reader));
        let tracked (participant_resource, reader_resource) = self.resource.split(
            participant,
            reader,
        );
        let tracked reader_known_retired = self.known_retired.tracked_duplicate();
        (
            CpuRcuParticipant { resource: participant_resource, known_retired: self.known_retired },
            CpuRcuReaderFragment { resource: reader_resource, known_retired: reader_known_retired },
        )
    }

    /// Splits half of the participant's current rational fraction in place.
    ///
    /// Repeated nested reads therefore remain unbounded: each live reader gets
    /// a positive fraction, while the participant retains a positive fraction
    /// for subsequent splits. The complete fraction can be recovered only by
    /// returning every fragment.
    pub proof fn tracked_start_reader_in_place(
        tracked &mut self,
        start_view: Irc11ThreadView,
    ) -> (tracked reader: CpuRcuReaderFragment)
        requires
            old(self).wf(),
            old(self).view().spec_le(start_view),
        ensures
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).generation() == old(self).generation(),
            final(self).view() == old(self).view(),
            final(self).known_retired() == old(self).known_retired(),
            final(self).fraction() == old(self).fraction() / 2real,
            final(self).wf(),
            reader.participant_id() == old(self).id(),
            reader.cpu() == old(self).cpu(),
            reader.generation() == old(self).generation(),
            reader.participant_view() == old(self).view(),
            reader.known_retired() == old(self).known_retired(),
            reader.fraction() == old(self).fraction() / 2real,
            reader.wf(),
    {
        let ghost old_cpu = self.cpu();
        let ghost old_view = self.view();
        let ghost reader_fraction = self.fraction() / 2real;
        assert(0real < reader_fraction < self.fraction());
        let tracked mut owned = CpuRcuParticipant::new(old_cpu, old_view);
        tracked_swap(self, &mut owned);
        let tracked (mut participant, reader) = owned.tracked_start_reader(
            start_view,
            reader_fraction,
        );
        tracked_swap(self, &mut participant);
        reader
    }

    /// Returns a reader fragment to its CPU-local participant.
    pub proof fn tracked_stop_reader(
        tracked self,
        tracked reader: CpuRcuReaderFragment,
    ) -> (tracked res: CpuRcuParticipant)
        requires
            self.wf(),
            reader.wf(),
            self.id() == reader.participant_id(),
        ensures
            res.id() == self.id(),
            res.cpu() == self.cpu(),
            res.generation() == self.generation(),
            res.view() == self.view(),
            res.known_retired() == self.known_retired(),
            res.fraction() == self.fraction() + reader.fraction(),
            res.wf(),
    {
        use_type_invariant(&self);
        use_type_invariant(&reader);
        let tracked mut participant_resource = self.resource;
        participant_resource.validate_2(&reader.resource);
        let tracked resource = participant_resource.join(reader.resource);
        CpuRcuParticipant { resource, known_retired: self.known_retired }
    }

    /// Returns a reader fragment to this participant in place.
    pub proof fn tracked_stop_reader_in_place(
        tracked &mut self,
        tracked reader: CpuRcuReaderFragment,
    )
        requires
            old(self).wf(),
            reader.wf(),
            old(self).id() == reader.participant_id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).generation() == old(self).generation(),
            final(self).view() == old(self).view(),
            final(self).known_retired() == old(self).known_retired(),
            final(self).fraction() == old(self).fraction() + reader.fraction(),
            final(self).wf(),
    {
        let ghost old_cpu = self.cpu();
        let ghost old_view = self.view();
        let tracked mut owned = CpuRcuParticipant::new(old_cpu, old_view);
        tracked_swap(self, &mut owned);
        let tracked mut participant = owned.tracked_stop_reader(reader);
        tracked_swap(self, &mut participant);
    }

    /// Closes the current generation and imports retirement facts observed by
    /// the report view.
    ///
    /// A whole fraction is incompatible with every live reader fragment.
    /// The returned participant starts the next generation and retains the
    /// report view and persistent retirement facts for task sessions that run
    /// later on this CPU.
    pub proof fn tracked_report_quiescent_with(
        tracked self,
        tracked binding: CpuRcuCoreBinding,
        report_view: Irc11ThreadView,
        tracked learned: &RcuRetiredFacts,
    ) -> (tracked res: (CpuRcuParticipant, CpuRcuClosedGeneration))
        requires
            self.wf(),
            self.fraction() == 1real,
            self.view().spec_le(report_view),
            learned.observed_by(report_view),
            binding.cpu() == self.cpu(),
            binding.single_local_id() == self.id(),
        ensures
            res.0.id() == self.id(),
            res.0.cpu() == self.cpu(),
            res.0.generation() == self.generation() + 1,
            res.0.view() == report_view,
            res.0.known_retired() == self.known_retired().union(learned.records()),
            res.0.fraction() == 1real,
            res.0.wf(),
            res.1.participant_id() == self.id(),
            res.1.cpu() == self.cpu(),
            res.1.closed_generation() == self.generation(),
            res.1.view() == report_view,
            res.1.known_retired() == self.known_retired().union(learned.records()),
            res.1.scheduler() == binding.registry(),
            res.1.wf(),
    {
        use_type_invariant(&self);
        let ghost old_cpu = self.cpu();
        let ghost old_generation = self.generation();
        let ghost old_view = self.view();
        let ghost old_known_retired = self.known_retired();
        let ghost merged_records = old_known_retired.union(learned.records());
        assert(self.resource.value() == CpuRcuCarrier::state(
            old_cpu,
            old_generation,
            old_view,
            old_known_retired,
            1real,
        ));
        assert(CpuRcuCarrier::records_observed(old_known_retired, old_view));
        assert(CpuRcuCarrier::records_observed(merged_records, report_view)) by {
            assert forall|record: RcuRetiredRecord| #[trigger]
                merged_records.contains(record) implies record.removal.observed_by(report_view) by {
                if old_known_retired.contains(record) {
                    assert(record.removal.observed_by(old_view));
                    old_view.lemma_spec_le_transitive(report_view, report_view);
                } else {
                    assert(learned.records().contains(record));
                }
            };
        };
        let ghost report = CpuRcuReportView {
            cpu: old_cpu,
            generation: old_generation,
            view: report_view,
            known_retired: merged_records,
        };
        let ghost next_state = CpuRcuCarrier::state(
            old_cpu,
            old_generation + 1,
            report_view,
            merged_records,
            1real,
        );
        let ghost next = CpuRcuCarrier {
            state: next_state.state,
            closed: Set::empty().insert(report),
        };
        assert forall|frame: Option<CpuRcuCarrier>|
            #![trigger Option::<CpuRcuCarrier>::op(Some(self.resource.value()), frame).valid()]
            Option::<CpuRcuCarrier>::op(
                Some(self.resource.value()),
                frame,
            ).valid() implies Option::<CpuRcuCarrier>::op(Some(next), frame).valid() by {
            match frame {
                Some(CpuRcuCarrier { state: None, closed }) => {
                    let ghost frame_carrier = CpuRcuCarrier { state: None, closed };
                    let ghost combined = CpuRcuCarrier::op(self.resource.value(), frame_carrier);
                    assert(combined.valid());
                    assert(Option::<CpuRcuState>::op(self.resource.value().state, None)
                        == self.resource.value().state);
                    assert(self.resource.value().closed.is_empty());
                    assert(self.resource.value().closed.union(closed) =~= closed);
                    assert(combined == CpuRcuCarrier {
                        state: self.resource.value().state,
                        closed,
                    });
                    assert(combined.state_view() == CpuRcuStateView {
                        cpu: old_cpu,
                        generation: old_generation,
                        view: old_view,
                        known_retired: old_known_retired,
                    });
                    assert(CpuRcuCarrier::reports_fit(
                        CpuRcuStateView {
                            cpu: old_cpu,
                            generation: old_generation,
                            view: old_view,
                            known_retired: old_known_retired,
                        },
                        closed,
                    ));
                    assert forall|old_report: CpuRcuReportView| #[trigger]
                        closed.contains(old_report) implies {
                        &&& old_report.cpu == old_cpu
                        &&& old_report.generation < old_generation + 1
                        &&& old_report.view.spec_le(report_view)
                        &&& old_report.known_retired.subset_of(merged_records)
                    } by {
                        assert(old_report.generation < old_generation);
                        old_report.view.lemma_spec_le_transitive(old_view, report_view);
                        assert(old_report.known_retired.subset_of(old_known_retired));
                        assert(old_known_retired.subset_of(merged_records));
                    };
                },
                None => {
                    assert(next.valid());
                },
                _ => {},
            }
        };
        let tracked combined = self.resource.update(next);
        let ghost participant = CpuRcuCarrier::state(
            old_cpu,
            old_generation + 1,
            report_view,
            merged_records,
            1real,
        );
        let ghost closed = CpuRcuCarrier::closed(report);
        assert(Option::<CpuRcuState>::op(participant.state, closed.state) == participant.state);
        assert(participant.closed.union(closed.closed) =~= Set::empty().insert(report));
        assert(next == CpuRcuCarrier::op(participant, closed));
        let tracked (participant_resource, closed_resource) = combined.split(participant, closed);
        let tracked mut known_retired = self.known_retired;
        known_retired.tracked_merge(learned);
        let tracked closed_known_retired = known_retired.tracked_duplicate();
        assert(known_retired.records() == merged_records);
        lemma_choose_singleton_report(report);
        (
            CpuRcuParticipant { resource: participant_resource, known_retired },
            CpuRcuClosedGeneration {
                resource: closed_resource,
                known_retired: closed_known_retired,
                binding,
            },
        )
    }

    /// Closes the current generation without importing additional retirement
    /// facts.
    pub proof fn tracked_report_quiescent(
        tracked self,
        tracked binding: CpuRcuCoreBinding,
        report_view: Irc11ThreadView,
    ) -> (tracked res: (CpuRcuParticipant, CpuRcuClosedGeneration))
        requires
            self.wf(),
            self.fraction() == 1real,
            self.view().spec_le(report_view),
            binding.cpu() == self.cpu(),
            binding.single_local_id() == self.id(),
        ensures
            res.0.id() == self.id(),
            res.0.cpu() == self.cpu(),
            res.0.generation() == self.generation() + 1,
            res.0.view() == report_view,
            res.0.known_retired() == self.known_retired(),
            res.0.fraction() == 1real,
            res.0.wf(),
            res.1.participant_id() == self.id(),
            res.1.cpu() == self.cpu(),
            res.1.closed_generation() == self.generation(),
            res.1.view() == report_view,
            res.1.known_retired() == self.known_retired(),
            res.1.scheduler() == binding.registry(),
            res.1.wf(),
    {
        let tracked empty = RcuRetiredFacts::empty();
        let tracked res = self.tracked_report_quiescent_with(binding, report_view, &empty);
        assert(empty.records() == Set::<RcuRetiredRecord>::empty());
        assert(self.known_retired().union(empty.records()) =~= self.known_retired());
        res
    }

    /// Closes the current generation while retaining this CPU's canonical
    /// participant in place.
    ///
    /// The full-fraction requirement is the resource-level statement that no
    /// reader fragment from the generation being closed remains live.
    pub proof fn tracked_report_quiescent_in_place(
        tracked &mut self,
        tracked binding: CpuRcuCoreBinding,
        report_view: Irc11ThreadView,
    ) -> (tracked closed: CpuRcuClosedGeneration)
        requires
            old(self).wf(),
            old(self).fraction() == 1real,
            old(self).view().spec_le(report_view),
            binding.cpu() == old(self).cpu(),
            binding.single_local_id() == old(self).id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).generation() == old(self).generation() + 1,
            final(self).view() == report_view,
            final(self).known_retired() == old(self).known_retired(),
            final(self).fraction() == 1real,
            final(self).wf(),
            closed.participant_id() == old(self).id(),
            closed.cpu() == old(self).cpu(),
            closed.closed_generation() == old(self).generation(),
            closed.view() == report_view,
            closed.known_retired() == old(self).known_retired(),
            closed.scheduler() == binding.registry(),
            closed.wf(),
    {
        let ghost old_cpu = self.cpu();
        let ghost old_view = self.view();
        let tracked mut owned = CpuRcuParticipant::new(old_cpu, old_view);
        tracked_swap(self, &mut owned);
        let tracked (mut participant, closed) = owned.tracked_report_quiescent(
            binding,
            report_view,
        );
        tracked_swap(self, &mut participant);
        closed
    }

    /// In-place form of [`Self::tracked_report_quiescent_with`].
    pub proof fn tracked_report_quiescent_with_in_place(
        tracked &mut self,
        tracked binding: CpuRcuCoreBinding,
        report_view: Irc11ThreadView,
        tracked learned: &RcuRetiredFacts,
    ) -> (tracked closed: CpuRcuClosedGeneration)
        requires
            old(self).wf(),
            old(self).fraction() == 1real,
            old(self).view().spec_le(report_view),
            learned.observed_by(report_view),
            binding.cpu() == old(self).cpu(),
            binding.single_local_id() == old(self).id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).generation() == old(self).generation() + 1,
            final(self).view() == report_view,
            final(self).known_retired() == old(self).known_retired().union(learned.records()),
            final(self).fraction() == 1real,
            final(self).wf(),
            closed.participant_id() == old(self).id(),
            closed.cpu() == old(self).cpu(),
            closed.closed_generation() == old(self).generation(),
            closed.view() == report_view,
            closed.known_retired() == old(self).known_retired().union(learned.records()),
            closed.scheduler() == binding.registry(),
            closed.wf(),
    {
        let ghost old_cpu = self.cpu();
        let ghost old_view = self.view();
        let tracked mut owned = CpuRcuParticipant::new(old_cpu, old_view);
        tracked_swap(self, &mut owned);
        let tracked (mut participant, closed) = owned.tracked_report_quiescent_with(
            binding,
            report_view,
            learned,
        );
        tracked_swap(self, &mut participant);
        closed
    }
}

impl CpuCoreLocalState for CpuRcuParticipant {
    open spec fn belongs_to_cpu(self, cpu: CpuId) -> bool {
        self.cpu() == cpu
    }

    open spec fn local_key(self) -> Seq<Loc> {
        seq![self.id()]
    }
}

impl CpuRcuParticipant {
    /// Exposes the participant's generic CPU-local identity to scheduler
    /// clients without requiring them to unfold this module's trait impl.
    pub proof fn lemma_cpu_core_local_state(tracked &self)
        ensures
            self.belongs_to_cpu(self.cpu()),
            self.local_key() == seq![self.id()],
    {
    }
}

impl CpuRcuReaderFragment {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.resource.value().has_valid_state()
        &&& self.resource.value().closed.is_empty()
        &&& self.resource.value().state_view().known_retired == self.known_retired.records()
        &&& CpuRcuCarrier::records_observed(
            self.resource.value().state_view().known_retired,
            self.resource.value().state_view().view,
        )
    }

    pub closed spec fn participant_id(self) -> Loc {
        self.resource.loc()
    }

    pub closed spec fn cpu(self) -> CpuId {
        self.resource.value().state_view().cpu
    }

    pub closed spec fn generation(self) -> nat {
        self.resource.value().state_view().generation
    }

    pub closed spec fn participant_view(self) -> Irc11ThreadView {
        self.resource.value().state_view().view
    }

    pub closed spec fn known_retired(self) -> Set<RcuRetiredRecord> {
        self.known_retired.records()
    }

    pub proof fn tracked_known_retired(tracked &self, record: RcuRetiredRecord) -> (tracked res:
        &super::rcu::RcuRetiredFact)
        requires
            self.known_retired().contains(record),
        ensures
            res.wf(),
            res.record() == record,
    {
        use_type_invariant(self);
        reveal(CpuRcuReaderFragment::known_retired);
        assert(self.known_retired() == self.known_retired.records());
        assert(self.known_retired.records().contains(record));
        self.known_retired.tracked_borrow(record)
    }

    /// Borrows the persistent retirement facts known at this reader's
    /// generation, after lifting their observations to `view`.
    pub proof fn tracked_retired_facts_observed_by(
        tracked &self,
        view: Irc11ThreadView,
    ) -> (tracked res: &RcuRetiredFacts)
        requires
            self.participant_view().spec_le(view),
        ensures
            res.records() == self.known_retired(),
            res.observed_by(view),
    {
        use_type_invariant(self);
        assert forall|record: RcuRetiredRecord| #[trigger]
            self.known_retired.records().contains(record) implies record.removal.observed_by(
            view,
        ) by {
            assert(self.resource.value().state_view().known_retired.contains(record));
            assert(record.removal.observed_by(self.participant_view()));
            self.participant_view().lemma_spec_le_transitive(view, view);
        };
        &self.known_retired
    }

    pub closed spec fn fraction(self) -> real {
        self.resource.value().fraction()
    }

    pub open spec fn wf(self) -> bool {
        0real < self.fraction() <= 1real
    }

    /// Splits this live-reader authority into two equal fragments.
    ///
    /// RCU uses the second fragment as the active-lease witness retained by
    /// the root invariant. The first remains in the executable read guard.
    /// Neither fragment alone permits the CPU participant to report a
    /// quiescent state.
    pub proof fn tracked_split(tracked self) -> (tracked res: (Self, Self))
        requires
            self.wf(),
        ensures
            res.0.wf(),
            res.1.wf(),
            res.0.participant_id() == self.participant_id(),
            res.1.participant_id() == self.participant_id(),
            res.0.cpu() == self.cpu(),
            res.1.cpu() == self.cpu(),
            res.0.generation() == self.generation(),
            res.1.generation() == self.generation(),
            res.0.participant_view() == self.participant_view(),
            res.1.participant_view() == self.participant_view(),
            res.0.known_retired() == self.known_retired(),
            res.1.known_retired() == self.known_retired(),
            res.0.fraction() == self.fraction() / 2real,
            res.1.fraction() == self.fraction() / 2real,
    {
        use_type_invariant(&self);
        let ghost half = self.fraction() / 2real;
        let ghost carrier = CpuRcuCarrier::state(
            self.cpu(),
            self.generation(),
            self.participant_view(),
            self.known_retired(),
            half,
        );
        assert(0real < half <= 1real);
        assert(FractionRA::op(FractionRA::Frac(half), FractionRA::Frac(half)) == FractionRA::Frac(
            self.fraction(),
        ));
        assert(AgreementRA::op(
            AgreementRA::Agree(self.resource.value().state_view()),
            AgreementRA::Agree(self.resource.value().state_view()),
        ) == AgreementRA::Agree(self.resource.value().state_view()));
        assert(self.resource.value() == CpuRcuCarrier::state(
            self.cpu(),
            self.generation(),
            self.participant_view(),
            self.known_retired(),
            self.fraction(),
        ));
        assert(Option::<CpuRcuState>::op(carrier.state, carrier.state)
            == self.resource.value().state);
        assert(carrier.closed.union(carrier.closed) == self.resource.value().closed);
        assert(self.resource.value() == CpuRcuCarrier::op(carrier, carrier));
        let tracked duplicate_known_retired = self.known_retired.tracked_duplicate();
        let tracked (left, right) = self.resource.split(carrier, carrier);
        (
            CpuRcuReaderFragment { resource: left, known_retired: self.known_retired },
            CpuRcuReaderFragment { resource: right, known_retired: duplicate_known_retired },
        )
    }

    /// Recombines two fragments from the same CPU participant generation.
    pub proof fn tracked_join(tracked self, tracked other: Self) -> (tracked res: Self)
        requires
            self.wf(),
            other.wf(),
            self.participant_id() == other.participant_id(),
        ensures
            res.wf(),
            res.participant_id() == self.participant_id(),
            res.cpu() == self.cpu(),
            res.generation() == self.generation(),
            res.participant_view() == self.participant_view(),
            res.known_retired() == self.known_retired(),
            res.fraction() == self.fraction() + other.fraction(),
    {
        use_type_invariant(&self);
        use_type_invariant(&other);
        let tracked mut resource = self.resource;
        resource.validate_2(&other.resource);
        let tracked resource = resource.join(other.resource);
        CpuRcuReaderFragment { resource, known_retired: self.known_retired }
    }
}

impl<T> CpuRcuReadGuardToken<T> {
    pub closed spec fn paper_guard(self) -> RcuReadGuardToken<T> {
        self.paper_guard
    }

    pub closed spec fn reader_fragment(self) -> CpuRcuReaderFragment {
        self.reader
    }

    pub closed spec fn binding(self) -> CpuRcuCoreBinding {
        self.binding
    }

    pub closed spec fn scheduler(self) -> Loc {
        self.binding().registry()
    }

    pub closed spec fn participant_id(self) -> Loc {
        self.reader_fragment().participant_id()
    }

    pub closed spec fn cpu(self) -> CpuId {
        self.reader_fragment().cpu()
    }

    pub closed spec fn generation(self) -> nat {
        self.reader_fragment().generation()
    }

    pub closed spec fn participant_view(self) -> Irc11ThreadView {
        self.reader_fragment().participant_view()
    }

    pub closed spec fn known_retired(self) -> Set<RcuRetiredRecord> {
        self.reader_fragment().known_retired()
    }

    pub closed spec fn domain(self) -> Loc {
        self.paper_guard().domain()
    }

    pub closed spec fn reader_context(self) -> RcuReaderContext {
        self.paper_guard().reader()
    }

    pub closed spec fn root(self) -> Loc {
        self.paper_guard().root()
    }

    pub closed spec fn start_view(self) -> Irc11ThreadView {
        self.paper_guard().start_view()
    }

    pub closed spec fn retire_observation_registry(self) -> Loc {
        self.paper_guard().retire_observation_registry()
    }

    pub closed spec fn reader_registry(self) -> Loc {
        self.paper_guard().reader_registry()
    }

    pub closed spec fn expired(self) -> Set<nat> {
        self.paper_guard().expired()
    }

    pub closed spec fn protected(self) -> Map<usize, nat> {
        self.paper_guard().protected()
    }

    pub closed spec fn seen_removed(self) -> RcuSeenRemoved<T> {
        self.paper_guard().seen_removed()
    }

    pub open spec fn protects(self, addr: usize, obj: nat) -> bool {
        self.paper_guard().protects(addr, obj)
    }

    pub open spec fn protects_pointer(self, ptr: RcuProtectedPtr<T>) -> bool {
        ptr.protected_by(self.paper_guard())
    }

    /// Instantiates the entry-time expiration guarantee for one known
    /// retirement record belonging to this guard's RCU root.
    pub proof fn lemma_known_retired_expired(tracked &self, record: RcuRetiredRecord)
        requires
            self.wf(),
            self.known_retired().contains(record),
            record.domain == self.domain(),
            record.retire_observation_registry == self.retire_observation_registry(),
            record.removal.root == self.root(),
        ensures
            self.expired().contains(record.obj),
    {
    }

    /// Forwards the paper guard's traversal-side expiration consequence.
    pub proof fn lemma_expired_is_removed(tracked &self)
        requires
            self.wf(),
        ensures
            self.expired().subset_of(self.seen_removed().removed),
    {
        self.paper_guard.lemma_expired_is_removed();
    }

    /// A pointer protected by this guard cannot belong to its entry-time
    /// expired set.
    pub proof fn lemma_protected_not_expired(tracked &self, tracked protected: &RcuProtectedPtr<T>)
        requires
            self.wf(),
            protected.protected_by(self.paper_guard()),
        ensures
            !self.expired().contains(protected.obj()),
    {
        self.paper_guard.lemma_protected_not_expired(protected.ptr().addr(), protected.obj());
    }

    /// Agreement between the abstract guard and its concrete CPU participant.
    pub open spec fn wf(self) -> bool {
        &&& self.paper_guard().wf()
        &&& self.reader_fragment().wf()
        &&& self.binding().locals_key().len() == 1
        &&& self.binding().single_local_id() == self.participant_id()
        &&& self.binding().cpu() == self.cpu()
        &&& self.scheduler() == self.reader_context().scheduler
        &&& self.reader_context().cpu == self.cpu()
        &&& self.reader_context().generation == self.generation()
        &&& self.participant_view().spec_le(self.start_view())
        &&& forall|record: RcuRetiredRecord| #[trigger]
            self.known_retired().contains(record) && record.domain == self.domain()
                && record.retire_observation_registry == self.retire_observation_registry()
                && record.removal.root == self.root() ==> self.expired().contains(record.obj)
    }

    /// Attaches the CPU implementation fragment to a freshly started paper
    /// guard.
    pub proof fn tracked_new(
        tracked paper_guard: RcuReadGuardToken<T>,
        tracked reader: CpuRcuReaderFragment,
        tracked binding: CpuRcuCoreBinding,
    ) -> (tracked res: Self)
        requires
            paper_guard.wf(),
            reader.wf(),
            paper_guard.reader().cpu == reader.cpu(),
            paper_guard.reader().generation == reader.generation(),
            binding.registry() == paper_guard.reader().scheduler,
            binding.cpu() == reader.cpu(),
            binding.locals_key().len() == 1,
            binding.single_local_id() == reader.participant_id(),
            reader.participant_view().spec_le(paper_guard.start_view()),
            forall|record: RcuRetiredRecord| #[trigger]
                reader.known_retired().contains(record) && record.domain == paper_guard.domain()
                    && record.retire_observation_registry
                    == paper_guard.retire_observation_registry() && record.removal.root
                    == paper_guard.root() ==> paper_guard.expired().contains(record.obj),
        ensures
            res.wf(),
            res.paper_guard() == paper_guard,
            res.reader_fragment() == reader,
            res.reader_context() == paper_guard.reader(),
            res.scheduler() == binding.registry(),
            res.binding() == binding,
            res.binding().cpu() == binding.cpu(),
            res.binding().single_local_id() == binding.single_local_id(),
            res.participant_id() == reader.participant_id(),
            res.cpu() == reader.cpu(),
            res.generation() == reader.generation(),
            res.participant_view() == reader.participant_view(),
            res.known_retired() == reader.known_retired(),
            res.domain() == paper_guard.domain(),
            res.root() == paper_guard.root(),
            res.start_view() == paper_guard.start_view(),
            res.reader_registry() == paper_guard.reader_registry(),
            res.retire_observation_registry() == paper_guard.retire_observation_registry(),
            res.expired() == paper_guard.expired(),
            res.seen_removed() == paper_guard.seen_removed(),
            res.protected() == paper_guard.protected(),
    {
        CpuRcuReadGuardToken { paper_guard, reader, binding }
    }

    /// Separates the implementation fragment from the abstract guard.
    ///
    /// This is intentionally consuming. The normal destruction path should use
    /// [`Self::tracked_stop`] so the abstract `Guard -> Inactive` transition
    /// cannot be forgotten.
    pub proof fn tracked_into_parts(tracked self) -> (tracked res: (
        RcuReadGuardToken<T>,
        CpuRcuReaderFragment,
        CpuRcuCoreBinding,
    ))
        requires
            self.wf(),
        ensures
            res.0 == self.paper_guard(),
            res.1 == self.reader_fragment(),
            res.2 == self.binding(),
            res.0.domain() == self.domain(),
            res.0.reader_registry() == self.reader_registry(),
            res.0.reader() == self.reader_context(),
            res.0.root() == self.root(),
            res.0.start_view() == self.start_view(),
            res.0.retire_observation_registry() == self.retire_observation_registry(),
            res.0.expired() == self.expired(),
            res.0.seen_removed() == self.seen_removed(),
            res.0.protected() == self.protected(),
            res.1.participant_id() == self.participant_id(),
            res.1.cpu() == self.cpu(),
            res.1.generation() == self.generation(),
            res.1.participant_view() == self.participant_view(),
            res.1.known_retired() == self.known_retired(),
            res.2.registry() == self.scheduler(),
            res.2.cpu() == self.cpu(),
            res.2.locals_key().len() == 1,
            res.2.single_local_id() == self.participant_id(),
            res.0.wf(),
            res.1.wf(),
            res.0.reader().cpu == res.1.cpu(),
            res.0.reader().generation == res.1.generation(),
            res.1.participant_view().spec_le(res.0.start_view()),
            forall|record: RcuRetiredRecord| #[trigger]
                res.1.known_retired().contains(record) && record.domain == res.0.domain()
                    && record.retire_observation_registry == res.0.retire_observation_registry()
                    && record.removal.root == res.0.root() ==> res.0.expired().contains(record.obj),
    {
        let ghost known_retired = self.known_retired();
        let ghost domain = self.domain();
        let ghost retire_observation_registry = self.retire_observation_registry();
        let ghost root = self.root();
        let ghost expired = self.expired();
        assert forall|record: RcuRetiredRecord| #[trigger]
            known_retired.contains(record) && record.domain == domain
                && record.retire_observation_registry == retire_observation_registry
                && record.removal.root == root implies expired.contains(record.obj) by {};
        let tracked CpuRcuReadGuardToken { paper_guard, reader, binding } = self;
        assert(reader.known_retired() == known_retired);
        assert(paper_guard.domain() == domain);
        assert(paper_guard.retire_observation_registry() == retire_observation_registry);
        assert(paper_guard.root() == root);
        assert(paper_guard.expired() == expired);
        assert forall|record: RcuRetiredRecord| #[trigger]
            reader.known_retired().contains(record) && record.domain == paper_guard.domain()
                && record.retire_observation_registry == paper_guard.retire_observation_registry()
                && record.removal.root == paper_guard.root() implies paper_guard.expired().contains(
            record.obj,
        ) by {
            assert(known_retired.contains(record));
        };
        (paper_guard, reader, binding)
    }

    /// Ends the paper guard locally and returns the CPU fragment that Drop must
    /// join back into the CPU-local participant.
    pub proof fn tracked_stop(tracked self) -> (tracked res: (RcuInactive, CpuRcuReaderFragment))
        requires
            self.wf(),
        ensures
            res.0.wf(),
            res.0.domain() == self.domain(),
            res.0.reader() == self.reader_context(),
            res.1 == self.reader_fragment(),
            res.1.wf(),
            res.1.participant_id() == self.participant_id(),
            res.1.cpu() == self.cpu(),
            res.1.generation() == self.generation(),
    {
        let tracked (paper_guard, reader, _binding) = self.tracked_into_parts();
        let tracked base = paper_guard.tracked_into_base();
        let tracked inactive = base.tracked_stop();
        (inactive, reader)
    }

    /// Splits out the CPU fragment retained with an active physical read
    /// lease, while preserving a valid guard for the executable reader.
    pub proof fn tracked_split_lease_fragment(tracked self) -> (tracked res: (
        Self,
        CpuRcuReaderFragment,
    ))
        requires
            self.wf(),
        ensures
            res.0.wf(),
            res.0.paper_guard() == self.paper_guard(),
            res.0.binding() == self.binding(),
            res.0.participant_id() == self.participant_id(),
            res.0.cpu() == self.cpu(),
            res.0.generation() == self.generation(),
            res.0.participant_view() == self.participant_view(),
            res.0.known_retired() == self.known_retired(),
            res.0.reader_fragment().fraction() == self.reader_fragment().fraction() / 2real,
            res.1.wf(),
            res.1.participant_id() == self.participant_id(),
            res.1.cpu() == self.cpu(),
            res.1.generation() == self.generation(),
            res.1.participant_view() == self.participant_view(),
            res.1.known_retired() == self.known_retired(),
            res.1.fraction() == self.reader_fragment().fraction() / 2real,
    {
        let ghost known_retired = self.known_retired();
        let ghost domain = self.domain();
        let ghost retire_observation_registry = self.retire_observation_registry();
        let ghost root = self.root();
        let ghost expired = self.expired();
        assert forall|record: RcuRetiredRecord| #[trigger]
            known_retired.contains(record) && record.domain == domain
                && record.retire_observation_registry == retire_observation_registry
                && record.removal.root == root implies expired.contains(record.obj) by {};
        let tracked CpuRcuReadGuardToken { paper_guard, reader, binding } = self;
        let tracked (reader, lease_reader) = reader.tracked_split();
        assert forall|record: RcuRetiredRecord| #[trigger]
            reader.known_retired().contains(record) && record.domain == paper_guard.domain()
                && record.retire_observation_registry == paper_guard.retire_observation_registry()
                && record.removal.root == paper_guard.root() implies paper_guard.expired().contains(
            record.obj,
        ) by {
            assert(known_retired.contains(record));
        };
        let tracked guard = CpuRcuReadGuardToken::tracked_new(paper_guard, reader, binding);
        (guard, lease_reader)
    }

    /// Returns an active lease's CPU fragment to its executable guard before
    /// the normal `Guard -> Inactive` transition.
    pub proof fn tracked_join_lease_fragment(
        tracked self,
        tracked lease_reader: CpuRcuReaderFragment,
    ) -> (tracked res: Self)
        requires
            self.wf(),
            lease_reader.wf(),
            self.participant_id() == lease_reader.participant_id(),
        ensures
            res.wf(),
            res.paper_guard() == self.paper_guard(),
            res.binding() == self.binding(),
            res.participant_id() == self.participant_id(),
            res.cpu() == self.cpu(),
            res.generation() == self.generation(),
            res.participant_view() == self.participant_view(),
            res.known_retired() == self.known_retired(),
            res.domain() == self.domain(),
            res.root() == self.root(),
            res.reader_registry() == self.reader_registry(),
            res.retire_observation_registry() == self.retire_observation_registry(),
            res.reader_context() == self.reader_context(),
            res.start_view() == self.start_view(),
            res.expired() == self.expired(),
            res.seen_removed() == self.seen_removed(),
            res.protected() == self.protected(),
            res.reader_fragment().fraction() == self.reader_fragment().fraction()
                + lease_reader.fraction(),
    {
        let ghost known_retired = self.known_retired();
        let ghost domain = self.domain();
        let ghost retire_observation_registry = self.retire_observation_registry();
        let ghost root = self.root();
        let ghost expired = self.expired();
        assert forall|record: RcuRetiredRecord| #[trigger]
            known_retired.contains(record) && record.domain == domain
                && record.retire_observation_registry == retire_observation_registry
                && record.removal.root == root implies expired.contains(record.obj) by {};
        let tracked CpuRcuReadGuardToken { paper_guard, reader, binding } = self;
        let tracked reader = reader.tracked_join(lease_reader);
        assert forall|record: RcuRetiredRecord| #[trigger]
            reader.known_retired().contains(record) && record.domain == paper_guard.domain()
                && record.retire_observation_registry == paper_guard.retire_observation_registry()
                && record.removal.root == paper_guard.root() implies paper_guard.expired().contains(
            record.obj,
        ) by {
            assert(known_retired.contains(record));
        };
        CpuRcuReadGuardToken::tracked_new(paper_guard, reader, binding)
    }

    /// Applies the paper's `Guard-protect` rule without changing CPU
    /// participation or the captured start view.
    pub proof fn tracked_protect(tracked &mut self, tracked info: &RcuBlockInfo<T>)
        requires
            old(self).wf(),
            old(self).paper_guard().can_protect(*info),
        ensures
            final(self).wf(),
            final(self).reader_fragment() == old(self).reader_fragment(),
            final(self).participant_id() == old(self).participant_id(),
            final(self).cpu() == old(self).cpu(),
            final(self).generation() == old(self).generation(),
            final(self).participant_view() == old(self).participant_view(),
            final(self).domain() == old(self).domain(),
            final(self).root() == old(self).root(),
            final(self).start_view() == old(self).start_view(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).expired() == old(self).expired(),
            final(self).protected() == old(self).protected().insert(info.addr(), info.obj()),
            final(self).protects(info.addr(), info.obj()),
    {
        let ghost known_retired = self.known_retired();
        let ghost domain = self.domain();
        let ghost retire_observation_registry = self.retire_observation_registry();
        let ghost root = self.root();
        let ghost expired = self.expired();
        assert forall|record: RcuRetiredRecord| #[trigger]
            known_retired.contains(record) && record.domain == domain
                && record.retire_observation_registry == retire_observation_registry
                && record.removal.root == root implies expired.contains(record.obj) by {};
        self.paper_guard.tracked_protect(info);
        assert(self.known_retired() == known_retired);
        assert(self.domain() == domain);
        assert(self.retire_observation_registry() == retire_observation_registry);
        assert(self.root() == root);
        assert(self.expired() == expired);
        assert forall|record: RcuRetiredRecord| #[trigger]
            self.known_retired().contains(record) && record.domain == self.domain()
                && record.retire_observation_registry == self.retire_observation_registry()
                && record.removal.root == self.root() implies self.expired().contains(
            record.obj,
        ) by {
            assert(known_retired.contains(record));
        };
    }
}

impl<T> CpuRcuReadLeaseWitness<T> {
    pub closed spec fn reader(self) -> CpuRcuReaderFragment {
        self.reader
    }

    pub closed spec fn paper_guard(self) -> RcuReadGuardToken<T> {
        self.paper_guard
    }

    /// Persistent scheduler registration for the CPU participant retained by
    /// this lease. This survives type erasure in the root registry so a grace
    /// period report can recover the canonical participant for the same CPU.
    pub closed spec fn binding(self) -> CpuRcuCoreBinding {
        self.binding
    }

    pub closed spec fn protected(self) -> RcuProtectedPtr<T> {
        self.protected
    }

    pub open spec fn wf(self) -> bool {
        &&& self.reader().wf()
        &&& self.paper_guard().wf()
        &&& online_cpus().contains(self.reader().cpu())
        &&& self.binding().registry() == self.paper_guard().reader().scheduler
        &&& self.binding().cpu() == self.reader().cpu()
        &&& self.binding().locals_key().len() == 1
        &&& self.binding().single_local_id() == self.reader().participant_id()
        &&& self.paper_guard().reader().cpu == self.reader().cpu()
        &&& self.paper_guard().reader().generation == self.reader().generation()
        &&& self.reader().participant_view().spec_le(self.paper_guard().start_view())
        &&& self.paper_guard().expired().subset_of(self.paper_guard().seen_removed().removed)
        &&& forall|record: RcuRetiredRecord| #[trigger]
            self.reader().known_retired().contains(record) && record.domain
                == self.paper_guard().domain() && record.retire_observation_registry
                == self.paper_guard().retire_observation_registry() && record.removal.root
                == self.paper_guard().root() ==> self.paper_guard().expired().contains(record.obj)
        &&& self.protected().protected_by(self.paper_guard())
    }

    /// Relates this lease to the canonical participant closed by a grace-period
    /// report for the same scheduler and CPU.
    pub proof fn lemma_same_participant_as_closed(
        tracked &self,
        tracked closed: &CpuRcuClosedGeneration,
    )
        requires
            self.wf(),
            closed.wf(),
            closed.scheduler() == self.binding().registry(),
            closed.cpu() == self.reader().cpu(),
        ensures
            self.reader().participant_id() == closed.participant_id(),
    {
        closed.lemma_same_participant_as_binding(&self.binding);
    }

    /// Splits the registry fragment from a live executable guard.
    pub proof fn tracked_from_guard(
        tracked guard: CpuRcuReadGuardToken<T>,
        tracked protected: RcuProtectedPtr<T>,
    ) -> (tracked res: (CpuRcuReadGuardToken<T>, Self))
        requires
            guard.wf(),
            protected.protected_by(guard.paper_guard()),
            online_cpus().contains(guard.cpu()),
        ensures
            res.0.wf(),
            res.0.paper_guard() == guard.paper_guard(),
            res.0.binding() == guard.binding(),
            res.0.participant_id() == guard.participant_id(),
            res.0.cpu() == guard.cpu(),
            res.0.generation() == guard.generation(),
            res.0.participant_view() == guard.participant_view(),
            res.0.known_retired() == guard.known_retired(),
            res.0.participant_id() == guard.participant_id(),
            res.0.cpu() == guard.cpu(),
            res.0.generation() == guard.generation(),
            res.0.known_retired() == guard.known_retired(),
            res.0.reader_fragment().fraction() == guard.reader_fragment().fraction() / 2real,
            res.1.wf(),
            res.1.reader().participant_id() == guard.participant_id(),
            res.1.reader().cpu() == guard.cpu(),
            res.1.reader().generation() == guard.generation(),
            res.1.reader().participant_view() == guard.participant_view(),
            res.1.reader().known_retired() == guard.known_retired(),
            res.1.reader().fraction() == guard.reader_fragment().fraction() / 2real,
            res.1.paper_guard() == guard.paper_guard(),
            res.1.binding().registry() == guard.scheduler(),
            res.1.binding().cpu() == guard.cpu(),
            res.1.binding().locals_key() == guard.binding().locals_key(),
            res.1.binding().single_local_id() == guard.participant_id(),
            res.1.protected() == protected,
    {
        guard.lemma_expired_is_removed();
        let ghost paper_guard = guard.paper_guard();
        let tracked binding = guard.binding.tracked_duplicate();
        let tracked (guard, reader) = guard.tracked_split_lease_fragment();
        let tracked witness = CpuRcuReadLeaseWitness { reader, paper_guard, binding, protected };
        (guard, witness)
    }

    /// Builds the direct-root protection witness returned by a guarded atomic
    /// load and splits off the registry's CPU-reader fragment in one step.
    pub proof fn tracked_from_loaded_guard(
        tracked guard: CpuRcuReadGuardToken<T>,
        tracked info: &RcuBlockInfo<T>,
    ) -> (tracked res: (CpuRcuReadGuardToken<T>, Self))
        requires
            guard.wf(),
            info.wf(),
            info.domain() == guard.domain(),
            guard.protects(info.addr(), info.obj()),
            !guard.seen_removed().removed.contains(info.obj()),
            online_cpus().contains(guard.cpu()),
        ensures
            res.0.wf(),
            res.0.paper_guard() == guard.paper_guard(),
            res.0.binding() == guard.binding(),
            res.0.participant_id() == guard.participant_id(),
            res.0.cpu() == guard.cpu(),
            res.0.generation() == guard.generation(),
            res.0.participant_view() == guard.participant_view(),
            res.0.known_retired() == guard.known_retired(),
            res.0.reader_fragment().fraction() == guard.reader_fragment().fraction() / 2real,
            res.1.wf(),
            res.1.reader().participant_id() == guard.participant_id(),
            res.1.reader().cpu() == guard.cpu(),
            res.1.reader().generation() == guard.generation(),
            res.1.reader().participant_view() == guard.participant_view(),
            res.1.reader().known_retired() == guard.known_retired(),
            res.1.reader().fraction() == guard.reader_fragment().fraction() / 2real,
            res.1.paper_guard() == guard.paper_guard(),
            res.1.binding().registry() == guard.scheduler(),
            res.1.binding().cpu() == guard.cpu(),
            res.1.binding().locals_key() == guard.binding().locals_key(),
            res.1.binding().single_local_id() == guard.participant_id(),
            res.1.protected().domain() == info.domain(),
            res.1.protected().obj() == info.obj(),
            res.1.protected().ptr() == info.ptr(),
    {
        let tracked protected = RcuProtectedPtr::tracked_from_guard(&guard.paper_guard, info);
        Self::tracked_from_guard(guard, protected)
    }

    /// Returns the registry fragment to the corresponding executable guard.
    pub proof fn tracked_return_to_guard(
        tracked self,
        tracked guard: CpuRcuReadGuardToken<T>,
    ) -> (tracked res: CpuRcuReadGuardToken<T>)
        requires
            self.wf(),
            guard.wf(),
            self.reader().participant_id() == guard.participant_id(),
        ensures
            res.wf(),
            res.paper_guard() == guard.paper_guard(),
            res.binding() == guard.binding(),
            res.participant_id() == guard.participant_id(),
            res.cpu() == guard.cpu(),
            res.generation() == guard.generation(),
            res.participant_view() == guard.participant_view(),
            res.known_retired() == guard.known_retired(),
            res.reader_fragment().fraction() == guard.reader_fragment().fraction()
                + self.reader().fraction(),
    {
        guard.tracked_join_lease_fragment(self.reader)
    }
}

impl<T> RcuReclaimClaim<T> {
    pub closed spec fn registry(self) -> Loc {
        self.points_to.id()
    }

    pub closed spec fn obj(self) -> nat {
        self.points_to.key()
    }

    pub closed spec fn is_pending(self) -> bool {
        self.points_to.value() is Some
    }

    pub closed spec fn ptr(self) -> *mut T
        recommends
            self.is_pending(),
    {
        self.points_to.value()->Some_0
    }
}

impl RcuReclaimedWitness {
    pub closed spec fn record(self) -> RcuRetiredRecord {
        self.record
    }

    pub closed spec fn closed_generations(self) -> Map<CpuId, CpuRcuClosedGeneration> {
        self.closed_generations
    }

    pub closed spec fn scheduler(self) -> Loc {
        self.scheduler
    }

    /// Persistent base-retirement fact retained after physical reclamation.
    pub closed spec fn retired_fact(self) -> RcuRetiredFact {
        self.retired
    }

    /// Persistent retirement fact used to agree the callback summary with the
    /// root domain's authoritative removal observation.
    pub proof fn tracked_retired_fact(tracked &self) -> (tracked res: &RcuRetiredFact)
        requires
            self.wf(),
        ensures
            res.wf(),
            res.record() == self.record(),
    {
        &self.retired
    }

    pub proof fn tracked_closed_generation(tracked &self, cpu: CpuId) -> (tracked res:
        &CpuRcuClosedGeneration)
        requires
            self.wf(),
            online_cpus().contains(cpu),
        ensures
            *res == self.closed_generations()[cpu],
            res.wf(),
            res.cpu() == cpu,
            res.scheduler() == self.scheduler(),
    {
        self.closed_generations.tracked_borrow(cpu)
    }

    pub open spec fn wf(self) -> bool {
        &&& self.retired_fact().wf()
        &&& self.retired_fact().record() == self.record()
        &&& self.closed_generations().dom() == online_cpus()
        &&& forall|cpu: CpuId| #[trigger]
            self.closed_generations().contains_key(cpu) ==> {
                let closed = self.closed_generations()[cpu];
                &&& closed.wf()
                &&& closed.cpu() == cpu
                &&& closed.scheduler() == self.scheduler()
                &&& closed.known_retired().contains(self.record())
            }
    }

    pub proof fn tracked_new(
        scheduler: Loc,
        tracked retired: RcuRetiredFact,
        tracked closed_generations: Map<CpuId, CpuRcuClosedGeneration>,
    ) -> (tracked res: Self)
        requires
            retired.wf(),
            closed_generations.dom() == online_cpus(),
            forall|cpu: CpuId| #[trigger]
                closed_generations.contains_key(cpu) ==> {
                    let closed = closed_generations[cpu];
                    &&& closed.wf()
                    &&& closed.cpu() == cpu
                    &&& closed.scheduler() == scheduler
                    &&& closed.known_retired().contains(retired.record())
                },
        ensures
            res.wf(),
            res.record() == retired.record(),
            res.scheduler() == scheduler,
    {
        let ghost record = retired.record();
        Self { record, scheduler, retired, closed_generations }
    }

    /// Classifies a coexisting reader as later than the completed grace period.
    pub proof fn tracked_later_reader(
        tracked &self,
        tracked reader: CpuRcuReaderFragment,
    ) -> (tracked res: CpuRcuReaderFragment)
        requires
            self.wf(),
            reader.wf(),
            online_cpus().contains(reader.cpu()),
            self.closed_generations()[reader.cpu()].participant_id() == reader.participant_id(),
        ensures
            res == reader,
            res.wf(),
            res.known_retired().contains(self.record()),
    {
        let tracked closed = self.closed_generations.tracked_borrow(reader.cpu());
        let tracked reader = closed.lemma_later_reader(reader);
        assert(closed.known_retired().contains(self.record()));
        reader
    }
}

impl RcuActiveLeaseBinding {
    pub closed spec fn from_record<T>(
        record: vstd_extra::rcu_read_pool::RcuReadLeaseRecord<nat, CpuRcuReadLeaseWitness<T>>,
    ) -> Self {
        Self {
            key: record.key(),
            pool_id: record.pool_id(),
            fraction: record.fraction(),
            participant_id: record.witness().reader().participant_id(),
            reader_fraction: record.witness().reader().fraction(),
            domain: record.witness().paper_guard().domain(),
            root: record.witness().paper_guard().root(),
            reader: record.witness().paper_guard().reader(),
            start_view: record.witness().paper_guard().start_view(),
            protected_addr: record.witness().protected().ptr().addr(),
        }
    }
}

impl<O> RcuRootReadLease<O> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.active.key() == self.lease.lease_id()
        &&& self.active.value().key == self.lease.key()
        &&& self.active.value().pool_id == self.lease.pool_id()
        &&& self.active.value().fraction == self.lease.fraction()
    }

    pub closed spec fn lease_id(self) -> nat {
        self.lease.lease_id()
    }

    pub closed spec fn key(self) -> nat {
        self.lease.key()
    }

    pub closed spec fn pool_id(self) -> Loc {
        self.lease.pool_id()
    }

    pub closed spec fn fraction(self) -> real {
        self.lease.fraction()
    }

    pub closed spec fn resource(self) -> O {
        self.lease.resource()
    }

    pub closed spec fn active_registry(self) -> Loc {
        self.active.id()
    }

    pub closed spec fn participant_id(self) -> Loc {
        self.active.value().participant_id
    }

    pub closed spec fn reader_fraction(self) -> real {
        self.active.value().reader_fraction
    }

    pub closed spec fn domain(self) -> Loc {
        self.active.value().domain
    }

    pub closed spec fn root(self) -> Loc {
        self.active.value().root
    }

    pub closed spec fn reader_context(self) -> RcuReaderContext {
        self.active.value().reader
    }

    pub closed spec fn start_view(self) -> Irc11ThreadView {
        self.active.value().start_view
    }

    pub closed spec fn protected_addr(self) -> usize {
        self.active.value().protected_addr
    }

    pub proof fn borrow(tracked &self) -> (tracked resource: &O)
        ensures
            *resource == self.resource(),
    {
        self.lease.borrow()
    }
}

impl<T, O> RcuRootPermissionState<T, O> {
    /// Creates an empty permission registry for one RCU root.
    pub proof fn empty(
        scheduler: Loc,
        domain: Loc,
        root: Loc,
        retire_observation_registry: Loc,
    ) -> (tracked res: Self)
        ensures
            res.wf(),
            res.scheduler() == scheduler,
            res.domain() == domain,
            res.root() == root,
            res.retire_observation_registry() == retire_observation_registry,
            res.keys() == Set::<nat>::empty(),
            res.allocations() == Set::<nat>::empty(),
            res.reclaimed() == Map::<nat, RcuReclaimedWitness>::empty(),
            res.active_ids() == Set::<nat>::empty(),
    {
        let tracked registry = RcuTrackedReadPoolRegistry::empty();
        let tracked (active_leases, _active) = GhostMapAuth::new(Map::empty());
        let tracked (reclaim_state, _claims) = GhostMapAuth::new(Map::empty());
        let tracked res = RcuRootPermissionState {
            registry,
            active_leases,
            reclaim_state,
            unretired_claims: Map::tracked_empty(),
            reclaimed: Map::tracked_empty(),
            scheduler,
            domain,
            root,
            retire_observation_registry,
        };
        assert(res.allocations() == Set::<nat>::empty());
        assert(res.unretired_claims().dom() == Set::<nat>::empty());
        assert(res.reclaimed().dom() == Set::<nat>::empty());
        assert(res.active_lease_bindings().dom() == Set::<nat>::empty());
        assert(res.reclaimed().dom() == res.allocations().difference(res.keys()));
        assert forall|obj: nat| #[trigger] res.reclaimed().contains_key(obj) implies {
            let completed = res.reclaimed()[obj];
            &&& completed.wf()
            &&& completed.record().domain == res.domain()
            &&& completed.record().obj == obj
            &&& completed.record().retire_observation_registry == res.retire_observation_registry()
            &&& completed.record().removal.root == res.root()
        } by {};
        assert forall|obj: nat| #[trigger] res.allocations().contains(obj) implies {
            res.keys().contains(obj) <==> res.reclaim_states()[obj] is Some
        } by {};
        res
    }

    pub closed spec fn registry(self) -> RcuTrackedReadPoolRegistry<
        nat,
        O,
        CpuRcuReadLeaseWitness<T>,
    > {
        self.registry
    }

    pub proof fn tracked_registry_mut(tracked &mut self) -> (tracked res:
        &mut RcuTrackedReadPoolRegistry<nat, O, CpuRcuReadLeaseWitness<T>>)
        ensures
            *res == old(self).registry(),
            final(self).registry() == *final(res),
            *final(res) == old(self).registry() ==> *final(self) == *old(self),
    {
        &mut self.registry
    }

    pub closed spec fn domain(self) -> Loc {
        self.domain
    }

    pub closed spec fn scheduler(self) -> Loc {
        self.scheduler
    }

    pub closed spec fn root(self) -> Loc {
        self.root
    }

    pub closed spec fn retire_observation_registry(self) -> Loc {
        self.retire_observation_registry
    }

    pub closed spec fn keys(self) -> Set<nat> {
        self.registry().keys()
    }

    pub closed spec fn contains(self, obj: nat) -> bool {
        self.registry().contains(obj)
    }

    pub proof fn lemma_contains_iff_key(tracked &self, obj: nat)
        ensures
            self.contains(obj) <==> self.keys().contains(obj),
    {
        self.registry.lemma_contains_iff_key(obj);
    }

    /// Opens pool membership for every allocation identity at once.
    pub proof fn lemma_all_contains_iff_keys(tracked &self)
        ensures
            forall|obj: nat| #[trigger] self.contains(obj) <==> self.keys().contains(obj),
    {
        reveal(RcuRootPermissionState::contains);
        reveal(RcuRootPermissionState::keys);
        self.registry.lemma_all_contains_iff_keys();
    }

    /// Opens the allocation-state facts associated with a live permission pool.
    pub proof fn lemma_live_reclaim_state(tracked &self, obj: nat)
        requires
            self.wf(),
            self.contains(obj),
        ensures
            self.keys().contains(obj),
            self.allocations().contains(obj),
            self.reclaim_states().dom().contains(obj),
            self.reclaim_states()[obj] is Some,
    {
        self.registry.lemma_contains_iff_key(obj);
        assert(self.keys().contains(obj));
        assert(self.keys().subset_of(self.allocations()));
        assert(self.allocations().contains(obj));
    }

    /// An unretired root claim always names a live permission pool.
    pub proof fn lemma_unretired_is_live(tracked &self, obj: nat)
        requires
            self.wf(),
            self.has_unretired_claim(obj),
        ensures
            self.contains(obj),
            self.keys().contains(obj),
            self.allocations().contains(obj),
            self.reclaim_states().dom().contains(obj),
            self.reclaim_states()[obj] is Some,
    {
        assert(self.unretired_claims().dom().contains(obj));
        assert(self.keys().contains(obj));
        self.registry.lemma_contains_iff_key(obj);
        self.lemma_live_reclaim_state(obj);
    }

    /// Opens the live allocation facts for every key in one quantifier.
    pub proof fn lemma_all_live_reclaim_states(tracked &self)
        requires
            self.wf(),
        ensures
            forall|obj: nat| #[trigger]
                self.keys().contains(obj) ==> {
                    &&& self.contains(obj)
                    &&& self.allocations().contains(obj)
                    &&& self.reclaim_states().dom().contains(obj)
                    &&& self.reclaim_states()[obj] is Some
                },
    {
        reveal(RcuRootPermissionState::contains);
        reveal(RcuRootPermissionState::keys);
        self.registry.lemma_all_contains_iff_keys();
        assert forall|obj: nat| #[trigger] self.keys().contains(obj) implies {
            &&& self.contains(obj)
            &&& self.allocations().contains(obj)
            &&& self.reclaim_states().dom().contains(obj)
            &&& self.reclaim_states()[obj] is Some
        } by {
            assert(self.contains(obj));
            assert(self.allocations().contains(obj));
        };
    }

    /// Every allocation identity ever registered by this root.
    pub closed spec fn allocations(self) -> Set<nat> {
        self.reclaim_state.dom()
    }

    pub closed spec fn reclaim_states(self) -> Map<nat, Option<*mut T>> {
        self.reclaim_state@
    }

    /// Every allocation retained by the append-only identity registry has a
    /// corresponding reclaim-state cell, including after that cell changes
    /// from `Some(ptr)` to `None` at reclamation.
    pub proof fn lemma_allocation_has_reclaim_state(tracked &self, obj: nat)
        requires
            self.wf(),
            self.allocations().contains(obj),
        ensures
            self.reclaim_states().dom().contains(obj),
    {
    }

    /// Opens every append-only allocation cell in one quantified fact.
    pub proof fn lemma_all_allocations_have_reclaim_states(tracked &self)
        requires
            self.wf(),
        ensures
            forall|obj: nat| #[trigger]
                self.allocations().contains(obj) ==> self.reclaim_states().dom().contains(obj),
    {
    }

    pub closed spec fn unretired_claims(self) -> Map<nat, GhostPointsTo<nat, Option<*mut T>>> {
        self.unretired_claims
    }

    pub closed spec fn reclaimed(self) -> Map<nat, RcuReclaimedWitness> {
        self.reclaimed
    }

    pub closed spec fn reclaim_registry(self) -> Loc {
        self.reclaim_state.id()
    }

    pub closed spec fn ownership(self, obj: nat) -> O
        recommends
            self.contains(obj),
    {
        self.registry().pool(obj).resource()
    }

    pub closed spec fn has_unretired_claim(self, obj: nat) -> bool {
        self.unretired_claims().contains_key(obj)
    }

    /// Relates the claim predicate to membership in the claim map domain.
    pub proof fn lemma_has_unretired_iff_domain(tracked &self, obj: nat)
        ensures
            self.has_unretired_claim(obj) <==> self.unretired_claims().dom().contains(obj),
    {
    }

    /// Opens claim-map membership for all allocation identities.
    pub proof fn lemma_all_unretired_domains(tracked &self)
        ensures
            forall|obj: nat| #[trigger]
                self.has_unretired_claim(obj) <==> self.unretired_claims().dom().contains(obj),
    {
    }

    pub closed spec fn active_ids(self) -> Set<nat> {
        self.registry().active_ids()
    }

    pub closed spec fn active_lease_bindings(self) -> Map<nat, RcuActiveLeaseBinding> {
        self.active_leases@
    }

    pub closed spec fn active_lease_registry(self) -> Loc {
        self.active_leases.id()
    }

    pub open spec fn has_active(self, obj: nat) -> bool {
        self.registry().has_active(obj)
    }

    pub closed spec fn active_record(
        self,
        lease_id: nat,
    ) -> vstd_extra::rcu_read_pool::RcuReadLeaseRecord<nat, CpuRcuReadLeaseWitness<T>>
        recommends
            self.active_ids().contains(lease_id),
    {
        self.registry().active_record(lease_id)
    }

    /// Exposes the active-lease registry projections without revealing the
    /// rest of the root permission state's representation.
    pub proof fn lemma_active_registry_projection(tracked &self)
        ensures
            self.active_ids() == self.registry().active_ids(),
            forall|lease_id: nat| #[trigger]
                self.active_ids().contains(lease_id) ==> self.active_record(lease_id)
                    == self.registry().active_record(lease_id),
    {
    }

    /// The registry accounting is valid and every active witness belongs to
    /// this exact RCU root.
    pub open spec fn wf(self) -> bool {
        &&& self.registry().wf()
        &&& self.active_lease_bindings().dom() == self.active_ids()
        &&& forall|lease_id: nat| #[trigger]
            self.active_ids().contains(lease_id) ==> self.active_lease_bindings()[lease_id]
                == RcuActiveLeaseBinding::from_record(self.active_record(lease_id))
        &&& self.registry().keys().subset_of(self.allocations())
        &&& forall|obj: nat| #[trigger]
            self.allocations().contains(obj) ==> {
                self.keys().contains(obj) <==> self.reclaim_states()[obj] is Some
            }
        &&& self.unretired_claims().dom().subset_of(self.registry().keys())
        &&& self.reclaimed().dom() == self.allocations().difference(self.keys())
        &&& forall|obj: nat| #[trigger]
            self.reclaimed().contains_key(obj) ==> {
                let completed = self.reclaimed()[obj];
                &&& completed.wf()
                &&& completed.scheduler() == self.scheduler()
                &&& completed.record().domain == self.domain()
                &&& completed.record().obj == obj
                &&& completed.record().retire_observation_registry
                    == self.retire_observation_registry()
                &&& completed.record().removal.root == self.root()
            }
        &&& forall|obj: nat| #[trigger]
            self.unretired_claims().contains_key(obj) ==> {
                let claim = self.unretired_claims()[obj];
                &&& claim.id() == self.reclaim_registry()
                &&& claim.key() == obj
                &&& claim.value() == Some(self.reclaim_states()[obj]->Some_0)
            }
        &&& forall|lease_id: nat| #[trigger]
            self.active_ids().contains(lease_id) ==> {
                let record = self.active_record(lease_id);
                let witness = record.witness();
                &&& witness.wf()
                &&& witness.binding().registry() == self.scheduler()
                &&& record.key() == witness.protected().obj()
                &&& witness.protected().domain() == self.domain()
                &&& witness.paper_guard().domain() == self.domain()
                &&& witness.paper_guard().root() == self.root()
                &&& witness.paper_guard().retire_observation_registry()
                    == self.retire_observation_registry()
            }
    }

    pub proof fn tracked_reclaimed(tracked &self, obj: nat) -> (tracked res: &RcuReclaimedWitness)
        requires
            self.wf(),
            self.allocations().contains(obj),
            !self.contains(obj),
        ensures
            self.reclaimed().contains_key(obj),
            *res == self.reclaimed()[obj],
            res.wf(),
            res.record().domain == self.domain(),
            res.record().obj == obj,
            res.record().retire_observation_registry == self.retire_observation_registry(),
            res.record().removal.root == self.root(),
    {
        self.registry.lemma_contains_iff_key(obj);
        assert(self.reclaimed().contains_key(obj));
        self.reclaimed.tracked_borrow(obj)
    }

    /// Registers the complete physical ownership of one published allocation.
    pub proof fn tracked_insert(
        tracked &mut self,
        tracked info: &RcuBlockInfo<T>,
        tracked ownership: O,
    )
        requires
            old(self).wf(),
            info.wf(),
            info.domain() == old(self).domain(),
            !old(self).allocations().contains(info.obj()),
        ensures
            final(self).wf(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).domain() == old(self).domain(),
            final(self).root() == old(self).root(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).reclaim_registry() == old(self).reclaim_registry(),
            final(self).active_lease_registry() == old(self).active_lease_registry(),
            final(self).keys() == old(self).keys().insert(info.obj()),
            final(self).allocations() == old(self).allocations().insert(info.obj()),
            final(self).reclaim_states() == old(self).reclaim_states().insert(
                info.obj(),
                Some(info.ptr()),
            ),
            final(self).reclaimed() == old(self).reclaimed(),
            final(self).has_unretired_claim(info.obj()),
            final(self).unretired_claims().dom() == old(self).unretired_claims().dom().insert(
                info.obj(),
            ),
            final(self).contains(info.obj()),
            final(self).active_ids() == old(self).active_ids(),
            final(self).registry().pool(info.obj()).resource() == ownership,
            final(self).ownership(info.obj()) == ownership,
            forall|obj: nat| #[trigger]
                old(self).contains(obj) ==> final(self).ownership(obj) == old(self).ownership(obj),
    {
        let ghost old_active = self.active_ids();
        let ghost new_obj = info.obj();
        self.registry.lemma_contains_iff_key(new_obj);
        assert(!self.contains(new_obj)) by {
            if self.contains(new_obj) {
                reveal(RcuRootPermissionState::contains);
                reveal(RcuRootPermissionState::keys);
            }
        };
        self.registry.insert(info.obj(), ownership);
        let tracked claim = self.reclaim_state.insert(info.obj(), Some(info.ptr()));
        self.unretired_claims.tracked_insert(info.obj(), claim);
        assert(self.registry().keys().subset_of(self.allocations())) by {
            assert forall|obj: nat| #[trigger]
                self.registry().keys().contains(obj) implies self.allocations().contains(obj) by {
                if obj != new_obj {
                    assert(old(self).keys().contains(obj));
                    assert(old(self).allocations().contains(obj));
                }
            };
        };
        assert forall|obj: nat| #[trigger] self.allocations().contains(obj) implies {
            self.keys().contains(obj) <==> self.reclaim_states()[obj] is Some
        } by {
            if obj == new_obj {
                assert(self.keys().contains(obj));
                assert(self.reclaim_states()[obj] == Some(info.ptr()));
            } else {
                assert(old(self).allocations().contains(obj));
                assert(self.reclaim_states()[obj] == old(self).reclaim_states()[obj]);
                assert(self.keys().contains(obj) == old(self).keys().contains(obj));
            }
        };
        assert(self.unretired_claims().dom().subset_of(self.registry().keys()));
        assert(self.reclaimed().dom() == self.allocations().difference(self.keys())) by {
            assert(self.reclaimed() == old(self).reclaimed());
            assert(old(self).reclaimed().dom() == old(self).allocations().difference(
                old(self).keys(),
            ));
        };
        assert forall|obj: nat| #[trigger] self.reclaimed().contains_key(obj) implies {
            let completed = self.reclaimed()[obj];
            &&& completed.wf()
            &&& completed.record().domain == self.domain()
            &&& completed.record().obj == obj
            &&& completed.record().retire_observation_registry == self.retire_observation_registry()
            &&& completed.record().removal.root == self.root()
        } by {
            assert(old(self).reclaimed().contains_key(obj));
            assert(self.reclaimed()[obj] == old(self).reclaimed()[obj]);
        };
        assert forall|obj: nat| #[trigger] self.unretired_claims().contains_key(obj) implies {
            let saved = self.unretired_claims()[obj];
            &&& saved.id() == self.reclaim_registry()
            &&& saved.key() == obj
            &&& saved.value() == Some(self.reclaim_states()[obj]->Some_0)
        } by {
            if obj == new_obj {
                assert(self.unretired_claims()[obj] == claim);
            } else {
                assert(old(self).unretired_claims().contains_key(obj));
                assert(self.unretired_claims()[obj] == old(self).unretired_claims()[obj]);
            }
        };
        assert forall|lease_id: nat| #[trigger] self.active_ids().contains(lease_id) implies {
            let record = self.active_record(lease_id);
            let witness = record.witness();
            &&& witness.wf()
            &&& record.key() == witness.protected().obj()
            &&& witness.protected().domain() == self.domain()
            &&& witness.paper_guard().domain() == self.domain()
            &&& witness.paper_guard().root() == self.root()
            &&& witness.paper_guard().retire_observation_registry()
                == self.retire_observation_registry()
        } by {
            assert(old_active.contains(lease_id));
            assert(old(self).active_ids().contains(lease_id));
            assert(self.registry().active_record(lease_id) == old(self).registry().active_record(
                lease_id,
            ));
            assert(self.active_record(lease_id) == old(self).active_record(lease_id));
        };
    }

    /// Moves the unique reclaim claim out when the root publication is retired.
    pub proof fn tracked_retire(tracked &mut self, obj: nat) -> (tracked claim: RcuReclaimClaim<T>)
        requires
            old(self).wf(),
            old(self).has_unretired_claim(obj),
        ensures
            final(self).wf(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).domain() == old(self).domain(),
            final(self).root() == old(self).root(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).reclaim_registry() == old(self).reclaim_registry(),
            final(self).active_lease_registry() == old(self).active_lease_registry(),
            final(self).keys() == old(self).keys(),
            final(self).allocations() == old(self).allocations(),
            final(self).reclaim_states() == old(self).reclaim_states(),
            final(self).reclaimed() == old(self).reclaimed(),
            final(self).registry() == old(self).registry(),
            forall|candidate: nat| #[trigger]
                old(self).contains(candidate) ==> final(self).ownership(candidate) == old(
                    self,
                ).ownership(candidate),
            final(self).active_ids() == old(self).active_ids(),
            !final(self).has_unretired_claim(obj),
            final(self).unretired_claims().dom() == old(self).unretired_claims().dom().remove(obj),
            claim.registry() == old(self).reclaim_registry(),
            claim.obj() == obj,
            claim.is_pending(),
            claim.ptr() == old(self).reclaim_states()[obj]->Some_0,
    {
        let tracked points_to = self.unretired_claims.tracked_remove(obj);
        assert(self.registry() == old(self).registry());
        assert(self.reclaim_states() == old(self).reclaim_states());
        assert(self.reclaim_registry() == old(self).reclaim_registry());
        assert(self.unretired_claims().dom().subset_of(self.registry().keys()));
        assert forall|other: nat| #[trigger] self.unretired_claims.contains_key(other) implies {
            let claim = self.unretired_claims[other];
            &&& claim.id() == self.reclaim_state.id()
            &&& claim.key() == other
            &&& claim.value() == Some(self.reclaim_states()[other]->Some_0)
        } by {
            assert(old(self).unretired_claims.contains_key(other));
            assert(self.unretired_claims[other] == old(self).unretired_claims[other]);
        };
        assert forall|lease_id: nat| #[trigger] self.active_ids().contains(lease_id) implies {
            let record = self.active_record(lease_id);
            let witness = record.witness();
            &&& witness.wf()
            &&& record.key() == witness.protected().obj()
            &&& witness.protected().domain() == self.domain()
            &&& witness.paper_guard().domain() == self.domain()
            &&& witness.paper_guard().root() == self.root()
            &&& witness.paper_guard().retire_observation_registry()
                == self.retire_observation_registry()
        } by {
            assert(old(self).active_ids().contains(lease_id));
            assert(self.active_record(lease_id) == old(self).active_record(lease_id));
            assert(self.domain() == old(self).domain());
            assert(self.root() == old(self).root());
            assert(self.retire_observation_registry() == old(self).retire_observation_registry());
        };
        RcuReclaimClaim { points_to }
    }

    /// Splits a physical read lease for an allocation already protected by a
    /// traversal-level guard.
    ///
    /// Unlike [`Self::tracked_split_loaded`], this transition borrows the
    /// explicit [`RcuProtectedPtr`] minted by a traversal step.  This lets an
    /// internal-link load use the same AId-indexed physical pool as a direct
    /// root load without reconstructing protection from the guard map.  A
    /// persistent copy is retained in the active registry record while the
    /// caller keeps the original for further traversal.  The CPU reader
    /// fragment is split at the same time.
    pub proof fn tracked_split_protected(
        tracked &mut self,
        tracked guard: CpuRcuReadGuardToken<T>,
        tracked protected: &RcuProtectedPtr<T>,
    ) -> (tracked res: (CpuRcuReadGuardToken<T>, RcuRootReadLease<O>))
        requires
            old(self).wf(),
            old(self).contains(protected.obj()),
            guard.wf(),
            guard.scheduler() == old(self).scheduler(),
            protected.domain() == old(self).domain(),
            protected.protected_by(guard.paper_guard()),
            guard.domain() == old(self).domain(),
            guard.root() == old(self).root(),
            guard.retire_observation_registry() == old(self).retire_observation_registry(),
            online_cpus().contains(guard.cpu()),
        ensures
            final(self).wf(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).domain() == old(self).domain(),
            final(self).root() == old(self).root(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).reclaim_registry() == old(self).reclaim_registry(),
            final(self).active_lease_registry() == old(self).active_lease_registry(),
            final(self).keys() == old(self).keys(),
            final(self).allocations() == old(self).allocations(),
            final(self).reclaim_states() == old(self).reclaim_states(),
            final(self).reclaimed() == old(self).reclaimed(),
            final(self).unretired_claims() == old(self).unretired_claims(),
            forall|candidate: nat| #[trigger]
                final(self).has_unretired_claim(candidate) == old(self).has_unretired_claim(
                    candidate,
                ),
            forall|obj: nat| #[trigger]
                old(self).contains(obj) ==> final(self).ownership(obj) == old(self).ownership(obj),
            res.0.wf(),
            res.0.paper_guard() == guard.paper_guard(),
            res.0.binding() == guard.binding(),
            res.0.participant_id() == guard.participant_id(),
            res.0.scheduler() == guard.scheduler(),
            res.0.cpu() == guard.cpu(),
            res.0.generation() == guard.generation(),
            res.0.participant_view() == guard.participant_view(),
            res.0.known_retired() == guard.known_retired(),
            res.0.domain() == guard.domain(),
            res.0.root() == guard.root(),
            res.0.reader_registry() == guard.reader_registry(),
            res.0.retire_observation_registry() == guard.retire_observation_registry(),
            res.0.reader_context() == guard.reader_context(),
            res.0.start_view() == guard.start_view(),
            res.0.expired() == guard.expired(),
            res.0.seen_removed() == guard.seen_removed(),
            res.0.protected() == guard.protected(),
            res.0.reader_fragment().fraction() == guard.reader_fragment().fraction() / 2real,
            res.1.key() == protected.obj(),
            res.1.resource() == old(self).ownership(protected.obj()),
            res.1.active_registry() == old(self).active_lease_registry(),
            res.1.participant_id() == guard.participant_id(),
            res.1.reader_fraction() == res.0.reader_fragment().fraction(),
            res.1.domain() == guard.domain(),
            res.1.root() == guard.root(),
            res.1.reader_context() == guard.reader_context(),
            res.1.start_view() == guard.start_view(),
            res.1.protected_addr() == protected.ptr().addr(),
            final(self).active_ids() == old(self).active_ids().insert(res.1.lease_id()),
            final(self).active_record(res.1.lease_id()).witness().paper_guard()
                == guard.paper_guard(),
            final(self).active_record(res.1.lease_id()).witness().protected() == *protected,
    {
        let tracked saved_protected = protected.tracked_duplicate();
        let tracked (guard, witness) = CpuRcuReadLeaseWitness::tracked_from_guard(
            guard,
            saved_protected,
        );
        let tracked lease = self.registry.split_lease(protected.obj(), witness);
        let ghost binding = RcuActiveLeaseBinding::from_record(
            self.active_record(lease.lease_id()),
        );
        reveal(RcuActiveLeaseBinding::from_record);
        assert(self.active_record(lease.lease_id()).witness() == witness);
        assert(self.active_record(lease.lease_id()).witness().protected() == *protected);
        assert(binding.protected_addr == protected.ptr().addr());
        let tracked active = self.active_leases.insert(lease.lease_id(), binding);
        assert forall|lease_id: nat| #[trigger] self.active_ids().contains(lease_id) implies {
            let record = self.active_record(lease_id);
            let witness = record.witness();
            &&& witness.wf()
            &&& record.key() == witness.protected().obj()
            &&& witness.protected().domain() == self.domain()
            &&& witness.paper_guard().domain() == self.domain()
            &&& witness.paper_guard().root() == self.root()
            &&& witness.paper_guard().retire_observation_registry()
                == self.retire_observation_registry()
        } by {
            if lease_id == lease.lease_id() {
                assert(self.active_record(lease_id).witness() == witness);
                assert(self.active_record(lease_id).key() == protected.obj());
            } else {
                assert(old(self).active_ids().contains(lease_id));
                assert(self.active_record(lease_id) == old(self).active_record(lease_id));
            }
        };
        let tracked lease = RcuRootReadLease { lease, active };
        (guard, lease)
    }

    /// Splits a physical read lease for the object selected by a direct-root
    /// guarded load.
    ///
    /// The direct-root adapter materializes the same traversal protection
    /// witness and delegates to [`Self::tracked_split_protected`].
    pub proof fn tracked_split_loaded(
        tracked &mut self,
        tracked guard: CpuRcuReadGuardToken<T>,
        tracked info: &RcuBlockInfo<T>,
    ) -> (tracked res: (CpuRcuReadGuardToken<T>, RcuRootReadLease<O>))
        requires
            old(self).wf(),
            old(self).contains(info.obj()),
            guard.wf(),
            guard.scheduler() == old(self).scheduler(),
            info.wf(),
            info.domain() == old(self).domain(),
            guard.domain() == old(self).domain(),
            guard.root() == old(self).root(),
            guard.retire_observation_registry() == old(self).retire_observation_registry(),
            guard.protects(info.addr(), info.obj()),
            !guard.seen_removed().removed.contains(info.obj()),
            online_cpus().contains(guard.cpu()),
        ensures
            final(self).wf(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).domain() == old(self).domain(),
            final(self).root() == old(self).root(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).reclaim_registry() == old(self).reclaim_registry(),
            final(self).active_lease_registry() == old(self).active_lease_registry(),
            final(self).keys() == old(self).keys(),
            final(self).allocations() == old(self).allocations(),
            final(self).reclaim_states() == old(self).reclaim_states(),
            final(self).reclaimed() == old(self).reclaimed(),
            final(self).unretired_claims() == old(self).unretired_claims(),
            forall|candidate: nat| #[trigger]
                final(self).has_unretired_claim(candidate) == old(self).has_unretired_claim(
                    candidate,
                ),
            forall|obj: nat| #[trigger]
                old(self).contains(obj) ==> final(self).ownership(obj) == old(self).ownership(obj),
            res.0.wf(),
            res.0.paper_guard() == guard.paper_guard(),
            res.0.binding() == guard.binding(),
            res.0.participant_id() == guard.participant_id(),
            res.0.scheduler() == guard.scheduler(),
            res.0.cpu() == guard.cpu(),
            res.0.generation() == guard.generation(),
            res.0.participant_view() == guard.participant_view(),
            res.0.known_retired() == guard.known_retired(),
            res.0.domain() == guard.domain(),
            res.0.root() == guard.root(),
            res.0.reader_registry() == guard.reader_registry(),
            res.0.retire_observation_registry() == guard.retire_observation_registry(),
            res.0.reader_context() == guard.reader_context(),
            res.0.start_view() == guard.start_view(),
            res.0.expired() == guard.expired(),
            res.0.seen_removed() == guard.seen_removed(),
            res.0.protected() == guard.protected(),
            res.0.reader_fragment().fraction() == guard.reader_fragment().fraction() / 2real,
            res.1.key() == info.obj(),
            res.1.resource() == old(self).ownership(info.obj()),
            res.1.active_registry() == old(self).active_lease_registry(),
            res.1.participant_id() == guard.participant_id(),
            res.1.reader_fraction() == res.0.reader_fragment().fraction(),
            res.1.domain() == guard.domain(),
            res.1.root() == guard.root(),
            res.1.reader_context() == guard.reader_context(),
            res.1.start_view() == guard.start_view(),
            res.1.protected_addr() == info.addr(),
            final(self).active_ids() == old(self).active_ids().insert(res.1.lease_id()),
            final(self).active_record(res.1.lease_id()).witness().paper_guard()
                == guard.paper_guard(),
            final(self).active_record(res.1.lease_id()).witness().protected().obj() == info.obj(),
    {
        let tracked protected = RcuProtectedPtr::tracked_from_guard(&guard.paper_guard, info);
        let tracked res = self.tracked_split_protected(guard, &protected);
        info.lemma_wf_facts();
        assert(res.1.protected_addr() == info.ptr().addr());
        res
    }

    /// Returns one physical lease and rejoins its CPU fragment with the
    /// executable guard that originally issued it.
    pub proof fn tracked_return_loaded(
        tracked &mut self,
        tracked lease: RcuRootReadLease<O>,
        tracked guard: CpuRcuReadGuardToken<T>,
    ) -> (tracked res: CpuRcuReadGuardToken<T>)
        requires
            old(self).wf(),
            lease.active_registry() == old(self).active_lease_registry(),
            lease.participant_id() == guard.participant_id(),
            lease.reader_fraction() == guard.reader_fragment().fraction(),
            lease.domain() == guard.domain(),
            lease.root() == guard.root(),
            lease.reader_context() == guard.reader_context(),
            lease.start_view() == guard.start_view(),
            guard.protects(lease.protected_addr(), lease.key()),
            guard.wf(),
        ensures
            final(self).wf(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).domain() == old(self).domain(),
            final(self).root() == old(self).root(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).reclaim_registry() == old(self).reclaim_registry(),
            final(self).active_lease_registry() == old(self).active_lease_registry(),
            final(self).keys() == old(self).keys(),
            final(self).allocations() == old(self).allocations(),
            final(self).reclaim_states() == old(self).reclaim_states(),
            final(self).reclaimed() == old(self).reclaimed(),
            final(self).unretired_claims() == old(self).unretired_claims(),
            forall|obj: nat| #[trigger]
                final(self).has_unretired_claim(obj) == old(self).has_unretired_claim(obj),
            forall|obj: nat| #[trigger] final(self).contains(obj) == old(self).contains(obj),
            forall|obj: nat| #[trigger]
                old(self).contains(obj) ==> final(self).ownership(obj) == old(self).ownership(obj),
            final(self).active_ids() == old(self).active_ids().remove(lease.lease_id()),
            res.wf(),
            res.paper_guard() == guard.paper_guard(),
            res.binding() == guard.binding(),
            res.participant_id() == guard.participant_id(),
            res.cpu() == guard.cpu(),
            res.generation() == guard.generation(),
            res.participant_view() == guard.participant_view(),
            res.known_retired() == guard.known_retired(),
            res.domain() == guard.domain(),
            res.root() == guard.root(),
            res.reader_registry() == guard.reader_registry(),
            res.retire_observation_registry() == guard.retire_observation_registry(),
            res.reader_context() == guard.reader_context(),
            res.start_view() == guard.start_view(),
            res.expired() == guard.expired(),
            res.seen_removed() == guard.seen_removed(),
            res.protected() == guard.protected(),
            res.reader_fragment().fraction() == guard.reader_fragment().fraction() + old(
                self,
            ).active_record(lease.lease_id()).witness().reader().fraction(),
            res.reader_fragment().fraction() == guard.reader_fragment().fraction() * 2real,
    {
        use_type_invariant(&lease);
        let ghost protected_addr = lease.protected_addr();
        let tracked RcuRootReadLease { lease, active } = lease;
        active.agree(&self.active_leases);
        assert(self.active_ids().contains(lease.lease_id()));
        assert(self.active_lease_bindings()[lease.lease_id()] == RcuActiveLeaseBinding::from_record(
            self.active_record(lease.lease_id()),
        ));
        assert(self.active_record(lease.lease_id()).key() == lease.key());
        assert(self.active_record(lease.lease_id()).pool_id() == lease.pool_id());
        assert(self.active_record(lease.lease_id()).fraction() == lease.fraction());
        assert(self.active_record(lease.lease_id()).witness().reader().participant_id()
            == guard.participant_id());
        assert(self.active_record(lease.lease_id()).witness().paper_guard().domain()
            == guard.domain());
        assert(self.active_record(lease.lease_id()).witness().paper_guard().root() == guard.root());
        assert(self.active_record(lease.lease_id()).witness().paper_guard().reader()
            == guard.reader_context());
        assert(self.active_record(lease.lease_id()).witness().paper_guard().start_view()
            == guard.start_view());
        assert(self.active_record(lease.lease_id()).witness().protected().ptr().addr()
            == protected_addr);
        let ghost returned_id = lease.lease_id();
        let ghost returned_key = lease.key();
        self.active_leases.delete_points_to(active);
        let tracked witness = self.registry.return_lease(lease);
        let tracked guard = witness.tracked_return_to_guard(guard);
        assert forall|lease_id: nat| #[trigger] self.active_ids().contains(lease_id) implies {
            let record = self.active_record(lease_id);
            let witness = record.witness();
            &&& witness.wf()
            &&& record.key() == witness.protected().obj()
            &&& witness.protected().domain() == self.domain()
            &&& witness.paper_guard().domain() == self.domain()
            &&& witness.paper_guard().root() == self.root()
            &&& witness.paper_guard().retire_observation_registry()
                == self.retire_observation_registry()
        } by {
            assert(lease_id != returned_id);
            assert(old(self).active_ids().contains(lease_id));
            assert(self.active_record(lease_id) == old(self).active_record(lease_id));
        };
        assert forall|obj: nat| #[trigger] old(self).contains(obj) implies self.ownership(obj)
            == old(self).ownership(obj) by {
            if obj == returned_key {
                assert(self.registry().pool(obj).resource() == old(self).registry().pool(
                    obj,
                ).resource());
            } else {
                assert(self.registry().pool(obj) == old(self).registry().pool(obj));
            }
        };
        assert forall|obj: nat| #[trigger]
            self.has_unretired_claim(obj) == old(self).has_unretired_claim(obj) by {};
        assert forall|obj: nat| #[trigger] self.contains(obj) == old(self).contains(obj) by {};
        guard
    }

    /// A completed grace period rules out every still-active lease for the
    /// retired allocation.
    ///
    /// Any lease coexisting with the persistent closed-generation report must
    /// be a later reader. Such a reader already knows the retirement record,
    /// so its paper guard marks the allocation expired. That contradicts the
    /// same lease's protection witness.
    pub proof fn lemma_completed_excludes_active(
        tracked &mut self,
        tracked completed: &RcuReclaimedWitness,
        obj: nat,
    )
        requires
            old(self).wf(),
            completed.wf(),
            completed.scheduler() == old(self).scheduler(),
            completed.record().domain == old(self).domain(),
            completed.record().obj == obj,
            completed.record().retire_observation_registry == old(
                self,
            ).retire_observation_registry(),
            completed.record().removal.root == old(self).root(),
        ensures
            *final(self) == *old(self),
            !final(self).has_active(obj),
    {
        if self.has_active(obj) {
            assert(exists|lease_id: nat|
                #![auto]
                self.active_ids().contains(lease_id) && self.active_record(lease_id).key() == obj);
            let ghost lease_id = choose|lease_id: nat|
                #![auto]
                self.active_ids().contains(lease_id) && self.active_record(lease_id).key() == obj;
            let ghost record = self.active_record(lease_id);
            assert(record.key() == obj);
            assert(record.witness().wf());
            assert(record.witness().binding().registry() == self.scheduler());
            assert(record.witness().protected().obj() == obj);
            assert(record.witness().protected().domain() == self.domain());
            assert(record.witness().paper_guard().domain() == self.domain());
            assert(record.witness().paper_guard().root() == self.root());
            assert(record.witness().paper_guard().retire_observation_registry()
                == self.retire_observation_registry());
            let tracked witness = self.registry.tracked_borrow_active_witness_mut(lease_id);
            assert(*witness == record.witness());
            let tracked closed = completed.tracked_closed_generation(witness.reader().cpu());
            witness.lemma_same_participant_as_closed(closed);
            assert(closed.participant_id() == witness.reader().participant_id());
            closed.lemma_later_lease_witness_ref(witness);
            assert(closed.known_retired().contains(completed.record()));
            assert(completed.record().domain == witness.paper_guard().domain());
            assert(completed.record().retire_observation_registry
                == witness.paper_guard().retire_observation_registry());
            assert(completed.record().removal.root == witness.paper_guard().root());
            assert(witness.reader().known_retired().contains(completed.record()));
            assert(witness.paper_guard().expired().contains(obj));
            assert(witness.protected().protected_by(witness.paper_guard()));
            assert(!witness.paper_guard().seen_removed().removed.contains(obj));
            assert(witness.paper_guard().expired().subset_of(
                witness.paper_guard().seen_removed().removed,
            ));
            assert(false);
        }
    }

    /// Recovers one allocation after completion has ruled out every active
    /// lease for its identity.
    pub proof fn tracked_reclaim(
        tracked &mut self,
        tracked claim: RcuReclaimClaim<T>,
        tracked completed: RcuReclaimedWitness,
    ) -> (tracked ownership: O)
        requires
            old(self).wf(),
            claim.registry() == old(self).reclaim_registry(),
            claim.is_pending(),
            !old(self).has_active(claim.obj()),
            completed.wf(),
            completed.scheduler() == old(self).scheduler(),
            completed.record().domain == old(self).domain(),
            completed.record().obj == claim.obj(),
            completed.record().retire_observation_registry == old(
                self,
            ).retire_observation_registry(),
            completed.record().removal.root == old(self).root(),
        ensures
            final(self).wf(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).domain() == old(self).domain(),
            final(self).root() == old(self).root(),
            final(self).retire_observation_registry() == old(self).retire_observation_registry(),
            final(self).reclaim_registry() == old(self).reclaim_registry(),
            final(self).active_lease_registry() == old(self).active_lease_registry(),
            final(self).keys() == old(self).keys().remove(claim.obj()),
            final(self).allocations() == old(self).allocations(),
            final(self).active_ids() == old(self).active_ids(),
            final(self).unretired_claims() == old(self).unretired_claims(),
            forall|candidate: nat| #[trigger]
                final(self).has_unretired_claim(candidate) == old(self).has_unretired_claim(
                    candidate,
                ),
            final(self).reclaimed() == old(self).reclaimed().insert(claim.obj(), completed),
            forall|candidate: nat| #[trigger]
                final(self).keys().contains(candidate) ==> {
                    &&& old(self).keys().contains(candidate)
                    &&& old(self).contains(candidate)
                    &&& final(self).ownership(candidate) == old(self).ownership(candidate)
                },
            forall|candidate: nat| #[trigger]
                old(self).allocations().contains(candidate) && candidate != claim.obj()
                    ==> final(self).reclaim_states()[candidate] == old(
                    self,
                ).reclaim_states()[candidate],
            old(self).contains(claim.obj()),
            claim.ptr() == old(self).reclaim_states()[claim.obj()]->Some_0,
            ownership == old(self).registry().pool(claim.obj()).resource(),
            ownership == old(self).ownership(claim.obj()),
            final(self).reclaimed().contains_pair(claim.obj(), completed),
    {
        let ghost obj = claim.obj();
        self.registry.lemma_all_contains_iff_keys();
        let tracked RcuReclaimClaim { mut points_to } = claim;
        points_to.agree(&self.reclaim_state);
        assert(self.reclaim_state@[obj] == Some(points_to.value()->Some_0));
        assert(self.allocations().contains(obj));
        assert(self.keys().contains(obj));
        self.registry.lemma_contains_iff_key(obj);
        reveal(RcuRootPermissionState::contains);
        reveal(RcuRootPermissionState::keys);
        assert(self.contains(obj));
        if self.unretired_claims.contains_key(obj) {
            let tracked existing = self.unretired_claims.tracked_borrow_mut(obj);
            points_to.disjoint(existing);
            assert(false);
        }
        let ghost old_reclaim_states = self.reclaim_states();
        points_to.update(&mut self.reclaim_state, None);
        let tracked ownership = self.registry.reclaim(obj);
        self.reclaimed.tracked_insert(obj, completed);
        assert forall|lease_id: nat| #[trigger] self.active_ids().contains(lease_id) implies {
            let record = self.active_record(lease_id);
            let witness = record.witness();
            &&& witness.wf()
            &&& witness.binding().registry() == self.scheduler()
            &&& record.key() == witness.protected().obj()
            &&& witness.protected().domain() == self.domain()
            &&& witness.paper_guard().domain() == self.domain()
            &&& witness.paper_guard().root() == self.root()
            &&& witness.paper_guard().retire_observation_registry()
                == self.retire_observation_registry()
        } by {
            assert(old(self).active_ids().contains(lease_id));
            assert(old(self).active_record(lease_id).key() != obj);
            assert(self.registry().active_records() == old(self).registry().active_records());
            assert(self.registry().active_record(lease_id) == old(self).registry().active_record(
                lease_id,
            ));
            assert(self.active_record(lease_id) == old(self).active_record(lease_id));
        };
        assert(self.registry().keys().subset_of(self.allocations()));
        assert forall|candidate: nat| #[trigger] self.allocations().contains(candidate) implies {
            self.keys().contains(candidate) <==> self.reclaim_states()[candidate] is Some
        } by {
            if candidate == obj {
                assert(!self.keys().contains(candidate));
                assert(self.reclaim_states()[candidate] is None);
            } else {
                assert(self.reclaim_states()[candidate] == old_reclaim_states[candidate]);
                assert(self.keys().contains(candidate) == old(self).keys().contains(candidate));
            }
        };
        assert(self.unretired_claims().dom().subset_of(self.registry().keys()));
        assert(self.reclaimed().dom() == self.allocations().difference(self.keys())) by {
            assert(old(self).reclaimed().dom() == old(self).allocations().difference(
                old(self).keys(),
            ));
        };
        assert forall|candidate: nat| #[trigger] self.reclaimed().contains_key(candidate) implies {
            let saved = self.reclaimed()[candidate];
            &&& saved.wf()
            &&& saved.scheduler() == self.scheduler()
            &&& saved.record().domain == self.domain()
            &&& saved.record().obj == candidate
            &&& saved.record().retire_observation_registry == self.retire_observation_registry()
            &&& saved.record().removal.root == self.root()
        } by {
            if candidate == obj {
                assert(self.reclaimed()[candidate] == completed);
            } else {
                assert(old(self).reclaimed().contains_key(candidate));
                assert(self.reclaimed()[candidate] == old(self).reclaimed()[candidate]);
            }
        };
        self.registry.lemma_all_contains_iff_keys();
        assert forall|candidate: nat| #[trigger] self.keys().contains(candidate) implies {
            &&& old(self).keys().contains(candidate)
            &&& old(self).contains(candidate)
            &&& self.ownership(candidate) == old(self).ownership(candidate)
        } by {
            assert(candidate != obj);
            assert(self.contains(candidate));
            assert(old(self).keys().contains(candidate));
            assert(old(self).contains(candidate));
            assert(self.registry().pool(candidate) == old(self).registry().pool(candidate));
        };
        ownership
    }
}

impl CpuRcuClosedGeneration {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.resource.value().state is None
        &&& self.resource.value().closed =~= Set::empty().insert(self.report())
        &&& self.report().known_retired == self.known_retired.records()
        &&& self.binding.single_local_id() == self.resource.loc()
        &&& self.binding.cpu() == self.report().cpu
        &&& CpuRcuCarrier::records_observed(self.report().known_retired, self.report().view)
    }

    closed spec fn report(self) -> CpuRcuReportView {
        choose|report: CpuRcuReportView| self.resource.value().closed.contains(report)
    }

    pub closed spec fn participant_id(self) -> Loc {
        self.resource.loc()
    }

    pub closed spec fn binding(self) -> CpuRcuCoreBinding {
        self.binding
    }

    pub closed spec fn scheduler(self) -> Loc {
        self.binding().registry()
    }

    pub closed spec fn cpu(self) -> CpuId {
        self.report().cpu
    }

    pub closed spec fn closed_generation(self) -> nat {
        self.report().generation
    }

    pub closed spec fn view(self) -> Irc11ThreadView {
        self.report().view
    }

    pub closed spec fn known_retired(self) -> Set<RcuRetiredRecord> {
        self.known_retired.records()
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.resource.value() == CpuRcuCarrier::closed(self.report())
        &&& self.binding().single_local_id() == self.participant_id()
        &&& self.binding().cpu() == self.cpu()
    }

    /// Relates this report to another client of the scheduler's canonical
    /// CPU-local registration. Agreement of the registry entry rules out a
    /// second RCU participant identity for the same CPU.
    pub proof fn lemma_same_participant_as_binding(tracked &self, tracked other: &CpuRcuCoreBinding)
        requires
            self.wf(),
            other.registry() == self.scheduler(),
            other.cpu() == self.cpu(),
            other.locals_key().len() == 1,
        ensures
            other.single_local_id() == self.participant_id(),
    {
        self.binding.lemma_same_cpu_agree(other);
    }

    /// Splits the idempotent closed-generation fact.
    pub proof fn tracked_duplicate(tracked self) -> (tracked res: (
        CpuRcuClosedGeneration,
        CpuRcuClosedGeneration,
    ))
        requires
            self.wf(),
        ensures
            res.0.participant_id() == self.participant_id(),
            res.0.cpu() == self.cpu(),
            res.0.closed_generation() == self.closed_generation(),
            res.0.view() == self.view(),
            res.0.known_retired() == self.known_retired(),
            res.0.scheduler() == self.scheduler(),
            res.0.wf(),
            res.1.participant_id() == self.participant_id(),
            res.1.cpu() == self.cpu(),
            res.1.closed_generation() == self.closed_generation(),
            res.1.view() == self.view(),
            res.1.known_retired() == self.known_retired(),
            res.1.scheduler() == self.scheduler(),
            res.1.wf(),
    {
        use_type_invariant(&self);
        let ghost report = self.report();
        let ghost records = self.known_retired.records();
        let ghost carrier = CpuRcuCarrier::closed(self.report());
        assert(carrier.closed.union(carrier.closed) =~= carrier.closed);
        assert(carrier == CpuRcuCarrier::op(carrier, carrier));
        let tracked (left, right) = self.resource.split(carrier, carrier);
        let tracked right_known_retired = self.known_retired.tracked_duplicate();
        let tracked right_binding = self.binding.tracked_duplicate();
        assert(left.value() == carrier);
        assert(right.value() == carrier);
        lemma_choose_singleton_report(report);
        assert((choose|candidate: CpuRcuReportView| left.value().closed.contains(candidate))
            == report);
        assert((choose|candidate: CpuRcuReportView| right.value().closed.contains(candidate))
            == report);
        assert(report.known_retired == records);
        assert(right_known_retired.records() == records);
        (
            CpuRcuClosedGeneration {
                resource: left,
                known_retired: self.known_retired,
                binding: self.binding,
            },
            CpuRcuClosedGeneration {
                resource: right,
                known_retired: right_known_retired,
                binding: right_binding,
            },
        )
    }

    /// Creates another copy of this persistent closed-generation fact.
    ///
    /// This is admissible because composing the idempotent carrier with itself
    /// leaves the carrier unchanged. The monitor uses this operation when one
    /// completed grace period authorizes multiple callbacks.
    pub proof fn tracked_duplicate_from_ref(tracked &self) -> (tracked duplicate:
        CpuRcuClosedGeneration)
        requires
            self.wf(),
        ensures
            duplicate.participant_id() == self.participant_id(),
            duplicate.cpu() == self.cpu(),
            duplicate.closed_generation() == self.closed_generation(),
            duplicate.view() == self.view(),
            duplicate.known_retired() == self.known_retired(),
            duplicate.scheduler() == self.scheduler(),
            duplicate.wf(),
    {
        use_type_invariant(self);
        let ghost report = self.report();
        let ghost records = self.known_retired.records();
        let ghost carrier = CpuRcuCarrier::closed(self.report());
        assert(carrier.closed.union(carrier.closed) =~= carrier.closed);
        assert(CpuRcuCarrier::op(carrier, carrier) == carrier);
        assert(frame_preserving_update_opt::<CpuRcuCarrier>(
            carrier,
            CpuRcuCarrier::op(carrier, carrier),
        )) by {
            assert forall|frame: Option<CpuRcuCarrier>|
                #![trigger Option::<CpuRcuCarrier>::op(Some(carrier), frame),
                    Option::<CpuRcuCarrier>::op(
                        Some(CpuRcuCarrier::op(carrier, carrier)),
                        frame,
                    )]
                Option::<CpuRcuCarrier>::op(Some(carrier), frame).valid() implies Option::<
                CpuRcuCarrier,
            >::op(Some(CpuRcuCarrier::op(carrier, carrier)), frame).valid() by {
                assert(CpuRcuCarrier::op(carrier, carrier) == carrier);
            };
        };
        let tracked resource = self.resource.duplicate_previous(carrier);
        let tracked known_retired = self.known_retired.tracked_duplicate();
        let tracked binding = self.binding.tracked_duplicate();
        assert(resource.value() == carrier);
        lemma_choose_singleton_report(report);
        assert((choose|candidate: CpuRcuReportView| resource.value().closed.contains(candidate))
            == report);
        assert(report.known_retired == records);
        assert(known_retired.records() == records);
        CpuRcuClosedGeneration { resource, known_retired, binding }
    }

    /// Any reader coexisting with this report started in a later generation
    /// and carries a participant view that includes the report view.
    pub proof fn lemma_later_reader(
        tracked &self,
        tracked mut reader: CpuRcuReaderFragment,
    ) -> (tracked res: CpuRcuReaderFragment)
        requires
            self.wf(),
            reader.wf(),
            self.participant_id() == reader.participant_id(),
        ensures
            res == reader,
            res.wf(),
            self.closed_generation() < res.generation(),
            self.view().spec_le(res.participant_view()),
            self.known_retired().subset_of(res.known_retired()),
    {
        use_type_invariant(&reader);
        use_type_invariant(self);
        assert(reader.resource.value().state_view().known_retired
            == reader.known_retired.records());
        assert(self.report().known_retired == self.known_retired.records());
        reader.resource.validate_2(&self.resource);
        let ghost report = self.report();
        let ghost reader_state = reader.resource.value().state_view();
        assert(CpuRcuCarrier::op(reader.resource.value(), self.resource.value()).valid());
        assert(Option::<CpuRcuState>::op(reader.resource.value().state, None)
            == reader.resource.value().state);
        assert(reader.resource.value().closed.is_empty());
        assert(reader.resource.value().closed.union(Set::empty().insert(report))
            =~= Set::empty().insert(report));
        assert(CpuRcuCarrier::op(reader.resource.value(), self.resource.value()) == CpuRcuCarrier {
            state: reader.resource.value().state,
            closed: Set::empty().insert(report),
        });
        assert(CpuRcuCarrier::reports_fit(reader_state, Set::empty().insert(report)));
        assert(Set::empty().insert(report).contains(report));
        assert(report.generation < reader_state.generation);
        assert(self.view().spec_le(reader.participant_view()));
        assert(report.known_retired.subset_of(reader_state.known_retired));
        assert(self.known_retired().subset_of(reader.known_retired()));
        reader
    }

    /// Reference-preserving form of [`Self::lemma_later_reader`].
    ///
    /// This form is used when a reader fragment is retained as the witness of
    /// an active read lease. Validating it against the persistent closed-
    /// generation resource does not consume either token.
    pub proof fn lemma_later_reader_ref(tracked &self, tracked reader: &mut CpuRcuReaderFragment)
        requires
            self.wf(),
            old(reader).wf(),
            self.participant_id() == old(reader).participant_id(),
        ensures
            *final(reader) == *old(reader),
            self.closed_generation() < final(reader).generation(),
            self.view().spec_le(final(reader).participant_view()),
            self.known_retired().subset_of(final(reader).known_retired()),
    {
        use_type_invariant(&*reader);
        use_type_invariant(self);
        assert(reader.resource.value().state_view().known_retired
            == reader.known_retired.records());
        assert(self.report().known_retired == self.known_retired.records());
        reader.resource.validate_2(&self.resource);
        let ghost report = self.report();
        let ghost reader_state = reader.resource.value().state_view();
        assert(CpuRcuCarrier::op(reader.resource.value(), self.resource.value()).valid());
        assert(Option::<CpuRcuState>::op(reader.resource.value().state, None)
            == reader.resource.value().state);
        assert(reader.resource.value().closed.is_empty());
        assert(reader.resource.value().closed.union(Set::empty().insert(report))
            =~= Set::empty().insert(report));
        assert(CpuRcuCarrier::op(reader.resource.value(), self.resource.value()) == CpuRcuCarrier {
            state: reader.resource.value().state,
            closed: Set::empty().insert(report),
        });
        assert(CpuRcuCarrier::reports_fit(reader_state, Set::empty().insert(report)));
        assert(Set::empty().insert(report).contains(report));
        assert(report.generation < reader_state.generation);
        assert(self.view().spec_le(reader.participant_view()));
        assert(report.known_retired.subset_of(reader_state.known_retired));
        assert(self.known_retired().subset_of(reader.known_retired()));
    }

    /// Classifies an active physical-lease witness as a later reader without
    /// consuming the witness retained by the root registry.
    pub proof fn lemma_later_lease_witness_ref<T>(
        tracked &self,
        tracked witness: &mut CpuRcuReadLeaseWitness<T>,
    )
        requires
            self.wf(),
            old(witness).wf(),
            self.participant_id() == old(witness).reader().participant_id(),
        ensures
            *final(witness) == *old(witness),
            self.closed_generation() < final(witness).reader().generation(),
            self.view().spec_le(final(witness).reader().participant_view()),
            self.known_retired().subset_of(final(witness).reader().known_retired()),
    {
        self.lemma_later_reader_ref(&mut witness.reader);
    }

    /// Lifts [`Self::lemma_later_reader`] to the task view used to start a
    /// reader.
    ///
    /// This is the paper's later-reader branch: once the task imports the
    /// persistent CPU view, it also observes every detachment observation
    /// carried by an earlier report.
    pub proof fn lemma_later_reader_start_view(
        tracked &self,
        tracked reader: CpuRcuReaderFragment,
        start_view: Irc11ThreadView,
    ) -> (tracked res: CpuRcuReaderFragment)
        requires
            self.wf(),
            reader.wf(),
            self.participant_id() == reader.participant_id(),
            reader.participant_view().spec_le(start_view),
        ensures
            res == reader,
            res.wf(),
            self.closed_generation() < res.generation(),
            self.view().spec_le(start_view),
            self.known_retired().subset_of(res.known_retired()),
    {
        let tracked reader = self.lemma_later_reader(reader);
        self.view().lemma_spec_le_transitive(reader.participant_view(), start_view);
        reader
    }

    /// A reader from a generation covered by this report cannot remain live.
    pub proof fn lemma_excludes_old_reader(tracked &self, tracked reader: CpuRcuReaderFragment)
        requires
            self.wf(),
            reader.wf(),
            self.participant_id() == reader.participant_id(),
            reader.generation() <= self.closed_generation(),
        ensures
            false,
    {
        let tracked _reader = self.lemma_later_reader(reader);
    }

    /// A complete refined guard coexisting with this report necessarily
    /// started after the generation closed by the report.
    pub proof fn lemma_later_guard<T>(
        tracked &self,
        tracked guard: CpuRcuReadGuardToken<T>,
    ) -> (tracked res: CpuRcuReadGuardToken<T>)
        requires
            self.wf(),
            guard.wf(),
            self.participant_id() == guard.participant_id(),
            self.cpu() == guard.cpu(),
        ensures
            res.wf(),
            res.paper_guard() == guard.paper_guard(),
            res.reader_fragment() == guard.reader_fragment(),
            res.scheduler() == guard.scheduler(),
            res.participant_id() == guard.participant_id(),
            res.cpu() == guard.cpu(),
            res.generation() == guard.generation(),
            res.domain() == guard.domain(),
            res.root() == guard.root(),
            res.retire_observation_registry() == guard.retire_observation_registry(),
            res.start_view() == guard.start_view(),
            res.expired() == guard.expired(),
            res.seen_removed() == guard.seen_removed(),
            self.closed_generation() < res.generation(),
            self.view().spec_le(res.start_view()),
            self.known_retired().subset_of(res.known_retired()),
    {
        let tracked (paper_guard, reader, binding) = guard.tracked_into_parts();
        let tracked reader = self.lemma_later_reader_start_view(reader, paper_guard.start_view());
        CpuRcuReadGuardToken::tracked_new(paper_guard, reader, binding)
    }

    /// Reference-preserving classification of a live refined guard.
    pub proof fn lemma_later_guard_ref<T>(
        tracked &self,
        tracked guard: &mut CpuRcuReadGuardToken<T>,
    )
        requires
            self.wf(),
            old(guard).wf(),
            self.participant_id() == old(guard).participant_id(),
            self.cpu() == old(guard).cpu(),
        ensures
            *final(guard) == *old(guard),
            self.closed_generation() < final(guard).generation(),
            self.view().spec_le(final(guard).start_view()),
            self.known_retired().subset_of(final(guard).known_retired()),
    {
        self.lemma_later_reader_ref(&mut guard.reader);
        self.view().lemma_spec_le_transitive(guard.start_view(), guard.start_view());
    }

    /// The old-reader branch of the paper proof: a guard from a generation
    /// covered by this report cannot still own its CPU reader fragment.
    pub proof fn lemma_excludes_old_guard<T>(tracked &self, tracked guard: CpuRcuReadGuardToken<T>)
        requires
            self.wf(),
            guard.wf(),
            self.scheduler() == guard.scheduler(),
            self.cpu() == guard.cpu(),
            guard.generation() <= self.closed_generation(),
        ensures
            false,
    {
        self.binding.lemma_same_cpu_agree(&guard.binding);
        assert(self.participant_id() == guard.participant_id());
        let tracked (_paper_guard, reader, _binding) = guard.tracked_into_parts();
        self.lemma_excludes_old_reader(reader);
    }
}

/// Regression proof for both sides of the grace-period reader dichotomy.
proof fn cpu_rcu_generation_smoke_test(cpu: CpuId, initial: Irc11ThreadView, later: Irc11ThreadView)
    requires
        initial.spec_le(later),
{
    let tracked participant = CpuRcuParticipant::new(cpu, initial);
    let tracked core = CpuCoreOwner::new(cpu, participant);
    let ghost registration = core.registration();
    let tracked (mut registry, _entries) = GhostMapAuth::new(
        Map::<CpuId, CpuCoreRegistration>::empty(),
    );
    let tracked entry = registry.insert(cpu, registration);
    let tracked binding = CpuCoreOwnerBinding::tracked_new(entry, &core);
    let tracked (handle, participant) = core.tracked_open();
    let tracked (participant, reader) = participant.tracked_start_reader(initial, 0.5real);
    let tracked participant = participant.tracked_stop_reader(reader);
    assert(participant.fraction() == 1real);
    let tracked (participant, closed) = participant.tracked_report_quiescent(binding, later);
    let tracked (participant, new_reader) = participant.tracked_start_reader(later, 0.5real);
    let tracked new_reader = closed.lemma_later_reader_start_view(new_reader, later);
    assert(closed.closed_generation() < new_reader.generation());
    assert(closed.view().spec_le(later));
    let tracked participant = participant.tracked_stop_reader(new_reader);
    let tracked _core = handle.tracked_restore(participant);
}

} // verus!
