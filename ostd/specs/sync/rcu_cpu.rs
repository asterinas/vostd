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
    mm::cpu::CpuId,
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
        map::GhostMapAuth,
        product::ProductRA,
        relations::frame_preserving_update_opt,
    },
};

use super::{
    rcu::{
        RcuBlockInfo, RcuInactive, RcuProtectedPtr, RcuReadGuardToken, RcuReaderContext,
        RcuRetiredFacts, RcuRetiredRecord, RcuSeenRemoved,
    },
    weak_memory::WmView,
};

verus! {

broadcast use vstd::set::group_set_lemmas;

/// One CPU quiescent report retained by the participant PCM.
pub ghost struct CpuRcuReportView {
    pub cpu: CpuId,
    pub generation: nat,
    pub view: WmView,
    pub known_retired: Set<RcuRetiredRecord>,
}

pub(super) ghost struct CpuRcuStateView {
    pub(super) cpu: CpuId,
    pub(super) generation: nat,
    pub(super) view: WmView,
    pub(super) known_retired: Set<RcuRetiredRecord>,
}

pub(super) type CpuRcuState = ProductRA<FractionRA, AgreementRA<CpuRcuStateView>>;

pub(super) ghost struct CpuRcuCarrier {
    pub(super) state: Option<CpuRcuState>,
    pub(super) closed: Set<CpuRcuReportView>,
}

impl CpuRcuCarrier {
    pub(super) open spec fn records_observed(records: Set<RcuRetiredRecord>, view: WmView) -> bool {
        forall|record: RcuRetiredRecord| #[trigger]
            records.contains(record) ==> record.removal.observed_by(view)
    }

    pub(super) open spec fn state(
        cpu: CpuId,
        generation: nat,
        view: WmView,
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
    pub proof fn new(cpu: CpuId, view: WmView) -> (tracked res: Self)
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

    pub closed spec fn view(self) -> WmView {
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
        start_view: WmView,
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
        start_view: WmView,
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
        report_view: WmView,
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
                    assert(old_view.seen_at(record.removal.root) <= report_view.seen_at(
                        record.removal.root,
                    ));
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
        report_view: WmView,
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
        report_view: WmView,
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
        report_view: WmView,
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

    pub closed spec fn participant_view(self) -> WmView {
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
    pub proof fn tracked_retired_facts_observed_by(tracked &self, view: WmView) -> (tracked res:
        &RcuRetiredFacts)
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
            assert(self.participant_view().seen_at(record.removal.root) <= view.seen_at(
                record.removal.root,
            ));
        };
        &self.known_retired
    }

    pub closed spec fn fraction(self) -> real {
        self.resource.value().fraction()
    }

    pub open spec fn wf(self) -> bool {
        0real < self.fraction() <= 1real
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

    pub closed spec fn participant_view(self) -> WmView {
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

    pub closed spec fn start_view(self) -> WmView {
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
            res.2.registry() == self.scheduler(),
            res.2.cpu() == self.cpu(),
            res.2.single_local_id() == self.participant_id(),
            res.0.wf(),
            res.1.wf(),
            res.0.reader().cpu == res.1.cpu(),
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

    pub closed spec fn view(self) -> WmView {
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

    /// Lifts [`Self::lemma_later_reader`] to the task view used to start a
    /// reader.
    ///
    /// This is the paper's later-reader branch: once the task imports the
    /// persistent CPU view, it also observes every detachment observation
    /// carried by an earlier report.
    pub proof fn lemma_later_reader_start_view(
        tracked &self,
        tracked reader: CpuRcuReaderFragment,
        start_view: WmView,
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
proof fn cpu_rcu_generation_smoke_test(cpu: CpuId, initial: WmView, later: WmView)
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
