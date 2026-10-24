// SPDX-License-Identifier: MPL-2.0
//! CPU-local reader generations and persistent quiescent reports.
//!
//! # Verified Properties
//! Positive reader fractions prevent closing their CPU generation. A report
//! and a coexisting reader from the same canonical participant agree that the
//! reader is newer and includes the report's view and retirement facts.
//!
//! These resources must be installed in the scheduler's CPU-local aggregate.
//! Executable callers must disable preemption while holding a reader fragment,
//! and use their native subjective view when starting or reporting. This module
//! neither creates a native ViewSeen nor establishes those runtime obligations.
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
use vstd_extra::atomic_irc11::{ThreadView as Irc11ThreadView, ThreadViewOrder};

use crate::specs::task::cpu_core::{
    CpuCoreLocalState, CpuCoreOwner, CpuCoreOwnerBinding, CpuCoreRegistration,
};

use super::retirement::{RcuRetiredFacts, RcuRetiredRecord};
use crate::cpu::CpuId;

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
        &super::retirement::RcuRetiredFact)
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
