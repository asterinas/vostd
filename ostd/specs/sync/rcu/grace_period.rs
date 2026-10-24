// SPDX-License-Identifier: MPL-2.0
//! Grace-period batches and per-callback reclamation evidence.
//!
//! # Verified Properties
//! A batch closes only after every CPU in its fixed online set supplies a
//! canonical closed-generation report covering every callback's retirement.
//! Reports from another scheduler or an earlier view do not satisfy the
//! invariant. Completing a batch yields evidence, not physical ownership.
use vstd::{prelude::*, resource::Loc};
use vstd_extra::{atomic_irc11::ThreadView, ownership::Inv};

use super::{
    cpu::CpuRcuClosedGeneration,
    retirement::{RcuRetiredFact, RcuRetiredRecord},
};
use crate::cpu::CpuId;

verus! {

broadcast use {vstd::set::group_set_lemmas, vstd::thread_view::group_thread_view_axioms};

/// Callback identity and observations that every reporting CPU must cover.
pub ghost struct RcuCallbackSummary {
    pub scheduler: Loc,
    pub retired: RcuRetiredRecord,
    pub epoch: nat,
    pub retire_view: ThreadView,
}

/// Persistent completion evidence for one fixed batch.
pub tracked struct CompletedGracePeriod {
    ghost scheduler: Loc,
    ghost epoch: nat,
    ghost online: Set<CpuId>,
    ghost callbacks: Seq<RcuCallbackSummary>,
    reports: Map<CpuId, CpuRcuClosedGeneration>,
}

/// Object-specific authorization; physical permission is recovered separately.
pub tracked struct RcuReclaimPermit {
    ghost summary: RcuCallbackSummary,
    ghost online: Set<CpuId>,
    fact: RcuRetiredFact,
    reports: Map<CpuId, CpuRcuClosedGeneration>,
}

/// Whether a CPU report covers a particular queued callback.
pub open spec fn report_covers(
    report: CpuRcuClosedGeneration,
    callback: RcuCallbackSummary,
) -> bool {
    &&& report.wf()
    &&& report.scheduler() == callback.scheduler
    &&& report.view().contains(callback.retire_view)
    &&& report.known_retired().contains(callback.retired)
}

/// Reports collected while a single epoch is active.
pub tracked struct RcuGracePeriod {
    ghost scheduler: Loc,
    ghost epoch: nat,
    ghost online: Set<CpuId>,
    ghost callbacks: Seq<RcuCallbackSummary>,
    reports: Map<CpuId, CpuRcuClosedGeneration>,
}

impl Inv for RcuGracePeriod {
    closed spec fn inv(self) -> bool {
        &&& self.reports.dom().subset_of(self.online)
        &&& forall|i: int|
            0 <= i < self.callbacks.len() ==> {
                let callback = #[trigger] self.callbacks[i];
                &&& callback.epoch == self.epoch
                &&& callback.scheduler == self.scheduler
                &&& callback.retired.removal.observed_by(callback.retire_view)
            }
        &&& forall|cpu: CpuId| #[trigger]
            self.reports.contains_key(cpu) ==> {
                &&& self.reports[cpu].cpu() == cpu
                &&& self.reports[cpu].wf()
                &&& self.reports[cpu].scheduler() == self.scheduler
                &&& forall|i: int|
                    0 <= i < self.callbacks.len() ==> report_covers(
                        self.reports[cpu],
                        #[trigger] self.callbacks[i],
                    )
            }
    }
}

impl RcuGracePeriod {
    /// Starts an epoch without reusing any report from an earlier batch.
    pub proof fn tracked_start(
        scheduler: Loc,
        epoch: nat,
        online: Set<CpuId>,
        callbacks: Seq<RcuCallbackSummary>,
    ) -> (tracked res: Self)
        requires
            forall|i: int|
                0 <= i < callbacks.len() ==> {
                    let callback = #[trigger] callbacks[i];
                    &&& callback.epoch == epoch
                    &&& callback.scheduler == scheduler
                    &&& callback.retired.removal.observed_by(callback.retire_view)
                },
        ensures
            res.inv(),
            res.scheduler() == scheduler,
            res.epoch() == epoch,
            res.online() == online,
            res.callbacks() == callbacks,
            res.reported() == Set::<CpuId>::empty(),
    {
        Self { scheduler, epoch, online, callbacks, reports: Map::tracked_empty() }
    }

    /// Scheduler registry that owns the reporting CPU participants.
    pub closed spec fn scheduler(self) -> Loc {
        self.scheduler
    }

    /// Global batch epoch, distinct from each CPU's reader generation.
    pub closed spec fn epoch(self) -> nat {
        self.epoch
    }

    /// Stable online set for this batch; hotplug is not modeled.
    pub closed spec fn online(self) -> Set<CpuId> {
        self.online
    }

    /// Callbacks assigned to this batch before it started.
    pub closed spec fn callbacks(self) -> Seq<RcuCallbackSummary> {
        self.callbacks
    }

    /// Exact ghost counterpart of the monitor's CPU report mask.
    pub closed spec fn reported(self) -> Set<CpuId> {
        self.reports.dom()
    }

    /// A well-formed active mask never contains an unconfigured CPU.
    pub proof fn lemma_reported_subset(self)
        requires
            self.inv(),
        ensures
            self.reported().subset_of(self.online()),
    {
    }

    /// Accepts a report only after checking all retire views in the active batch.
    pub proof fn tracked_report(tracked &mut self, tracked report: CpuRcuClosedGeneration)
        requires
            old(self).inv(),
            old(self).online().contains(report.cpu()),
            report.wf(),
            report.scheduler() == old(self).scheduler(),
            forall|i: int|
                0 <= i < old(self).callbacks().len() ==> report_covers(
                    report,
                    #[trigger] old(self).callbacks()[i],
                ),
        ensures
            final(self).inv(),
            final(self).scheduler() == old(self).scheduler(),
            final(self).epoch() == old(self).epoch(),
            final(self).online() == old(self).online(),
            final(self).callbacks() == old(self).callbacks(),
            final(self).reported() == old(self).reported().insert(report.cpu()),
    {
        let ghost cpu = report.cpu();
        self.reports.tracked_insert(cpu, report);
        assert forall|other: CpuId| #[trigger] self.reports.contains_key(other) implies {
            &&& self.reports[other].cpu() == other
            &&& self.reports[other].wf()
            &&& self.reports[other].scheduler() == self.scheduler
            &&& forall|i: int|
                0 <= i < self.callbacks.len() ==> report_covers(
                    self.reports[other],
                    #[trigger] self.callbacks[i],
                )
        } by {
            if other != cpu {
                assert(old(self).reports.contains_key(other));
            }
            assert forall|i: int| 0 <= i < self.callbacks.len() implies report_covers(
                self.reports[other],
                #[trigger] self.callbacks[i],
            ) by {
                if other == cpu {
                    assert(self.reports[other] == report);
                    assert(report_covers(report, old(self).callbacks()[i]));
                } else {
                    assert(report_covers(old(self).reports[other], old(self).callbacks[i]));
                    assert(self.reports[other] == old(self).reports[other]);
                }
                assert(self.callbacks[i] == old(self).callbacks[i]);
            };
        };
    }

    /// Consumes a fully reported epoch without granting any physical ownership.
    pub proof fn tracked_complete(tracked self) -> (tracked res: CompletedGracePeriod)
        requires
            self.inv(),
            self.reported() == self.online(),
        ensures
            res.inv(),
            res.scheduler() == self.scheduler(),
            res.epoch() == self.epoch(),
            res.online() == self.online(),
            res.callbacks() == self.callbacks(),
    {
        CompletedGracePeriod {
            scheduler: self.scheduler,
            epoch: self.epoch,
            online: self.online,
            callbacks: self.callbacks,
            reports: self.reports,
        }
    }
}

impl Inv for CompletedGracePeriod {
    closed spec fn inv(self) -> bool {
        &&& self.reports.dom() == self.online
        &&& forall|i: int|
            0 <= i < self.callbacks.len() ==> {
                let callback = #[trigger] self.callbacks[i];
                &&& callback.scheduler == self.scheduler
                &&& callback.epoch == self.epoch
                &&& callback.retired.removal.observed_by(callback.retire_view)
            }
        &&& forall|cpu: CpuId| #[trigger]
            self.reports.contains_key(cpu) ==> {
                &&& self.reports[cpu].cpu() == cpu
                &&& self.reports[cpu].wf()
                &&& self.reports[cpu].scheduler() == self.scheduler
                &&& forall|i: int|
                    0 <= i < self.callbacks.len() ==> report_covers(
                        self.reports[cpu],
                        #[trigger] self.callbacks[i],
                    )
            }
    }
}

impl CompletedGracePeriod {
    /// Scheduler registry whose participants supplied this batch's reports.
    pub closed spec fn scheduler(self) -> Loc {
        self.scheduler
    }

    /// Completed batch epoch.
    pub closed spec fn epoch(self) -> nat {
        self.epoch
    }

    /// CPUs covered by completion.
    pub closed spec fn online(self) -> Set<CpuId> {
        self.online
    }

    /// Exact batch whose callbacks can be authorized.
    pub closed spec fn callbacks(self) -> Seq<RcuCallbackSummary> {
        self.callbacks
    }

    /// Authorizes a batch member only with its matching retirement certificate.
    pub proof fn tracked_authorize(
        tracked &self,
        index: int,
        tracked fact: &RcuRetiredFact,
    ) -> (tracked res: RcuReclaimPermit)
        requires
            self.inv(),
            0 <= index < self.callbacks().len(),
            fact.record() == self.callbacks()[index].retired,
        ensures
            res.inv(),
            res.summary() == self.callbacks()[index],
            res.online() == self.online(),
    {
        let tracked reports = duplicate_reports(&self.reports, self.online);
        let tracked fact = fact.tracked_duplicate();
        RcuReclaimPermit { summary: self.callbacks[index], online: self.online, fact, reports }
    }
}

impl Inv for RcuReclaimPermit {
    closed spec fn inv(self) -> bool {
        &&& self.fact.record() == self.summary.retired
        &&& self.summary.retired.removal.observed_by(self.summary.retire_view)
        &&& self.reports.dom() == self.online
        &&& forall|cpu: CpuId| #[trigger]
            self.reports.contains_key(cpu) ==> {
                &&& self.reports[cpu].cpu() == cpu
                &&& report_covers(self.reports[cpu], self.summary)
            }
    }
}

impl RcuReclaimPermit {
    /// Callback identity and retirement view covered by this permit.
    pub closed spec fn summary(self) -> RcuCallbackSummary {
        self.summary
    }

    /// Fixed CPU set whose reader generations were closed.
    pub closed spec fn online(self) -> Set<CpuId> {
        self.online
    }

    /// Borrows one canonical report to exclude a live physical lease.
    pub proof fn tracked_report(tracked &self, cpu: CpuId) -> (tracked res: &CpuRcuClosedGeneration)
        requires
            self.inv(),
            self.online().contains(cpu),
        ensures
            res.cpu() == cpu,
            report_covers(*res, self.summary()),
    {
        self.reports.tracked_borrow(cpu)
    }
}

// Copy only idempotent reports. No live-reader fraction is duplicated.
proof fn duplicate_reports(
    tracked source: &Map<CpuId, CpuRcuClosedGeneration>,
    keys: Set<CpuId>,
) -> (tracked res: Map<CpuId, CpuRcuClosedGeneration>)
    requires
        keys.subset_of(source.dom()),
        forall|cpu: CpuId| #[trigger] source.contains_key(cpu) ==> source[cpu].wf(),
    ensures
        res.dom() == keys,
        forall|cpu: CpuId| #[trigger]
            res.contains_key(cpu) ==> {
                &&& res[cpu].wf()
                &&& res[cpu].cpu() == source[cpu].cpu()
                &&& res[cpu].scheduler() == source[cpu].scheduler()
                &&& res[cpu].participant_id() == source[cpu].participant_id()
                &&& res[cpu].closed_generation() == source[cpu].closed_generation()
                &&& res[cpu].view() == source[cpu].view()
                &&& res[cpu].known_retired() == source[cpu].known_retired()
            },
    decreases keys.len(),
{
    if keys.is_empty() {
        Map::tracked_empty()
    } else {
        let ghost cpu = keys.choose();
        let tracked mut res = duplicate_reports(source, keys.remove(cpu));
        let tracked report = source.tracked_borrow(cpu).tracked_duplicate_from_ref();
        res.tracked_insert(cpu, report);
        assert(keys == keys.remove(cpu).insert(cpu));
        res
    }
}

} // verus!
