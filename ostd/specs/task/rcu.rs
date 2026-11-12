// SPDX-License-Identifier: MPL-2.0
//! Explicit RCU access to the scheduler's checked-out native task view.
//!
//! # Verified Properties
//! Attaching consumes the scheduled core owner. Readers borrow fractions of
//! that core's canonical participant; detaching or reporting requires all of
//! them back. No operation creates a replacement subjective `ViewSeen`.
//!
//! The kernel must keep the task on this CPU until detach. These capabilities
//! model that obligation; they do not implement `disable_preempt` or scheduling.
use vstd::{prelude::*, resource::Loc};
use vstd_extra::{
    atomic_irc11::{ThreadView, ViewSeen},
    ownership::Inv,
};

use super::cpu_core::{CpuCoreOwner, CpuCoreOwnerHandle};
use crate::specs::sync::rcu::{
    cpu::{CpuRcuClosedGeneration, CpuRcuCoreBinding, CpuRcuParticipant, CpuRcuReaderFragment},
    retirement::RcuRetiredFacts,
};

use crate::{cpu::CpuId, task::RunningTaskContext};

verus! {

broadcast use vstd::thread_view::group_thread_view_axioms;

/// One pinned running interval, including its real checked-out native view.
pub tracked struct RunningRcuContext {
    task: RunningTaskContext,
    core: CpuCoreOwnerHandle<CpuRcuParticipant>,
    participant: CpuRcuParticipant,
    binding: CpuRcuCoreBinding,
}

impl View for RunningRcuContext {
    type V = ThreadView;

    closed spec fn view(&self) -> ThreadView {
        self.task@
    }
}

impl Inv for RunningRcuContext {
    closed spec fn inv(self) -> bool {
        &&& self.core.wf()
        &&& self.core.cpu() == self.task.cpu()
        &&& self.core.current_task() == Some(self.task.task())
        &&& self.core.expected_locals_key() == seq![self.participant.id()]
        &&& self.participant.wf()
        &&& self.participant.cpu() == self.task.cpu()
        &&& self.binding.cpu() == self.task.cpu()
        &&& self.binding.owner_id() == self.core.id()
        &&& self.binding.locals_key() == self.core.expected_locals_key()
        &&& self@.contains(self.participant.view())
    }
}

impl RunningRcuContext {
    pub closed spec fn cpu(self) -> CpuId {
        self.task.cpu()
    }

    pub closed spec fn task(self) -> Loc {
        self.task.task()
    }

    pub closed spec fn view_registry(self) -> Loc {
        self.task.registry_id()
    }

    pub closed spec fn binding(self) -> CpuRcuCoreBinding {
        self.binding
    }

    pub closed spec fn participant(self) -> CpuRcuParticipant {
        self.participant
    }

    pub open spec fn scheduler(self) -> Loc {
        self.binding().registry()
    }

    /// Stable identities across native operations and reader transitions.
    pub open spec fn same_identity(self, other: Self) -> bool {
        &&& self.cpu() == other.cpu()
        &&& self.task() == other.task()
        &&& self.view_registry() == other.view_registry()
        &&& self.binding() == other.binding()
        &&& self.participant().id() == other.participant().id()
    }

    /// Attaches a canonical CPU aggregate to an already scheduled task.
    pub proof fn tracked_attach(
        tracked task: RunningTaskContext,
        tracked core: CpuCoreOwner<CpuRcuParticipant>,
        tracked binding: CpuRcuCoreBinding,
    ) -> (tracked res: Self)
        requires
            core.wf(),
            core.cpu() == task.cpu(),
            core.current_task() == Some(task.task()),
            core.locals().wf(),
            core.locals().fraction() == 1real,
            core.locals().cpu() == task.cpu(),
            core.locals_key() == seq![core.locals().id()],
            binding.cpu() == core.cpu(),
            binding.owner_id() == core.id(),
            binding.locals_key() == core.locals_key(),
            task@.contains(core.locals().view()),
        ensures
            res.inv(),
            res.cpu() == task.cpu(),
            res.task() == task.task(),
            res.view_registry() == task.registry_id(),
            res@ == task@,
            res.binding() == binding,
            res.participant() == core.locals(),
    {
        let tracked (core, participant) = core.tracked_open();
        Self { task, core, participant, binding }
    }

    /// Borrows the actual view. Callers must preserve monotonicity to restore inv.
    pub proof fn tracked_view_mut(tracked &mut self) -> (tracked res: &mut ViewSeen)
        requires
            old(self).inv(),
        ensures
            old(self)@.contains(old(self).participant().view()),
            res@ == old(self)@,
            final(self)@ == final(res)@,
            final(self).same_identity(*old(self)),
            final(self).participant() == old(self).participant(),
            final(self).inv() == final(res)@.contains(old(self).participant().view()),
    {
        self.task.tracked_borrow_irc11_view_mut()
    }

    /// Copies only persistent registration evidence, not the core or reader.
    pub proof fn tracked_binding(tracked &self) -> (tracked res: CpuRcuCoreBinding)
        requires
            self.inv(),
        ensures
            res.registry() == self.scheduler(),
            res.cpu() == self.cpu(),
            res.owner_id() == self.binding().owner_id(),
            res.locals_key() == self.binding().locals_key(),
            res.locals_key() == seq![self.participant().id()],
    {
        self.binding.tracked_duplicate()
    }

    pub proof fn tracked_start_reader(tracked &mut self) -> (tracked res: CpuRcuReaderFragment)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).same_identity(*old(self)),
            final(self)@ == old(self)@,
            final(self).participant().view() == old(self).participant().view(),
            final(self).participant().generation() == old(self).participant().generation(),
            final(self).participant().known_retired() == old(self).participant().known_retired(),
            final(self).participant().fraction() == old(self).participant().fraction() / 2real,
            res.wf(),
            res.participant_id() == old(self).participant().id(),
            res.cpu() == old(self).cpu(),
            res.participant_view() == old(self).participant().view(),
            res.generation() == old(self).participant().generation(),
            res.known_retired() == old(self).participant().known_retired(),
            res.fraction() == old(self).participant().fraction() / 2real,
            old(self)@.contains(res.participant_view()),
    {
        self.participant.tracked_start_reader_in_place(self.task@)
    }

    pub proof fn tracked_stop_reader(tracked &mut self, tracked reader: CpuRcuReaderFragment)
        requires
            old(self).inv(),
            reader.wf(),
            reader.participant_id() == old(self).participant().id(),
        ensures
            final(self).inv(),
            final(self).same_identity(*old(self)),
            final(self)@ == old(self)@,
            final(self).participant().view() == old(self).participant().view(),
            final(self).participant().generation() == old(self).participant().generation(),
            final(self).participant().known_retired() == old(self).participant().known_retired(),
            final(self).participant().fraction() == old(self).participant().fraction()
                + reader.fraction(),
    {
        self.participant.tracked_stop_reader_in_place(reader);
    }

    /// Reports the native view only after every reader on this CPU has closed.
    pub proof fn tracked_report(
        tracked &mut self,
        tracked learned: &RcuRetiredFacts,
    ) -> (tracked res: CpuRcuClosedGeneration)
        requires
            old(self).inv(),
            old(self).participant().fraction() == 1real,
            learned.observed_by(old(self)@),
        ensures
            final(self).inv(),
            final(self).same_identity(*old(self)),
            final(self)@ == old(self)@,
            final(self).participant().fraction() == 1real,
            final(self).participant().view() == old(self)@,
            final(self).participant().generation() == old(self).participant().generation() + 1,
            res.wf(),
            res.scheduler() == old(self).scheduler(),
            res.cpu() == old(self).cpu(),
            res.view() == old(self)@,
            learned.records().subset_of(res.known_retired()),
    {
        let tracked binding = self.binding.tracked_duplicate();
        self.participant.tracked_report_quiescent_with_in_place(binding, self.task@, learned)
    }

    /// Returns both original scheduler capabilities; outstanding readers forbid this.
    pub proof fn tracked_detach(tracked self) -> (tracked res: (
        RunningTaskContext,
        CpuCoreOwner<CpuRcuParticipant>,
    ))
        requires
            self.inv(),
            self.participant().fraction() == 1real,
        ensures
            res.0@ == self@,
            res.0.cpu() == self.cpu(),
            res.0.task() == self.task(),
            res.0.registry_id() == self.view_registry(),
            res.1.wf(),
            res.1.cpu() == self.cpu(),
            res.1.current_task() == Some(self.task()),
            res.1.locals() == self.participant(),
            res.1.locals().wf(),
            res.1.locals().fraction() == 1real,
            res.1.locals().cpu() == self.cpu(),
            res.1.locals_key() == seq![res.1.locals().id()],
            res.0@.contains(res.1.locals().view()),
            res.1.id() == self.binding().owner_id(),
            res.1.locals_key() == self.binding().locals_key(),
    {
        self.participant.lemma_cpu_core_local_state();
        let tracked core = self.core.tracked_restore(self.participant);
        (self.task, core)
    }
}

} // verus!
