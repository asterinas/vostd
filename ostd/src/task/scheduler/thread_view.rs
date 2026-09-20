// SPDX-License-Identifier: MPL-2.0
//! OSTD scheduler bridge for native IRC11 task views.
//!
//! This module gives the generic `vstd_extra` view registry an OSTD-specific
//! task identity and CPU identity. Schedule-in moves the checked-out view into
//! a [`RunningTaskContext`]; schedule-out consumes that context and stores the
//! updated view back in the registry.
use vstd::{prelude::*, resource::Loc};
use vstd_extra::{atomic_irc11::ThreadView, scheduler_thread_view::SchedulerThreadViewRegistry};

use crate::{specs::mm::cpu::CpuId, task::RunningTaskContext};

verus! {

/// Scheduler-owned authoritative state for OSTD task and CPU IRC11 views.
pub tracked struct SchedulerIrc11State {
    registry: SchedulerThreadViewRegistry<Loc, CpuId>,
}

impl SchedulerIrc11State {
    /// Creates an empty scheduler view registry.
    pub proof fn new() -> (tracked res: Self)
        ensures
            res.wf(),
            res.stored_task_views() == Map::<Loc, ThreadView>::empty(),
            res.cpu_thread_views() == Map::<CpuId, ThreadView>::empty(),
    {
        let tracked registry = SchedulerThreadViewRegistry::new();
        SchedulerIrc11State { registry }
    }

    /// Stable identity shared by all contexts checked out from this state.
    pub closed spec fn id(&self) -> Loc {
        self.registry.id()
    }

    /// Native views currently parked in scheduler-owned task entries.
    pub closed spec fn stored_task_views(&self) -> Map<Loc, ThreadView> {
        self.registry.stored_task_views()
    }

    /// Persistent native view for every registered CPU.
    pub closed spec fn cpu_thread_views(&self) -> Map<CpuId, ThreadView> {
        self.registry.cpu_thread_views()
    }

    /// Whether the task has an entry in this scheduler registry.
    pub closed spec fn task_is_registered(&self, task: Loc) -> bool {
        self.registry.task_is_registered(task)
    }

    /// Whether the task is registered and not currently checked out.
    pub closed spec fn task_is_stored(&self, task: Loc) -> bool {
        self.registry.task_is_stored(task)
    }

    /// Whether the CPU owns its persistent scheduler view.
    pub closed spec fn cpu_is_registered(&self, cpu: CpuId) -> bool {
        self.registry.cpu_is_registered(cpu)
    }

    /// Whether this exact task/CPU pair is currently checked out.
    pub closed spec fn task_runs_on(&self, task: Loc, cpu: CpuId) -> bool {
        self.registry.task_runs_on(task, cpu)
    }

    /// Whether a task is currently checked out on this CPU.
    pub closed spec fn cpu_is_running(&self, cpu: CpuId) -> bool {
        self.registry.cpu_is_running(cpu)
    }

    /// Stored view of a task that is not currently running.
    pub closed spec fn task_view(&self, task: Loc) -> ThreadView
        recommends
            self.task_is_stored(task),
    {
        self.registry.task_view(task)
    }

    /// Persistent view associated with a registered CPU.
    pub closed spec fn cpu_view(&self, cpu: CpuId) -> ThreadView
        recommends
            self.cpu_is_registered(cpu),
    {
        self.registry.cpu_view(cpu)
    }

    /// Internal consistency and one-task/one-CPU checkout ownership.
    pub closed spec fn wf(&self) -> bool {
        self.registry.wf()
    }

    /// Registers a task with an initially empty subjective view.
    pub proof fn tracked_register_task(tracked &mut self, task: Loc)
        requires
            old(self).wf(),
            !old(self).task_is_registered(task),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).task_is_stored(task),
            final(self).task_view(task) == ThreadView::empty(),
            final(self).cpu_thread_views() == old(self).cpu_thread_views(),
    {
        self.registry.tracked_register_task(task);
    }

    /// Registers an idle CPU with an initially empty persistent view.
    pub proof fn tracked_register_cpu(tracked &mut self, cpu: CpuId)
        requires
            old(self).wf(),
            !old(self).cpu_is_registered(cpu),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).stored_task_views() == old(self).stored_task_views(),
            final(self).cpu_is_registered(cpu),
            !final(self).cpu_is_running(cpu),
            final(self).cpu_view(cpu) == ThreadView::empty(),
    {
        self.registry.tracked_register_cpu(cpu);
    }

    /// Checks a task view out for one running interval on `cpu`.
    pub proof fn tracked_schedule_in(tracked &mut self, task: Loc, cpu: CpuId) -> (tracked context:
        RunningTaskContext)
        requires
            old(self).wf(),
            old(self).task_is_stored(task),
            old(self).cpu_is_registered(cpu),
            !old(self).cpu_is_running(cpu),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            context.registry_id() == old(self).id(),
            context.task() == task,
            context.cpu() == cpu,
            context@ == old(self).task_view(task).join(old(self).cpu_view(cpu)),
            final(self).task_runs_on(task, cpu),
    {
        let tracked scheduled_view = self.registry.tracked_schedule_in(task, cpu);
        RunningTaskContext::tracked_from_scheduled_view(scheduled_view)
    }

    /// Stores a running task's updated view and releases its CPU assignment.
    pub proof fn tracked_schedule_out(tracked &mut self, tracked context: RunningTaskContext)
        requires
            old(self).wf(),
            context.registry_id() == old(self).id(),
            old(self).task_runs_on(context.task(), context.cpu()),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).task_is_stored(context.task()),
            !final(self).cpu_is_running(context.cpu()),
            final(self).task_view(context.task()) == context@,
            final(self).cpu_view(context.cpu()) == old(self).cpu_view(context.cpu()).join(context@),
    {
        let tracked scheduled_view = context.tracked_into_scheduled_view();
        self.registry.tracked_schedule_out(scheduled_view);
    }
}

} // verus!
