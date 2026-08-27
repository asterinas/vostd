//! Scheduler ownership for native IRC11 thread views.
//!
//! A registered task's view is normally stored in
//! [`SchedulerThreadViewRegistry`]. Scheduling the task removes that view and
//! returns a linear [`ScheduledTaskView`]. Weak-memory operations update this
//! checked-out value. Scheduling out consumes it, restores the task entry, and
//! joins the task's observations into the CPU's persistent view.
//!
//! The two running maps are deliberately redundant. Their inverse invariant
//! makes the scheduling contract explicit: one task runs on at most one CPU,
//! and one CPU runs at most one task.
use vstd::{prelude::*, resource::Loc};

use crate::{
    atomic_irc11::{ThreadView, ThreadViewToken},
    resource::ghost_resource::excl::ExclusiveGhost,
};

verus! {

/// The native weak-memory view checked out for one currently scheduled task.
///
/// Its private registry, task, and CPU identities ensure that the token can be
/// returned only through the matching scheduler entry.
pub tracked struct ScheduledTaskView<TaskId, CpuId> {
    ghost registry_id: Loc,
    ghost task: TaskId,
    ghost cpu: CpuId,
    thread_view: ThreadViewToken,
}

/// Scheduler-owned authoritative state for task and CPU thread views.
///
/// `task_views` contains exactly the task views that are currently parked in
/// the scheduler. A running task is absent from that map; its token resides in
/// a [`ScheduledTaskView`] until [`Self::tracked_schedule_out`] consumes it.
pub tracked struct SchedulerThreadViewRegistry<TaskId, CpuId> {
    identity: ExclusiveGhost<()>,
    task_views: Map<TaskId, ThreadViewToken>,
    cpu_views: Map<CpuId, ThreadViewToken>,
    ghost running_by_task: Map<TaskId, CpuId>,
    ghost running_by_cpu: Map<CpuId, TaskId>,
}

impl<TaskId, CpuId> View for ScheduledTaskView<TaskId, CpuId> {
    type V = ThreadView;

    closed spec fn view(&self) -> ThreadView {
        self.thread_view@
    }
}

impl<TaskId, CpuId> ScheduledTaskView<TaskId, CpuId> {
    /// Identity of the scheduler registry that checked out this view.
    pub closed spec fn registry_id(&self) -> Loc {
        self.registry_id
    }

    /// Task whose native view this token carries.
    pub closed spec fn task(&self) -> TaskId {
        self.task
    }

    /// CPU on which the task was scheduled.
    pub closed spec fn cpu(&self) -> CpuId {
        self.cpu
    }

    /// Borrows the task-owned token for one or more native weak-memory calls.
    pub proof fn tracked_borrow_thread_view_mut(tracked &mut self) -> (tracked view:
        &mut ThreadViewToken)
        ensures
            (*view)@ == old(self)@,
            final(self).registry_id() == old(self).registry_id(),
            final(self).task() == old(self).task(),
            final(self).cpu() == old(self).cpu(),
            final(self)@ == (*final(view))@,
    {
        &mut self.thread_view
    }
}

impl<TaskId, CpuId> SchedulerThreadViewRegistry<TaskId, CpuId> {
    /// Allocates an empty scheduler registry with a fresh logical identity.
    pub proof fn new() -> (tracked res: Self)
        ensures
            res.wf(),
            res.stored_task_views() == Map::<TaskId, ThreadView>::empty(),
            res.cpu_thread_views() == Map::<CpuId, ThreadView>::empty(),
            res.running_tasks() == Map::<TaskId, CpuId>::empty(),
            res.running_cpus() == Map::<CpuId, TaskId>::empty(),
    {
        let tracked identity = ExclusiveGhost::alloc(());
        let tracked task_views = Map::tracked_empty();
        let tracked cpu_views = Map::tracked_empty();
        let ghost running_by_task = Map::empty();
        let ghost running_by_cpu = Map::empty();
        SchedulerThreadViewRegistry {
            identity,
            task_views,
            cpu_views,
            running_by_task,
            running_by_cpu,
        }
    }

    /// Stable identity used to reject a token from another scheduler.
    pub closed spec fn id(&self) -> Loc {
        self.identity.id()
    }

    /// Views currently parked in scheduler-owned task entries.
    pub closed spec fn stored_task_views(&self) -> Map<TaskId, ThreadView> {
        Map::new(self.task_views.dom(), |task: TaskId| self.task_views[task]@)
    }

    /// Persistent per-CPU views used to carry observations across tasks.
    pub closed spec fn cpu_thread_views(&self) -> Map<CpuId, ThreadView> {
        Map::new(self.cpu_views.dom(), |cpu: CpuId| self.cpu_views[cpu]@)
    }

    /// Current task-to-CPU assignments.
    pub closed spec fn running_tasks(&self) -> Map<TaskId, CpuId> {
        self.running_by_task
    }

    /// Current CPU-to-task assignments.
    pub closed spec fn running_cpus(&self) -> Map<CpuId, TaskId> {
        self.running_by_cpu
    }

    /// Whether `task` is known either as stored or currently running.
    pub open spec fn task_is_registered(&self, task: TaskId) -> bool {
        self.stored_task_views().contains_key(task) || self.running_tasks().contains_key(task)
    }

    /// Whether `task` currently has its view parked in the scheduler.
    pub open spec fn task_is_stored(&self, task: TaskId) -> bool {
        self.stored_task_views().contains_key(task)
    }

    /// Whether `cpu` has a persistent scheduler-owned view.
    pub open spec fn cpu_is_registered(&self, cpu: CpuId) -> bool {
        self.cpu_thread_views().contains_key(cpu)
    }

    /// Whether `cpu` currently runs a task.
    pub open spec fn cpu_is_running(&self, cpu: CpuId) -> bool {
        self.running_cpus().contains_key(cpu)
    }

    /// Whether the scheduler records exactly this task/CPU assignment.
    pub open spec fn task_runs_on(&self, task: TaskId, cpu: CpuId) -> bool {
        &&& self.running_tasks().contains_key(task)
        &&& self.running_tasks()[task] == cpu
        &&& self.running_cpus().contains_key(cpu)
        &&& self.running_cpus()[cpu] == task
    }

    /// Stored native view for a non-running registered task.
    pub closed spec fn task_view(&self, task: TaskId) -> ThreadView
        recommends
            self.task_is_stored(task),
    {
        self.stored_task_views()[task]
    }

    /// Persistent native view for a registered CPU.
    pub closed spec fn cpu_view(&self, cpu: CpuId) -> ThreadView
        recommends
            self.cpu_is_registered(cpu),
    {
        self.cpu_thread_views()[cpu]
    }

    /// Internal consistency and the one-task/one-CPU scheduling invariant.
    pub closed spec fn wf(&self) -> bool {
        &&& self.identity.wf()
        &&& forall|task: TaskId| #[trigger]
            self.running_by_task.contains_key(task) ==> {
                let cpu = self.running_by_task[task];
                &&& !self.task_views.contains_key(task)
                &&& self.cpu_views.contains_key(cpu)
                &&& self.running_by_cpu.contains_key(cpu)
                &&& self.running_by_cpu[cpu] == task
            }
        &&& forall|cpu: CpuId| #[trigger]
            self.running_by_cpu.contains_key(cpu) ==> {
                let task = self.running_by_cpu[cpu];
                &&& self.cpu_views.contains_key(cpu)
                &&& self.running_by_task.contains_key(task)
                &&& self.running_by_task[task] == cpu
            }
    }

    /// Registers a task with the empty native view used at thread creation.
    pub proof fn tracked_register_task(tracked &mut self, task: TaskId)
        requires
            old(self).wf(),
            !old(self).task_is_registered(task),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).stored_task_views() == old(self).stored_task_views().insert(
                task,
                ThreadView::empty(),
            ),
            final(self).cpu_thread_views() == old(self).cpu_thread_views(),
            final(self).running_tasks() == old(self).running_tasks(),
            final(self).running_cpus() == old(self).running_cpus(),
            final(self).task_is_stored(task),
            final(self).task_view(task) == ThreadView::empty(),
    {
        let tracked thread_view = ThreadViewToken::new();
        self.task_views.tracked_insert(task, thread_view);
    }

    /// Registers an idle CPU with an empty persistent native view.
    pub proof fn tracked_register_cpu(tracked &mut self, cpu: CpuId)
        requires
            old(self).wf(),
            !old(self).cpu_is_registered(cpu),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).stored_task_views() == old(self).stored_task_views(),
            final(self).cpu_thread_views() == old(self).cpu_thread_views().insert(
                cpu,
                ThreadView::empty(),
            ),
            final(self).running_tasks() == old(self).running_tasks(),
            final(self).running_cpus() == old(self).running_cpus(),
            final(self).cpu_is_registered(cpu),
            !final(self).cpu_is_running(cpu),
            final(self).cpu_view(cpu) == ThreadView::empty(),
    {
        let tracked thread_view = ThreadViewToken::new();
        self.cpu_views.tracked_insert(cpu, thread_view);
    }

    /// Checks a task view out of the scheduler at schedule-in.
    ///
    /// The returned task view imports the CPU's persistent observations. The
    /// bidirectional running entries reserve both identities until the token is
    /// returned by [`Self::tracked_schedule_out`].
    pub proof fn tracked_schedule_in(
        tracked &mut self,
        task: TaskId,
        cpu: CpuId,
    ) -> (tracked res: ScheduledTaskView<TaskId, CpuId>)
        requires
            old(self).wf(),
            old(self).task_is_stored(task),
            old(self).cpu_is_registered(cpu),
            !old(self).cpu_is_running(cpu),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            res.registry_id() == old(self).id(),
            res.task() == task,
            res.cpu() == cpu,
            res@ == old(self).task_view(task).join(old(self).cpu_view(cpu)),
            final(self).stored_task_views() == old(self).stored_task_views().remove(task),
            final(self).cpu_thread_views() == old(self).cpu_thread_views(),
            final(self).running_tasks() == old(self).running_tasks().insert(task, cpu),
            final(self).running_cpus() == old(self).running_cpus().insert(cpu, task),
            final(self).task_runs_on(task, cpu),
    {
        let tracked mut thread_view = self.task_views.tracked_remove(task);
        let tracked cpu_view = self.cpu_views.tracked_borrow(cpu);
        thread_view.tracked_join(cpu_view);
        self.running_by_task = self.running_by_task.insert(task, cpu);
        self.running_by_cpu = self.running_by_cpu.insert(cpu, task);
        ScheduledTaskView {
            registry_id: self.id(),
            task,
            cpu,
            thread_view,
        }
    }

    /// Returns a running task view at schedule-out.
    ///
    /// The task keeps its updated view for a later schedule-in. The CPU also
    /// imports that view so the next task scheduled on the same CPU inherits
    /// every observation made before this schedule-out boundary.
    pub proof fn tracked_schedule_out(
        tracked &mut self,
        tracked running: ScheduledTaskView<TaskId, CpuId>,
    )
        requires
            old(self).wf(),
            running.registry_id() == old(self).id(),
            old(self).task_runs_on(running.task(), running.cpu()),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).stored_task_views() == old(self).stored_task_views().insert(
                running.task(),
                running@,
            ),
            final(self).cpu_thread_views() == old(self).cpu_thread_views().insert(
                running.cpu(),
                old(self).cpu_view(running.cpu()).join(running@),
            ),
            final(self).running_tasks() == old(self).running_tasks().remove(running.task()),
            final(self).running_cpus() == old(self).running_cpus().remove(running.cpu()),
            final(self).task_is_stored(running.task()),
            !final(self).cpu_is_running(running.cpu()),
            final(self).task_view(running.task()) == running@,
            final(self).cpu_view(running.cpu()) == old(self).cpu_view(running.cpu()).join(running@),
    {
        let tracked ScheduledTaskView {
            registry_id: _,
            task,
            cpu,
            thread_view,
        } = running;
        let tracked cpu_view = self.cpu_views.tracked_borrow_mut(cpu);
        cpu_view.tracked_join(&thread_view);
        self.task_views.tracked_insert(task, thread_view);
        self.running_by_task = self.running_by_task.remove(task);
        self.running_by_cpu = self.running_by_cpu.remove(cpu);
    }
}

fn test_schedule_in_out_round_trip() {
    proof {
        let tracked mut registry = SchedulerThreadViewRegistry::<nat, nat>::new();
        registry.tracked_register_cpu(0);
        registry.tracked_register_task(1);

        let ghost task_before = registry.task_view(1);
        let ghost cpu_before = registry.cpu_view(0);
        let tracked running = registry.tracked_schedule_in(1, 0);
        assert(running@ == task_before.join(cpu_before));
        assert(registry.task_runs_on(1, 0));

        registry.tracked_schedule_out(running);
        assert(registry.task_is_stored(1));
        assert(!registry.cpu_is_running(0));
        assert(registry.wf());
    }
}

} // verus!
