// SPDX-License-Identifier: MPL-2.0
//! Task scheduling.
//!
//! # Scheduler Injection
//!
//! The task scheduler of an OS is a complex beast,
//! and the most suitable scheduling algorithm often depends on the target usage scenario.
//! To avoid code bloat and offer flexibility,
//! OSTD does not include a gigantic, one-size-fits-all task scheduler.
//! Instead, it allows the client to implement a custom scheduler (in safe Rust, of course)
//! and register it with OSTD.
//! This feature is known as **scheduler injection**.
//!
//! The client kernel performs scheduler injection via the [`inject_scheduler`] API.
//! This API should be called as early as possible during kernel initialization,
//! before any [`Task`]-related APIs are used.
//! This requirement is reasonable since `Task`s depend on the scheduler.
//!
//! # Scheduler Abstraction
//!
//! The `inject_scheduler` API accepts an object implementing the [`Scheduler`] trait,
//! which abstracts over any SMP-aware task scheduler.
//! Whenever an OSTD client spawns a new task (via [`crate::task::TaskOptions`])
//! or wakes a sleeping task (e.g., via [`crate::sync::Waker`]),
//! OSTD internally forwards the corresponding `Arc<Task>`
//! to the scheduler by invoking the [`Scheduler::enqueue`] method.
//! This allows the injected scheduler to manage all runnable tasks.
//!
//! Each enqueued task is dispatched to one of the per-CPU local runqueues,
//! which manage all runnable tasks on a specific CPU.
//! A local runqueue is abstracted by the [`LocalRunQueue`] trait.
//! OSTD accesses the local runqueue of the current CPU
//! via [`Scheduler::local_rq_with`] or [`Scheduler::mut_local_rq_with`],
//! which return immutable and mutable references to `dyn LocalRunQueue`, respectively.
//!
//! The [`LocalRunQueue`] trait enables OSTD to inspect and manipulate local runqueues.
//! For instance, OSTD invokes the [`LocalRunQueue::pick_next`] method
//! to let the scheduler select the next task to run.
//! OSTD then performs a context switch to that task,
//! which becomes the _current_ running task, accessible via [`LocalRunQueue::current`].
//! When the current task is about to sleep (e.g., via [`crate::sync::Waiter`]),
//! OSTD removes it from the local runqueue using [`LocalRunQueue::dequeue_current`].
//!
//! The interfaces of `Scheduler` and `LocalRunQueue` are simple
//! yet (perhaps surprisingly) powerful enough to support
//! even complex and advanced task scheduler implementations.
//! Scheduler implementations are free to employ any load-balancing strategy
//! to dispatch enqueued tasks across local runqueues,
//! and each local runqueue is free to choose any prioritization strategy
//! for selecting the next task to run.
//! Based on OSTD's scheduling abstractions,
//! the Asterinas kernel has successfully supported multiple Linux scheduling classes,
//! including both real-time and normal policies.
//!
//! # Safety Impact
//!
//! While OSTD delegates scheduling decisions to the injected task scheduler,
//! it verifies these decisions to avoid undefined behavior.
//! In particular, it enforces the following safety invariant:
//!
//! > A task must not be scheduled to run on more than one CPU at a time.
//!
//! Violating this invariant—e.g., running the same task on two CPUs concurrently—
//! can have catastrophic consequences,
//! as the task's stack and internal state may be corrupted by concurrent modifications.

use vstd::{map::Map, prelude::*, resource::Loc};

use super::Task;
use crate::{
    specs::mm::cpu::CpuId,
    specs::sync::weak_memory::{ThreadView, WmView},
    sync::{OnceImpl, RoArc, TrivialPred},
};

verus! {

/// A task-like object that can be identified in scheduler ghost state.
pub trait Schedulable {
    spec fn sched_id(&self) -> Loc;
}

impl Schedulable for Task {
    open spec fn sched_id(&self) -> Loc {
        self.id()
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub ghost enum TaskSchedState {
    New,
    Runnable,
    Blocked,
    Running,
    Exited,
}

/// Abstract proof view of the scheduler state.
///
/// `runqueues` contains runnable-but-not-current tasks, `current` contains
/// the task currently running on each CPU, and `state` records the scheduler
/// state for every known task. `task_views` is the logical per-task
/// weak-memory view. `stored_views` records views still owned by the scheduler
/// resource; `checked_out_views` records views temporarily held by guards.
pub ghost struct SchedulerView {
    pub runqueues: Map<CpuId, Seq<Loc>>,
    pub current: Map<CpuId, Option<Loc>>,
    pub state: Map<Loc, TaskSchedState>,
    pub task_views: Map<Loc, WmView>,
    pub stored_views: Map<Loc, WmView>,
    pub checked_out_views: Map<Loc, WmView>,
}

impl SchedulerView {
    pub open spec fn task_is_known(self, task: Loc) -> bool {
        self.state.contains_key(task)
    }

    pub open spec fn task_has_thread_view(self, task: Loc) -> bool {
        self.task_views.contains_key(task)
    }

    pub open spec fn task_thread_view(self, task: Loc) -> WmView
        recommends
            self.task_has_thread_view(task),
    {
        self.task_views[task]
    }

    pub open spec fn task_view_is_stored(self, task: Loc) -> bool {
        self.stored_views.contains_key(task)
    }

    pub open spec fn task_view_is_checked_out(self, task: Loc) -> bool {
        self.checked_out_views.contains_key(task)
    }

    pub open spec fn task_in_runqueue(self, task: Loc) -> bool {
        exists|cpu: CpuId, idx: int|
            self.runqueues.contains_key(cpu)
                && 0 <= idx
                && idx < self.runqueues[cpu].len()
                && (#[trigger] self.runqueues[cpu][idx]) == task
    }

    pub open spec fn task_is_current(self, task: Loc) -> bool {
        exists|cpu: CpuId|
            #[trigger] self.current.contains_key(cpu)
                && self.current[cpu] is Some
                && self.current[cpu]->0 == task
    }

    pub open spec fn task_is_runnable(self, task: Loc) -> bool {
        &&& self.state.contains_key(task)
        &&& (self.state[task] is Runnable || self.state[task] is Running)
    }

    pub open spec fn task_is_live(self, task: Loc) -> bool {
        &&& self.state.contains_key(task)
        &&& !(self.state[task] is Exited)
    }

    /// Prevent that two tasks happen to be the same task, which would be a violation of the
    /// scheduler's safety invariant.
    pub open spec fn no_duplicate_task(self, task: Loc) -> bool {
        &&& forall|cpu1: CpuId, cpu2: CpuId, idx1: int, idx2: int|
            #![trigger self.runqueues[cpu1][idx1], self.runqueues[cpu2][idx2]]
            self.runqueues.contains_key(cpu1)
                && self.runqueues.contains_key(cpu2)
                && 0 <= idx1
                && idx1 < self.runqueues[cpu1].len()
                && 0 <= idx2
                && idx2 < self.runqueues[cpu2].len()
                && self.runqueues[cpu1][idx1] == task
                && self.runqueues[cpu2][idx2] == task
                ==> cpu1 == cpu2 && idx1 == idx2
        &&& forall|cpu1: CpuId, cpu2: CpuId|
            #![trigger self.current.contains_key(cpu1), self.current.contains_key(cpu2)]
            self.current.contains_key(cpu1)
                && self.current.contains_key(cpu2)
                && self.current[cpu1] is Some
                && self.current[cpu2] is Some
                && self.current[cpu1]->0 == task
                && self.current[cpu2]->0 == task
                ==> cpu1 == cpu2
        &&& !(self.task_in_runqueue(task) && self.task_is_current(task))
    }

    pub open spec fn checkout_task_view(self, cpu: CpuId) -> SchedulerView
        recommends
            self.current.contains_key(cpu),
            self.current[cpu] is Some,
            self.task_view_is_stored(self.current[cpu]->0),
            !self.task_view_is_checked_out(self.current[cpu]->0),
    {
        let task = self.current[cpu]->0;
        SchedulerView {
            stored_views: self.stored_views.remove(task),
            checked_out_views: self.checked_out_views.insert(task, self.stored_views[task]),
            ..self
        }
    }

    pub open spec fn update_checked_out_task_view(self, task: Loc, view: WmView) -> SchedulerView
        recommends
            self.task_view_is_checked_out(task),
    {
        SchedulerView {
            task_views: self.task_views.insert(task, view),
            checked_out_views: self.checked_out_views.insert(task, view),
            ..self
        }
    }

    pub open spec fn checkin_task_view(self, task: Loc, view: WmView) -> SchedulerView
        recommends
            self.task_view_is_checked_out(task),
            !self.task_view_is_stored(task),
            self.checked_out_views[task] == view,
    {
        SchedulerView {
            task_views: self.task_views.insert(task, view),
            stored_views: self.stored_views.insert(task, view),
            checked_out_views: self.checked_out_views.remove(task),
            ..self
        }
    }

    pub open spec fn wf(self) -> bool {
        &&& forall|cpu: CpuId|
            #[trigger] self.runqueues.contains_key(cpu) ==> valid_cpu(cpu)
        &&& forall|cpu: CpuId|
            #[trigger] self.current.contains_key(cpu) ==> valid_cpu(cpu)
        &&& forall|cpu: CpuId, idx: int|
            #![trigger self.runqueues[cpu][idx]]
            self.runqueues.contains_key(cpu)
                && 0 <= idx
                && idx < self.runqueues[cpu].len()
                ==> self.state.contains_key(self.runqueues[cpu][idx])
                    && self.state[self.runqueues[cpu][idx]] is Runnable
        &&& forall|cpu: CpuId|
            #[trigger] self.current.contains_key(cpu)
                && self.current[cpu] is Some
                ==> self.state.contains_key(self.current[cpu]->0)
                    && self.state[self.current[cpu]->0] is Running
        &&& forall|task: Loc|
            #[trigger] self.state.contains_key(task) ==> self.no_duplicate_task(task)
        &&& forall|task: Loc|
            #[trigger] self.state.contains_key(task)
                && !(self.state[task] is Exited)
                ==> self.task_views.contains_key(task)
        &&& forall|task: Loc|
            #[trigger] self.task_views.contains_key(task) ==> self.state.contains_key(task)
                && !(self.state[task] is Exited)
        &&& forall|task: Loc|
            #[trigger] self.stored_views.contains_key(task) ==> self.task_views.contains_key(task)
                && self.stored_views[task] == self.task_views[task]
                && !self.checked_out_views.contains_key(task)
                && self.task_is_live(task)
        &&& forall|task: Loc|
            #[trigger] self.checked_out_views.contains_key(task) ==> self.task_views.contains_key(
                task,
            )
                && self.checked_out_views[task] == self.task_views[task]
                && !self.stored_views.contains_key(task)
                && self.task_is_live(task)
                && self.task_is_current(task)
        &&& forall|task: Loc|
            #[trigger] self.task_views.contains_key(task) ==> (self.stored_views.contains_key(task)
                || self.checked_out_views.contains_key(task))
    }
}

/// Tracked owner of per-task weak-memory views.
///
/// This is the resource that should eventually back `disable_preempt()`:
/// a guard borrows or moves out the current task's `ThreadView`, atomic
/// operations update it, and guard drop writes it back to the same task entry.
pub tracked struct SchedulerThreadViews {
    tracked views: Map<Loc, ThreadView>,
}

/// A checked-out per-task `ThreadView`.
///
/// The `task` field records where the linear `ThreadView` must be written
/// back. This prevents proofs from taking one task's view and re-inserting it
/// under another task id.
pub tracked struct TaskThreadView {
    ghost task: Loc,
    tracked thread_view: ThreadView,
}

impl TaskThreadView {
    pub proof fn new(task: Loc, tracked thread_view: ThreadView) -> (tracked res: Self)
        ensures
            res.task() == task,
            res.view() == thread_view@,
    {
        TaskThreadView { task, thread_view }
    }

    pub closed spec fn task(self) -> Loc {
        self.task
    }

    pub closed spec fn view(self) -> WmView {
        self.thread_view@
    }

    pub closed spec fn wf(self, sched_view: SchedulerView) -> bool {
        &&& sched_view.wf()
        &&& sched_view.checked_out_views.contains_key(self.task())
        &&& sched_view.checked_out_views[self.task()] == self.view()
        &&& sched_view.task_views.contains_key(self.task())
        &&& sched_view.task_views[self.task()] == self.view()
    }

    pub proof fn borrow_thread_view_mut(tracked &mut self) -> (tracked tv: &mut ThreadView)
        ensures
            (*tv)@ == old(self).view(),
            final(self).task() == old(self).task(),
            final(self).view() == (*final(tv))@,
    {
        &mut self.thread_view
    }
}

impl SchedulerThreadViews {
    pub proof fn empty() -> (tracked res: Self)
        ensures
            res.view() == Map::<Loc, WmView>::empty(),
    {
        let tracked views = Map::<Loc, ThreadView>::tracked_empty();
        SchedulerThreadViews { views }
    }

    pub closed spec fn view(self) -> Map<Loc, WmView> {
        Map::new(
            self.views.dom(),
            |task: Loc| self.views[task]@,
        )
    }

    pub closed spec fn contains(self, task: Loc) -> bool {
        self.views.contains_key(task)
    }

    pub closed spec fn thread_view(self, task: Loc) -> WmView
        recommends
            self.contains(task),
    {
        self.views[task]@
    }

    pub closed spec fn wf(self, sched_view: SchedulerView) -> bool {
        self.view() == sched_view.stored_views
    }

    pub proof fn insert_initial_thread_view(tracked &mut self, tracked token: TaskThreadView)
        requires
            !old(self).contains(token.task()),
        ensures
            final(self).view() == old(self).view().insert(token.task(), token.view()),
    {
        let tracked TaskThreadView { task, thread_view } = token;
        self.views.tracked_insert(task, thread_view);
    }

    pub proof fn take_current_thread_view(
        tracked &mut self,
        sched_view: SchedulerView,
        cpu: CpuId,
    ) -> (tracked token: TaskThreadView)
        requires
            old(self).wf(sched_view),
            sched_view.wf(),
            sched_view.current.contains_key(cpu),
            sched_view.current[cpu] is Some,
            sched_view.task_view_is_stored(sched_view.current[cpu]->0),
            old(self).contains(sched_view.current[cpu]->0),
        ensures
            token.task() == sched_view.current[cpu]->0,
            token.view() == old(self).thread_view(sched_view.current[cpu]->0),
            final(self).view() == old(self).view().remove(sched_view.current[cpu]->0),
    {
        let task = sched_view.current[cpu]->0;
        let tracked thread_view = self.views.tracked_remove(task);
        TaskThreadView { task, thread_view }
    }

    pub proof fn put_checked_out_thread_view(
        tracked &mut self,
        sched_view: SchedulerView,
        tracked token: TaskThreadView,
    )
        requires
            token.wf(sched_view),
            !old(self).contains(token.task()),
        ensures
            final(self).view() == old(self).view().insert(token.task(), token.view()),
    {
        let tracked TaskThreadView { task, thread_view } = token;
        self.views.tracked_insert(task, thread_view);
    }
}

/// Logical identity of a runnable task handle.
///
/// `RoArc` does not yet expose a proof-level view of its pointee. Keep this
/// abstract at the scheduler boundary and connect it to `RoArc`'s internals
/// later when the task registry is introduced.
pub uninterp spec fn runnable_id<T: Schedulable>(runnable: &RoArc<T>) -> Loc;

pub open spec fn valid_cpu(_cpu: CpuId) -> bool {
    true
}

pub open spec fn can_enqueue(view: SchedulerView, task: Loc, flags: EnqueueFlags) -> bool {
    match flags {
        EnqueueFlags::Spawn => !view.state.contains_key(task) || view.state[task] is New,
        EnqueueFlags::Wake => view.state.contains_key(task) && !(view.state[task] is Exited),
    }
}

/// An SMP-aware task scheduler.
pub trait Scheduler<T: Schedulable = Task>: Sync + Send {
    spec fn view(&self) -> SchedulerView;

    spec fn wf(&self) -> bool;

    /// Enqueues a runnable task.
    ///
    /// The scheduler implementer can perform load-balancing or some time accounting work here.
    ///
    /// The newly-enqueued task may have a higher priority than the currently running one on a CPU
    /// and thus should preempt the latter.
    /// In this case, this method returns the ID of that CPU.
    fn enqueue(&self, runnable: RoArc<T>, flags: EnqueueFlags) -> (r: Option<CpuId>)
        requires
            self.wf(),
            self.view().wf(),
            can_enqueue(self.view(), runnable_id(&runnable), flags),
        ensures
            self.wf(),
            self.view().wf(),
            self.view().task_is_runnable(runnable_id(&runnable)),
            self.view().no_duplicate_task(runnable_id(&runnable)),
            r matches Some(cpu) ==> valid_cpu(cpu),
    ;
}

exec static SCHEDULER: OnceImpl<&'static dyn Scheduler<Task>, TrivialPred>
    ensures
        SCHEDULER.wf(),
        SCHEDULER.inv() == TrivialPred,
{
    OnceImpl::new(Ghost(TrivialPred))
}

/// Possible actions of a rescheduling.
enum ReschedAction {
    /// Keep running current task and do nothing.
    DoNothing,
    /// Loop until finding a task to swap out the current.
    Retry,
    /// Switch to target task.
    SwitchTo(RoArc<Task>),
}


/// Possible triggers of an `enqueue` action.
#[derive(PartialEq, Copy, Clone)]
pub enum EnqueueFlags {
    /// Spawn a new task.
    Spawn,
    /// Wake a sleeping task.
    Wake,
}

/// Possible triggers of an `update_current` action.
#[derive(PartialEq, Copy, Clone)]
pub enum UpdateFlags {
    /// Timer interrupt.
    Tick,
    /// Task waiting.
    Wait,
    /// Task yielding.
    Yield,
    /// Task exiting.
    Exit,
}

} // verus!

/*
// mod fifo_scheduler;
// pub mod info;
use alloc::sync::Arc;
use spin::Once;

// use super::{preempt::cpu_local, processor, Task};
use super::Task;
// use crate::{
//     cpu::{CpuId, CpuSet, PinCurrentCpu},
//     prelude::*,
//     task::disable_preempt,
//     timer,
// };
use crate::specs::mm::cpu::CpuId;

/// Injects a custom implementation of task scheduler into OSTD.
///
/// This function can only be called once and must be called during the initialization phase of kernel,
/// before any [`Task`]-related APIs are invoked.
pub fn inject_scheduler(scheduler: &'static dyn Scheduler<Task>) {
    /* SCHEDULER.call_once(|| scheduler);

    timer::register_callback(|| {
        SCHEDULER.get().unwrap().mut_local_rq_with(&mut |local_rq| {
            let should_pick_next = local_rq.update_current(UpdateFlags::Tick);
            if should_pick_next {
                cpu_local::set_need_preempt();
            }
        })
    }); */
}


/// A SMP-aware task scheduler.
pub trait Scheduler<T = Task>: Sync + Send {

    /// Gets an immutable access to the local runqueue of the current CPU.
    fn local_rq_with(&self, f: &mut dyn FnMut(&dyn LocalRunQueue<T>));

    /// Gets a mutable access to the local runqueue of the current CPU.
    fn mut_local_rq_with(&self, f: &mut dyn FnMut(&mut dyn LocalRunQueue<T>));
}

/// A per-CPU, local runqueue.
///
/// This abstraction allows OSTD to inspect and manipulate local runqueues.
///
/// Conceptually, a local runqueue maintains:
/// 1. A priority queue of runnable tasks.
///    The definition of "priority" is left to the concrete implementation.
/// 2. The current running task.
///
/// # Interactions with OSTD
///
/// ## Overview
///
/// It is crucial for implementers of `LocalRunQueue`
/// to understand how OSTD interacts with local runqueues.
///
/// A local runqueue is consulted by OSTD in response to one of four scheduling events:
/// - **Yielding**, triggered by [`Task::yield_now`], where the current task voluntarily gives up CPU time.
/// - **Sleeping**, triggered by [`crate::sync::Waiter::wait`]
///   or any synchronization primitive built upon it (e.g., [`crate::sync::WaitQueue`], [`crate::sync::Mutex`]),
///   which blocks the current task until a wake-up event occurs.
/// - **Ticking**, triggered periodically by the system timer
///   (see [`crate::arch::timer::TIMER_FREQ`]),
///   which provides an opportunity to do time accounting and consider preemption.
/// - **Exiting**, triggered when the execution logic of a task has come to an end,
///   which informs the scheduler that the task is exiting and will never be enqueued again.
///
/// The general workflow for OSTD to handle a scheduling event is as follows:
/// 1. Acquire exclusive access to the local runqueue using [`Scheduler::mut_local_rq_with`].
/// 2. Call [`LocalRunQueue::update_current`] to update the current task's state,
///    returning a boolean value that indicates
///    whether the current task should and can be replaced with another runnable task.
/// 3. If the task is about to sleep or exit, call [`LocalRunQueue::dequeue_current`]
///    to remove it from the runqueue.
/// 4. If the return value of `update_current` in Step 2 is true,
///    then select the next task to run with [`LocalRunQueue::pick_next`].
///
/// ## When to Pick the Next Task?
///
/// As shown above,
/// OSTD guarantees that `pick_next` is only called
/// when the current task should and can be replaced.
/// This avoids unnecessary invocations and improves efficiency.
///
/// But under what conditions should the current task be replaced?
/// Two criteria must be met:
/// 1. There exists at least one other runnable task in the runqueue.
/// 2. That task should preempt the current one, if present.
///
/// Some implications of these rules:
/// - If the runqueue is empty, `update_current` must return `false`—there's nothing to run.
/// - If the runqueue is non-empty but the current task is absent,
///   `update_current` should return `true`—anything is better than nothing.
/// - If the runqueue is non-empty and the flag is `UpdateFlags::WAIT`,
///   `update_current` should also return `true`,
///   because the current task is about to block.
/// - In other cases, the return value depends on the scheduler's prioritization policy.
///   For instance, a real-time task may only be preempted by a higher-priority task
///   or if it explicitly yields.
///   A normal task under Linux's CFS may be preempted by a task with smaller vruntime,
///   but never by the idle task.
///
/// When OSTD is unsure about whether the current task should or can be replaced,
/// it will invoke [`LocalRunQueue::try_pick_next`], the fallible version of `pick_next`.
///
/// ## Internal Working
///
/// To guide scheduler implementers,
/// we provide a simplified view of how OSTD interacts with local runqueues _internally_
/// in order to handle the four scheduling events.
///
/// ### Yielding
///
/// ```
/// # use ostd::prelude::*;
/// # use ostd::task::{*, scheduler::*};
/// #
/// # fn switch_to(next: Arc<Task>) {}
/// #
/// /// Yields the current task.
/// fn yield(scheduler: &'static dyn Scheduler) {
///     let next_task_opt: Option<Arc<Task>> = scheduler.mut_local_rq_with(|local_rq| {
///         let should_pick_next = local_rq.update_current(UpdateFlags::Yield);
///         should_pick_next.then(|| local_rq.pick_next().clone())
///     });
///     let Some(next_task) = next_task_opt {
///         switch_to(next_task);
///     }
/// }
/// ```
///
/// ### Sleeping
///
/// ```
/// # use ostd::prelude::*;
/// # use ostd::task::{*, scheduler::*};
/// #
/// # fn switch_to(next: Arc<Task>) {}
/// #
/// /// Puts the current task to sleep.
/// ///
/// /// The function takes a closure to check if the task is woken.
/// /// This function is used internally to guard against race conditions,
/// /// where the task is woken just before it goes to sleep.
/// fn sleep<F: Fn() -> bool>(scheduler: &'static dyn Scheduler, is_woken: F) {
///     let mut next_task_opt: Option<Arc<Task>> = None;
///     let mut is_first_try = true;
///     while scheduler.mut_local_rq_with(|local_rq| {
///         if is_first_try {
///             if is_woken() {
///                 return false; // exit loop
///             }
///             is_first_try = false;
///
///             let should_pick_next = local_rq.update_current(UpdateFlags::Wait);
///             let _current = local_rq.dequeue_current();
///             if !should_pick_next {
///                 return true; // continue loop
///             }
///             next_task_opt = Some(local_rq.pick_next().clone());
///             false // exit loop
///         } else {
///             next_task_opt = local_rq.try_pick_next().cloned();
///             next_task_opt.is_none()
///         }
///     }) {}
///     let Some(next_task) = next_task_opt {
///         switch_to(next_task);
///     }
/// }
/// ```
///
/// ### Ticking
///
/// ```
/// # use ostd::prelude::*;
/// # use ostd::task::{*, scheduler::*};
/// #
/// # fn switch_to(next: Arc<Task>) {}
/// # mod cpu_local {
/// #     fn set_need_preempt();
/// #     fn should_preempt() -> bool;
/// # }
/// #
/// /// A callback to be invoked periodically by the timer interrupt.
/// fn on_tick(scheduler: &'static dyn Scheduler) {
///     scheduler.mut_local_rq_with(|local_rq| {
///         let should_pick_next = local_rq.update_current(UpdateFlags::Tick);
///         if should_pick_next {
///             cpu_local::set_need_preempt();
///         }
///     });
/// }
///
/// /// A preemption point, called at an earliest convenient timing
/// /// when OSTD can safely preempt the current running task.
/// fn might_preempt(scheduler: &'static dyn Scheduler) {
///     if !cpu_local::should_preempt() {
///         return;
///     }
///     let next_task_opt: Option<Arc<Task>> = scheduler
///         .mut_local_rq_with(|local_rq| local_rq.try_pick_next().cloned())
///     let Some(next_task) = next_task_opt {
///         switch_to(next_task);
///     }
/// }
/// ```
///
/// ### Exiting
///
/// ```
/// # use ostd::prelude::*;
/// # use ostd::task::{*, scheduler::*};
/// #
/// # fn switch_to(next: Arc<Task>) {}
/// #
/// /// Exits the current task.
/// fn exit(scheduler: &'static dyn Scheduler) {
///     let mut next_task_opt: Option<Arc<Task>> = None;
///     let mut is_first_try = true;
///     while scheduler.mut_local_rq_with(|local_rq| {
///         if is_first_try {
///             is_first_try = false;
///             let should_pick_next = local_rq.update_current(UpdateFlags::Exit);
///             let _current = local_rq.dequeue_current();
///             if !should_pick_next {
///                 return true; // continue loop
///             }
///             next_task_opt = Some(local_rq.pick_next().clone());
///             false // exit loop
///         } else {
///             next_task_opt = local_rq.try_pick_next().cloned();
///             next_task_opt.is_none()
///         }
///     }) {}
///     let next_task = next_task_opt.unwrap();
///     switch_to(next_task);
/// }
/// ```
pub trait LocalRunQueue<T = Task> {
    /// Gets the current runnable task.
    fn current(&self) -> Option<&Arc<T>>;

    /// Updates the current runnable task's scheduling statistics and
    /// potentially its position in the runqueue.
    ///
    /// The return value of this method indicates whether an invocation of `pick_next` should be followed
    /// to find another task to replace the current one.
    #[must_use]
    fn update_current(&mut self, flags: UpdateFlags) -> bool;

    /// Picks the next runnable task.
    ///
    /// This method instructs the local runqueue to pick the next runnable task and replace the current one.
    /// A reference to the new "current" task will be returned by this method.
    /// If the "old" current task presents, then it is still runnable and thus remains in the runqueue.
    ///
    /// # Panics
    ///
    /// As explained in the type-level Rust doc,
    /// this method will only be invoked by OSTD after a call to `update_current` returns true.
    /// In case that this contract is broken by the caller,
    /// the implementer is free to exhibit any undesirable or incorrect behaviors, include panicking.
    fn pick_next(&mut self) -> &Arc<T> {
        self.try_pick_next().unwrap()
    }

    /// Tries to pick the next runnable task.
    ///
    /// This method instructs the local runqueue to pick the next runnable task on a best-effort basis.
    /// If such a task can be picked, then this task supersedes the current task and
    /// the new the method returns a reference to the new "current" task.
    /// If the "old" current task presents, then it is still runnable and thus remains in the runqueue.
    fn try_pick_next(&mut self) -> Option<&Arc<T>>;

    /// Removes the current runnable task from runqueue.
    ///
    /// This method returns the current runnable task.
    /// If there is no current runnable task, this method returns `None`.
    fn dequeue_current(&mut self) -> Option<Arc<T>>;
}

/// Preempts the current task.
#[track_caller]
pub(crate) fn might_preempt() {
    /*
    if !cpu_local::should_preempt() {
        return;
    }
    reschedule(|local_rq| {
        let next_task_opt = local_rq.try_pick_next();
        if let Some(next_task) = next_task_opt {
            ReschedAction::SwitchTo(next_task.clone())
        } else {
            ReschedAction::DoNothing
        }
    })
    */
}

/// Blocks the current task unless `has_unparked()` returns `true`.
///
/// Note that this method may return due to spurious wake events. It's the caller's responsibility
/// to detect them (if necessary).
#[track_caller]
pub(crate) fn park_current<F>(has_unparked: F)
where
    F: Fn() -> bool,
{
    let mut current = None;
    let mut is_first_try = true;

    reschedule(|local_rq: &mut dyn LocalRunQueue| {
        let next_task_opt = if is_first_try {
            if has_unparked() {
                return ReschedAction::DoNothing;
            }
            is_first_try = false;

            // Note the race conditions: the current task may be woken after the above `has_unparked`
            // check, but before the below `dequeue_current` action, we need to make sure that the
            // wakeup event isn't lost.
            //
            // Currently, for the FIFO and CFS scheduler, `Scheduler::enqueue` will try to lock `local_rq`
            // when the above race condition occurs, so it will wait until we finish calling the
            // `dequeue_current` method and nothing bad will happen. This may need to be revisited
            // after more complex schedulers are introduced.

            let should_pick_next = local_rq.update_current(UpdateFlags::Wait);
            current = local_rq.dequeue_current();
            should_pick_next.then(|| local_rq.pick_next())
        } else {
            local_rq.try_pick_next()
        };

        if let Some(next_task) = next_task_opt {
            if Arc::ptr_eq(current.as_ref().unwrap(), next_task) {
                // The current task has been woken and picked as the next runnable task.
                return ReschedAction::DoNothing;
            }
            return ReschedAction::SwitchTo(next_task.clone());
        }

        ReschedAction::Retry
    });
}

/// Unblocks a target task.
pub(crate) fn unpark_target(runnable: Arc<Task>) {
    let preempt_cpu = SCHEDULER
        .get()
        .unwrap()
        .enqueue(runnable, EnqueueFlags::Wake);
    if let Some(preempt_cpu_id) = preempt_cpu {
        // set_need_preempt(preempt_cpu_id);
    }
}

/// Enqueues a newly built task.
///
/// Note that the new task is not guaranteed to run at once.
/*
#[track_caller]
pub(super) fn run_new_task(runnable: Arc<Task>) {
    // FIXME: remove this check for `SCHEDULER`.
    // Currently OSTD cannot know whether its user has injected a scheduler.
    if !SCHEDULER.is_completed() {
        fifo_scheduler::init();
    }

    let preempt_cpu = SCHEDULER
        .get()
        .unwrap()
        .enqueue(runnable, EnqueueFlags::Spawn);
    if let Some(preempt_cpu_id) = preempt_cpu {
        set_need_preempt(preempt_cpu_id);
    }

    might_preempt();
}
*/

/*
fn set_need_preempt(cpu_id: CpuId) {
    let preempt_guard = disable_preempt();

    if preempt_guard.current_cpu() == cpu_id {
        cpu_local::set_need_preempt();
    } else {
        crate::smp::inter_processor_call(&CpuSet::from(cpu_id), || {
            cpu_local::set_need_preempt();
        });
    }
}
*/

/// Dequeues the current task from its runqueue.
///
/// This should only be called if the current is to exit.
/*
#[track_caller]
pub(super) fn exit_current() -> ! {
    let mut is_first_try = true;

    reschedule(|local_rq: &mut dyn LocalRunQueue| {
        let next_task_opt = if is_first_try {
            is_first_try = false;
            let should_pick_next = local_rq.update_current(UpdateFlags::Exit);
            let _current = local_rq.dequeue_current();
            should_pick_next.then(|| local_rq.pick_next())
        } else {
            local_rq.try_pick_next()
        };

        if let Some(next_task) = next_task_opt {
            ReschedAction::SwitchTo(next_task.clone())
        } else {
            ReschedAction::Retry
        }
    });

    unreachable!()
}
*/

/// Yields execution.
/*
#[track_caller]
pub(super) fn yield_now() {
    reschedule(|local_rq| {
        let should_pick_next = local_rq.update_current(UpdateFlags::Yield);
        let next_task_opt = should_pick_next.then(|| local_rq.pick_next());
        if let Some(next_task) = next_task_opt {
            ReschedAction::SwitchTo(next_task.clone())
        } else {
            ReschedAction::DoNothing
        }
    })
}
*/

/// Do rescheduling by acting on the scheduling decision (`ReschedAction`) made by a
/// user-given closure.
///
/// The closure makes the scheduling decision by taking the local runqueue has its input.
#[track_caller]
fn reschedule<F>(mut f: F)
where
    F: FnMut(&mut dyn LocalRunQueue) -> ReschedAction,
{
    // Even if the decision below is `DoNothing`, we should clear this flag. Meanwhile, to avoid
    // race conditions, we should do this before making the decision.
    // cpu_local::clear_need_preempt();

    let next_task = loop {
        let mut action = ReschedAction::DoNothing;
        SCHEDULER.get().unwrap().mut_local_rq_with(&mut |rq| {
            action = f(rq);
        });

        match action {
            ReschedAction::DoNothing => {
                return;
            }
            ReschedAction::Retry => {
                continue;
            }
            ReschedAction::SwitchTo(next_task) => {
                break next_task;
            }
        };
    };

    // `switch_to_task` will spin if it finds that the next task is still running on some CPU core,
    // which guarantees soundness regardless of the scheduler implementation.
    //
    // FIXME: The scheduler decision and context switching are not atomic, which can lead to some
    // strange behavior even if the scheduler is implemented correctly. See "Problem 2" at
    // <https://github.com/asterinas/asterinas/issues/1633> for details.
    // processor::switch_to_task(next_task);
}


*/
