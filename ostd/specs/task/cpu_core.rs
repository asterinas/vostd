// SPDX-License-Identifier: MPL-2.0
//! Proof model for ownership of one CPU's local resources.
//!
//! A [`CpuCoreOwner`] permanently owns the CPU-local resources assigned to one
//! logical CPU. Scheduling changes only the owner's `current_task`; it never
//! transfers those resources to the task. Runtime CPU-local access temporarily
//! opens the owner into a linear [`CpuCoreOwnerHandle`] and its typed local
//! state, then restores that state before returning the owner to the scheduler.
//!
//! The proof lifecycle is:
//!
//! 1. [`CpuCoreOwner::tracked_schedule_in`] creates a fresh
//!    [`CpuExecutionToken`].
//! 2. [`CpuExecutionToken::tracked_disable_preempt`] increments the session's
//!    preemption depth and returns a [`CpuPreemptGuardToken`].
//! 3. [`CpuCoreOwner::tracked_open_current`] uses that guard to open only the
//!    CPU-local resources belonging to the pinned CPU.
//! 4. The caller restores the resources, consumes every preemption guard, and
//!    calls [`CpuCoreOwner::tracked_schedule_out`] at depth zero.
//!
//! This module is still a pure proof model. Connecting these tokens to the
//! executable scheduler and [`crate::task::DisabledPreemptGuard`] is a separate
//! refinement step.
use core::marker::PhantomData;

use vstd::{prelude::*, resource::Loc};
use vstd_extra::resource::ghost_resource::excl::ExclusiveGhost;

use crate::specs::mm::cpu::CpuId;
use crate::specs::task::cpu_local::CpuLocalAuth;

verus! {

/// Logical scheduling state carried by a CPU-local resource owner.
pub ghost struct CpuCoreOwnerView {
    /// Stable logical CPU represented by this core.
    pub cpu: CpuId,
    /// Task currently executing on this core, or `None` while the core is idle.
    pub current_task: Option<Loc>,
    /// Identity of the current execution session.
    ///
    /// Every schedule-in creates a fresh session. Keeping its identity in the
    /// core prevents a preemption guard from an older session from authorizing
    /// CPU-local access after a context switch.
    pub current_execution: Option<Loc>,
    /// Ordered identities of the CPU-local resources assigned to this core.
    pub locals_key: Seq<Loc>,
}

/// State of one task's execution session on a CPU.
pub ghost struct CpuExecutionView {
    /// Identity of the [`CpuCoreOwner`] on which the task is running.
    pub core_id: Loc,
    /// CPU on which this execution session is pinned.
    pub cpu: CpuId,
    /// Task running in this execution session.
    pub task: Loc,
    /// Number of live preemption guards in this execution session.
    pub preempt_depth: nat,
}

/// Logical identity carried by a live preemption guard.
pub ghost struct CpuPreemptGuardView {
    /// Execution session in which preemption was disabled.
    pub execution_id: Loc,
    /// Core owner associated with the execution session.
    pub core_id: Loc,
    /// CPU on which the guard pins execution.
    pub cpu: CpuId,
    /// Task that disabled preemption.
    pub task: Loc,
}

/// A typed collection of resources that belongs permanently to one CPU.
///
/// Implementations may aggregate any number of differently typed CPU-local
/// points-to resources in a tracked struct. The predicate must state that all
/// resources in the aggregate belong to `cpu`. `local_key` must faithfully and
/// stably list their identities: changing, replacing, reordering, adding, or
/// removing a resource must change the key.
pub trait CpuCoreLocalState {
    spec fn belongs_to_cpu(self, cpu: CpuId) -> bool;

    /// Ordered identities of the resources comprising this local state.
    ///
    /// The key must remain unchanged while the payload is detached from its
    /// core. Ordering makes two same-typed fields distinguishable.
    spec fn local_key(self) -> Seq<Loc>;
}

impl CpuCoreLocalState for () {
    open spec fn belongs_to_cpu(self, _cpu: CpuId) -> bool {
        true
    }

    open spec fn local_key(self) -> Seq<Loc> {
        Seq::empty()
    }
}

impl<A: CpuCoreLocalState, B: CpuCoreLocalState> CpuCoreLocalState for (A, B) {
    open spec fn belongs_to_cpu(self, cpu: CpuId) -> bool {
        self.0.belongs_to_cpu(cpu) && self.1.belongs_to_cpu(cpu)
    }

    open spec fn local_key(self) -> Seq<Loc> {
        self.0.local_key() + self.1.local_key()
    }
}

/// Linear identity and scheduling state left while CPU-local resources are
/// temporarily being accessed.
///
/// A handle cannot be duplicated. Restoring a [`CpuCoreOwner`] requires
/// returning a local-state aggregate of the same type, with the same ordered
/// resource identities, whose resources all belong to this handle's CPU.
pub tracked struct CpuCoreOwnerHandle<L: CpuCoreLocalState> {
    state: ExclusiveGhost<CpuCoreOwnerView>,
    marker: PhantomData<L>,
}

/// Scheduler-owned proof state for one CPU's local resources.
///
/// `L` is deliberately generic instead of type-erased. A subsystem can define
/// a tracked aggregate containing all CPU-local resources it needs and use that
/// aggregate as the owner's payload.
pub tracked struct CpuCoreOwner<L: CpuCoreLocalState> {
    handle: CpuCoreOwnerHandle<L>,
    locals: L,
}

/// Linear ownership of one task's current execution session.
///
/// The scheduler creates this token when scheduling a task in, keeps it in the
/// current CPU's proof context, and consumes it when scheduling the task out.
/// A context switch is only permitted when `preempt_depth()` is zero.
pub tracked struct CpuExecutionToken {
    state: ExclusiveGhost<CpuExecutionView>,
}

/// Linear proof counterpart of an executable disabled-preemption guard.
///
/// Each token contributes one unit to its execution session's preemption
/// depth. Returning it through [`CpuExecutionToken::tracked_enable_preempt`]
/// removes that unit.
pub tracked struct CpuPreemptGuardToken {
    state: ExclusiveGhost<CpuPreemptGuardView>,
}

impl<L: CpuCoreLocalState> View for CpuCoreOwnerHandle<L> {
    type V = CpuCoreOwnerView;

    closed spec fn view(&self) -> Self::V {
        self.state.view()
    }
}

impl<L: CpuCoreLocalState> View for CpuCoreOwner<L> {
    type V = CpuCoreOwnerView;

    closed spec fn view(&self) -> Self::V {
        self.handle@
    }
}

impl View for CpuExecutionToken {
    type V = CpuExecutionView;

    closed spec fn view(&self) -> Self::V {
        self.state@
    }
}

impl View for CpuPreemptGuardToken {
    type V = CpuPreemptGuardView;

    closed spec fn view(&self) -> Self::V {
        self.state@
    }
}

impl<L: CpuCoreLocalState> CpuCoreOwnerHandle<L> {
    /// Unique identity of this core resource.
    pub closed spec fn id(&self) -> Loc {
        self.state.id()
    }

    /// Stable CPU represented by this handle.
    pub closed spec fn cpu(&self) -> CpuId {
        self@.cpu
    }

    /// Task currently running on this CPU.
    pub closed spec fn current_task(&self) -> Option<Loc> {
        self@.current_task
    }

    /// Current execution session on this CPU.
    pub closed spec fn current_execution(&self) -> Option<Loc> {
        self@.current_execution
    }

    /// Whether no task is currently associated with this core.
    pub open spec fn is_idle(&self) -> bool {
        self.current_task() is None && self.current_execution() is None
    }

    /// Internal validity of the exclusive core state.
    pub closed spec fn wf(&self) -> bool {
        &&& self.state.wf()
        &&& (self.current_task() is None) == (self.current_execution() is None)
    }

    /// Ordered resource identities expected when restoring the core.
    pub closed spec fn expected_locals_key(&self) -> Seq<Loc> {
        self@.locals_key
    }

    /// Restores a complete core after a temporary CPU-local access.
    pub proof fn tracked_restore(tracked self, tracked locals: L) -> (tracked res: CpuCoreOwner<L>)
        requires
            self.wf(),
            locals.belongs_to_cpu(self.cpu()),
            locals.local_key() == self.expected_locals_key(),
        ensures
            res.id() == self.id(),
            res@ == self@,
            res.wf(),
            res.locals() == locals,
            res.locals().local_key() == self.expected_locals_key(),
    {
        CpuCoreOwner { handle: self, locals }
    }
}

impl<L: CpuCoreLocalState> CpuCoreOwner<L> {
    /// Creates an idle core with its permanent CPU-local resource aggregate.
    pub proof fn new(cpu: CpuId, tracked locals: L) -> (tracked res: Self)
        requires
            locals.belongs_to_cpu(cpu),
        ensures
            res.cpu() == cpu,
            res.is_idle(),
            res.wf(),
            res.locals() == locals,
    {
        let ghost locals_key = locals.local_key();
        let tracked state = ExclusiveGhost::alloc(
            CpuCoreOwnerView { cpu, current_task: None, current_execution: None, locals_key },
        );
        let tracked handle = CpuCoreOwnerHandle { state, marker: PhantomData };
        CpuCoreOwner { handle, locals }
    }

    /// Unique identity of this core resource.
    pub closed spec fn id(&self) -> Loc {
        self.handle.id()
    }

    /// Stable CPU represented by this core.
    pub closed spec fn cpu(&self) -> CpuId {
        self@.cpu
    }

    /// Task currently running on this CPU.
    pub closed spec fn current_task(&self) -> Option<Loc> {
        self@.current_task
    }

    /// Current execution session on this CPU.
    pub closed spec fn current_execution(&self) -> Option<Loc> {
        self@.current_execution
    }

    /// Whether no task is currently associated with this core.
    pub open spec fn is_idle(&self) -> bool {
        self.current_task() is None && self.current_execution() is None
    }

    /// CPU-local resource aggregate permanently assigned to this core.
    pub closed spec fn locals(&self) -> L {
        self.locals
    }

    /// Ordered identities of the CPU-local resources assigned to this core.
    pub closed spec fn locals_key(&self) -> Seq<Loc> {
        self.handle.expected_locals_key()
    }

    /// The core identity is valid and every local resource belongs to its CPU.
    pub closed spec fn wf(&self) -> bool {
        &&& self.handle.wf()
        &&& self.locals().belongs_to_cpu(self.cpu())
        &&& self.locals().local_key() == self.locals_key()
    }

    /// Associates a task with an idle CPU core and starts a fresh execution
    /// session.
    pub proof fn tracked_schedule_in(tracked &mut self, task: Loc) -> (tracked res:
        CpuExecutionToken)
        requires
            old(self).wf(),
            old(self).is_idle(),
        ensures
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).current_task() == Some(task),
            final(self).current_execution() == Some(res.id()),
            final(self).locals() == old(self).locals(),
            final(self).locals_key() == old(self).locals_key(),
            final(self).wf(),
            res.wf(),
            res.core_id() == final(self).id(),
            res.cpu() == final(self).cpu(),
            res.task() == task,
            res.preempt_depth() == 0,
            res.matches_core(final(self)),
    {
        let tracked execution_state = ExclusiveGhost::alloc(
            CpuExecutionView { core_id: self.id(), cpu: self.cpu(), task, preempt_depth: 0 },
        );
        let tracked execution = CpuExecutionToken { state: execution_state };
        let ghost next = CpuCoreOwnerView {
            cpu: self.cpu(),
            current_task: Some(task),
            current_execution: Some(execution.id()),
            locals_key: self.locals_key(),
        };
        self.handle.state.update(next);
        execution
    }

    /// Ends the current execution session and makes this CPU idle.
    ///
    /// Requiring zero preemption depth rules out a context switch while any
    /// [`CpuPreemptGuardToken`] from this session remains live.
    pub proof fn tracked_schedule_out(
        tracked &mut self,
        tracked execution: CpuExecutionToken,
    ) -> (task: Loc)
        requires
            old(self).wf(),
            !old(self).is_idle(),
            execution.wf(),
            execution.matches_core(old(self)),
            execution.preempt_depth() == 0,
        ensures
            old(self).current_task() == Some(task),
            task == execution.task(),
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).is_idle(),
            final(self).locals() == old(self).locals(),
            final(self).locals_key() == old(self).locals_key(),
            final(self).wf(),
    {
        let task = self.current_task()->0;
        let ghost next = CpuCoreOwnerView {
            cpu: self.cpu(),
            current_task: None,
            current_execution: None,
            locals_key: self.locals_key(),
        };
        self.handle.state.update(next);
        task
    }

    /// Temporarily separates the typed CPU-local state from the core handle.
    ///
    /// The caller may update the returned resources, but must eventually call
    /// [`CpuCoreOwnerHandle::tracked_restore`] with resources that still
    /// belong to this CPU.
    pub proof fn tracked_open(tracked self) -> (tracked res: (CpuCoreOwnerHandle<L>, L))
        requires
            self.wf(),
        ensures
            res.0.id() == self.id(),
            res.0@ == self@,
            res.0.wf(),
            res.0.expected_locals_key() == self.locals_key(),
            res.1 == self.locals(),
            res.1.belongs_to_cpu(res.0.cpu()),
            res.1.local_key() == res.0.expected_locals_key(),
    {
        (self.handle, self.locals)
    }

    /// Opens CPU-local resources while execution is pinned to this CPU.
    ///
    /// This is the client-facing form of [`Self::tracked_open`]. The
    /// preemption token proves that the current execution session cannot be
    /// scheduled out while the returned CPU-local resources are being used.
    pub proof fn tracked_open_current(
        tracked self,
        tracked preempt_guard: &CpuPreemptGuardToken,
    ) -> (tracked res: (CpuCoreOwnerHandle<L>, L))
        requires
            self.wf(),
            preempt_guard.wf(),
            preempt_guard.matches_core(&self),
        ensures
            res.0.id() == self.id(),
            res.0@ == self@,
            res.0.wf(),
            res.0.cpu() == preempt_guard.cpu(),
            res.0.current_task() == Some(preempt_guard.task()),
            res.0.current_execution() == Some(preempt_guard.execution_id()),
            res.0.expected_locals_key() == self.locals_key(),
            res.1 == self.locals(),
            res.1.belongs_to_cpu(preempt_guard.cpu()),
            res.1.local_key() == res.0.expected_locals_key(),
    {
        (self.handle, self.locals)
    }
}

impl CpuExecutionToken {
    /// Unique identity of this execution session.
    pub closed spec fn id(&self) -> Loc {
        self.state.id()
    }

    /// Identity of the core owner running this session.
    pub closed spec fn core_id(&self) -> Loc {
        self@.core_id
    }

    /// CPU on which this session executes.
    pub closed spec fn cpu(&self) -> CpuId {
        self@.cpu
    }

    /// Task running in this session.
    pub closed spec fn task(&self) -> Loc {
        self@.task
    }

    /// Number of live preemption guards in this session.
    pub closed spec fn preempt_depth(&self) -> nat {
        self@.preempt_depth
    }

    /// Internal validity of the execution token.
    pub closed spec fn wf(&self) -> bool {
        self.state.wf()
    }

    /// Whether this is the current execution session of `core`.
    pub open spec fn matches_core<L: CpuCoreLocalState>(&self, core: &CpuCoreOwner<L>) -> bool {
        &&& self.core_id() == core.id()
        &&& self.cpu() == core.cpu()
        &&& core.current_task() == Some(self.task())
        &&& core.current_execution() == Some(self.id())
    }

    /// Disables preemption once and returns the corresponding linear guard.
    pub proof fn tracked_disable_preempt(tracked &mut self) -> (tracked res: CpuPreemptGuardToken)
        requires
            old(self).wf(),
        ensures
            final(self).id() == old(self).id(),
            final(self).core_id() == old(self).core_id(),
            final(self).cpu() == old(self).cpu(),
            final(self).task() == old(self).task(),
            final(self).preempt_depth() == old(self).preempt_depth() + 1,
            final(self).wf(),
            res.wf(),
            res.execution_id() == final(self).id(),
            res.core_id() == final(self).core_id(),
            res.cpu() == final(self).cpu(),
            res.task() == final(self).task(),
            res.matches_execution(final(self)),
    {
        let ghost next = CpuExecutionView {
            core_id: self.core_id(),
            cpu: self.cpu(),
            task: self.task(),
            preempt_depth: self.preempt_depth() + 1,
        };
        self.state.update(next);
        let tracked state = ExclusiveGhost::alloc(
            CpuPreemptGuardView {
                execution_id: self.id(),
                core_id: self.core_id(),
                cpu: self.cpu(),
                task: self.task(),
            },
        );
        CpuPreemptGuardToken { state }
    }

    /// Re-enables one level of preemption by consuming its guard.
    pub proof fn tracked_enable_preempt(tracked &mut self, tracked guard: CpuPreemptGuardToken)
        requires
            old(self).wf(),
            guard.wf(),
            guard.matches_execution(old(self)),
            old(self).preempt_depth() > 0,
        ensures
            final(self).id() == old(self).id(),
            final(self).core_id() == old(self).core_id(),
            final(self).cpu() == old(self).cpu(),
            final(self).task() == old(self).task(),
            final(self).preempt_depth() + 1 == old(self).preempt_depth(),
            final(self).wf(),
    {
        let ghost next = CpuExecutionView {
            core_id: self.core_id(),
            cpu: self.cpu(),
            task: self.task(),
            preempt_depth: (self.preempt_depth() - 1) as nat,
        };
        self.state.update(next);
    }
}

impl CpuPreemptGuardToken {
    /// Identity of this guard token.
    pub closed spec fn id(&self) -> Loc {
        self.state.id()
    }

    /// Execution session in which preemption was disabled.
    pub closed spec fn execution_id(&self) -> Loc {
        self@.execution_id
    }

    /// Identity of the core owner associated with this guard.
    pub closed spec fn core_id(&self) -> Loc {
        self@.core_id
    }

    /// CPU to which this guard pins execution.
    pub closed spec fn cpu(&self) -> CpuId {
        self@.cpu
    }

    /// Task that owns this guard.
    pub closed spec fn task(&self) -> Loc {
        self@.task
    }

    /// Internal validity of the guard token.
    pub closed spec fn wf(&self) -> bool {
        self.state.wf()
    }

    /// Whether this guard belongs to `execution`.
    pub open spec fn matches_execution(&self, execution: &CpuExecutionToken) -> bool {
        &&& self.execution_id() == execution.id()
        &&& self.core_id() == execution.core_id()
        &&& self.cpu() == execution.cpu()
        &&& self.task() == execution.task()
    }

    /// Whether this guard pins the current execution session of `core`.
    pub open spec fn matches_core<L: CpuCoreLocalState>(&self, core: &CpuCoreOwner<L>) -> bool {
        &&& self.core_id() == core.id()
        &&& self.cpu() == core.cpu()
        &&& core.current_task() == Some(self.task())
        &&& core.current_execution() == Some(self.execution_id())
    }
}

/// Regression proof that a CPU-local points-to resource remains owned by the
/// same core across scheduling and a temporary local-state access.
proof fn cpu_core_owns_cpu_local_points_to<V>(initial: Map<CpuId, V>, cpu: CpuId, new_value: V)
    requires
        initial.contains_key(cpu),
{
    let tracked (mut auth, mut points_to_set) = CpuLocalAuth::new(initial);
    let tracked points_to = points_to_set.tracked_take(cpu);
    let tracked mut core = CpuCoreOwner::new(cpu, points_to);

    let ghost task = auth.id();
    let tracked mut execution = core.tracked_schedule_in(task);
    let tracked outer_guard = execution.tracked_disable_preempt();
    let tracked inner_guard = execution.tracked_disable_preempt();
    assert(execution.preempt_depth() == 2);
    let tracked (handle, mut points_to) = core.tracked_open_current(&inner_guard);
    assert(handle.cpu() == cpu);
    assert(handle.current_task() == Some(task));

    points_to.tracked_update(&mut auth, new_value);
    let tracked mut core = handle.tracked_restore(points_to);
    assert(core.cpu() == cpu);
    assert(core.current_task() == Some(task));

    execution.tracked_enable_preempt(inner_guard);
    assert(execution.preempt_depth() == 1);
    execution.tracked_enable_preempt(outer_guard);
    assert(execution.preempt_depth() == 0);
    let finished_task = core.tracked_schedule_out(execution);
    assert(finished_task == task);
    assert(core.is_idle());
}

} // verus!
