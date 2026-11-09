// SPDX-License-Identifier: MPL-2.0
//! Proof model for ownership of one CPU's local resources.
//!
//! A [`CpuCoreOwner`] permanently owns the CPU-local resources assigned to one
//! logical CPU. Scheduling changes only the owner's `current_task`; it never
//! transfers those resources to the task. Runtime CPU-local access temporarily
//! opens the owner into a linear [`CpuCoreOwnerHandle`] and its typed local
//! state, then restores that state before returning the owner to the scheduler.
//!
//! Local IRQ guard transitions model both `DisabledLocalIrqGuard` and the
//! current `DisabledPreemptGuard`, which owns an IRQ guard. The executable
//! guard constructors, `Drop`, and hardware instructions are not yet tied to
//! this proof state; callers must establish that link before using the model
//! as an end-to-end guarantee.
use vstd::{prelude::*, resource::Loc};
use vstd_extra::resource::ghost_resource::excl::ExclusiveGhost;

use crate::specs::task::cpu_local::CpuLocalAuth;

use core::marker::PhantomData;

use crate::cpu::CpuId;

verus! {

/// Logical scheduling state carried by a CPU-local resource owner.
pub ghost struct CpuCoreOwnerView {
    /// Stable logical CPU represented by this core.
    pub cpu: CpuId,
    /// Task currently executing on this core, or `None` while the core is idle.
    pub current_task: Option<Loc>,
    /// Ordered identities of the CPU-local resources assigned to this core.
    pub locals_key: Seq<Loc>,
    /// Whether maskable local interrupts are enabled on this CPU.
    pub irq_enabled: bool,
    /// Number of outstanding local IRQ guards on this CPU.
    pub irq_guard_depth: nat,
}

/// Linear proof of one outstanding local IRQ guard on a particular CPU.
///
/// The recorded state belongs to the CPU, not to the task currently running
/// on it. The depth enforces reverse-order release of nested guards.
pub tracked struct LocalIrqGuardToken {
    /// Unique release obligation, moved rather than copied on transfer.
    nonce: ExclusiveGhost<()>,
    ghost core_id: Loc,
    ghost cpu: CpuId,
    ghost depth: nat,
    ghost was_enabled: bool,
}

impl LocalIrqGuardToken {
    /// CPU core that issued this guard.
    pub closed spec fn core_id(&self) -> Loc {
        self.core_id
    }

    /// CPU on which this guard must be released.
    pub closed spec fn cpu(&self) -> CpuId {
        self.cpu
    }

    /// Nesting depth before this guard was acquired.
    pub closed spec fn depth(&self) -> nat {
        self.depth
    }

    /// Local IRQ state captured when this guard was acquired.
    pub closed spec fn was_enabled(&self) -> bool {
        self.was_enabled
    }

    /// Moves the unique release obligation to a replacement guard.
    pub proof fn tracked_transfer(tracked self) -> (tracked res: Self)
        ensures
            res.core_id() == self.core_id(),
            res.cpu() == self.cpu(),
            res.depth() == self.depth(),
            res.was_enabled() == self.was_enabled(),
    {
        self
    }
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

    /// Whether no task is currently associated with this core.
    pub open spec fn is_idle(&self) -> bool {
        self.current_task() is None
    }

    /// Internal validity of the exclusive core state.
    pub closed spec fn wf(&self) -> bool {
        self.state.wf() && (self@.irq_guard_depth > 0 ==> !self@.irq_enabled)
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
    pub proof fn new(cpu: CpuId, tracked locals: L, irq_enabled: bool) -> (tracked res: Self)
        requires
            locals.belongs_to_cpu(cpu),
        ensures
            res.cpu() == cpu,
            res.is_idle(),
            res.wf(),
            res.locals() == locals,
            res.irq_enabled() == irq_enabled,
            res.irq_guard_depth() == 0,
    {
        let ghost locals_key = locals.local_key();
        let tracked state = ExclusiveGhost::alloc(
            CpuCoreOwnerView {
                cpu,
                current_task: None,
                locals_key,
                irq_enabled,
                irq_guard_depth: 0,
            },
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

    /// Whether no task is currently associated with this core.
    pub open spec fn is_idle(&self) -> bool {
        self.current_task() is None
    }

    /// CPU-local resource aggregate permanently assigned to this core.
    pub closed spec fn locals(&self) -> L {
        self.locals
    }

    /// Ordered identities of the CPU-local resources assigned to this core.
    pub closed spec fn locals_key(&self) -> Seq<Loc> {
        self.handle.expected_locals_key()
    }

    /// Whether this CPU currently accepts maskable local interrupts.
    pub closed spec fn irq_enabled(&self) -> bool {
        self@.irq_enabled
    }

    /// Number of local IRQ guards that have not yet been released.
    pub closed spec fn irq_guard_depth(&self) -> nat {
        self@.irq_guard_depth
    }

    /// The core identity is valid and every local resource belongs to its CPU.
    pub closed spec fn wf(&self) -> bool {
        &&& self.handle.wf()
        &&& self.locals().belongs_to_cpu(self.cpu())
        &&& self.locals().local_key() == self.locals_key()
    }

    /// Models acquiring a local IRQ guard and masking local interrupts.
    pub proof fn tracked_disable_local(tracked &mut self) -> (tracked guard: LocalIrqGuardToken)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).current_task() == old(self).current_task(),
            final(self).locals() == old(self).locals(),
            guard.core_id() == old(self).id(),
            guard.cpu() == old(self).cpu(),
            guard.depth() == old(self).irq_guard_depth(),
            guard.was_enabled() == old(self).irq_enabled(),
            final(self).irq_guard_depth() == old(self).irq_guard_depth() + 1,
            !final(self).irq_enabled(),
    {
        let tracked guard = LocalIrqGuardToken {
            nonce: ExclusiveGhost::alloc(()),
            core_id: self.id(),
            cpu: self.cpu(),
            depth: self.irq_guard_depth(),
            was_enabled: self.irq_enabled(),
        };
        let ghost next = CpuCoreOwnerView {
            cpu: self.cpu(),
            current_task: self.current_task(),
            locals_key: self.locals_key(),
            irq_enabled: false,
            irq_guard_depth: self.irq_guard_depth() + 1,
        };
        self.handle.state.update(next);
        guard
    }

    /// Models dropping the most recently acquired local IRQ guard.
    ///
    /// The hardware `Drop` implementation is outside Verus; this transition
    /// records the state it must establish when it is connected to the model.
    pub proof fn tracked_restore_local(tracked &mut self, tracked guard: LocalIrqGuardToken)
        requires
            old(self).wf(),
            guard.core_id() == old(self).id(),
            guard.cpu() == old(self).cpu(),
            guard.depth() + 1 == old(self).irq_guard_depth(),
            guard.depth() > 0 ==> !guard.was_enabled(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).current_task() == old(self).current_task(),
            final(self).locals() == old(self).locals(),
            final(self).irq_guard_depth() == guard.depth(),
            final(self).irq_enabled() == guard.was_enabled(),
    {
        let ghost next = CpuCoreOwnerView {
            cpu: self.cpu(),
            current_task: self.current_task(),
            locals_key: self.locals_key(),
            irq_enabled: guard.was_enabled(),
            irq_guard_depth: guard.depth(),
        };
        self.handle.state.update(next);
    }

    /// Associates a task with an idle CPU core.
    pub proof fn tracked_schedule_in(tracked &mut self, task: Loc)
        requires
            old(self).wf(),
            old(self).is_idle(),
        ensures
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).current_task() == Some(task),
            final(self).locals() == old(self).locals(),
            final(self).locals_key() == old(self).locals_key(),
            final(self).irq_enabled() == old(self).irq_enabled(),
            final(self).irq_guard_depth() == old(self).irq_guard_depth(),
            final(self).wf(),
    {
        let ghost next = CpuCoreOwnerView {
            cpu: self.cpu(),
            current_task: Some(task),
            locals_key: self.locals_key(),
            irq_enabled: self.irq_enabled(),
            irq_guard_depth: self.irq_guard_depth(),
        };
        self.handle.state.update(next);
    }

    /// Makes this CPU idle and returns the task that was running on it.
    pub proof fn tracked_schedule_out(tracked &mut self) -> (task: Loc)
        requires
            old(self).wf(),
            !old(self).is_idle(),
        ensures
            old(self).current_task() == Some(task),
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).is_idle(),
            final(self).locals() == old(self).locals(),
            final(self).locals_key() == old(self).locals_key(),
            final(self).irq_enabled() == old(self).irq_enabled(),
            final(self).irq_guard_depth() == old(self).irq_guard_depth(),
            final(self).wf(),
    {
        let task = self.current_task()->0;
        let ghost next = CpuCoreOwnerView {
            cpu: self.cpu(),
            current_task: None,
            locals_key: self.locals_key(),
            irq_enabled: self.irq_enabled(),
            irq_guard_depth: self.irq_guard_depth(),
        };
        self.handle.state.update(next);
        task
    }

    /// Models a timer interrupt preempting the current task.
    ///
    /// Masked local interrupts cannot enter this transition. Voluntary
    /// scheduling uses `tracked_schedule_out` and has separate preconditions.
    pub proof fn tracked_timer_preempt(tracked &mut self) -> (task: Loc)
        requires
            old(self).wf(),
            !old(self).is_idle(),
            old(self).irq_enabled(),
        ensures
            old(self).current_task() == Some(task),
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).is_idle(),
            final(self).locals() == old(self).locals(),
            final(self).irq_enabled(),
            final(self).irq_guard_depth() == 0,
            final(self).wf(),
    {
        self.tracked_schedule_out()
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
}

/// Regression proof that a CPU-local points-to resource remains owned by the
/// same core across scheduling and a temporary local-state access.
proof fn cpu_core_owns_cpu_local_points_to<V>(initial: Map<CpuId, V>, cpu: CpuId, new_value: V)
    requires
        initial.contains_key(cpu),
{
    let tracked (mut auth, mut points_to_set) = CpuLocalAuth::new(initial);
    let tracked points_to = points_to_set.tracked_take(cpu);
    let tracked mut core = CpuCoreOwner::new(cpu, points_to, true);

    let ghost task = auth.id();
    core.tracked_schedule_in(task);
    let tracked (handle, mut points_to) = core.tracked_open();
    assert(handle.cpu() == cpu);
    assert(handle.current_task() == Some(task));

    points_to.tracked_update(&mut auth, new_value);
    let tracked mut core = handle.tracked_restore(points_to);
    assert(core.cpu() == cpu);
    assert(core.current_task() == Some(task));

    let finished_task = core.tracked_schedule_out();
    assert(finished_task == task);
    assert(core.is_idle());
}

/// Regression proof for nested IRQ masking, transfer, LIFO restoration, and
/// the timer-preemption gate. It covers both initially enabled and disabled IRQs.
proof fn nested_local_irq_guards_restore_state<L: CpuCoreLocalState>(
    cpu: CpuId,
    tracked locals: L,
    task: Loc,
    initially_enabled: bool,
)
    requires
        locals.belongs_to_cpu(cpu),
{
    let tracked mut core = CpuCoreOwner::new(cpu, locals, initially_enabled);
    core.tracked_schedule_in(task);

    let tracked outer = core.tracked_disable_local();
    assert(!core.irq_enabled());
    assert(core.irq_guard_depth() == 1);
    assert(outer.was_enabled() == initially_enabled);

    let tracked inner = core.tracked_disable_local();
    assert(!inner.was_enabled());
    assert(core.irq_guard_depth() == 2);
    let tracked inner = inner.tracked_transfer();
    core.tracked_restore_local(inner);
    assert(!core.irq_enabled());
    assert(core.irq_guard_depth() == 1);

    core.tracked_restore_local(outer);
    assert(core.irq_guard_depth() == 0);
    assert(core.irq_enabled() == initially_enabled);

    if initially_enabled {
        let preempted = core.tracked_timer_preempt();
        assert(preempted == task);
    } else {
        let switched = core.tracked_schedule_out();
        assert(switched == task);
    }
}

} // verus!
