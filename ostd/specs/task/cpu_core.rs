// SPDX-License-Identifier: MPL-2.0
//! Proof model for ownership of one CPU's local resources.
//!
//! A [`CpuCoreOwner`] permanently owns the CPU-local resources assigned to one
//! logical CPU. Scheduling changes only the owner's `current_task`; it never
//! transfers those resources to the task. Runtime CPU-local access temporarily
//! opens the owner into a linear [`CpuCoreOwnerHandle`] and its typed local
//! state, then restores that state before returning the owner to the scheduler.
//!
//! The owner also records the CPU state that decides when the current task may
//! be switched out. Such a switch is the RCU quiescent point, so it requires
//! that no `DisabledPreemptGuard` is live and that local IRQs are enabled,
//! which are the checks `might_sleep` performs before `switch_to_task`.
//!
//! - Preemption guards are counted, not stacked, matching the CPU-local guard
//!   counter behind `DisabledPreemptGuard`; they may be released in any order.
//! - Local IRQ guards restore the saved IRQ state and must be released in
//!   reverse order.
//! - An interrupt runs nested on the interrupted task and never switches it
//!   out. Interrupt entry masks IRQs, and the bottom half disables preemption
//!   before unmasking them. Hence, no live preemption guard together with
//!   enabled IRQs implies that no interrupt is active on this CPU.
//!
//! The executable guards, `Drop`, trap entry and hardware instructions are not
//! yet tied to this proof state. NMIs, which ignore the IRQ mask, and the
//! bootstrap context, in which `might_sleep` skips its checks, are not modeled.
use vstd::{
    prelude::*,
    resource::{
        Loc,
        set::{GhostSetAuth, GhostSingleton},
    },
};
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
    ghost core_id: Loc,
    ghost cpu: CpuId,
    ghost depth: nat,
    ghost was_enabled: bool,
}

/// Linear proof of one live `DisabledPreemptGuard` on a particular CPU.
pub tracked struct PreemptGuardToken {
    ticket: GhostSingleton<nat>,
}

/// Linear proof that one interrupt handler is active on a particular CPU.
pub tracked struct InterruptToken {
    ticket: GhostSingleton<nat>,
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
}

impl PreemptGuardToken {
    /// Preemption-guard counter of the CPU core that issued this guard.
    pub closed spec fn id(&self) -> Loc {
        self.ticket.id()
    }
}

impl InterruptToken {
    /// Interrupt counter of the CPU core that entered this interrupt.
    pub closed spec fn id(&self) -> Loc {
        self.ticket.id()
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
    preempt_guards: CpuGuardCounter,
    interrupts: CpuGuardCounter,
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

    /// Identity of the counter that issues this CPU's preemption guards.
    pub closed spec fn preempt_guards_id(&self) -> Loc {
        self.preempt_guards.id()
    }

    /// Number of live preemption guards, mirroring the CPU-local guard count.
    pub closed spec fn preempt_count(&self) -> nat {
        self.preempt_guards.count()
    }

    /// Identity of the counter that tracks this CPU's active interrupts.
    pub closed spec fn interrupts_id(&self) -> Loc {
        self.interrupts.id()
    }

    /// Number of interrupt handlers nested on this CPU.
    pub closed spec fn interrupt_count(&self) -> nat {
        self.interrupts.count()
    }

    /// Internal validity of the exclusive core state.
    ///
    /// The last conjunct records that an interrupt can run with IRQs enabled
    /// only in its bottom half, which holds a preemption guard.
    pub closed spec fn wf(&self) -> bool {
        &&& self.state.wf()
        &&& self@.irq_guard_depth > 0 ==> !self@.irq_enabled
        &&& self.preempt_guards.wf()
        &&& self.interrupts.wf()
        &&& self.interrupts.count() > 0 && self@.irq_enabled ==> self.preempt_guards.count() > 0
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
            res.preempt_guards_id() == self.preempt_guards_id(),
            res.preempt_count() == self.preempt_count(),
            res.interrupts_id() == self.interrupts_id(),
            res.interrupt_count() == self.interrupt_count(),
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
            res.preempt_count() == 0,
            res.interrupt_count() == 0,
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
        let tracked handle = CpuCoreOwnerHandle {
            state,
            preempt_guards: CpuGuardCounter::new(),
            interrupts: CpuGuardCounter::new(),
            marker: PhantomData,
        };
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

    /// Identity of the counter that issues this CPU's preemption guards.
    pub closed spec fn preempt_guards_id(&self) -> Loc {
        self.handle.preempt_guards_id()
    }

    /// Number of live preemption guards, mirroring the CPU-local guard count.
    pub closed spec fn preempt_count(&self) -> nat {
        self.handle.preempt_count()
    }

    /// Identity of the counter that tracks this CPU's active interrupts.
    pub closed spec fn interrupts_id(&self) -> Loc {
        self.handle.interrupts_id()
    }

    /// Number of interrupt handlers nested on this CPU.
    pub closed spec fn interrupt_count(&self) -> nat {
        self.handle.interrupt_count()
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
            final(self).preempt_guards_id() == old(self).preempt_guards_id(),
            final(self).preempt_count() == old(self).preempt_count(),
            final(self).interrupts_id() == old(self).interrupts_id(),
            final(self).interrupt_count() == old(self).interrupt_count(),
            guard.core_id() == old(self).id(),
            guard.cpu() == old(self).cpu(),
            guard.depth() == old(self).irq_guard_depth(),
            guard.was_enabled() == old(self).irq_enabled(),
            final(self).irq_guard_depth() == old(self).irq_guard_depth() + 1,
            !final(self).irq_enabled(),
    {
        let tracked guard = LocalIrqGuardToken {
            core_id: self.id(),
            cpu: self.cpu(),
            depth: self.irq_guard_depth(),
            was_enabled: self.irq_enabled(),
        };
        let ghost next = CpuCoreOwnerView {
            irq_enabled: false,
            irq_guard_depth: self.irq_guard_depth() + 1,
            ..self@
        };
        self.handle.state.update(next);
        guard
    }

    /// Models dropping the most recently acquired local IRQ guard.
    ///
    /// The hardware `Drop` implementation is outside Verus; this transition
    /// records the state it must establish when it is connected to the model.
    /// Inside an interrupt, IRQs may be re-enabled only under a preemption
    /// guard, as in the bottom half.
    pub proof fn tracked_restore_local(tracked &mut self, tracked guard: LocalIrqGuardToken)
        requires
            old(self).wf(),
            guard.core_id() == old(self).id(),
            guard.cpu() == old(self).cpu(),
            guard.depth() + 1 == old(self).irq_guard_depth(),
            guard.depth() > 0 ==> !guard.was_enabled(),
            guard.was_enabled() && old(self).interrupt_count() > 0 ==> old(self).preempt_count()
                > 0,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).current_task() == old(self).current_task(),
            final(self).locals() == old(self).locals(),
            final(self).preempt_guards_id() == old(self).preempt_guards_id(),
            final(self).preempt_count() == old(self).preempt_count(),
            final(self).interrupts_id() == old(self).interrupts_id(),
            final(self).interrupt_count() == old(self).interrupt_count(),
            final(self).irq_guard_depth() == guard.depth(),
            final(self).irq_enabled() == guard.was_enabled(),
    {
        let ghost next = CpuCoreOwnerView {
            irq_enabled: guard.was_enabled(),
            irq_guard_depth: guard.depth(),
            ..self@
        };
        self.handle.state.update(next);
    }

    /// Models unmasking local IRQs without an IRQ guard.
    ///
    /// This is the `enable_local` call in the bottom half, which is made only
    /// after preemption has been disabled.
    pub proof fn tracked_enable_local(tracked &mut self)
        requires
            old(self).wf(),
            old(self).irq_guard_depth() == 0,
            old(self).interrupt_count() > 0 ==> old(self).preempt_count() > 0,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).current_task() == old(self).current_task(),
            final(self).locals() == old(self).locals(),
            final(self).preempt_guards_id() == old(self).preempt_guards_id(),
            final(self).preempt_count() == old(self).preempt_count(),
            final(self).interrupts_id() == old(self).interrupts_id(),
            final(self).interrupt_count() == old(self).interrupt_count(),
            final(self).irq_guard_depth() == 0,
            final(self).irq_enabled(),
    {
        let ghost next = CpuCoreOwnerView { irq_enabled: true, ..self@ };
        self.handle.state.update(next);
    }

    /// Models `disable_preempt`, which increments the CPU-local guard count.
    pub proof fn tracked_disable_preempt(tracked &mut self) -> (tracked guard: PreemptGuardToken)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).current_task() == old(self).current_task(),
            final(self).locals() == old(self).locals(),
            final(self).irq_enabled() == old(self).irq_enabled(),
            final(self).irq_guard_depth() == old(self).irq_guard_depth(),
            final(self).preempt_guards_id() == old(self).preempt_guards_id(),
            final(self).preempt_count() == old(self).preempt_count() + 1,
            final(self).interrupts_id() == old(self).interrupts_id(),
            final(self).interrupt_count() == old(self).interrupt_count(),
            guard.id() == old(self).preempt_guards_id(),
    {
        let tracked ticket = self.handle.preempt_guards.tracked_acquire();
        PreemptGuardToken { ticket }
    }

    /// Models dropping a preemption guard, which decrements the guard count.
    ///
    /// Guards may be released in any order. An interrupt handler running with
    /// IRQs enabled must keep at least one guard.
    pub proof fn tracked_enable_preempt(tracked &mut self, tracked guard: PreemptGuardToken)
        requires
            old(self).wf(),
            guard.id() == old(self).preempt_guards_id(),
            old(self).interrupt_count() > 0 && old(self).irq_enabled() ==> old(self).preempt_count()
                > 1,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).current_task() == old(self).current_task(),
            final(self).locals() == old(self).locals(),
            final(self).irq_enabled() == old(self).irq_enabled(),
            final(self).irq_guard_depth() == old(self).irq_guard_depth(),
            final(self).preempt_guards_id() == old(self).preempt_guards_id(),
            final(self).preempt_count() + 1 == old(self).preempt_count(),
            final(self).interrupts_id() == old(self).interrupts_id(),
            final(self).interrupt_count() == old(self).interrupt_count(),
    {
        let tracked PreemptGuardToken { ticket } = guard;
        self.handle.preempt_guards.tracked_release(ticket);
    }

    /// A live preemption guard prevents the current task from being switched out.
    pub proof fn lemma_preempt_guard_blocks_switch(tracked &self, tracked guard: &PreemptGuardToken)
        requires
            self.wf(),
            guard.id() == self.preempt_guards_id(),
        ensures
            self.preempt_count() > 0,
    {
        guard.ticket.agree(&self.handle.preempt_guards.live);
    }

    /// Models the hardware entering an interrupt handler.
    ///
    /// A maskable interrupt arrives only while IRQs are enabled; entry masks
    /// them. The interrupted task stays current on this CPU.
    pub proof fn tracked_enter_interrupt(tracked &mut self) -> (tracked entry: InterruptToken)
        requires
            old(self).wf(),
            old(self).irq_enabled(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).current_task() == old(self).current_task(),
            final(self).locals() == old(self).locals(),
            final(self).preempt_guards_id() == old(self).preempt_guards_id(),
            final(self).preempt_count() == old(self).preempt_count(),
            final(self).interrupts_id() == old(self).interrupts_id(),
            final(self).interrupt_count() == old(self).interrupt_count() + 1,
            final(self).irq_guard_depth() == 0,
            !final(self).irq_enabled(),
            entry.id() == old(self).interrupts_id(),
    {
        let tracked ticket = self.handle.interrupts.tracked_acquire();
        let ghost next = CpuCoreOwnerView { irq_enabled: false, ..self@ };
        self.handle.state.update(next);
        InterruptToken { ticket }
    }

    /// Models returning from an interrupt handler.
    ///
    /// The handler returns with IRQs masked. Returning restores the enabled IRQ
    /// state observed at entry, discarding IRQ guards the handler forgot. When
    /// it returns into an outer bottom half, that bottom half still holds its
    /// preemption guard.
    pub proof fn tracked_exit_interrupt(tracked &mut self, tracked entry: InterruptToken)
        requires
            old(self).wf(),
            entry.id() == old(self).interrupts_id(),
            !old(self).irq_enabled(),
            old(self).interrupt_count() > 1 ==> old(self).preempt_count() > 0,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).current_task() == old(self).current_task(),
            final(self).locals() == old(self).locals(),
            final(self).preempt_guards_id() == old(self).preempt_guards_id(),
            final(self).preempt_count() == old(self).preempt_count(),
            final(self).interrupts_id() == old(self).interrupts_id(),
            final(self).interrupt_count() + 1 == old(self).interrupt_count(),
            final(self).irq_guard_depth() == 0,
            final(self).irq_enabled(),
    {
        let tracked InterruptToken { ticket } = entry;
        self.handle.interrupts.tracked_release(ticket);
        let ghost next = CpuCoreOwnerView { irq_enabled: true, irq_guard_depth: 0, ..self@ };
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
            final(self).preempt_guards_id() == old(self).preempt_guards_id(),
            final(self).preempt_count() == old(self).preempt_count(),
            final(self).interrupts_id() == old(self).interrupts_id(),
            final(self).interrupt_count() == old(self).interrupt_count(),
            final(self).wf(),
    {
        let ghost next = CpuCoreOwnerView { current_task: Some(task), ..self@ };
        self.handle.state.update(next);
    }

    /// Switches the current task out at a quiescent point.
    ///
    /// The preconditions are the runtime checks of `might_sleep`. Together they
    /// exclude every interrupt handler, so a task switch never happens inside
    /// one.
    pub proof fn tracked_schedule_out(tracked &mut self) -> (task: Loc)
        requires
            old(self).wf(),
            !old(self).is_idle(),
            old(self).preempt_count() == 0,
            old(self).irq_enabled(),
        ensures
            old(self).current_task() == Some(task),
            old(self).interrupt_count() == 0,
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).is_idle(),
            final(self).locals() == old(self).locals(),
            final(self).locals_key() == old(self).locals_key(),
            final(self).irq_enabled() == old(self).irq_enabled(),
            final(self).irq_guard_depth() == old(self).irq_guard_depth(),
            final(self).preempt_guards_id() == old(self).preempt_guards_id(),
            final(self).preempt_count() == old(self).preempt_count(),
            final(self).interrupts_id() == old(self).interrupts_id(),
            final(self).interrupt_count() == old(self).interrupt_count(),
            final(self).wf(),
    {
        let task = self.current_task()->0;
        let ghost next = CpuCoreOwnerView { current_task: None, ..self@ };
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
            res.0.preempt_guards_id() == self.preempt_guards_id(),
            res.0.preempt_count() == self.preempt_count(),
            res.0.interrupts_id() == self.interrupts_id(),
            res.0.interrupt_count() == self.interrupt_count(),
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

/// Regression proof for nested IRQ masking and LIFO restoration. It covers
/// both initially enabled and disabled IRQs.
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
    core.tracked_restore_local(inner);
    assert(!core.irq_enabled());
    assert(core.irq_guard_depth() == 1);

    core.tracked_restore_local(outer);
    assert(core.irq_guard_depth() == 0);
    assert(core.irq_enabled() == initially_enabled);
}

/// Regression proof for preemption guards released out of order and for an
/// interrupt that interrupts a preemption-disabled task, follows the bottom-half
/// protocol of `call_irq_callback_functions`, and is itself interrupted.
proof fn interrupts_and_preemption_gate_task_switch<L: CpuCoreLocalState>(
    cpu: CpuId,
    tracked locals: L,
    task: Loc,
)
    requires
        locals.belongs_to_cpu(cpu),
{
    let tracked mut core = CpuCoreOwner::new(cpu, locals, true);
    core.tracked_schedule_in(task);

    // A task-level read-side critical section.
    let tracked first = core.tracked_disable_preempt();
    let tracked second = core.tracked_disable_preempt();

    // Top half: entry masks IRQs, and the task stays current.
    let tracked entry = core.tracked_enter_interrupt();
    assert(core.current_task() == Some(task));

    // Bottom half: disable preemption, then unmask IRQs.
    let tracked bottom_half = core.tracked_disable_preempt();
    core.tracked_enable_local();
    core.lemma_preempt_guard_blocks_switch(&bottom_half);

    // A nested interrupt in the bottom half.
    let tracked nested = core.tracked_enter_interrupt();
    assert(core.interrupt_count() == 2);
    core.tracked_exit_interrupt(nested);

    // The bottom half masks IRQs, forgets that guard and drops its preemption guard.
    let tracked _forgotten = core.tracked_disable_local();
    core.tracked_enable_preempt(bottom_half);
    core.tracked_exit_interrupt(entry);
    assert(core.interrupt_count() == 0);
    assert(core.irq_enabled());

    // Task guards are released in the opposite of LIFO order.
    core.tracked_enable_preempt(first);
    core.lemma_preempt_guard_blocks_switch(&second);
    core.tracked_enable_preempt(second);

    let switched = core.tracked_schedule_out();
    assert(switched == task);
}

/// Unordered collection of live guards of one kind on a CPU.
///
/// Every live guard owns a distinct ticket in `live`, so a guard is live only
/// while `count()` is positive.
tracked struct CpuGuardCounter {
    live: GhostSetAuth<nat>,
    ghost next: nat,
}

impl CpuGuardCounter {
    closed spec fn wf(&self) -> bool {
        forall|ticket: nat| #[trigger] self.live@.contains(ticket) ==> ticket < self.next
    }

    closed spec fn id(&self) -> Loc {
        self.live.id()
    }

    closed spec fn count(&self) -> nat {
        self.live@.len()
    }

    proof fn new() -> (tracked res: Self)
        ensures
            res.wf(),
            res.count() == 0,
    {
        let tracked (live, _) = GhostSetAuth::new(Set::empty());
        CpuGuardCounter { live, next: 0 }
    }

    proof fn tracked_acquire(tracked &mut self) -> (tracked ticket: GhostSingleton<nat>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).count() == old(self).count() + 1,
            ticket.id() == old(self).id(),
    {
        let tracked ticket = self.live.insert(self.next);
        self.next = self.next + 1;
        ticket
    }

    proof fn tracked_release(tracked &mut self, tracked ticket: GhostSingleton<nat>)
        requires
            old(self).wf(),
            ticket.id() == old(self).id(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).count() + 1 == old(self).count(),
    {
        ticket.agree(&self.live);
        self.live.delete_singleton(ticket);
    }
}

} // verus!
