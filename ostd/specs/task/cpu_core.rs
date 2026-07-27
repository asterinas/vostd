// SPDX-License-Identifier: MPL-2.0
//! Proof model for one CPU core.
//!
//! A [`CpuCore`] permanently owns the CPU-local resources assigned to one
//! logical CPU. Scheduling changes only the core's `current_task`; it never
//! transfers those resources to the task. Runtime CPU-local access temporarily
//! opens the core into a linear [`CpuCoreHandle`] and its typed local state,
//! then restores that state before returning the core to the scheduler.
use core::marker::PhantomData;

use vstd::{prelude::*, resource::Loc};
use vstd_extra::resource::ghost_resource::excl::ExclusiveGhost;

use crate::specs::mm::cpu::CpuId;
use crate::specs::task::cpu_local::CpuLocalInstance;

verus! {

/// Logical state of a CPU core that is independent of its CPU-local payload.
pub ghost struct CpuCoreView {
    /// Stable logical CPU represented by this core.
    pub cpu: CpuId,
    /// Task currently executing on this core, or `None` while the core is idle.
    pub current_task: Option<Loc>,
    /// Ordered identities of the CPU-local resources assigned to this core.
    pub locals_key: Seq<Loc>,
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
/// A handle cannot be duplicated. Restoring a [`CpuCore`] requires returning a
/// local-state aggregate of the same type, with the same ordered resource
/// identities, whose resources all belong to this handle's CPU.
pub tracked struct CpuCoreHandle<L: CpuCoreLocalState> {
    state: ExclusiveGhost<CpuCoreView>,
    marker: PhantomData<L>,
}

/// Proof-owned state of one CPU core.
///
/// `L` is deliberately generic instead of type-erased. A subsystem can define
/// a tracked aggregate containing all CPU-local resources it needs and use that
/// aggregate as the core's payload.
pub tracked struct CpuCore<L: CpuCoreLocalState> {
    handle: CpuCoreHandle<L>,
    locals: L,
}

impl<L: CpuCoreLocalState> View for CpuCoreHandle<L> {
    type V = CpuCoreView;

    closed spec fn view(&self) -> Self::V {
        self.state.view()
    }
}

impl<L: CpuCoreLocalState> View for CpuCore<L> {
    type V = CpuCoreView;

    closed spec fn view(&self) -> Self::V {
        self.handle@
    }
}

impl<L: CpuCoreLocalState> CpuCoreHandle<L> {
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
        self.state.wf()
    }

    /// Ordered resource identities expected when restoring the core.
    pub closed spec fn expected_locals_key(&self) -> Seq<Loc> {
        self@.locals_key
    }

    /// Restores a complete core after a temporary CPU-local access.
    pub proof fn tracked_restore(tracked self, tracked locals: L) -> (tracked res: CpuCore<L>)
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
        CpuCore { handle: self, locals }
    }
}

impl<L: CpuCoreLocalState> CpuCore<L> {
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
            CpuCoreView { cpu, current_task: None, locals_key },
        );
        let tracked handle = CpuCoreHandle { state, marker: PhantomData };
        CpuCore { handle, locals }
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

    /// The core identity is valid and every local resource belongs to its CPU.
    pub closed spec fn wf(&self) -> bool {
        &&& self.handle.wf()
        &&& self.locals().belongs_to_cpu(self.cpu())
        &&& self.locals().local_key() == self.locals_key()
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
            final(self).wf(),
    {
        let ghost next = CpuCoreView {
            cpu: self.cpu(),
            current_task: Some(task),
            locals_key: self.locals_key(),
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
            final(self).wf(),
    {
        let task = self.current_task()->0;
        let ghost next = CpuCoreView {
            cpu: self.cpu(),
            current_task: None,
            locals_key: self.locals_key(),
        };
        self.handle.state.update(next);
        task
    }

    /// Temporarily separates the typed CPU-local state from the core handle.
    ///
    /// The caller may update the returned resources, but must eventually call
    /// [`CpuCoreHandle::tracked_restore`] with resources that still belong to
    /// this CPU.
    pub proof fn tracked_open(tracked self) -> (tracked res: (CpuCoreHandle<L>, L))
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
    let tracked (mut instance, mut points_to_set) = CpuLocalInstance::new(initial);
    let tracked points_to = points_to_set.tracked_take(cpu);
    let tracked mut core = CpuCore::new(cpu, points_to);

    let ghost task = instance.id();
    core.tracked_schedule_in(task);
    let tracked (handle, mut points_to) = core.tracked_open();
    assert(handle.cpu() == cpu);
    assert(handle.current_task() == Some(task));

    points_to.tracked_update(&mut instance, new_value);
    let tracked mut core = handle.tracked_restore(points_to);
    assert(core.cpu() == cpu);
    assert(core.current_task() == Some(task));

    let finished_task = core.tracked_schedule_out();
    assert(finished_task == task);
    assert(core.is_idle());
}

} // verus!
