// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;

use crate::{
    sync::GuardTransfer,
    trap::irq::{disable_local, DisabledLocalIrqGuard},
};

#[cfg(feature = "irc11")]
use {
    crate::cpu::CpuId,
    vstd::resource::Loc,
    vstd_extra::{
        atomic_irc11::{ThreadView, ViewSeen},
        scheduler_thread_view::ScheduledTaskView,
    },
};

#[cfg(feature = "irc11")]
verus! {

/// Linear proof state carried by a task while it is running on one CPU.
///
/// The scheduler creates this value by checking out the task's persistent
/// IRC11 view. Weak-memory operations borrow the contained [`ViewSeen`], and
/// schedule-out must consume the context to return the updated view to the
/// same scheduler registry.
pub tracked struct RunningTaskContext {
    scheduled_view: ScheduledTaskView<Loc, CpuId>,
}

impl View for RunningTaskContext {
    type V = ThreadView;

    closed spec fn view(&self) -> ThreadView {
        self.scheduled_view@
    }
}

impl RunningTaskContext {
    /// Wraps the view checked out by the scheduler for a running interval.
    pub proof fn tracked_from_scheduled_view(
        tracked scheduled_view: ScheduledTaskView<Loc, CpuId>,
    ) -> (tracked res: Self)
        ensures
            res.registry_id() == scheduled_view.registry_id(),
            res.task() == scheduled_view.task(),
            res.cpu() == scheduled_view.cpu(),
            res@ == scheduled_view@,
    {
        RunningTaskContext { scheduled_view }
    }

    /// Scheduler registry that owns the parked form of this task view.
    pub closed spec fn registry_id(&self) -> Loc {
        self.scheduled_view.registry_id()
    }

    /// Task whose subjective view is currently checked out.
    pub closed spec fn task(&self) -> Loc {
        self.scheduled_view.task()
    }

    /// CPU on which this running interval was started.
    pub closed spec fn cpu(&self) -> CpuId {
        self.scheduled_view.cpu()
    }

    /// Borrows the unique native IRC11 view for weak-memory operations.
    pub proof fn tracked_borrow_irc11_view_mut(tracked &mut self) -> (tracked res: &mut ViewSeen)
        ensures
            (*res)@ == old(self)@,
            final(self).registry_id() == old(self).registry_id(),
            final(self).task() == old(self).task(),
            final(self).cpu() == old(self).cpu(),
            final(self)@ == (*final(res))@,
    {
        let tracked thread_view = self.scheduled_view.tracked_borrow_thread_view_mut();
        thread_view.tracked_borrow_mut()
    }

    /// Ends the running interval and returns the scheduler's checked-out token.
    pub proof fn tracked_into_scheduled_view(tracked self) -> (tracked res: ScheduledTaskView<
        Loc,
        CpuId,
    >)
        ensures
            res.registry_id() == self.registry_id(),
            res.task() == self.task(),
            res.cpu() == self.cpu(),
            res@ == self@,
    {
        self.scheduled_view
    }
}

} // verus!
/// A guard that prevents preemption until it is dropped.
///
/// The task scheduler and its CPU-local preemption count are not active yet.
/// Until they are restored, this guard masks local IRQs, including the timer
/// interrupt that could request preemption.
/// Nested guards must be dropped in reverse order.
#[verus_verify]
#[clippy::has_significant_drop]
#[must_use]
#[derive(Debug)]
pub struct DisabledPreemptGuard {
    irq_guard: DisabledLocalIrqGuard,
}

impl !Send for DisabledPreemptGuard {}

impl !Sync for DisabledPreemptGuard {}

verus! {

impl DisabledPreemptGuard {
    /// Whether this guard will restore local IRQs when dropped.
    pub closed spec fn restores_irqs_spec(self) -> bool {
        self.irq_guard.was_enabled_spec()
    }
}

impl GuardTransfer for DisabledPreemptGuard {
    fn transfer_to(&mut self) -> (ret: Self)
        ensures
            ret.restores_irqs_spec() == old(self).restores_irqs_spec(),
            !final(self).restores_irqs_spec(),
    {
        Self { irq_guard: self.irq_guard.transfer_to() }
    }
}

} // verus!
/// Disables preemption.
#[verus_verify]
pub fn disable_preempt() -> DisabledPreemptGuard {
    DisabledPreemptGuard {
        irq_guard: disable_local(),
    }
}
