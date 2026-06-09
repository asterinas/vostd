// SPDX-License-Identifier: MPL-2.0
use alloc::vec::Vec;

use vstd::prelude::*;
use vstd_extra::raw_callback::RawCallback;

use crate::specs::{
    mm::cpu::{AtomicCpuSet, CpuSet},
    sync::{
        rcu as rcu_spec,
        weak_memory::WeakAtomicBool,
    },
};
use crate::sync::{LocalIrqDisabled, SpinLock};

verus! {

pub type Callbacks = Vec<RcuCallback>;

type MonitorAtomicBool =
    WeakAtomicBool<(), rcu_spec::RcuMonitorFlagGhost, rcu_spec::RcuMonitorFlagInv>;

/// RCU-specific wrapper around a type-erased executable callback.
///
/// `RawCallback` is intentionally proof-opaque. The summary records the object
/// identity that the monitor invariant will use to decide when this callback is
/// safe to run after a grace period.
#[must_use]
pub struct RcuCallback {
    raw: RawCallback,
    summary: Ghost<rcu_spec::RcuCallbackSummary>,
}

impl View for RcuCallback {
    type V = rcu_spec::RcuCallbackSummary;

    closed spec fn view(&self) -> rcu_spec::RcuCallbackSummary {
        self.summary@
    }
}

impl RcuCallback {
    /// Converts a raw callback into an RCU callback, given a proof that the callback is
    /// safe to run after a grace period.
    #[inline]
    pub fn from_raw(
        raw: RawCallback,
        Tracked(cert): Tracked<rcu_spec::RcuCallbackSafety>,
    ) -> (res: Self)
        ensures
            res@ == cert@,
    {
        let ghost summary = cert@;
        Self { raw, summary: Ghost(summary) }
    }

    /// Runs the underlying callback. The reclaim-safety precondition is not
    /// encoded here yet; the next layer will prove it from the monitor/global
    /// RCU invariant before invoking this method.
    #[inline]
    #[verifier::external_body]
    pub unsafe fn call_once(self) {
        unsafe {
            self.raw.call_once();
        }
    }
}

pub open spec fn callback_summaries(callbacks: Callbacks) -> Seq<rcu_spec::RcuCallbackSummary> {
    Seq::new(callbacks@.len(), |i: int| callbacks@[i]@)
}

pub(super) struct GracePeriod {
    callbacks: Callbacks,
    cpu_mask: AtomicCpuSet,
    is_complete: bool,
}

impl GracePeriod {
    closed spec fn callback_summaries(self) -> Seq<rcu_spec::RcuCallbackSummary> {
        callback_summaries(self.callbacks)
    }

    closed spec fn has_pending_work(self) -> bool {
        !self.is_complete || self.callback_summaries().len() > 0
    }
}

pub(super) struct State {
    current_gp: GracePeriod,
    next_callbacks: Callbacks,
}

impl State {
    closed spec fn pending_summaries(self) -> Seq<rcu_spec::RcuCallbackSummary> {
        self.current_gp.callback_summaries().add(callback_summaries(self.next_callbacks))
    }

    closed spec fn has_pending_work(self) -> bool {
        self.current_gp.has_pending_work() || callback_summaries(self.next_callbacks).len() > 0
    }
}

/// A RCU monitor ensures the completion of _grace periods_ by keeping track
/// of each CPU's passing _quiescent states_.
pub(super) struct RcuMonitor {
    pub(super) is_monitoring: MonitorAtomicBool,
    pub(super) state: SpinLock<State, LocalIrqDisabled>,
}

impl RcuMonitor {
    closed spec fn wf(self) -> bool {
        &&& self.is_monitoring.well_formed()
        &&& self.state.type_inv()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

} // verus!

// use vstd::{
//     atomic_ghost::AtomicBool, atomic_with_ghost, predicate::Predicate as DataPredicate, prelude::*,
// };
// use vstd_extra::ownership::Inv;

// use crate::{
//     specs::mm::cpu::{AtomicCpuSet, CpuSet},
//     sync::{AtomicDataWithOwner, LocalIrqDisabled, SpinLock, once::Predicate as OncePredicate},
// };

// verus! {

// // This thing can be very tricky to deal with
// // type Callbacks = VecDeque<Box<dyn FnOnce() + Send + 'static>>;
// pub(super) struct GracePeriod {
//     // callbacks: Callbacks,
//     cpu_mask: AtomicCpuSet,
//     is_complete: bool,
// }

// pub(super) struct State {
//     current_gp: GracePeriod,
//     // next_callbacks: Callbacks,
// }

// /// Owner of this [`RcuMonitor`].
// pub(super) tracked struct RcuMonitorOwner {}

// impl DataPredicate<RcuMonitor> for RcuMonitorOwner {
//     closed spec fn predicate(&self, v: RcuMonitor) -> bool {
//         true
//     }
// }

// impl RcuMonitor {
//     #[verifier::type_invariant]
//     closed spec fn type_inv(self) -> bool {
//         self.wf()
//     }
// }

// pub(super) struct RcuMonitorPred;

// impl OncePredicate<AtomicDataWithOwner<RcuMonitor, RcuMonitorOwner>> for RcuMonitorPred {
//     closed spec fn inv(self, v: AtomicDataWithOwner<RcuMonitor, RcuMonitorOwner>) -> bool {
//         &&& v.permission@.predicate(v.data)
//         &&& v.data.inv()
//     }
// }

// impl Inv for RcuMonitor {
//     closed spec fn inv(self) -> bool {
//         self.wf()
//     }
// }

// impl Inv for State {
//     closed spec fn inv(self) -> bool {
//         self.current_gp.inv()
//     }
// }

// impl Inv for GracePeriod {
//     closed spec fn inv(self) -> bool {
//         true
//     }
// }

// #[verus_verify]
// impl RcuMonitor {
//     /// Creates a new RCU monitor.
//     pub(super) fn new() -> Self {
//         let state = SpinLock::new(State::new());
//         proof {
//             use_type_invariant(&state);
//             assert(state.type_inv());
//         }
//         let res = RcuMonitor {
//             is_monitoring: AtomicBool::new(Ghost(state), false, Tracked(false)),
//             state,
//         };

//         proof {
//             use_type_invariant(&res.state);
//             assert(res.state.type_inv());
//             assert(res.inv());
//         }
//         res
//     }

//     /// Creates a new RCU monitor together with its tracked owner for `Once`.
//     #[verus_spec(r =>
//         ensures
//             r.inv(),
//             r.data.inv(),
//             RcuMonitorPred.inv(r),
//     )]
//     pub(super) fn new_data() -> AtomicDataWithOwner<RcuMonitor, RcuMonitorOwner> {
//         let data = Self::new();
//         proof {
//             use_type_invariant(&data);
//             assert(data.inv());
//         }
//         AtomicDataWithOwner { data, permission: Tracked(RcuMonitorOwner {  }) }
//     }

//     fn is_monitoring(&self) -> bool {
//         proof {
//             use_type_invariant(self);
//         }
//         self.is_monitoring.load()
//     }

//     fn set_monitoring(&self, value: bool) {
//         proof {
//             use_type_invariant(self);
//         }
//         atomic_with_ghost! {
//             self.is_monitoring => store(value);
//             ghost g => {
//                 g = value;
//             }
//         }
//     }
// }

// impl State {
//     fn new() -> (res: Self)
//         ensures
//             res.inv(),
//     {
//         Self { current_gp: GracePeriod::new() }
//     }
// }

// impl GracePeriod {
//     fn new() -> (res: Self)
//         ensures
//             res.inv(),
//     {
//         Self { cpu_mask: AtomicCpuSet::new(CpuSet::new_empty()), is_complete: true }
//     }
// }

// } // verus!
// /*use alloc::collections::VecDeque;
// use core::sync::atomic::{
//     AtomicBool,
//     Ordering::{self, Relaxed},
// };

// use crate::{
//     cpu::{AtomicCpuSet, CpuId, CpuSet, PinCurrentCpu},
//     prelude::*,
//     sync::SpinLock,
//     task::atomic_mode::AsAtomicModeGuard,
// };

// impl RcuMonitor {
//     /// Creates a new RCU monitor.
//     ///
//     /// This function is used to initialize a singleton instance of `RcuMonitor`.
//     /// The singleton instance is globally accessible via the `RCU_MONITOR`.
//     pub(super) fn new() -> Self {
//         Self {
//             is_monitoring: AtomicBool::new(false),
//             state: SpinLock::new(State::new()),
//         }
//     }

//     pub(super) unsafe fn finish_grace_period(&self) {
//         // Fast path
//         if !self.is_monitoring.load(Relaxed) {
//             return;
//         }

//         // Check if the current GP is complete after passing the quiescent state
//         // on the current CPU. If GP is complete, take the callbacks of the current
//         // GP.
//         let callbacks = {
//             let mut state = self.state.disable_irq().lock();
//             let cpu = state.as_atomic_mode_guard().current_cpu();
//             if state.current_gp.is_complete() {
//                 return;
//             }

//             state.current_gp.finish_grace_period(cpu);
//             if !state.current_gp.is_complete() {
//                 return;
//             }

//             // Now that the current GP is complete, take its callbacks
//             let current_callbacks = state.current_gp.take_callbacks();

//             // Check if we need to watch for a next GP
//             if !state.next_callbacks.is_empty() {
//                 let callbacks = core::mem::take(&mut state.next_callbacks);
//                 state.current_gp.restart(callbacks);
//             } else {
//                 self.is_monitoring.store(false, Relaxed);
//             }

//             current_callbacks
//         };

//         // Invoke the callbacks to notify the completion of GP
//         for f in callbacks {
//             (f)();
//         }
//     }

//     pub(super) fn after_grace_period<F>(&self, f: F)
//     where
//         F: FnOnce() + Send + 'static,
//     {
//         let mut state = self.state.disable_irq().lock();

//         state.next_callbacks.push_back(Box::new(f));

//         if !state.current_gp.is_complete() {
//             return;
//         }

//         let callbacks = core::mem::take(&mut state.next_callbacks);
//         state.current_gp.restart(callbacks);
//         self.is_monitoring.store(true, Relaxed);
//     }
// }

// impl State {
//     fn new() -> Self {
//         Self {
//             current_gp: GracePeriod::new(),
//             next_callbacks: VecDeque::new(),
//         }
//     }
// }

// impl GracePeriod {
//     fn new() -> Self {
//         Self {
//             callbacks: Callbacks::new(),
//             cpu_mask: AtomicCpuSet::new(CpuSet::new_empty()),
//             is_complete: true,
//         }
//     }

//     fn is_complete(&self) -> bool {
//         self.is_complete
//     }

//     fn finish_grace_period(&mut self, this_cpu: CpuId) {
//         self.cpu_mask.add(this_cpu, Ordering::Relaxed);

//         if self.cpu_mask.load(Ordering::Relaxed).is_full() {
//             self.is_complete = true;
//         }
//     }

//     fn take_callbacks(&mut self) -> Callbacks {
//         core::mem::take(&mut self.callbacks)
//     }

//     fn restart(&mut self, callbacks: Callbacks) {
//         self.is_complete = false;
//         self.cpu_mask.store(&CpuSet::new_empty(), Ordering::Relaxed);
//         self.callbacks = callbacks;
//     }
// }
// */
