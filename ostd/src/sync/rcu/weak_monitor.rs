// SPDX-License-Identifier: MPL-2.0
//! Fixed-online-CPU callback batches with native lock publication.
//!
//! # Verified Properties
//! An active batch is immutable. Enqueue during it targets the next epoch;
//! starting that epoch clears all CPU reports. Every accepted report covers all
//! active callbacks. A completed batch supplies a matching permit for each
//! consuming callback invocation. The monitor publishes its accumulated retire
//! observations through an actual native release/acquire lock.
use crate::specs::{
    sync::rcu::{
        grace_period::{CompletedGracePeriod, RcuCallbackSummary, RcuGracePeriod, report_covers},
        retirement::RcuRetiredFacts,
    },
    task::rcu::RunningRcuContext,
};
use vstd::{
    cell::pcell::{PCell, PointsTo},
    prelude::*,
    resource::Loc,
};
use vstd_extra::{atomic_irc11::ThreadView, auxiliary::OptionExtraFns, ownership::Inv};

use super::{
    irc11::{PendingRcuDrop, RcuCallbackWork},
    non_null::NonNullPtr,
    weak_lock::{RcuWeakLock, WeakLockGuard, WeakLockPredicate},
};
use crate::cpu::CpuId;
use alloc::vec::Vec;

verus! {

broadcast use {
    vstd::thread_view::group_thread_view_axioms,
    vstd::seq::group_seq_axioms,
    vstd::seq::Seq::to_set_ensures,
    vstd::seq::Seq::lemma_push_to_set_commute,
    vstd::set::group_set_lemmas,
};

/// Stable monitor configuration; CPU hotplug is deliberately outside this model.
pub ghost struct RcuMonitorKey {
    pub scheduler: Loc,
    pub online: Set<CpuId>,
}

/* Executable Vec queues replace no legacy path. The explicit monitor can be
 * wired to kernel IRQ/preemption guards once those paths provide capabilities.
 * Origin Rust: <none; new executable code>
 */

struct MonitorState {
    current: Vec<RcuCallbackWork>,
    next: Vec<RcuCallbackWork>,
    online: Vec<CpuId>,
    reported: Vec<CpuId>,
    tracked_gp: Tracked<Option<RcuGracePeriod>>,
    tracked_facts: Tracked<RcuRetiredFacts>,
    ghost_key: Ghost<RcuMonitorKey>,
    ghost_next_epoch: Ghost<nat>,
    ghost_handoff: Ghost<ThreadView>,
}

spec fn summaries(callbacks: Seq<RcuCallbackWork>) -> Seq<RcuCallbackSummary> {
    callbacks.map(|i: int, callback: RcuCallbackWork| callback.summary())
}

impl MonitorState {
    closed spec fn queue_inv(self, queue: Seq<RcuCallbackWork>, epoch: nat) -> bool {
        forall|i: int|
            0 <= i < queue.len() ==> {
                let callback = #[trigger] queue[i];
                &&& callback.inv()
                &&& callback.online() == self.ghost_key@.online
                &&& callback.summary().scheduler == self.ghost_key@.scheduler
                &&& callback.summary().epoch == epoch
                &&& self.ghost_handoff@.contains(callback.summary().retire_view)
                &&& self.tracked_facts@.records().contains(callback.summary().retired)
            }
    }
}

impl Inv for MonitorState {
    closed spec fn inv(self) -> bool {
        &&& self.online@.to_set() == self.ghost_key@.online
        &&& self.tracked_facts@.observed_by(self.ghost_handoff@)
        &&& self.queue_inv(self.next@, self.ghost_next_epoch@)
        &&& match self.tracked_gp@ {
            Some(gp) => {
                &&& self.current@.len() > 0
                &&& gp.inv()
                &&& gp.reported() == self.reported@.to_set()
                &&& gp.scheduler() == self.ghost_key@.scheduler
                &&& gp.online() == self.ghost_key@.online
                &&& gp.epoch() + 1 == self.ghost_next_epoch@
                &&& gp.callbacks() == summaries(self.current@)
                &&& self.queue_inv(self.current@, gp.epoch())
            },
            None => self.current@.len() == 0 && self.next@.len() == 0 && self.reported@.len() == 0,
        }
    }
}

impl MonitorState {
    fn new(
        online: Vec<CpuId>,
        Ghost(key): Ghost<RcuMonitorKey>,
        Ghost(initial): Ghost<ThreadView>,
    ) -> (res: Self)
        requires
            online@.to_set() == key.online,
        ensures
            res.inv(),
            res.ghost_key@ == key,
            res.ghost_handoff@ == initial,
    {
        Self {
            current: Vec::new(),
            next: Vec::new(),
            online,
            reported: Vec::new(),
            tracked_gp: Tracked(None),
            tracked_facts: Tracked(RcuRetiredFacts::empty()),
            ghost_key: Ghost(key),
            ghost_next_epoch: Ghost(0),
            ghost_handoff: Ghost(initial),
        }
    }

    /// Starts precisely the pending callbacks; no report survives this transition.
    fn start_next(&mut self)
        requires
            old(self).tracked_facts@.observed_by(old(self).ghost_handoff@),
            old(self).queue_inv(old(self).next@, old(self).ghost_next_epoch@),
            old(self).tracked_gp@ is None,
            old(self).current@.len() == 0,
            old(self).online@.to_set() == old(self).ghost_key@.online,
        ensures
            final(self).inv(),
            final(self).ghost_key@ == old(self).ghost_key@,
            final(self).ghost_handoff@ == old(self).ghost_handoff@,
            final(self).next@.len() == 0,
            final(self).tracked_gp@ matches Some(gp) ==> gp.reported() == Set::<CpuId>::empty(),
    {
        self.reported = Vec::new();
        if self.next.len() != 0 {
            core::mem::swap(&mut self.current, &mut self.next);
            proof {
                assert forall|i: int| 0 <= i < summaries(self.current@).len() implies {
                    let callback = #[trigger] summaries(self.current@)[i];
                    &&& callback.epoch == self.ghost_next_epoch@
                    &&& callback.scheduler == self.ghost_key@.scheduler
                    &&& callback.retired.removal.observed_by(callback.retire_view)
                } by {
                    assert(self.current@[i].inv());
                    self.current@[i].lemma_summary();
                    assert(summaries(self.current@)[i] == self.current@[i].summary());
                };
                let tracked gp = RcuGracePeriod::tracked_start(
                    self.ghost_key@.scheduler,
                    self.ghost_next_epoch@,
                    self.ghost_key@.online,
                    summaries(self.current@),
                );
                self.tracked_gp = Tracked(Some(gp));
                self.ghost_next_epoch = Ghost(self.ghost_next_epoch@ + 1);
                assert(self.queue_inv(self.current@, self.tracked_gp@->Some_0.epoch()));
                assert(self.reported@.to_set() =~= Set::<CpuId>::empty());
                assert(self.tracked_gp@->Some_0.epoch() + 1 == self.ghost_next_epoch@);
                assert(self.inv());
            }
        } else {
            proof {
                assert(self.inv());
            }
        }
    }

    fn enqueue<P: NonNullPtr + Send>(
        &mut self,
        pending: PendingRcuDrop<P>,
        Tracked(context): Tracked<&RunningRcuContext>,
    )
        requires
            old(self).inv(),
            context.inv(),
            context@.contains(old(self).ghost_handoff@),
            pending.inv(),
            pending.key().scheduler == old(self).ghost_key@.scheduler,
            pending.key().online == old(self).ghost_key@.online,
            pending.record().removal.observed_by(context@),
        ensures
            final(self).inv(),
            final(self).ghost_key@ == old(self).ghost_key@,
            context@.contains(final(self).ghost_handoff@),
    {
        let ghost summary = RcuCallbackSummary {
            scheduler: self.ghost_key@.scheduler,
            retired: pending.record(),
            epoch: self.ghost_next_epoch@,
            retire_view: context@,
        };
        let callback = pending.into_callback(Ghost(summary));
        proof {
            self.tracked_facts.borrow_mut().tracked_insert(callback.tracked_fact());
            self.ghost_handoff = Ghost(context@);
        }
        self.next.push(callback);
        // The branch is executable: current is empty exactly when idle.
        if self.current.len() == 0 {
            self.start_next();
        }
    }

    fn report(&mut self, cpu: CpuId, Tracked(context): Tracked<&mut RunningRcuContext>)
        requires
            old(self).inv(),
            old(context).inv(),
            old(context).participant().fraction() == 1real,
            cpu == old(context).cpu(),
            old(context).scheduler() == old(self).ghost_key@.scheduler,
            old(self).ghost_key@.online.contains(old(context).cpu()),
            old(context)@.contains(old(self).ghost_handoff@),
        ensures
            final(self).inv(),
            final(self).ghost_key@ == old(self).ghost_key@,
            final(self).ghost_handoff@ == old(self).ghost_handoff@,
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context)@ == old(context)@,
            final(context).participant().fraction() == 1real,
    {
        let tracked report = context.tracked_report(self.tracked_facts.borrow());
        if self.current.len() != 0 {
            proof {
                let ghost previous = self.tracked_gp@->Some_0;
                self.tracked_gp.borrow_mut().tracked_borrow_mut().tracked_report(report);
                assert(self.tracked_gp@->Some_0.callbacks() == previous.callbacks());
            }
            if !contains_cpu(&self.reported, cpu) {
                self.reported.push(cpu);
            }
            proof {
                assert(self.reported@.to_set() =~= old(self).reported@.to_set().insert(cpu));
                assert(self.tracked_gp@->Some_0.reported() == self.reported@.to_set());
            }
        }
    }

    fn is_complete(&self) -> (res: bool)
        requires
            self.inv(),
        ensures
            res == (self.tracked_gp@ matches Some(gp) && gp.reported() == self.ghost_key@.online),
    {
        if self.current.len() == 0 {
            return false;
        }
        proof {
            self.tracked_gp@->Some_0.lemma_reported_subset();
        }
        let mut index = 0;
        while index < self.online.len()
            invariant
                self.inv(),
                self.tracked_gp@ is Some,
                0 <= index <= self.online@.len(),
                forall|i: int|
                    0 <= i < index ==> self.reported@.contains(#[trigger] self.online@[i]),
            decreases self.online@.len() - index,
        {
            if !contains_cpu(&self.reported, self.online[index]) {
                proof {
                    assert(self.online@.to_set().contains(self.online@[index as int]));
                    assert(!self.reported@.to_set().contains(self.online@[index as int]));
                }
                return false;
            }
            index += 1;
        }
        proof {
            self.tracked_gp@->Some_0.lemma_reported_subset();
            assert(self.online@.to_set().subset_of(self.reported@.to_set()));
            assert(self.online@.to_set() =~= self.reported@.to_set());
        }
        true
    }

    /// Detaches a batch only after the executable mask's completion check.
    fn complete(&mut self) -> (res: CompletedRcuBatch)
        requires
            old(self).inv(),
            old(self).tracked_gp@ is Some,
            old(self).tracked_gp@->Some_0.reported() == old(self).ghost_key@.online,
        ensures
            res.inv(),
            final(self).inv(),
            final(self).ghost_key@ == old(self).ghost_key@,
            final(self).ghost_handoff@ == old(self).ghost_handoff@,
    {
        let mut callbacks = Vec::new();
        core::mem::swap(&mut callbacks, &mut self.current);
        let tracked completed = self.tracked_gp.borrow_mut().tracked_take().tracked_complete();
        let result = CompletedRcuBatch { callbacks, tracked_completed: Tracked(completed) };
        self.start_next();
        result
    }
}

/// Detached completed batch; callbacks can execute after releasing the monitor lock.
#[must_use]
pub struct CompletedRcuBatch {
    callbacks: Vec<RcuCallbackWork>,
    tracked_completed: Tracked<CompletedGracePeriod>,
}

impl Inv for CompletedRcuBatch {
    closed spec fn inv(self) -> bool {
        &&& self.tracked_completed@.inv()
        &&& self.callbacks@.len() <= self.tracked_completed@.callbacks().len()
        &&& forall|i: int|
            0 <= i < self.callbacks@.len() ==> {
                let callback = #[trigger] self.callbacks@[i];
                &&& callback.inv()
                &&& callback.online() == self.tracked_completed@.online()
                &&& callback.summary() == self.tracked_completed@.callbacks()[i]
            }
    }
}

impl CompletedRcuBatch {
    /// Consumes every capture once, supplying that capture's own completion certificate.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Supplies each capture with its own checked completion certificate.
    ///
    /// ## Functional Correctness
    ///
    /// - Consumes queued callbacks once; callbacks execute after the monitor lock is released.
    ///
    /// ## Preconditions
    ///
    /// - The detached batch is valid; the caller invokes it outside the monitor lock.
    ///
    /// ## Postconditions
    ///
    /// - Consumes the batch; callbacks and destructors may panic or diverge.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn invoke(mut self)
        requires
            self.inv(),
    {
        while self.callbacks.len() > 0
            invariant
                self.inv(),
            decreases self.callbacks@.len(),
        {
            let index = self.callbacks.len() - 1;
            let callback = self.callbacks.pop().unwrap();
            let tracked permit = self.tracked_completed.borrow().tracked_authorize(
                index as int,
                callback.tracked_fact(),
            );
            callback.invoke(Tracked(permit));
        }
    }
}

ghost struct MonitorPredicate;

impl WeakLockPredicate<PointsTo<MonitorState>> for MonitorPredicate {
    type Key = (vstd::cell::CellId, RcuMonitorKey);

    closed spec fn inv(key: Self::Key, resource: PointsTo<MonitorState>) -> bool {
        resource.id() == key.0 && resource.value().inv() && resource.value().ghost_key@ == key.1
    }

    closed spec fn required_view(resource: PointsTo<MonitorState>) -> ThreadView {
        resource.value().ghost_handoff@
    }
}

/// Explicit native lock and executable callback storage for one fixed CPU set.
pub struct Irc11RcuMonitor {
    lock: RcuWeakLock<PointsTo<MonitorState>, MonitorPredicate>,
    data: PCell<MonitorState>,
}

/// Checked-out critical section. It does not mask IRQs or disable preemption.
#[must_use]
pub struct Irc11RcuMonitorGuard<'a> {
    monitor: &'a Irc11RcuMonitor,
    tracked_guard: Tracked<WeakLockGuard<PointsTo<MonitorState>>>,
}

impl Inv for Irc11RcuMonitor {
    closed spec fn inv(self) -> bool {
        self.lock.key().0 == self.data.id()
    }
}

impl Irc11RcuMonitor {
    /// Fixed scheduler and stable online CPU set.
    pub closed spec fn key(&self) -> RcuMonitorKey {
        self.lock.key().1
    }

    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Publishes the protected state through the native lock's release path.
    ///
    /// ## Functional Correctness
    ///
    /// - Initializes empty current/next queues for the fixed online CPU set.
    ///
    /// ## Preconditions
    ///
    /// - The running context is valid and the executable CPU list represents the key's online set.
    ///
    /// ## Postconditions
    ///
    /// - Returns a valid monitor with the requested key and preserves context identity and observations.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn new(
        online: Vec<CpuId>,
        Ghost(key): Ghost<RcuMonitorKey>,
        Tracked(context): Tracked<&mut RunningRcuContext>,
    ) -> (res: Self)
        requires
            old(context).inv(),
            online@.to_set() == key.online,
        ensures
            res.inv(),
            res.key() == key,
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant() == old(context).participant(),
            final(context)@.contains(old(context)@),
    {
        let state = MonitorState::new(online, Ghost(key), Ghost(context@));
        let (data, Tracked(permission)) = PCell::new(state);
        let lock = RcuWeakLock::new(
            Tracked(permission),
            Ghost((data.id(), key)),
            Tracked(context.tracked_view_mut()),
        );
        Self { lock, data }
    }

    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Exposes mutable monitor state only after successful native acquire.
    ///
    /// ## Functional Correctness
    ///
    /// - Attempts one lock acquisition and returns an optional critical-section guard.
    ///
    /// ## Preconditions
    ///
    /// - The monitor and actual running context are valid.
    ///
    /// ## Postconditions
    ///
    /// - Success returns a matching valid guard with its required observations imported; the context is preserved.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn try_acquire<'a>(&'a self, Tracked(context): Tracked<&mut RunningRcuContext>) -> (res:
        Option<Irc11RcuMonitorGuard<'a>>)
        requires
            self.inv(),
            old(context).inv(),
        ensures
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant() == old(context).participant(),
            final(context)@.contains(old(context)@),
            res matches Some(guard) ==> guard.inv() && guard.key() == self.key()
                && guard.observed_by(final(context)@),
    {
        let (acquired, Tracked(guard)) = self.lock.try_acquire(Tracked(context.tracked_view_mut()));
        if acquired {
            Some(
                Irc11RcuMonitorGuard {
                    monitor: self,
                    tracked_guard: Tracked(guard.tracked_unwrap()),
                },
            )
        } else {
            None
        }
    }
}

impl<'a> Inv for Irc11RcuMonitorGuard<'a> {
    closed spec fn inv(self) -> bool {
        &&& self.monitor.inv()
        &&& self.tracked_guard@.lock() == self.monitor.lock.id()
        &&& MonitorPredicate::inv(self.monitor.lock.key(), self.tracked_guard@.resource())
    }
}

impl<'a> Irc11RcuMonitorGuard<'a> {
    /// Fixed scheduler and stable online CPU set.
    pub closed spec fn key(&self) -> RcuMonitorKey {
        self.monitor.key()
    }

    /// Whether the caller has imported the acquired and queued retirement observations.
    pub closed spec fn observed_by(self, view: ThreadView) -> bool {
        view.contains(self.tracked_guard@.acquired_view()) && view.contains(
            self.tracked_guard@.resource().value().ghost_handoff@,
        )
    }

    /// Whether the checked-out proof mask contains all stable online CPUs.
    pub closed spec fn complete(self) -> bool {
        self.tracked_guard@.resource().value().tracked_gp@ matches Some(gp) && gp.reported()
            == self.key().online
    }

    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Does not reclaim or reconstruct the detached allocation.
    ///
    /// ## Functional Correctness
    ///
    /// - Queues the ticket for the next batch, starting it immediately when idle.
    ///
    /// ## Preconditions
    ///
    /// - The guard and context are valid; the context observes the monitor handoff and removal; ticket scheduler/online identities match.
    ///
    /// ## Postconditions
    ///
    /// - Preserves the monitor key and its observed valid state; consumes the retirement ticket.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn enqueue<P: NonNullPtr + Send>(
        &mut self,
        pending: PendingRcuDrop<P>,
        Tracked(context): Tracked<&RunningRcuContext>,
    )
        requires
            old(self).inv(),
            context.inv(),
            old(self).observed_by(context@),
            pending.inv(),
            pending.key().scheduler == old(self).key().scheduler,
            pending.key().online == old(self).key().online,
            pending.record().removal.observed_by(context@),
        ensures
            final(self).inv(),
            final(self).key() == old(self).key(),
            final(self).observed_by(context@),
    {
        self.monitor.data.borrow_mut(
            Tracked(self.tracked_guard.borrow_mut().tracked_resource_mut()),
        ).enqueue(pending, Tracked(context));
    }

    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - A whole reader fraction excludes any active reader on this CPU.
    ///
    /// ## Functional Correctness
    ///
    /// - Records the actual CPU's quiescent report in the current batch.
    ///
    /// ## Preconditions
    ///
    /// - The valid context matches the CPU and scheduler, is online, holds the whole reader fraction, and observes the guard.
    ///
    /// ## Postconditions
    ///
    /// - Preserves context identity and native view, retaining a whole participant and valid observed monitor state.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn report(&mut self, cpu: CpuId, Tracked(context): Tracked<&mut RunningRcuContext>)
        requires
            old(self).inv(),
            old(context).inv(),
            old(self).observed_by(old(context)@),
            cpu == old(context).cpu(),
            old(context).participant().fraction() == 1real,
            old(context).scheduler() == old(self).key().scheduler,
            old(self).key().online.contains(old(context).cpu()),
        ensures
            final(self).inv(),
            final(self).key() == old(self).key(),
            final(self).observed_by(final(context)@),
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context)@ == old(context)@,
            final(context).participant().fraction() == 1real,
    {
        self.monitor.data.borrow_mut(
            Tracked(self.tracked_guard.borrow_mut().tracked_resource_mut()),
        ).report(cpu, Tracked(context));
    }

    /// Checks the executable report mask against every configured online CPU.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Reads monitor state through the checked-out resource.
    ///
    /// ## Functional Correctness
    ///
    /// - Checks the executable report collection against every configured online CPU.
    ///
    /// ## Preconditions
    ///
    /// - The monitor guard is valid.
    ///
    /// ## Postconditions
    ///
    /// - Returns exactly whether the current grace period has all required reports.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn is_complete(&self) -> (res: bool)
        requires
            self.inv(),
        ensures
            res == self.complete(),
    {
        self.monitor.data.borrow(
            Tracked(self.tracked_guard.borrow().tracked_resource()),
        ).is_complete()
    }

    /// Detaches the completed batch and unlocks before handing it to the caller.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Unlocks before exposing the detached batch for invocation.
    ///
    /// ## Functional Correctness
    ///
    /// - Detaches the completed batch and starts the next epoch with fresh reports.
    ///
    /// ## Preconditions
    ///
    /// - The guard is valid and complete; the valid running context observes its handoff.
    ///
    /// ## Postconditions
    ///
    /// - Returns a valid completed batch after releasing the guard; preserves context identity, participant, and observations.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn finish(mut self, Tracked(context): Tracked<&mut RunningRcuContext>) -> (res:
        CompletedRcuBatch)
        requires
            self.inv(),
            self.complete(),
            old(context).inv(),
            self.observed_by(old(context)@),
        ensures
            res.inv(),
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant() == old(context).participant(),
            final(context)@.contains(old(context)@),
    {
        let batch = self.monitor.data.borrow_mut(
            Tracked(self.tracked_guard.borrow_mut().tracked_resource_mut()),
        ).complete();
        self.release(Tracked(context));
        batch
    }

    ///
    /// # Verified Properties
    ///
    /// ## Safety
    ///
    /// - Returns exclusive monitor ownership through native release.
    ///
    /// ## Functional Correctness
    ///
    /// - Publishes all queued retirement observations before unlocking.
    ///
    /// ## Preconditions
    ///
    /// - The guard and actual running context are valid and the context observes the guard.
    ///
    /// ## Postconditions
    ///
    /// - Consumes the guard and preserves the context's identity, participant, and prior observations.
    /* New explicit native RCU adapter; protocol resources erase without restoring legacy scheduler glue.
     * Origin Rust: <none; new executable code>
     */
    pub fn release(self, Tracked(context): Tracked<&mut RunningRcuContext>)
        requires
            self.inv(),
            old(context).inv(),
            self.observed_by(old(context)@),
        ensures
            final(context).inv(),
            final(context).same_identity(*old(context)),
            final(context).participant() == old(context).participant(),
            final(context)@.contains(old(context)@),
    {
        self.monitor.lock.release(self.tracked_guard, Tracked(context.tracked_view_mut()));
    }
}

// Compare runtime numeric IDs while preserving their exact typed set model.
fn contains_cpu(cpus: &Vec<CpuId>, cpu: CpuId) -> (res: bool)
    ensures
        res == cpus@.contains(cpu),
{
    let mut index = 0;
    while index < cpus.len()
        invariant
            0 <= index <= cpus@.len(),
            forall|i: int| 0 <= i < index ==> #[trigger] cpus@[i] != cpu,
        decreases cpus@.len() - index,
    {
        if cpus[index].as_usize() == cpu.as_usize() {
            proof {
                crate::cpu::lemma_cpu_id_injective(cpus@[index as int], cpu);
            }
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
