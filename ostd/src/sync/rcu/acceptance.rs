// SPDX-License-Identifier: MPL-2.0
//! Constructive acceptance clients for the explicit-context IRC11 path.
//!
//! These are verification clients, not boot or scheduler implementations. Their
//! contexts are constructed from real scheduler checkout and canonical core
//! registration. No nonempty subjective view or completed GP is assumed.
use vstd::{
    prelude::*,
    resource::{Loc, map::GhostMapAuth},
};
use vstd_extra::{
    atomic_irc11::ThreadView, ownership::Inv, rcu_objects::RcuDomainAuth,
    scheduler_thread_view::SchedulerThreadViewRegistry,
};

use crate::specs::{
    sync::rcu::cpu::CpuRcuParticipant,
    task::{
        cpu_core::{CpuCoreOwner, CpuCoreOwnerBinding, CpuCoreRegistration},
        rcu::RunningRcuContext,
    },
};

use super::{
    irc11::{Irc11RcuOption, Irc11RcuReadGuard},
    weak_monitor::{Irc11RcuMonitor, RcuMonitorKey},
};
use crate::{cpu::CpuId, task::RunningTaskContext};
use alloc::{boxed::Box, sync::Arc, vec::Vec};

verus! {

broadcast use {
    vstd::atomic_weak::group_view_history,
    vstd::seq::Seq::to_set_ensures,
    vstd::seq::Seq::lemma_push_to_set_commute,
};

proof fn registered_context(cpu: CpuId) -> (tracked res: (
    RunningRcuContext,
    SchedulerThreadViewRegistry<Loc, CpuId>,
))
    ensures
        res.0.inv(),
        res.0.cpu() == cpu,
        res.0.participant().fraction() == 1real,
        res.1.wf(),
        res.1.id() == res.0.view_registry(),
        res.1.task_runs_on(res.0.task(), cpu),
{
    let tracked mut views = SchedulerThreadViewRegistry::new();
    let ghost task = views.id();
    views.tracked_register_task(task);
    views.tracked_register_cpu(cpu);
    let tracked participant = CpuRcuParticipant::new(cpu, ThreadView::empty());
    participant.lemma_cpu_core_local_state();
    let tracked mut core = CpuCoreOwner::new(cpu, participant);
    let tracked (mut registry, _) = GhostMapAuth::<CpuId, CpuCoreRegistration>::new(Map::empty());
    let tracked entry = registry.insert(cpu, core.registration());
    let tracked binding = CpuCoreOwnerBinding::tracked_new(entry, &core);
    let tracked scheduled = views.tracked_schedule_in(task, cpu);
    core.tracked_schedule_in(task);
    let tracked task = RunningTaskContext::tracked_from_scheduled_view(scheduled);
    let tracked context = RunningRcuContext::tracked_attach(task, core, binding);
    (context, views)
}

proof fn return_context(
    tracked context: RunningRcuContext,
    tracked views: &mut SchedulerThreadViewRegistry<Loc, CpuId>,
)
    requires
        context.inv(),
        context.participant().fraction() == 1real,
        old(views).wf(),
        old(views).id() == context.view_registry(),
        old(views).task_runs_on(context.task(), context.cpu()),
    ensures
        final(views).wf(),
        final(views).task_is_stored(context.task()),
{
    let tracked binding = context.tracked_binding();
    let tracked (task, mut core) = context.tracked_detach();
    core.tracked_schedule_out();
    views.tracked_schedule_out(task.tracked_into_scheduled_view());
    // The same CPU and task resume with at least the old native observations.
    let tracked scheduled = views.tracked_schedule_in(context.task(), context.cpu());
    core.tracked_schedule_in(context.task());
    let tracked resumed_task = RunningTaskContext::tracked_from_scheduled_view(scheduled);
    assert(resumed_task@.contains(context@));
    ThreadView::contains_trans(resumed_task@, context@, core.locals().view());
    let tracked resumed = RunningRcuContext::tracked_attach(resumed_task, core, binding);
    assert(resumed@.contains(context@));
    let tracked (task, mut core) = resumed.tracked_detach();
    core.tracked_schedule_out();
    views.tracked_schedule_out(task.tracked_into_scheduled_view());
}

/* Acceptance code uses the same public API that the eventual kernel glue will
 * call. It is not installed as a runtime kernel entry point.
 * Origin Rust: <none; new executable code>
 */

fn box_read_update_and_callback(cpu: CpuId) {
    let tracked (mut context, mut views) = registered_context(cpu);
    let ghost online = Set::empty().insert(cpu);
    let root = Irc11RcuOption::<Box<usize>>::new(
        Some(Box::new(7)),
        Tracked(&mut context),
        Ghost(online),
    );
    let mut cpus = Vec::new();
    cpus.push(cpu);
    proof {
        assert(cpus@.to_set() =~= online);
    }
    let monitor = Irc11RcuMonitor::new(
        cpus,
        Ghost(RcuMonitorKey { scheduler: context.scheduler(), online }),
        Tracked(&mut context),
    );

    let first = root.read(Tracked(&mut context));
    let nested = root.read(Tracked(&mut context));
    if let Some(reference) = first.try_get() {
        let _value = reference.deref_target();
    }
    let retired_first = root.update(Some(Box::new(8)), Tracked(&mut context));
    let ghost first_view = context@;
    let retired_second = root.update(None, Tracked(&mut context));
    // Queueing needs no reclaim permit, even while the old physical lease is live.
    if let Some(mut guard) = monitor.try_acquire(Tracked(&mut context)) {
        if let Some(pending) = retired_first {
            proof {
                assert(context@.contains(first_view));
                ThreadView::contains_trans(
                    context@,
                    first_view,
                    pending.record().removal.message_view,
                );
            }
            guard.enqueue(pending, Tracked(&context));
        }
        if let Some(pending) = retired_second {
            guard.enqueue(pending, Tracked(&context));
        }
        guard.release(Tracked(&mut context));
    }
    nested.close(Tracked(&mut context));
    first.close(Tracked(&mut context));
    assert(context.participant().fraction() == 1real);

    if let Some(mut guard) = monitor.try_acquire(Tracked(&mut context)) {
        guard.report(cpu, Tracked(&mut context));
        if guard.is_complete() {
            guard.finish(Tracked(&mut context)).invoke();
        } else {
            guard.release(Tracked(&mut context));
        }
    }
    // A second batch needs a new report; finishing the first never authorizes it.

    if let Some(mut guard) = monitor.try_acquire(Tracked(&mut context)) {
        guard.report(cpu, Tracked(&mut context));
        if guard.is_complete() {
            guard.finish(Tracked(&mut context)).invoke();
        } else {
            guard.release(Tracked(&mut context));
        }
    }
    proof {
        return_context(context, &mut views);
    }
}

/* This client exercises the ArcRef adapter without Arc::clone on the read path.
 * Origin Rust: <none; new executable code>
 */

fn arc_and_null_reads(cpu: CpuId) {
    let tracked (mut context, mut views) = registered_context(cpu);
    let ghost online = Set::empty().insert(cpu);
    let root = Irc11RcuOption::<Arc<usize>>::new(None, Tracked(&mut context), Ghost(online));
    let empty = root.read(Tracked(&mut context));
    let _empty_reference = empty.try_get();
    empty.close(Tracked(&mut context));
    let _old_null = root.update(Some(Arc::new(11)), Tracked(&mut context));
    let guard = root.read(Tracked(&mut context));
    if let Some(reference) = guard.try_get() {
        let _value = reference.deref_target();
    }
    guard.close(Tracked(&mut context));
    proof {
        return_context(context, &mut views);
    }
}

/* Non-null reads can call get directly, including after replacement.
 * Origin Rust: <none; new executable code>
 */

fn nonnull_read(cpu: CpuId) {
    let tracked (mut context, mut views) = registered_context(cpu);
    let root = super::irc11::Irc11Rcu::new(
        Box::new(29usize),
        Tracked(&mut context),
        Ghost(Set::empty().insert(cpu)),
    );
    let guard = root.read(Tracked(&mut context));
    let reference = guard.get();
    let _value = reference.deref_target();
    guard.close(Tracked(&mut context));
    let _retired = root.update(Box::new(31), Tracked(&mut context));
    let later = root.read(Tracked(&mut context));
    let reference = later.get();
    let _value = reference.deref_target();
    let _conditional = later.compare_exchange(Box::new(37), Tracked(&mut context));
    proof {
        return_context(context, &mut views);
    }
}

/* One link is embedded in the allocation protected by the parent guard. The
 * physical borrow prevents closing the parent before the child's read closes.
 * Origin Rust: <none; new executable code>
 */

struct ListSource {
    next: Irc11RcuOption<Box<usize>>,
}

impl ListSource {
    #[verifier::type_invariant]
    closed spec fn well_formed(self) -> bool {
        self.next.inv()
    }

    fn new(next: Irc11RcuOption<Box<usize>>) -> (res: Self)
        requires
            next.inv(),
        ensures
            res.next == next,
    {
        Self { next }
    }
}

/* Constructs every premise of the owning-link client from empty scheduler and
 * allocation registries. This is an acceptance entry point, not kernel glue.
 * Origin Rust: <none; new executable acceptance code>
 */

fn linked_list_from_initialization(cpu: CpuId) {
    let tracked (mut context, mut views) = registered_context(cpu);
    let ghost online = Set::empty().insert(cpu);
    let tracked (parent_domain, child_domain) = RcuDomainAuth::tracked_new_pair();
    let ghost parent_id = parent_domain.id();
    let next = Irc11RcuOption::<Box<usize>>::new_with_domain(
        Some(Box::new(43)),
        Tracked(&mut context),
        Ghost(online),
        Ghost(true),
        Tracked(child_domain),
        Ghost(|_: <Box<usize> as super::non_null::NonNullPtr>::Permission| true),
    );
    let ghost child_key = next.key();
    let source = Box::new(ListSource::new(next));
    let ghost condition = |owned: <Box<ListSource> as super::non_null::NonNullPtr>::Permission|
        owned.value().next.key() == child_key;
    let root = Irc11RcuOption::<Box<ListSource>>::new_with_domain(
        Some(source),
        Tracked(&mut context),
        Ghost(online),
        Ghost(false),
        Tracked(parent_domain),
        Ghost(condition),
    );
    let parent = root.read(Tracked(&mut context));
    assert(parent.is_some());
    assert(parent.root_key().domain == parent_id);
    assert(parent.resource()->Some_0.value().next.key() == child_key);
    assert(parent.root_key().domain != child_key.domain);
    assert(parent.reader_in(context));
    assert(context.participant().fraction() + parent.fraction() == 1real);
    // Reject contradiction only after all initialization and read obligations
    // have been established; no preconstructed guard is assumed here.
    #[cfg(rcu_reject_link_initialized_vacuity)]
    assert(false);
    #[cfg(rcu_reject_link_wrong_publication)]
    {
        // A replacement with a different online set violates the fixed parent
        // predicate even though both owning pointers are individually valid.
        let different = Irc11RcuOption::<Box<usize>>::new(
            None,
            Tracked(&mut context),
            Ghost(Set::empty()),
        );
        let _rejected = root.update(
            Some(Box::new(ListSource::new(different))),
            Tracked(&mut context),
        );
    }
    linked_list_unlink_and_callback(parent, cpu, Tracked(&mut context));
    proof {
        return_context(context, &mut views);
    }
}

/* This is the paper's integrated single-step traversal client, not a general
 * concurrent linked-list implementation or a kernel scheduling entry point.
 * Origin Rust: <none; new executable code>
 */

fn linked_list_physical_step<'a>(
    parent_guard: Irc11RcuReadGuard<'a, Box<ListSource>>,
    Tracked(context): Tracked<&mut RunningRcuContext>,
)
    requires
        parent_guard.inv(),
        parent_guard.is_some(),
        old(context).inv(),
        parent_guard.reader_in(*old(context)),
        old(context)@.contains(parent_guard.start_view()),
        parent_guard.root_key().domain != parent_guard.resource()->Some_0.value().next.key().domain,
        // The list's client invariant places each embedded link in this scheduler.
        parent_guard.resource()->Some_0.value().next.key().scheduler == old(context).scheduler(),
        parent_guard.resource()->Some_0.value().next.key().online.contains(old(context).cpu()),
    ensures
        final(context).inv(),
        final(context).same_identity(*old(context)),
        final(context).participant().fraction() == old(context).participant().fraction()
            + parent_guard.fraction(),
{
    let parent = parent_guard.try_get().unwrap();
    let source = parent.deref_target();
    proof {
        use_type_invariant(source);
    }
    // This acquire is made through the physically protected predecessor.
    let child_guard = source.next.read_link(&parent_guard, Tracked(context));
    let ghost observation = child_guard.link_observation()->Some_0;
    assert(observation.inv());
    assert(observation.source == parent_guard.allocation()->Some_0);
    assert(observation.child == child_guard.allocation());
    assert(observation.start_view == parent_guard.start_view());
    assert(observation.generation == parent_guard.generation());
    #[cfg(rcu_reject_link_parent_close)]
    parent_guard.close(Tracked(context));
    if let Some(child) = child_guard.try_get() {
        let _value = child.deref_target();
    }
    child_guard.close(Tracked(context));
    // Closing the lease does not erase the persistent topology snapshot.
    assert(observation.guard.protected.contains(observation.source));
    parent_guard.close(Tracked(context));
}

/* A physically embedded owning link follows the full topology/lease/unlink/GP
 * callback path. The list client supplies its layout and distinct-domain facts;
 * this is not a shared-node/multi-predecessor list implementation.
 * Origin Rust: <none; new executable code>
 */

fn linked_list_unlink_and_callback<'a>(
    parent_guard: Irc11RcuReadGuard<'a, Box<ListSource>>,
    cpu: CpuId,
    Tracked(context): Tracked<&mut RunningRcuContext>,
)
    requires
        parent_guard.inv(),
        parent_guard.is_some(),
        old(context).inv(),
        parent_guard.reader_in(*old(context)),
        old(context)@.contains(parent_guard.start_view()),
        old(context).cpu() == cpu,
        old(context).participant().fraction() + parent_guard.fraction() == 1real,
        parent_guard.root_key().domain != parent_guard.resource()->Some_0.value().next.key().domain,
        parent_guard.resource()->Some_0.value().next.key().scheduler == old(context).scheduler(),
        parent_guard.resource()->Some_0.value().next.key().online == Set::empty().insert(cpu),
        parent_guard.resource()->Some_0.value().next.key().nullable,
    ensures
        final(context).inv(),
        final(context).same_identity(*old(context)),
        final(context).participant().fraction() == 1real,
{
    #[cfg(rcu_reject_link_vacuity)]
    assert(false);
    let ghost online = Set::empty().insert(cpu);
    let mut cpus = Vec::new();
    cpus.push(cpu);
    proof {
        assert(cpus@.to_set() =~= online);
    }
    let monitor = Irc11RcuMonitor::new(
        cpus,
        Ghost(RcuMonitorKey { scheduler: context.scheduler(), online }),
        Tracked(context),
    );
    let parent = parent_guard.try_get().unwrap();
    let source = parent.deref_target();
    proof {
        use_type_invariant(source);
    }
    let child_guard = source.next.read_link(&parent_guard, Tracked(context));
    let ghost observation = child_guard.link_observation()->Some_0;
    if let Some(child) = child_guard.try_get() {
        let _value = child.deref_target();
        assert(observation.child is Some);
        assert(!observation.guard.expired.contains(observation.child->Some_0));
        assert(observation.guard.protected.contains(observation.child->Some_0));
    }
    let pending = source.next.unlink(&parent_guard, Tracked(context));
    if let Some(pending) = pending {
        let ghost removal = pending.link_removal()->Some_0;
        assert(removal.inv());
        assert(removal.observed.removed.contains(removal.child));
        assert(removal.child.object == pending.record().obj);
        if let Some(mut monitor_guard) = monitor.try_acquire(Tracked(context)) {
            monitor_guard.enqueue(pending, Tracked(&*context));
            #[cfg(rcu_reject_link_report)]
            monitor_guard.report(cpu, Tracked(context));
            // Queueing is legal while child and parent leases still exist.
            monitor_guard.release(Tracked(context));
        }
    }
    // The unlink cannot invalidate an already acquired physical borrow.

    if let Some(child) = child_guard.try_get() {
        let _value = child.deref_target();
    }
    child_guard.close(Tracked(context));
    assert(observation.guard.protected.contains(observation.source));
    parent_guard.close(Tracked(context));
    assert(context.participant().fraction() == 1real);
    if let Some(mut monitor_guard) = monitor.try_acquire(Tracked(context)) {
        monitor_guard.report(cpu, Tracked(context));
        if monitor_guard.is_complete() {
            monitor_guard.finish(Tracked(context)).invoke();
        } else {
            monitor_guard.release(Tracked(context));
        }
    }
}

/* Native-history acceptance for the complementary topology lemma. This test
 * dereferences nothing: allocation registration alone grants no physical lease.
 * Origin Rust: <none; new executable code>
 */

fn native_link_hindsight(ptr: *mut usize)
    requires
        ptr.addr() != 0,
{
    use crate::specs::sync::rcu::traversal::{AllocationId, LinkGraph, SeenRemoved, TraversalGuard};
    use vstd_extra::{atomic_irc11::PAtomicWeakPtr, rcu_objects::RcuDomainAuth};
    let tracked mut domain = RcuDomainAuth::tracked_new();
    let tracked (source, _) = domain.tracked_register(ptr);
    let tracked (child, _) = domain.tracked_register(ptr);
    let (atomic, Tracked(points_to), Tracked(mut view), Ghost(timestamp)) = PAtomicWeakPtr::new(
        ptr,
    );
    let ghost source_id = AllocationId { domain: source.domain(), object: source.obj() };
    let ghost child_id = AllocationId { domain: child.domain(), object: child.obj() };
    let ghost graph;
    proof {
        let initial = LinkGraph::empty().register(&source);
        let initial = initial.register(&child);
        graph = initial.publish(source_id, timestamp, Some(child_id));
    }
    let ghost guard = TraversalGuard {
        reader: domain.id(),
        expired: Set::empty(),
        protected: Set::empty().insert(source_id),
        observed: SeenRemoved { removed: Set::empty(), links: Map::empty() },
    };
    let ghost start = view@;
    let loaded = atomic.load(
        core::sync::atomic::Ordering::Acquire,
        Tracked(&mut view),
        Tracked(&points_to),
    );
    proof {
        assert(loaded.2@.timestamp == timestamp);
        let protected = guard.protect_link(
            graph,
            source_id,
            child_id,
            &points_to,
            start,
            view@,
            loaded.0,
            loaded.2@.timestamp,
            loaded.2@.message_view,
            start,
        );
        assert(protected.protected.contains(source_id));
        assert(protected.protected.contains(child_id));
        assert(!protected.expired.contains(child_id));
    }
}

// Negative acceptance configuration: report must reject the live reader fraction.
#[cfg(rcu_reject_active_report)]
fn reject_report_with_active_reader(cpu: CpuId) {
    let tracked (mut context, _) = registered_context(cpu);
    let root = Irc11RcuOption::<Box<usize>>::new(
        Some(Box::new(41)),
        Tracked(&mut context),
        Ghost(Set::empty().insert(cpu)),
    );
    let guard = root.read(Tracked(&mut context));
    let tracked learned = crate::specs::sync::rcu::retirement::RcuRetiredFacts::empty();
    proof {
        let tracked _report = context.tracked_report(&learned);
    }
    guard.close(Tracked(&mut context));
}

} // verus!
