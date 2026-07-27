// SPDX-License-Identifier: MPL-2.0
//! Proof model for CPU-local state.
//!
//! A CPU-local object is modeled as one logical value for every CPU in its
//! configured domain.
//! [`CpuLocalInstance`] owns the authoritative map, while
//! [`CpuLocalPointsTo`] is the exclusive points-to resource for one CPU's
//! entry. Distinct CPUs therefore have independently owned resources and may
//! operate on them concurrently.
//!
//! This module only defines the resource algebra used by CPU-local clients. It
//! does not yet connect the resources to executable CPU-local storage,
//! preemption guards, or scheduler transitions. Those layers should keep the
//! authoritative instance in an invariant and transfer each points-to resource
//! into the corresponding CPU core's proof state.
use vstd::{
    prelude::*,
    resource::{
        Loc,
        map::{GhostMapAuth, GhostPointsTo, GhostSubmap},
    },
};

use crate::specs::mm::cpu::CpuId;
use crate::specs::task::cpu_core::CpuCoreLocalState;

verus! {

/// Authoritative logical contents of one CPU-local object.
///
/// The domain is fixed at allocation time. Updating a value requires both this
/// authority and the matching [`CpuLocalPointsTo`], so the executable invariant
/// cannot change a CPU's entry without its exclusive per-CPU permission.
pub tracked struct CpuLocalInstance<V> {
    auth: GhostMapAuth<CpuId, V>,
}

/// CPU-local points-to resources that have not yet been distributed.
///
/// A newly allocated model returns all resources in this collection. CPU setup
/// can split them into individual [`CpuLocalPointsTo`] resources and install
/// each resource in the corresponding CPU core's proof state.
pub tracked struct CpuLocalPointsToSet<V> {
    points_to: GhostSubmap<CpuId, V>,
}

/// Exclusive ownership of one CPU's entry in a CPU-local object.
///
/// Two live points-to resources associated with the same
/// [`CpuLocalInstance`] necessarily refer to different CPUs. Holding this
/// token does not by itself establish that the holder is currently executing
/// on that CPU; the scheduler glue must additionally bind `cpu()` to its
/// current-CPU token.
pub tracked struct CpuLocalPointsTo<V> {
    points_to: GhostPointsTo<CpuId, V>,
}

impl<V> CpuCoreLocalState for CpuLocalPointsTo<V> {
    open spec fn belongs_to_cpu(self, cpu: CpuId) -> bool {
        self.cpu() == cpu
    }

    open spec fn local_key(self) -> Seq<Loc> {
        seq![self.id()]
    }
}

impl<V> View for CpuLocalInstance<V> {
    type V = Map<CpuId, V>;

    closed spec fn view(&self) -> Self::V {
        self.auth@
    }
}

impl<V> View for CpuLocalPointsToSet<V> {
    type V = Map<CpuId, V>;

    closed spec fn view(&self) -> Self::V {
        self.points_to@
    }
}

impl<V> CpuLocalInstance<V> {
    /// Allocates proof state for CPU-local contents described by `initial`.
    ///
    /// Allocation returns the authoritative state and exclusive ownership of
    /// every points-to resource. No executable storage is allocated by this
    /// proof function.
    pub proof fn new(initial: Map<CpuId, V>) -> (tracked res: (
        CpuLocalInstance<V>,
        CpuLocalPointsToSet<V>,
    ))
        ensures
            res.0.id() == res.1.id(),
            res.0@ == initial,
            res.1@ == initial,
            res.0.cpus() == initial.dom(),
            res.1.cpus() == initial.dom(),
    {
        let tracked (auth, points_to) = GhostMapAuth::new(initial);
        (CpuLocalInstance { auth }, CpuLocalPointsToSet { points_to })
    }

    /// Identity shared by the authority and all of its points-to resources.
    pub closed spec fn id(&self) -> Loc {
        self.auth.id()
    }

    /// CPUs represented by this CPU-local object.
    pub open spec fn cpus(&self) -> Set<CpuId> {
        self@.dom()
    }

    /// The value currently associated with `cpu`.
    pub open spec fn value(&self, cpu: CpuId) -> V
        recommends
            self.cpus().contains(cpu),
    {
        self@[cpu]
    }

    /// Whether this instance contains exactly the configured CPU set.
    pub open spec fn covers(&self, cpus: Set<CpuId>) -> bool {
        self.cpus() == cpus
    }
}

impl<V> CpuLocalPointsToSet<V> {
    /// Identity of the corresponding [`CpuLocalInstance`].
    pub closed spec fn id(&self) -> Loc {
        self.points_to.id()
    }

    /// CPUs whose exclusive points-to resources are still held here.
    pub open spec fn cpus(&self) -> Set<CpuId> {
        self@.dom()
    }

    /// Whether this collection currently owns `cpu`'s points-to resource.
    pub open spec fn contains(&self, cpu: CpuId) -> bool {
        self.cpus().contains(cpu)
    }

    /// Splits out exclusive ownership of one CPU's entry.
    pub proof fn tracked_take(tracked &mut self, cpu: CpuId) -> (tracked res: CpuLocalPointsTo<V>)
        requires
            old(self).contains(cpu),
        ensures
            final(self).id() == old(self).id(),
            res.id() == final(self).id(),
            res.cpu() == cpu,
            res.value() == old(self)@[cpu],
            final(self)@ == old(self)@.remove(cpu),
            final(self).cpus() == old(self).cpus().remove(cpu),
    {
        let tracked points_to = self.points_to.split_points_to(cpu);
        let tracked res = CpuLocalPointsTo { points_to };
        assert(res.value() == old(self)@[cpu]);
        res
    }

    /// Returns an individual points-to resource to this collection.
    pub proof fn tracked_return(tracked &mut self, tracked points_to: CpuLocalPointsTo<V>)
        requires
            old(self).id() == points_to.id(),
            !old(self).contains(points_to.cpu()),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.insert(points_to.cpu(), points_to.value()),
            final(self).cpus() == old(self).cpus().insert(points_to.cpu()),
    {
        self.points_to.combine_points_to(points_to.points_to);
    }
}

impl<V> CpuLocalPointsTo<V> {
    /// Identity of the corresponding [`CpuLocalInstance`].
    pub closed spec fn id(&self) -> Loc {
        self.points_to.id()
    }

    /// CPU whose entry is owned by this points-to resource.
    pub closed spec fn cpu(&self) -> CpuId {
        self.points_to.key()
    }

    /// Current logical value of this CPU's entry.
    pub closed spec fn value(&self) -> V {
        self.points_to.value()
    }

    /// Establishes agreement with the authoritative CPU-local contents.
    pub proof fn lemma_agree(tracked &self, tracked instance: &CpuLocalInstance<V>)
        requires
            self.id() == instance.id(),
        ensures
            instance.cpus().contains(self.cpu()),
            instance.value(self.cpu()) == self.value(),
    {
        self.points_to.agree(&instance.auth);
    }

    /// Updates this CPU's logical value.
    ///
    /// Other CPUs' points-to resources remain disjoint and retain their values.
    pub proof fn tracked_update(
        tracked &mut self,
        tracked instance: &mut CpuLocalInstance<V>,
        value: V,
    )
        requires
            old(self).id() == old(instance).id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).value() == value,
            final(instance).id() == old(instance).id(),
            final(instance).cpus() == old(instance).cpus(),
            final(instance)@ == old(instance)@.insert(old(self).cpu(), value),
    {
        self.points_to.agree(&instance.auth);
        let ghost cpu = self.cpu();
        self.points_to.update(&mut instance.auth, value);
        assert(instance@ == old(instance)@.insert(cpu, value));
        assert(instance@.dom() == old(instance)@.dom());
    }

    /// Two points-to resources belonging to one instance refer to distinct CPUs.
    pub proof fn lemma_distinct(tracked &mut self, tracked other: &CpuLocalPointsTo<V>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).value() == old(self).value(),
            final(self).cpu() != other.cpu(),
    {
        self.points_to.disjoint(&other.points_to);
    }

    /// Two live points-to resources for the same CPU cannot belong to the same
    /// CPU-local instance.
    pub proof fn lemma_same_cpu_has_distinct_instance(
        tracked &mut self,
        tracked other: &CpuLocalPointsTo<V>,
    )
        requires
            old(self).cpu() == other.cpu(),
        ensures
            final(self).id() == old(self).id(),
            final(self).cpu() == old(self).cpu(),
            final(self).value() == old(self).value(),
            final(self).id() != other.id(),
    {
        if self.id() == other.id() {
            self.points_to.disjoint(&other.points_to);
        }
    }
}

/// Regression proof for splitting, independently updating, and returning two
/// CPU-local points-to resources.
proof fn cpu_local_points_to_smoke_test<V>(
    initial: Map<CpuId, V>,
    cpu1: CpuId,
    cpu2: CpuId,
    new_value: V,
)
    requires
        initial.contains_key(cpu1),
        initial.contains_key(cpu2),
        cpu1 != cpu2,
{
    let tracked (mut instance, mut points_to_set) = CpuLocalInstance::new(initial);
    let tracked mut points_to1 = points_to_set.tracked_take(cpu1);
    let tracked mut points_to2 = points_to_set.tracked_take(cpu2);

    points_to1.lemma_distinct(&points_to2);
    let ghost old_cpu2_value = points_to2.value();
    points_to1.tracked_update(&mut instance, new_value);
    points_to2.lemma_agree(&instance);
    assert(points_to2.value() == old_cpu2_value);

    points_to_set.tracked_return(points_to1);
    points_to_set.tracked_return(points_to2);
    assert(points_to_set.cpus() == initial.dom());
}

} // verus!
