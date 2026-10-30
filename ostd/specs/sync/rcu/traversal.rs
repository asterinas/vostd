// SPDX-License-Identifier: MPL-2.0
//! Paper-style Guard / SeenRemoved reasoning for historical list edges.
//!
//! # Verified Properties
//! Allocation identity, not address, indexes every edge. Native load coherence
//! and a protected predecessor rule out following an observed-dead edge into
//! the removed set. Retirement requires every historical incoming edge dead;
//! overwriting one of several incoming edges is insufficient. This is topology
//! evidence only: physical borrowing still requires the CPU/lease protocol.
use vstd::{prelude::*, resource::Loc};
use vstd_extra::{
    atomic_irc11::{AtomicHistory, AtomicPointsTo, ThreadView, load_acquire},
    ownership::Inv,
    rcu_objects::RcuBlockInfo,
};

verus! {

broadcast use {vstd::set::group_set_lemmas, vstd::atomic_weak::group_view_history};

/// AId includes the allocation registry, so unrelated roots cannot alias IDs.
pub ghost struct AllocationId {
    pub domain: Loc,
    pub object: nat,
}

/// Historical edge: predecessor allocation and its native publication timestamp.
pub type LinkEdge = (AllocationId, nat);

/// Allocation-indexed historical topology. Timestamps may have arbitrary gaps.
#[verifier::reject_recursive_types(T)]
pub ghost struct LinkGraph<T> {
    pub objects: Map<AllocationId, *mut T>,
    pub events: Map<LinkEdge, Option<AllocationId>>,
    pub incoming: Map<AllocationId, Set<LinkEdge>>,
    pub removed: Set<AllocationId>,
}

impl<T> Inv for LinkGraph<T> {
    open spec fn inv(self) -> bool {
        &&& self.incoming.dom() == self.objects.dom()
        &&& self.removed.subset_of(self.objects.dom())
        &&& forall|edge: LinkEdge| #[trigger]
            self.events.contains_key(edge) ==> {
                &&& self.objects.contains_key(edge.0)
                &&& self.events[edge] matches Some(child) ==> {
                    &&& self.objects.contains_key(child)
                    &&& self.incoming[child].contains(edge)
                }
            }
    }
}

impl<T> LinkGraph<T> {
    pub open spec fn empty() -> Self {
        Self {
            objects: Map::empty(),
            events: Map::empty(),
            incoming: Map::empty(),
            removed: Set::empty(),
        }
    }

    /// Registers an actual typed block certificate, retaining full pointer provenance.
    pub proof fn register(self, tracked info: &RcuBlockInfo<T>) -> (res: Self)
        requires
            self.inv(),
            info.inv(),
            !self.objects.contains_key(AllocationId { domain: info.domain(), object: info.obj() }),
        ensures
            res.inv(),
            res.events == self.events,
            res.removed == self.removed,
            res.objects == self.objects.insert(
                AllocationId { domain: info.domain(), object: info.obj() },
                info.ptr(),
            ),
            res.incoming == self.incoming.insert(
                AllocationId { domain: info.domain(), object: info.obj() },
                Set::empty(),
            ),
    {
        let id = AllocationId { domain: info.domain(), object: info.obj() };
        Self {
            objects: self.objects.insert(id, info.ptr()),
            incoming: self.incoming.insert(id, Set::empty()),
            ..self
        }
    }

    /// Appends a publication or null unlink. Removed allocations cannot be republished.
    pub proof fn publish(
        self,
        source: AllocationId,
        timestamp: nat,
        child: Option<AllocationId>,
    ) -> (res: Self)
        requires
            self.inv(),
            self.objects.contains_key(source),
            !self.removed.contains(source),
            !self.events.contains_key((source, timestamp)),
            child matches Some(id) ==> self.objects.contains_key(id) && !self.removed.contains(id),
        ensures
            res.inv(),
            res.objects == self.objects,
            res.removed == self.removed,
            res.events == self.events.insert((source, timestamp), child),
            res.incoming == match child {
                Some(id) => self.incoming.insert(id, self.incoming[id].insert((source, timestamp))),
                None => self.incoming,
            },
    {
        let incoming = match child {
            Some(id) => self.incoming.insert(id, self.incoming[id].insert((source, timestamp))),
            None => self.incoming,
        };
        let result = Self {
            incoming,
            events: self.events.insert((source, timestamp), child),
            ..self
        };
        assert(result.incoming.dom() =~= self.incoming.dom());
        assert forall|edge: LinkEdge| #[trigger] result.events.contains_key(edge) implies {
            &&& result.objects.contains_key(edge.0)
            &&& result.events[edge] matches Some(id) ==> {
                &&& result.objects.contains_key(id)
                &&& result.incoming[id].contains(edge)
            }
        } by {
            if edge != (source, timestamp) {
                assert(self.events.contains_key(edge));
            }
        };
        result
    }

    /// Relates all messages of one native link location to exact allocation IDs.
    pub open spec fn native_history(
        self,
        source: AllocationId,
        history: AtomicHistory<*mut T>,
    ) -> bool {
        forall|timestamp: nat|
            history.contains_timestamp(timestamp) ==> {
                &&& self.events.contains_key((source, timestamp))
                &&& match #[trigger] self.events[(source, timestamp)] {
                    Some(child) => equal(history.value(timestamp), self.objects[child]),
                    None => history.value(timestamp).addr() == 0,
                }
            }
    }
}

/// SeenRemoved(D, LV): observed removals and per-predecessor link lower bounds.
pub ghost struct SeenRemoved {
    pub removed: Set<AllocationId>,
    pub links: Map<AllocationId, nat>,
}

impl SeenRemoved {
    pub open spec fn seen_at(self, source: AllocationId) -> nat {
        if self.links.contains_key(source) {
            self.links[source]
        } else {
            0
        }
    }

    pub open spec fn dead(self, edge: LinkEdge) -> bool {
        self.removed.contains(edge.0) || self.seen_at(edge.0) > edge.1
    }

    pub open spec fn sound<T>(self, graph: LinkGraph<T>) -> bool {
        &&& self.bounds(graph)
        &&& self.removed.subset_of(graph.removed)
        &&& forall|child: AllocationId| #[trigger]
            self.removed.contains(child) ==> {
                &&& graph.incoming.contains_key(child)
                &&& forall|edge: LinkEdge| #[trigger]
                    graph.incoming[child].contains(edge) ==> self.dead(edge)
            }
    }

    /// Every link lower bound names a real event, never a fabricated future timestamp.
    pub open spec fn bounds<T>(self, graph: LinkGraph<T>) -> bool {
        forall|source: AllocationId| #[trigger]
            self.links.contains_key(source) ==> graph.events.contains_key(
                (source, self.links[source]),
            )
    }

    /// Joins a coherent link observation without losing any previously dead edge.
    pub proof fn observe<T>(
        self,
        graph: LinkGraph<T>,
        source: AllocationId,
        timestamp: nat,
    ) -> (res: Self)
        requires
            self.sound(graph),
            self.seen_at(source) <= timestamp,
            graph.events.contains_key((source, timestamp)),
        ensures
            res.sound(graph),
            res.removed == self.removed,
            res.links == self.links.insert(source, timestamp),
    {
        let result = Self { removed: self.removed, links: self.links.insert(source, timestamp) };
        assert forall|child: AllocationId| #[trigger] result.removed.contains(child) implies {
            &&& graph.incoming.contains_key(child)
            &&& forall|edge: LinkEdge| #[trigger]
                graph.incoming[child].contains(edge) ==> result.dead(edge)
        } by {
            assert forall|edge: LinkEdge| #[trigger]
                graph.incoming[child].contains(edge) implies result.dead(edge) by {
                assert(self.dead(edge));
                assert(result.seen_at(edge.0) >= self.seen_at(edge.0));
            };
        };
        result
    }

    /// The topology retirement rule consumes evidence for every historical incoming edge.
    pub proof fn retire<T>(self, graph: LinkGraph<T>, child: AllocationId) -> (res: (
        Self,
        LinkGraph<T>,
    ))
        requires
            graph.inv(),
            self.sound(graph),
            graph.objects.contains_key(child),
            forall|edge: LinkEdge| #[trigger]
                graph.incoming[child].contains(edge) ==> self.dead(edge),
        ensures
            res.1.inv(),
            res.0.sound(res.1),
            res.0.removed == self.removed.insert(child),
            res.0.links == self.links,
            res.1.removed == graph.removed.insert(child),
            res.1.objects == graph.objects,
            res.1.events == graph.events,
            res.1.incoming == graph.incoming,
    {
        let observed = Self { removed: self.removed.insert(child), links: self.links };
        let graph = LinkGraph { removed: graph.removed.insert(child), ..graph };
        assert forall|id: AllocationId| #[trigger] observed.removed.contains(id) implies {
            &&& graph.incoming.contains_key(id)
            &&& forall|edge: LinkEdge| #[trigger]
                graph.incoming[id].contains(edge) ==> observed.dead(edge)
        } by {
            assert forall|edge: LinkEdge| #[trigger]
                graph.incoming[id].contains(edge) implies observed.dead(edge) by {
                assert(self.dead(edge));
            };
        };
        (observed, graph)
    }
}

/// Guard(t, X, G), with allocation-indexed protection and an entry-time expired set.
pub ghost struct TraversalGuard {
    pub reader: Loc,
    pub expired: Set<AllocationId>,
    pub protected: Set<AllocationId>,
    pub observed: SeenRemoved,
}

impl TraversalGuard {
    pub open spec fn inv<T>(self, graph: LinkGraph<T>) -> bool {
        &&& graph.inv()
        &&& self.observed.sound(graph)
        &&& self.expired.subset_of(self.observed.removed)
        &&& self.protected.disjoint(self.observed.removed)
        &&& self.protected.subset_of(graph.objects.dom())
    }

    /// Native coherence plus historical-edge identity proves the child's non-expiration.
    /// `observed_view` is an actual previously seen message view, not a fabricated token.
    pub proof fn protect_link<T>(
        self,
        graph: LinkGraph<T>,
        source: AllocationId,
        child: AllocationId,
        tracked points_to: &AtomicPointsTo<*mut T>,
        start: ThreadView,
        after: ThreadView,
        ptr: *mut T,
        timestamp: nat,
        message_view: ThreadView,
        observed_view: ThreadView,
    ) -> (res: Self)
        requires
            self.inv(graph),
            self.protected.contains(source),
            graph.native_history(source, points_to.hist()),
            graph.events.contains_pair((source, timestamp), Some(child)),
            load_acquire(*points_to, start, after, ptr, timestamp, message_view),
            self.observed.links.contains_key(source) ==> {
                &&& start.contains(observed_view)
                &&& points_to.get_timestamp(observed_view) == Some(self.observed.seen_at(source))
            },
        ensures
            res.inv(graph),
            res.reader == self.reader,
            res.expired == self.expired,
            res.protected == self.protected.insert(child),
            res.observed.removed == self.observed.removed,
            res.observed.links == self.observed.links.insert(source, timestamp),
            !self.expired.contains(child),
            !self.observed.removed.contains(child),
            equal(ptr, graph.objects[child]),
    {
        if self.observed.links.contains_key(source) {
            points_to.get_timestamp_monotonic(start, observed_view);
        }
        assert(self.observed.seen_at(source) <= timestamp);
        assert(graph.incoming[child].contains((source, timestamp)));
        if self.observed.removed.contains(child) {
            assert(self.observed.dead((source, timestamp)));
            assert(false);
        }
        let observed = self.observed.observe(graph, source, timestamp);
        Self { protected: self.protected.insert(child), observed, ..self }
    }
}

/// A single still-live incoming edge prevents retirement, regardless of other unlinks.
pub proof fn live_incoming_blocks_retire<T>(
    graph: LinkGraph<T>,
    observed: SeenRemoved,
    child: AllocationId,
    edge: LinkEdge,
)
    requires
        graph.incoming.contains_key(child),
        graph.incoming[child].contains(edge),
        observed.bounds(graph),
        !observed.removed.contains(edge.0),
        forall|timestamp: nat| #[trigger]
            graph.events.contains_key((edge.0, timestamp)) ==> timestamp <= edge.1,
    ensures
        !observed.dead(edge),
        !(forall|incoming: LinkEdge| #[trigger]
            graph.incoming[child].contains(incoming) ==> observed.dead(incoming)),
{
    if observed.links.contains_key(edge.0) {
        assert(graph.events.contains_key((edge.0, observed.links[edge.0])));
    }
}

/// Two incoming edges, gapped timestamps, unlink, retirement, and ABA identity regression.
pub proof fn linked_list_unlink_regression<T>(
    tracked source: &RcuBlockInfo<T>,
    tracked second_source: &RcuBlockInfo<T>,
    tracked child: &RcuBlockInfo<T>,
    tracked reused: &RcuBlockInfo<T>,
)
    requires
        source.inv(),
        second_source.inv(),
        child.inv(),
        reused.inv(),
        source.domain() == second_source.domain(),
        source.domain() == child.domain(),
        source.domain() == reused.domain(),
        source.obj() < second_source.obj() < child.obj() < reused.obj(),
        child.ptr().addr() == reused.ptr().addr(),
{
    let source_id = AllocationId { domain: source.domain(), object: source.obj() };
    let second_id = AllocationId { domain: second_source.domain(), object: second_source.obj() };
    let child_id = AllocationId { domain: child.domain(), object: child.obj() };
    let reused_id = AllocationId { domain: reused.domain(), object: reused.obj() };
    let graph = LinkGraph::empty().register(source);
    let graph = graph.register(second_source);
    let graph = graph.register(child);
    let graph = graph.register(reused);
    let graph = graph.publish(source_id, 3, Some(child_id));
    let graph = graph.publish(second_id, 11, Some(child_id));
    let graph = graph.publish(source_id, 8, None);
    let observed = SeenRemoved { removed: Set::empty(), links: Map::empty().insert(source_id, 8) };
    live_incoming_blocks_retire(graph, observed, child_id, (second_id, 11));
    let graph = graph.publish(second_id, 19, None);
    let observed = observed.observe(graph, second_id, 19);
    let (observed, graph) = observed.retire(graph, child_id);
    let graph = graph.publish(source_id, 27, Some(reused_id));
    assert(graph.events[(source_id, 3)] == Some(child_id));
    assert(graph.events[(source_id, 27)] == Some(reused_id));
    assert(child_id != reused_id);
    assert(graph.removed.contains(child_id) && !graph.removed.contains(reused_id));
}

/// Constructs the regression's certificates; its aliasing addresses grant no memory access.
proof fn constructed_unlink_regression<T>(ptr: *mut T)
    requires
        ptr.addr() != 0,
{
    let tracked mut domain = vstd_extra::rcu_objects::RcuDomainAuth::tracked_new();
    let tracked (source, _) = domain.tracked_register(ptr);
    let tracked (second, _) = domain.tracked_register(ptr);
    let tracked (child, _) = domain.tracked_register(ptr);
    let tracked (reused, _) = domain.tracked_register(ptr);
    linked_list_unlink_regression(&source, &second, &child, &reused);
}

} // verus!
