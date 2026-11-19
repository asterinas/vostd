// SPDX-License-Identifier: MPL-2.0
//! Single-owner links: the historical topology of an embedded owning RCU slot.
//!
//! # Verified Properties
//! The graph is derived from the slot's complete native publication history,
//! never supplied by a reader. Each allocation is owned by this slot; this is
//! not the multi-incoming-edge shared-node representation. The source identity
//! comes from a physically protected predecessor in a different allocation
//! domain. Its pointer in this graph is only a heterogeneous identity label.
use vstd::{prelude::*, resource::Loc};
use vstd_extra::{
    atomic_irc11::{AtomicHistory, AtomicPointsTo, ThreadView},
    ownership::Inv,
    rcu_objects::owned_root::{RcuRootOwnedGhost, rcu_owned_root_history_inv},
};

use super::{
    retirement::RcuRemovalObservation,
    traversal::{AllocationId, LinkEdge, LinkGraph, SeenRemoved, TraversalGuard},
};

verus! {

broadcast use {
    vstd::set::group_set_lemmas,
    vstd::set::Set::lemma_map_by_contains,
    vstd::atomic_weak::group_view_history,
};

/// Injectively lifts this slot's finite object set into allocation identities.
pub open spec fn allocation_ids(domain: Loc, objects: Set<nat>) -> Set<AllocationId> {
    objects.map_by(|obj: nat| AllocationId { domain, object: obj }, |id: AllocationId| id.object)
}

/// Topology and protection returned by the very load that issued a physical lease.
#[verifier::reject_recursive_types(T)]
pub ghost struct RcuLinkObservation<T> {
    pub graph: LinkGraph<T>,
    pub guard: TraversalGuard,
    pub source: AllocationId,
    pub child: Option<AllocationId>,
    pub timestamp: nat,
    pub reader: Loc,
    pub generation: nat,
    pub start_view: ThreadView,
}

impl<T> Inv for RcuLinkObservation<T> {
    open spec fn inv(self) -> bool {
        &&& self.guard.inv(self.graph)
        &&& self.guard.reader == self.reader
        &&& self.guard.protected.contains(self.source)
        &&& self.graph.events.contains_pair((self.source, self.timestamp), self.child)
        &&& self.guard.observed.links.contains_pair(self.source, self.timestamp)
        &&& self.child matches Some(child) ==> {
            &&& self.guard.protected.contains(child)
            &&& !self.guard.expired.contains(child)
            &&& !self.guard.observed.removed.contains(child)
        }
    }
}

/// No-incoming-edge evidence retained alongside the exact linear retirement ticket.
#[verifier::reject_recursive_types(T)]
pub ghost struct RcuLinkRemoval<T> {
    pub graph: LinkGraph<T>,
    pub observed: SeenRemoved,
    pub source: AllocationId,
    pub child: AllocationId,
    pub removal: RcuRemovalObservation,
}

impl<T> Inv for RcuLinkRemoval<T> {
    open spec fn inv(self) -> bool {
        &&& self.graph.inv()
        &&& self.observed.sound(self.graph)
        &&& self.observed.removed.contains(self.child)
        &&& self.observed.links.contains_pair(self.source, self.removal.timestamp)
        &&& self.graph.events.contains_pair((self.source, self.removal.timestamp), None)
        &&& self.child.domain == self.removal.root
        &&& forall|edge: LinkEdge| #[trigger]
            self.graph.incoming[self.child].contains(edge) ==> self.observed.dead(edge)
    }
}

/// The exact one-source graph represented by an owning slot's typed history.
pub open spec fn owned_link_graph<T>(
    root: RcuRootOwnedGhost<T, ()>,
    removed: Set<nat>,
    source: AllocationId,
    source_ptr: *mut T,
) -> LinkGraph<T> {
    let objects = Map::new(
        allocation_ids(root.domain(), root.infos().dom()).insert(source),
        |id: AllocationId|
            if id == source {
                source_ptr
            } else {
                root.infos()[id.object].ptr()
            },
    );
    let events = Map::new(
        root.root().publications().dom().map_by(|ts: nat| (source, ts), |edge: LinkEdge| edge.1),
        |edge: LinkEdge|
            match root.root().publications()[edge.1] {
                Some(obj) => Some(AllocationId { domain: root.domain(), object: obj }),
                None => None,
            },
    );
    LinkGraph {
        objects,
        events,
        incoming: Map::new(
            objects.dom(),
            |id: AllocationId| events.dom().filter(|edge: LinkEdge| events[edge] == Some(id)),
        ),
        removed: allocation_ids(root.domain(), removed),
    }
}

/// Refines every native message, including stale messages and gapped timestamps.
pub proof fn lemma_owned_link_graph<T>(
    root: RcuRootOwnedGhost<T, ()>,
    history: AtomicHistory<*mut T>,
    removed: Set<nat>,
    source: AllocationId,
    source_ptr: *mut T,
)
    requires
        rcu_owned_root_history_inv(history, root),
        removed.subset_of(root.infos().dom()),
        source.domain != root.domain(),
    ensures
        owned_link_graph(root, removed, source, source_ptr).inv(),
        owned_link_graph(root, removed, source, source_ptr).native_history(source, history),
{
    let graph = owned_link_graph(root, removed, source, source_ptr);
    assert(graph.incoming.dom() =~= graph.objects.dom());
    assert(graph.removed.subset_of(graph.objects.dom()));
    assert forall|edge: LinkEdge| #[trigger] graph.events.contains_key(edge) implies {
        &&& graph.objects.contains_key(edge.0)
        &&& graph.events[edge] matches Some(child) ==> {
            &&& graph.objects.contains_key(child)
            &&& graph.incoming[child].contains(edge)
        }
    } by {
        assert(root.root().publications().contains_key(edge.1));
        if let Some(obj) = root.root().publications()[edge.1] {
            assert(root.root().objects().contains_key(obj));
            assert(root.infos().contains_key(obj));
        }
    };
    assert forall|ts: nat| history.contains_timestamp(ts) implies {
        &&& graph.events.contains_key((source, ts))
        &&& match #[trigger] graph.events[(source, ts)] {
            Some(child) => equal(history.value(ts), graph.objects[child]),
            None => history.value(ts).addr() == 0,
        }
    } by {
        assert(root.root().publications().contains_key(ts));
        if let Some(obj) = root.root().publications()[ts] {
            assert(equal(root.infos()[obj].ptr(), history.value(ts)));
        }
    };
}

/// The reader's actual native view bounds every historical edge it knows dead.
pub proof fn lemma_observed_link_removals<T>(
    tracked points_to: &AtomicPointsTo<*mut T>,
    graph: LinkGraph<T>,
    source: AllocationId,
    domain: Loc,
    removals: Map<nat, RcuRemovalObservation>,
    view: ThreadView,
) -> (res: (SeenRemoved, ThreadView))
    requires
        graph.inv(),
        graph.native_history(source, points_to.hist()),
        allocation_ids(domain, removals.dom()).subset_of(graph.removed),
        forall|ts: nat|
            points_to.hist().contains_timestamp(ts) ==> graph.events.contains_key((source, ts)),
        forall|obj: nat| #[trigger]
            removals.contains_key(obj) ==> {
                &&& points_to.get_timestamp(removals[obj].message_view) == Some(
                    removals[obj].timestamp,
                )
                &&& graph.events.contains_key((source, removals[obj].timestamp))
                &&& forall|edge: LinkEdge| #[trigger]
                    graph.incoming[AllocationId { domain, object: obj }].contains(edge) ==> {
                        &&& edge.0 == source
                        &&& edge.1 < removals[obj].timestamp
                    }
            },
    ensures
        res.0.sound(graph),
        res.0.removed == allocation_ids(
            domain,
            removals.dom().filter(|obj: nat| removals[obj].observed_by(view)),
        ),
        res.0.links.dom().subset_of(Set::empty().insert(source)),
        res.0.links.contains_key(source) ==> {
            &&& view.contains(res.1)
            &&& points_to.get_timestamp(res.1) == Some(res.0.seen_at(source))
        },
    decreases removals.len(),
{
    let visible = removals.dom().filter(|obj: nat| removals[obj].observed_by(view));
    if visible.is_empty() {
        assert(allocation_ids(domain, visible) =~= Set::<AllocationId>::empty());
        (SeenRemoved { removed: Set::empty(), links: Map::empty() }, view)
    } else {
        let obj = visible.choose();
        let rest = removals.remove(obj);
        assert(allocation_ids(domain, rest.dom()).subset_of(graph.removed));
        let (previous, previous_view) = lemma_observed_link_removals(
            points_to,
            graph,
            source,
            domain,
            rest,
            view,
        );
        let (links, observed_view) = if previous.links.contains_key(source) && previous.seen_at(
            source,
        ) >= removals[obj].timestamp {
            (previous.links, previous_view)
        } else {
            (Map::empty().insert(source, removals[obj].timestamp), removals[obj].message_view)
        };
        let child = AllocationId { domain, object: obj };
        let observed = SeenRemoved { removed: previous.removed.insert(child), links };
        assert forall|id: AllocationId| #[trigger] observed.removed.contains(id) implies {
            &&& graph.incoming.contains_key(id)
            &&& forall|edge: LinkEdge| #[trigger]
                graph.incoming[id].contains(edge) ==> observed.dead(edge)
        } by {
            assert forall|edge: LinkEdge| #[trigger]
                graph.incoming[id].contains(edge) implies observed.dead(edge) by {
                if id == child {
                    assert(edge.0 == source && edge.1 < removals[obj].timestamp);
                } else {
                    assert(previous.dead(edge));
                    assert(observed.seen_at(edge.0) >= previous.seen_at(edge.0));
                }
            };
        };
        assert(observed.removed =~= allocation_ids(domain, visible));
        (observed, observed_view)
    }
}

} // verus!
