// A cell permission is Objective only when its stored value is. Otherwise a
// thread could park its `ViewSeen` in a cell, publish the permission through
// an atomic invariant, and let another thread read that view back without
// synchronizing. CI expects this file to be rejected.
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::prelude::*;
use vstd::thread_view::*;

verus! {

pub struct Parked;

impl InvariantPredicate<vstd::cell::CellId, PointsTo<Tracked<ViewSeen>>> for Parked {
    open spec fn inv(id: vstd::cell::CellId, perm: PointsTo<Tracked<ViewSeen>>) -> bool {
        perm.id() == id
    }
}

fn park(view: Tracked<ViewSeen>) {
    let (cell, Tracked(perm)) = PCell::new(view);
    let tracked _published = AtomicInvariant::<_, _, Parked>::new(cell.id(), perm, 0);
}

} // verus!
