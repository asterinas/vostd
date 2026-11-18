// Non-atomic memory permissions are subjective under iRC11: publishing one
// through an atomic invariant would let another thread use it without
// synchronizing. CI expects this file to be rejected.
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::prelude::*;

verus! {

pub struct Published;

impl InvariantPredicate<vstd::cell::CellId, PointsTo<u64>> for Published {
    open spec fn inv(id: vstd::cell::CellId, perm: PointsTo<u64>) -> bool {
        perm.id() == id
    }
}

fn publish() {
    let (cell, Tracked(perm)) = PCell::new(7u64);
    let tracked _published = AtomicInvariant::<_, _, Published>::new(cell.id(), perm, 0);
}

} // verus!
