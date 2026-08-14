use vstd::atomic::PAtomicUsize;
use vstd::atomic_weak::PAtomicWeakUsize;
use vstd::prelude::*;

verus! {

fn sc_and_irc11_atomics_coexist() {
    let (_sc_atomic, Tracked(_sc_permission)) = PAtomicUsize::new(0);
    let (_irc11_atomic, Tracked(_irc11_points_to), Tracked(_view_seen), Ghost(_timestamp)) =
        PAtomicWeakUsize::new(0);
}

} // verus!
