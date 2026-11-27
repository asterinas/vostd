// A failed compare_exchange reports the value it actually read. If its spec
// claimed the expected value instead, the contradiction with the history would
// prove `false`. CI expects this file to be rejected.
use core::sync::atomic::Ordering;
use vstd::atomic_weak::PAtomicWeakUsize;
use vstd::prelude::*;
use vstd::thread_view::*;

verus! {

fn failed_compare_exchange_is_consistent() {
    let (atomic, Tracked(mut pt), Tracked(mut view), Ghost(_ts)) = PAtomicWeakUsize::new(0);
    let ghost history = pt.hist();
    proof_decl! {
        let tracked release_view = ReleaseViewSeen::new();
    }
    let (result, Tracked(_acquire_view), Ghost(update)) = atomic.compare_exchange(
        5,
        6,
        Ordering::Relaxed,
        Ordering::Relaxed,
        Tracked(&mut view),
        Tracked(release_view),
        Tracked(&mut pt),
    );
    if let Err(_) = result {
        proof {
            assert(history.contains_timestamp(update.load_timestamp));
            assert(history.get(update.load_timestamp)->Some_0.0 == 0);
            assert(false);
        }
    }
}

} // verus!
