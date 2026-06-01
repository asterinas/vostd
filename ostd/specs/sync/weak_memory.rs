//! Weak-memory atomic wrappers used by the verification layer.
//!
//! This module is a TCB boundary: executable atomic operations are connected to
//! Rust atomics with `external_body`, while proofs rely only on the ghost specs
//! below.  The first concrete wrapper is `AtomicUsizeW`; pointer atomics and CAS
//! should be layered on top after the view/history model stabilizes.
use core::sync::atomic::{AtomicUsize, Ordering};

use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::prelude::*;
use vstd::resource::map::{GhostMapAuth, GhostPersistentPointsTo};
use vstd::resource::Loc;
use vstd::seq::Seq;

verus! {

pub type AtomicId = Loc;

/// Logical timestamp into one atomic object's message history.
/// Timestamp 0 is always the initial message installed by `new`.
pub type Timestamp = nat;

/// A thread-local weak-memory view.
///
/// `seen[id] = ts` means this thread has advanced past all messages for `id`
/// older than `ts`; future reads from that atomic must not go backwards.
pub ghost struct WmView {
    pub seen: Map<AtomicId, Timestamp>,
}

impl WmView {
    pub open spec fn empty() -> Self {
        WmView { seen: Map::empty() }
    }

    pub open spec fn seen_at(self, id: AtomicId) -> Timestamp {
        if self.seen.contains_key(id) {
            self.seen[id]
        } else {
            // Missing entries are equivalent to only seeing the initial write.
            0nat
        }
    }

    /// Monotonically advance the view for one atomic object.
    pub open spec fn observe(self, id: AtomicId, ts: Timestamp) -> Self {
        WmView {
            seen: self.seen.insert(
                id,
                if self.seen_at(id) <= ts {
                    ts
                } else {
                    self.seen_at(id)
                },
            ),
        }
    }

    /// Pointwise maximum of two views.
    ///
    /// This is the ghost effect of an acquire read: the reader imports the
    /// release view carried by the message it read.
    pub open spec fn join(self, other: Self) -> Self {
        WmView {
            seen: Map::new(
                |id: AtomicId| self.seen.contains_key(id) || other.seen.contains_key(id),
                |id: AtomicId|
                    if self.seen_at(id) <= other.seen_at(id) {
                        other.seen_at(id)
                    } else {
                        self.seen_at(id)
                    },
            ),
        }
    }

    pub open spec fn le(self, other: Self) -> bool {
        forall|id: AtomicId| #[trigger] self.seen_at(id) <= other.seen_at(id)
    }
}

/// One message in an atomic object's modification history.
///
/// `view` is the release view published with this value. Relaxed stores publish
/// only their own timestamp; release stores publish the writer's current view.
pub ghost struct Msg<V> {
    pub value: V,
    pub view: WmView,
}

pub type History<V> = Seq<Msg<V>>;

/// User-supplied invariant predicate for a weak-memory atomic.
///
/// This mirrors `vstd::atomic_ghost::AtomicInvariantPredicate`, except the
/// predicate is over the whole message history rather than one current value.
pub trait WeakAtomicInvariantPredicate<K, V, G> {
    spec fn atomic_inv(k: K, history: History<V>, g: G) -> bool;
}

/// Authoritative ghost state for one atomic object's history.
///
/// This is intentionally a thin wrapper around vstd's map resource algebra:
/// [`GhostMapAuth`] owns the authoritative timestamp-to-message map, while `len`
/// records that the domain is the contiguous range `0..len`.
///
/// The proof-facing atomic wrapper below stores this token inside an
/// `AtomicInvariant` next to the executable atomic.
pub tracked struct HistAuth<V> {
    auth: GhostMapAuth<Timestamp, Msg<V>>,
    pub ghost len: nat,
}

impl<V> HistAuth<V> {
    pub closed spec fn id(self) -> AtomicId {
        self.auth.id()
    }

    pub closed spec fn map(self) -> Map<Timestamp, Msg<V>> {
        self.auth@
    }

    pub closed spec fn len(self) -> nat {
        self.len
    }

    pub closed spec fn history(self) -> History<V> {
        Seq::new(self.len(), |i: int| self.map()[i as nat])
    }

    pub open spec fn wf(self) -> bool {
        &&& self.len() > 0
        &&& self.map().dom() =~= Set::new(|ts: Timestamp| ts < self.len())
    }

    pub open spec fn valid_ts(self, ts: Timestamp) -> bool {
        ts < self.len()
    }

    pub open spec fn msg_at(self, ts: Timestamp) -> Msg<V>
        recommends
            self.valid_ts(ts),
    {
        self.map()[ts]
    }

    /// RC11-style relaxed readability: a read may choose any message that is
    /// not older than the thread's current view for this location.
    pub open spec fn readable(self, view: WmView, ts: Timestamp) -> bool {
        &&& self.valid_ts(ts)
        &&& view.seen_at(self.id()) <= ts
    }

    /// Append one message to the authoritative history and return a persistent
    /// snapshot for the newly allocated timestamp.
    pub proof fn append_msg(tracked &mut self, msg: Msg<V>) -> (tracked snap: MsgSnap<V>)
        requires
            old(self).wf(),
        ensures
            final(self).id() == old(self).id(),
            final(self).history() == old(self).history().push(msg),
            final(self).wf(),
            snap.id() == final(self).id(),
            snap.ts() == old(self).history().len(),
            snap.msg() == msg,
            snap.agrees_with(*final(self)),
    {
        let ghost ts = self.len();

        let tracked pt = self.auth.insert(ts, msg);
        self.len = self.len + 1;

        let tracked psnap = pt.persist();
        MsgSnap { snap: psnap }
    }
}

/// A stable proof handle for one message; a snapshot of the message.
///
/// The underlying vstd token is persistent/duplicable, so a message snapshot
/// can be copied through proofs without granting permission to mutate history.
///
/// Stores return snapshots so higher layers can connect a concrete write to
/// later ownership-transfer predicates without exposing the whole history.
pub tracked struct MsgSnap<V> {
    snap: GhostPersistentPointsTo<Timestamp, Msg<V>>,
}

impl<V> MsgSnap<V> {
    pub closed spec fn id(self) -> AtomicId {
        self.snap.id()
    }

    /// Fetch the timestamp of this specific message.
    pub closed spec fn ts(self) -> Timestamp {
        self.snap.key()
    }

    /// Fetch the ghost message value of this specific message.
    pub closed spec fn msg(self) -> Msg<V> {
        self.snap.value()
    }

    pub open spec fn agrees_with(self, auth: HistAuth<V>) -> bool {
        &&& self.id() == auth.id()
        &&& auth.valid_ts(self.ts())
        &&& self.msg() == auth.msg_at(self.ts())
    }

    pub proof fn duplicate(tracked &self) -> (tracked snap: MsgSnap<V>)
        ensures
            snap.id() == self.id(),
            snap.ts() == self.ts(),
            snap.msg() == self.msg(),
    {
        let tracked psnap = self.snap.duplicate();
        MsgSnap { snap: psnap }
    }

    pub proof fn agree(tracked &self, tracked auth: &HistAuth<V>)
        requires
            self.id() == auth.id(),
            auth.wf(),
        ensures
            self.agrees_with(*auth),
    {
        self.snap.agree(&auth.auth);
        assert(auth.map().contains_pair(self.ts(), self.msg()));
    }
}

/// Predicate adapter stored inside `AtomicInvariant`.
///
/// The invariant contains the authoritative history and user ghost state. The
/// constant pairs the user key `K` with the logical atomic id.
pub struct WeakAtomicPredUsize<Pred> {
    p: Pred,
}

impl<K, G, Pred> InvariantPredicate<(K, AtomicId), (HistAuth<usize>, G)> for WeakAtomicPredUsize<
    Pred,
> where Pred: WeakAtomicInvariantPredicate<K, usize, G> {
    open spec fn inv(k_id: (K, AtomicId), hist_g: (HistAuth<usize>, G)) -> bool {
        let (k, id) = k_id;
        let (hist, g) = hist_g;
        &&& hist.id() == id
        &&& hist.wf()
        &&& Pred::atomic_inv(k, hist.history(), g)
    }
}

/// A weak-memory atomic with an `atomic_ghost`-style invariant.
///
/// `AtomicUsizeW` remains the TCB executable wrapper. This type is the proof
/// facing wrapper: it stores the authoritative history in an `AtomicInvariant`
/// and exposes `well_formed`/`type_inv` predicates tying that history to the
/// executable atomic id. As in `vstd::atomic_ghost`, outer data structures put
/// this predicate in their own `#[verifier::type_invariant]`.
pub struct WeakAtomicUsize<K, G, Pred> {
    #[doc(hidden)]
    pub atomic: AtomicUsizeW,
    #[doc(hidden)]
    pub atomic_inv: Tracked<
        AtomicInvariant<(K, AtomicId), (HistAuth<usize>, G), WeakAtomicPredUsize<Pred>>,
    >,
}

impl<K, G, Pred> WeakAtomicUsize<K, G, Pred> {
    pub closed spec fn constant(&self) -> K {
        self.atomic_inv@.constant().0
    }

    pub closed spec fn well_formed(&self) -> bool {
        self.atomic_inv@.constant().1 == self.atomic.id()
    }

    pub closed spec fn type_inv(&self) -> bool {
        self.well_formed()
    }
}

impl<K, G, Pred> WeakAtomicUsize<K, G, Pred> where Pred: WeakAtomicInvariantPredicate<K, usize, G> {
    #[inline(always)]
    pub const fn new(Ghost(k): Ghost<K>, init: usize, Tracked(g): Tracked<G>) -> (res: Self)
        requires
            Pred::atomic_inv(k, seq![Msg { value: init, view: WmView::empty() }], g),
        ensures
            res.well_formed(),
            res.constant() == k,
    {
        let (atomic, Tracked(hist)) = AtomicUsizeW::new(init);
        let tracked pair = (hist, g);
        assert(WeakAtomicPredUsize::<Pred>::inv((k, atomic.id()), pair));
        let tracked atomic_inv = AtomicInvariant::new((k, atomic.id()), pair, 0);
        WeakAtomicUsize { atomic, atomic_inv: Tracked(atomic_inv) }
    }

    #[inline(always)]
    pub fn load_relaxed(&self, Tracked(tv): Tracked<&mut ThreadView>) -> (res: (
        usize,
        Ghost<Timestamp>,
    ))
        requires
            self.well_formed(),
    {
        let result;
        vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            let tracked (hist, g) = pair;
            result = self.atomic.load_relaxed(Tracked(&hist), Tracked(tv));
            proof {
                pair = (hist, g);
            }
        });
        result
    }

    #[inline(always)]
    pub fn load_acquire(&self, Tracked(tv): Tracked<&mut ThreadView>) -> (res: (
        usize,
        Ghost<Timestamp>,
    ))
        requires
            self.well_formed(),
    {
        let result;
        vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            let tracked (hist, g) = pair;
            result = self.atomic.load_acquire(Tracked(&hist), Tracked(tv));
            proof {
                pair = (hist, g);
            }
        });
        result
    }
}

pub struct TrueWeakAtomicInv;

impl<K, V, G> WeakAtomicInvariantPredicate<K, V, G> for TrueWeakAtomicInv {
    open spec fn atomic_inv(k: K, history: History<V>, g: G) -> bool {
        true
    }
}

/// Similar to Verus' macro [`atomic_with_ghost!`] for atomics with ghost state,
/// but for weak-memory atomics with per-thread view tokens and message histories.
/// 
/// The macro opens the atomic invariant, performs the specified operation, and
/// provides the previous history, new history, and operation snapshot to the user-
/// provided proof block. The user can then write proofs about the effects of the
/// operation on the history and thread view, using the snapshot to connect to the
/// authoritative history.
#[macro_export]
macro_rules! weak_atomic_with_ghost {
    (
        $atomic:expr => store_release($value:expr, $tv:expr);
        update $prev:ident -> $next:ident;
        snapshot $snap:ident;
        ghost $g:ident => $b:block
    ) => {
            ::vstd::prelude::verus_exec_expr! {{
            let atomic = &($atomic);
            let value = $value;
            ::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (mut hist, mut $g) = pair;
                let ghost $prev = hist.history();
                let snap_tracked = atomic.atomic.store_release(Tracked(&mut hist), $tv, value);
                let ghost $next = hist.history();

                proof {
                    let tracked $snap = snap_tracked.get();
                    $b
                }

                proof {
                    pair = (hist, $g);
                }
            });
        }}
    };
    (
        $atomic:expr => store_relaxed($value:expr, $tv:expr);
        update $prev:ident -> $next:ident;
        snapshot $snap:ident;
        ghost $g:ident => $b:block
    ) => {
            ::vstd::prelude::verus_exec_expr! {{
            let atomic = &($atomic);
            let value = $value;
            ::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (mut hist, mut $g) = pair;
                let ghost $prev = hist.history();
                let snap_tracked = atomic.atomic.store_relaxed(Tracked(&mut hist), $tv, value);
                let ghost $next = hist.history();

                proof {
                    let tracked $snap = snap_tracked.get();
                    $b
                }

                proof {
                    pair = (hist, $g);
                }
            });
        }}
    };
}

/// Explicit per-thread view token.
///
/// Passing this token through atomic operations makes the weak-memory effects
/// visible in specs instead of hiding them in global or thread-local state.
pub tracked struct ThreadView {
    pub ghost view: WmView,
}

impl View for ThreadView {
    type V = WmView;

    open spec fn view(&self) -> WmView {
        self.view
    }
}

impl ThreadView {
    pub proof fn new() -> (tracked res: Self)
        ensures
            res@ == WmView::empty(),
    {
        ThreadView { view: WmView::empty() }
    }

    pub proof fn observe(tracked &mut self, id: AtomicId, ts: Timestamp)
        ensures
            final(self)@ == old(self)@.observe(id, ts),
    {
        self.view = self.view.observe(id, ts);
    }

    pub proof fn join(tracked &mut self, view: WmView)
        ensures
            final(self)@ == old(self)@.join(view),
    {
        self.view = self.view.join(view);
    }
}

#[repr(transparent)]
#[verifier::external_body]
/// TCB wrapper around Rust's `AtomicUsize`.
///
/// The executable field is the real atomic object. The proof layer sees only
/// the specs below, plus the uninterpreted logical identity `id`.
pub struct AtomicUsizeW {
    value: AtomicUsize,
}

impl AtomicUsizeW {
    /// Logical identity of this atomic object.
    ///
    /// `id` has no runtime representation; it indexes ghost histories and
    /// thread views. The `new` spec ties the fresh history to this identity.
    pub uninterp spec fn id(&self) -> AtomicId;

    #[inline(always)]
    #[verifier::external_body]
    pub const fn new(init: usize) -> (res: (Self, Tracked<HistAuth<usize>>))
        ensures
            res.1@.id() == res.0.id(),
            res.1@.history() == seq![Msg { value: init, view: WmView::empty() }],
            res.1@.wf(),
    {
        let atomic = AtomicUsizeW { value: AtomicUsize::new(init) };
        (atomic, Tracked::assume_new())
    }

    /// Relaxed load: choose a readable message and advance only this location's
    /// timestamp in the caller's thread view.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load_relaxed(
        &self,
        Tracked(auth): Tracked<&HistAuth<usize>>,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (usize, Ghost<Timestamp>))
        requires
            auth.id() == self.id(),
            auth.wf(),
        ensures
            ({
                let ts = res.1@;
                &&& auth.readable(old(tv)@, ts)
                &&& res.0 == auth.msg_at(ts).value
                &&& final(tv)@ == old(tv)@.observe(self.id(), ts)
            }),
        opens_invariants none
        no_unwind
    {
        let value = self.value.load(Ordering::Relaxed);
        (value, Ghost::assume_new())
    }

    /// Acquire load: same readable message choice as relaxed, plus import the
    /// release view carried by the selected message.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load_acquire(
        &self,
        Tracked(auth): Tracked<&HistAuth<usize>>,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (usize, Ghost<Timestamp>))
        requires
            auth.id() == self.id(),
            auth.wf(),
        ensures
            ({
                let ts = res.1@;
                &&& auth.readable(old(tv)@, ts)
                &&& res.0 == auth.msg_at(ts).value
                &&& final(tv)@ == old(tv)@.observe(self.id(), ts).join(auth.msg_at(ts).view)
            }),
        opens_invariants none
        no_unwind
    {
        let value = self.value.load(Ordering::Acquire);
        (value, Ghost::assume_new())
    }

    /// Relaxed store: append a new message whose published view contains only
    /// this store's own timestamp.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store_relaxed(
        &self,
        Tracked(auth): Tracked<&mut HistAuth<usize>>,
        Tracked(tv): Tracked<&mut ThreadView>,
        value: usize,
    ) -> (snap: Tracked<MsgSnap<usize>>)
        requires
            old(auth).id() == self.id(),
            old(auth).wf(),
        ensures
            ({
                let ts = old(auth).history().len();
                let msg = Msg { value, view: WmView::empty().observe(self.id(), ts) };
                &&& final(auth).id() == old(auth).id()
                &&& final(auth).history() == old(auth).history().push(msg)
                &&& final(auth).wf()
                &&& final(tv)@ == old(tv)@.observe(self.id(), ts)
                &&& snap@.id() == self.id()
                &&& snap@.ts() == ts
                &&& snap@.msg() == msg
                &&& snap@.agrees_with(*final(auth))
            }),
        opens_invariants none
        no_unwind
    {
        self.value.store(value, Ordering::Relaxed);
        Tracked::assume_new()
    }

    /// Release store: append a new message carrying the writer's current view,
    /// then advance the writer's view for this location.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store_release(
        &self,
        Tracked(auth): Tracked<&mut HistAuth<usize>>,
        Tracked(tv): Tracked<&mut ThreadView>,
        value: usize,
    ) -> (snap: Tracked<MsgSnap<usize>>)
        requires
            old(auth).id() == self.id(),
            old(auth).wf(),
        ensures
            ({
                let ts = old(auth).history().len();
                let msg = Msg { value, view: old(tv)@.observe(self.id(), ts) };
                &&& final(auth).id() == old(auth).id()
                &&& final(auth).history() == old(auth).history().push(msg)
                &&& final(auth).wf()
                &&& final(tv)@ == old(tv)@.observe(self.id(), ts)
                &&& snap@.id() == self.id()
                &&& snap@.ts() == ts
                &&& snap@.msg() == msg
                &&& snap@.agrees_with(*final(auth))
            }),
        opens_invariants none
        no_unwind
    {
        self.value.store(value, Ordering::Release);
        Tracked::assume_new()
    }
}

#[cfg(verus_keep_ghost)]
fn smoke_test_weak_atomic_with_ghost() {
    let atomic = WeakAtomicUsize::<(), (), TrueWeakAtomicInv>::new(Ghost(()), 0, Tracked(()));
    let tracked mut tv = ThreadView::new();
    weak_atomic_with_ghost! {
        atomic => store_release(1, Tracked(&mut tv));
        update prev -> next;
        snapshot snap;
        ghost g => {
            assert(next == prev.push(snap.msg()));
            assert(snap.ts() == prev.len());
            assert(snap.msg().value == 1);
        }
    }
    weak_atomic_with_ghost! {
        atomic => store_relaxed(2, Tracked(&mut tv));
        update prev -> next;
        snapshot snap;
        ghost g => {
            assert(next == prev.push(snap.msg()));
            assert(snap.ts() == prev.len());
            assert(snap.msg().value == 2);
        }
    }
}

} // verus!
