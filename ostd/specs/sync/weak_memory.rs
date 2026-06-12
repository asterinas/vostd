//! Weak-memory atomic wrappers used by the verification layer.
//!
//! This module is a TCB boundary: executable atomic operations are connected to
//! Rust atomics with `external_body`, while proofs rely only on the ghost specs
//! below. Concrete wrappers currently cover Rust integer atomics, `AtomicBoolW`,
//! and `AtomicPtrW`, all using the same view/history model.
//!
//! We focus on the repaired C11/RC11-style memory model, where relaxed behavior
//! is modeled as reading from previously written messages in a location’s modi-
//! fication history, subject to coherence. In particular, relaxed reads may ob-
//! serve stale writes, but a thread’s view prevents it from going backwards,
//! and reads do not observe future writes that have not been added to the history.
//!
//! # References
//!
//! - [RCU Verification](https://dl.acm.org/doi/pdf/10.1145/3729246)
use core::sync::atomic::{
    AtomicBool, AtomicI8, AtomicI16, AtomicI32, AtomicIsize, AtomicPtr, AtomicU8, AtomicU16,
    AtomicU32, AtomicUsize, Ordering,
};

use super::rcu as rcu_spec;

#[cfg(target_has_atomic = "64")]
use core::sync::atomic::{AtomicI64, AtomicU64};

use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::map::{GhostMapAuth, GhostPersistentPointsTo};
use vstd::seq::Seq;

verus! {

// The "global" memory is defined wihtin the invariant we need to preserve and,
// by the definition of Iris operations, invariant can be opened by a thread
// provided that the invariant holds and it can close afterwards provided that
// the invariant holds as well.
//
// Thanks to Verus' native support for the semantics, we only need to define
// what means for `atomic` and we can freely open the invariant and provide
// customized macros for doing ergonomic updates on both the physical resources
// and the ghost tokens like message histories, views, etc.
/// An `AtomicId` is just an abstract identifier (memory location) of one atomic object.
pub type AtomicId = Loc;

/// Logical timestamp into one atomic object's message history.
/// Timestamp 0 is always the initial message installed by `new`.
pub type Timestamp = nat;

/// A thread-local weak-memory view.
///
/// `seen[id] = ts` means this thread has advanced past all messages for `id`
/// older than `ts`; future reads from that atomic must not go backwards.
///
/// Typically, if another thread has published a message with timestamp `ts` for `id`,
/// and the reader reads the message via some atomic operations, then the reader's
/// thread view will advance to at least `ts` for `id`.
pub ghost struct WmView {
    pub seen: Map<AtomicId, Timestamp>,
}

impl WmView {
    /// Creates an empty view.
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
    ///
    /// Just as the name indicates, `observe` means that the current thread has observed
    /// a message written by another thread with a specific timestamp; because the atomic
    /// operation never "goes back", the thread's view for that atomic must advance to at
    /// least that timestamp.
    ///
    /// "During a read from `l`, a thread can observe any message `m` from `M(l)` where
    /// `m.time >= V(l)`, and updates its view to incorporate `m.time`."
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

    /// Partial ordering two threads' views.
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
    // Private: code outside this TCB module must not forge the history length,
    // which would desynchronize `len` from the authoritative map domain.
    ghost len: nat,
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

    pub closed spec fn history(self) -> History<V>
        recommends
            self.wf(),
    {
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

} // verus!
/// Generate the proof-facing wrapper for one concrete weak-memory atomic type.
///
/// The generated type keeps the executable TCB wrapper separate from the
/// invariant protocol. Adding `AtomicU32W` or `AtomicBoolW` later should require
/// a new executable wrapper plus one macro invocation, not another copy of the
/// invariant glue.
macro_rules! declare_weak_atomic_type {
    ($weak_atomic:ident, $pred_adapter:ident, $raw_atomic:ident, $value_ty:ty) => {
        verus! {
        /// Predicate adapter stored inside `AtomicInvariant`.
        ///
        /// The invariant contains the authoritative history and user ghost
        /// state. The constant pairs the user key `K` with the logical atomic id.
        pub struct $pred_adapter<Pred> {
            p: Pred,
        }

        impl<K, G, Pred> InvariantPredicate<(K, AtomicId), (HistAuth<$value_ty>, G)> for $pred_adapter<
            Pred,
        > where Pred: WeakAtomicInvariantPredicate<K, $value_ty, G> {
            open spec fn inv(k_id: (K, AtomicId), hist_g: (HistAuth<$value_ty>, G)) -> bool {
                let (k, id) = k_id;
                let (hist, g) = hist_g;
                &&& hist.id() == id
                &&& hist.wf()
                &&& Pred::atomic_inv(k, hist.history(), g)
            }
        }

        /// A weak-memory atomic with an `atomic_ghost`-style invariant.
        ///
        /// The executable atomic remains the TCB wrapper. This proof-facing
        /// wrapper stores the authoritative history in an `AtomicInvariant` and
        /// exposes `well_formed`/`type_inv` predicates tying that history to the
        /// executable atomic id. As in `vstd::atomic_ghost`, outer data
        /// structures put this predicate in their own
        /// `#[verifier::type_invariant]`.
        pub struct $weak_atomic<K, G, Pred> {
            #[doc(hidden)]
            atomic: $raw_atomic,
            #[doc(hidden)]
            atomic_inv: Tracked<
                AtomicInvariant<(K, AtomicId), (HistAuth<$value_ty>, G), $pred_adapter<Pred>>,
            >,
        }

        impl<K, G, Pred> $weak_atomic<K, G, Pred> {
            pub closed spec fn constant(&self) -> K {
                self.atomic_inv@.constant().0
            }

            pub closed spec fn well_formed(&self) -> bool {
                self.atomic_inv@.constant().1 == self.atomic.id()
            }

            #[verifier::type_invariant]
            pub closed spec fn type_inv(&self) -> bool {
                self.well_formed()
            }
        }

        impl<K, G, Pred> $weak_atomic<K, G, Pred> where
            Pred: WeakAtomicInvariantPredicate<K, $value_ty, G>,
        {
            #[inline(always)]
            pub const fn new(
                Ghost(k): Ghost<K>,
                init: $value_ty,
                Tracked(g): Tracked<G>,
            ) -> (res: Self)
                requires
                    Pred::atomic_inv(k, seq![Msg { value: init, view: WmView::empty() }], g),
                ensures
                    res.well_formed(),
                    res.constant() == k,
            {
                let (atomic, Tracked(hist)) = $raw_atomic::new(init);
                let tracked pair = (hist, g);
                assert($pred_adapter::<Pred>::inv((k, atomic.id()), pair));
                let tracked atomic_inv = AtomicInvariant::new((k, atomic.id()), pair, 0);
                $weak_atomic { atomic, atomic_inv: Tracked(atomic_inv) }
            }

            #[inline(always)]
            pub fn load_relaxed(
                &self,
                Tracked(tv): Tracked<&mut ThreadView>,
            ) -> (res: ($value_ty, Ghost<Timestamp>)) {
                let result;
                proof {
                    use_type_invariant(self);
                }
                vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
                    let tracked (hist, g) = pair;
                    proof {
                        assert(hist.id() == self.atomic_inv@.constant().1);
                        assert(self.atomic_inv@.constant().1 == self.atomic.id());
                        assert(hist.id() == self.atomic.id());
                    }
                    result = self.atomic.load_relaxed(Tracked(&hist), Tracked(tv));
                    proof {
                        pair = (hist, g);
                    }
                });
                result
            }

            #[inline(always)]
            pub fn load_acquire(
                &self,
                Tracked(tv): Tracked<&mut ThreadView>,
            ) -> (res: ($value_ty, Ghost<Timestamp>)) {
                let result;
                proof {
                    use_type_invariant(self);
                }
                vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
                    let tracked (hist, g) = pair;
                    proof {
                        assert(hist.id() == self.atomic_inv@.constant().1);
                        assert(self.atomic_inv@.constant().1 == self.atomic.id());
                        assert(hist.id() == self.atomic.id());
                    }
                    result = self.atomic.load_acquire(Tracked(&hist), Tracked(tv));
                    proof {
                        pair = (hist, g);
                    }
                });
                result
            }
        }
        }
    };
}

declare_weak_atomic_type!(WeakAtomicU8, WeakAtomicPredU8, AtomicU8W, u8);
declare_weak_atomic_type!(WeakAtomicU16, WeakAtomicPredU16, AtomicU16W, u16);
declare_weak_atomic_type!(WeakAtomicU32, WeakAtomicPredU32, AtomicU32W, u32);
declare_weak_atomic_type!(WeakAtomicUsize, WeakAtomicPredUsize, AtomicUsizeW, usize);
declare_weak_atomic_type!(WeakAtomicBool, WeakAtomicPredBool, AtomicBoolW, bool);

#[cfg(target_has_atomic = "64")]
declare_weak_atomic_type!(WeakAtomicU64, WeakAtomicPredU64, AtomicU64W, u64);

declare_weak_atomic_type!(WeakAtomicI8, WeakAtomicPredI8, AtomicI8W, i8);
declare_weak_atomic_type!(WeakAtomicI16, WeakAtomicPredI16, AtomicI16W, i16);
declare_weak_atomic_type!(WeakAtomicI32, WeakAtomicPredI32, AtomicI32W, i32);
declare_weak_atomic_type!(WeakAtomicIsize, WeakAtomicPredIsize, AtomicIsizeW, isize);

#[cfg(target_has_atomic = "64")]
declare_weak_atomic_type!(WeakAtomicI64, WeakAtomicPredI64, AtomicI64W, i64);

verus! {

/// Predicate adapter for weak-memory pointer atomics.
///
/// The history stores raw pointer values. This tracks the atomic pointer value
/// itself; ownership of the pointee must be modeled by the user ghost state `G`.
pub struct WeakAtomicPredPtr<T, Pred> {
    t: T,
    p: Pred,
}

impl<T, K, G, Pred> InvariantPredicate<(K, AtomicId), (HistAuth<*mut T>, G)> for WeakAtomicPredPtr<
    T,
    Pred,
> where Pred: WeakAtomicInvariantPredicate<K, *mut T, G> {
    open spec fn inv(k_id: (K, AtomicId), hist_g: (HistAuth<*mut T>, G)) -> bool {
        let (k, id) = k_id;
        let (hist, g) = hist_g;
        &&& hist.id() == id
        &&& hist.wf()
        &&& Pred::atomic_inv(k, hist.history(), g)
    }
}

/// Weak-memory atomic pointer with an `atomic_ghost`-style invariant.
///
/// This is the pointer analogue of [`WeakAtomicUsize`]. It deliberately models
/// only the atomic pointer value and its release/acquire synchronization history;
/// any ownership or validity claim about the pointed-to allocation belongs in
/// the user-supplied ghost state `G` and invariant predicate.
#[verifier::accept_recursive_types(T)]
pub struct WeakAtomicPtr<T, K, G, Pred> {
    #[doc(hidden)]
    atomic: AtomicPtrW<T>,
    #[doc(hidden)]
    atomic_inv: Tracked<
        AtomicInvariant<(K, AtomicId), (HistAuth<*mut T>, G), WeakAtomicPredPtr<T, Pred>>,
    >,
}

impl<T, K, G, Pred> WeakAtomicPtr<T, K, G, Pred> {
    pub closed spec fn constant(&self) -> K {
        self.atomic_inv@.constant().0
    }

    pub closed spec fn well_formed(&self) -> bool {
        self.atomic_inv@.constant().1 == self.atomic.id()
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(&self) -> bool {
        self.well_formed()
    }
}

impl<T, K, G, Pred> WeakAtomicPtr<T, K, G, Pred> where
    Pred: WeakAtomicInvariantPredicate<K, *mut T, G>,
 {
    #[inline(always)]
    pub const fn new(Ghost(k): Ghost<K>, init: *mut T, Tracked(g): Tracked<G>) -> (res: Self)
        requires
            Pred::atomic_inv(k, seq![Msg { value: init, view: WmView::empty() }], g),
        ensures
            res.well_formed(),
            res.constant() == k,
    {
        let (atomic, Tracked(hist)) = AtomicPtrW::<T>::new(init);
        let tracked pair = (hist, g);
        assert(WeakAtomicPredPtr::<T, Pred>::inv((k, atomic.id()), pair));
        let tracked atomic_inv = AtomicInvariant::new((k, atomic.id()), pair, 0);
        WeakAtomicPtr { atomic, atomic_inv: Tracked(atomic_inv) }
    }

    #[inline(always)]
    pub fn load_relaxed(&self, Tracked(tv): Tracked<&mut ThreadView>) -> (res: (
        *mut T,
        Ghost<Timestamp>,
    )) {
        let result;
        proof {
            use_type_invariant(self);
        }
        vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            let tracked (hist, g) = pair;
            proof {
                assert(hist.id() == self.atomic_inv@.constant().1);
                assert(self.atomic_inv@.constant().1 == self.atomic.id());
                assert(hist.id() == self.atomic.id());
            }
            result = self.atomic.load_relaxed(Tracked(&hist), Tracked(tv));
            proof {
                pair = (hist, g);
            }
        });
        result
    }

    #[inline(always)]
    pub fn load_acquire(&self, Tracked(tv): Tracked<&mut ThreadView>) -> (res: (
        *mut T,
        Ghost<Timestamp>,
    )) {
        let result;
        proof {
            use_type_invariant(self);
        }
        vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            let tracked (hist, g) = pair;
            proof {
                assert(hist.id() == self.atomic_inv@.constant().1);
                assert(self.atomic_inv@.constant().1 == self.atomic.id());
                assert(hist.id() == self.atomic.id());
            }
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

impl<T, K> WeakAtomicPtr<T, K, (), TrueWeakAtomicInv> {
    // TODO: Move exec code into, `vstd_extra`?
    /// Release-store helper for users with the trivial atomic invariant.
    ///
    /// This keeps early weak-memory clients from depending on the macro while
    /// we are still shaping the client-specific ghost state.
    #[inline(always)]
    pub fn store_release_simple(&self, value: *mut T, Tracked(tv): Tracked<&mut ThreadView>) {
        proof {
            use_type_invariant(self);
        }
        vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            let tracked (mut hist, g) = pair;
            proof {
                assert(hist.id() == self.atomic_inv@.constant().1);
                assert(self.atomic_inv@.constant().1 == self.atomic.id());
                assert(hist.id() == self.atomic.id());
            }
            let _snap = self.atomic.store_release(Tracked(&mut hist), Tracked(tv), value);
            proof {
                pair = (hist, g);
            }
        });
    }

    /// Strong AcqRel/Acquire CAS helper for users with the trivial invariant.
    #[inline(always)]
    pub fn compare_exchange_acqrel_acquire_simple(
        &self,
        current: *mut T,
        new: *mut T,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (Result<*mut T, *mut T>, Ghost<Timestamp>)) {
        let result;
        proof {
            use_type_invariant(self);
        }
        vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            let tracked (mut hist, g) = pair;
            proof {
                assert(hist.id() == self.atomic_inv@.constant().1);
                assert(self.atomic_inv@.constant().1 == self.atomic.id());
                assert(hist.id() == self.atomic.id());
            }
            let cas_result = self.atomic.compare_exchange_acqrel_acquire(
                Tracked(&mut hist),
                Tracked(tv),
                current,
                new,
            );
            result = (cas_result.0, cas_result.1);
            proof {
                pair = (hist, g);
            }
        });
        result
    }
}

impl<T> WeakAtomicPtr<T, bool, (), rcu_spec::RcuWeakAtomicInv> {
    /// Acquire-load helper for RCU root pointers.
    #[inline(always)]
    pub fn load_acquire_rcu(&self, Tracked(tv): Tracked<&mut ThreadView>) -> (res: (
        *mut T,
        Ghost<Timestamp>,
    ))
        requires
            self.well_formed(),
        ensures
            !self.constant() ==> !res.0.is_null(),
    {
        let result;
        proof {
            use_type_invariant(self);
        }
        vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            let tracked (hist, g) = pair;
            proof {
                assert(hist.id() == self.atomic_inv@.constant().1);
                assert(self.atomic_inv@.constant().1 == self.atomic.id());
                assert(hist.id() == self.atomic.id());
            }
            result = self.atomic.load_acquire(Tracked(&hist), Tracked(tv));
            proof {
                assert(rcu_spec::rcu_history_inv(self.constant(), hist.history()));
                if !self.constant() {
                    rcu_spec::rcu_history_inv_read_nonnull::<T>(hist.history(), result.1@);
                    assert(!result.0.is_null());
                }
                pair = (hist, g);
            }
        });
        result
    }

    /// Release-store helper for RCU root pointers.
    #[inline(always)]
    pub fn store_release_rcu(&self, value: *mut T, Tracked(tv): Tracked<&mut ThreadView>)
        requires
            self.well_formed(),
            self.constant() || !value.is_null(),
    {
        proof {
            use_type_invariant(self);
        }
        vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            let tracked (mut hist, g) = pair;
            proof {
                assert(hist.id() == self.atomic_inv@.constant().1);
                assert(self.atomic_inv@.constant().1 == self.atomic.id());
                assert(hist.id() == self.atomic.id());
            }
            let ghost prev = hist.history();
            let snap = self.atomic.store_release(Tracked(&mut hist), Tracked(tv), value);
            let ghost next = hist.history();
            proof {
                if !self.constant() {
                    assert(!value.is_null());
                    assert(snap@.msg().value.addr() != 0);
                }
                rcu_spec::preserve_rcu_history_inv_on_push(
                    self.constant(),
                    prev,
                    next,
                    snap@.msg(),
                );
                pair = (hist, g);
            }
        });
    }

    /// Strong AcqRel/Acquire CAS helper for RCU root pointers.
    #[inline(always)]
    pub fn compare_exchange_acqrel_acquire_rcu(
        &self,
        current: *mut T,
        new: *mut T,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (Result<*mut T, *mut T>, Ghost<Timestamp>))
        requires
            self.well_formed(),
            self.constant() || !new.is_null(),
    {
        let result;
        proof {
            use_type_invariant(self);
        }
        vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            let tracked (mut hist, g) = pair;
            proof {
                assert(hist.id() == self.atomic_inv@.constant().1);
                assert(self.atomic_inv@.constant().1 == self.atomic.id());
                assert(hist.id() == self.atomic.id());
            }
            let ghost prev = hist.history();
            let cas_result = self.atomic.compare_exchange_acqrel_acquire(
                Tracked(&mut hist),
                Tracked(tv),
                current,
                new,
            );
            result = (cas_result.0, cas_result.1);
            let ghost next = hist.history();
            proof {
                match cas_result.0 {
                    Result::Ok(_) => {
                        let tracked snap_opt = cas_result.2.get();
                        match snap_opt {
                            Option::Some(snap) => {
                                if !self.constant() {
                                    assert(!new.is_null());
                                    assert(snap.msg().value.addr() != 0);
                                }
                                rcu_spec::preserve_rcu_history_inv_on_push(
                                    self.constant(),
                                    prev,
                                    next,
                                    snap.msg(),
                                );
                            },
                            Option::None => {
                                assert(false);
                            },
                        }
                    },
                    Result::Err(_) => {
                        assert(next == prev);
                        assert(rcu_spec::rcu_history_inv(self.constant(), next));
                    },
                }
                pair = (hist, g);
            }
        });
        result
    }
}

impl WeakAtomicBool<(), rcu_spec::RcuMonitorFlagGhost, rcu_spec::RcuMonitorFlagInv> {
    /// Relaxed-store helper for the RCU monitor flag.
    ///
    /// The executable flag remains a relaxed atomic flag, matching the old
    /// monitor protocol. The proof-side effect is stronger: each stored flag
    /// message appends the lock-protected monitor-state snapshot supplied by
    /// the writer.
    #[inline(always)]
    pub fn store_relaxed_rcu_monitor(
        &self,
        value: bool,
        Ghost(state): Ghost<rcu_spec::MonitorStateView>,
        Tracked(tv): Tracked<&mut ThreadView>,
    )
        requires
            self.well_formed(),
            state.wf(),
            !value ==> state.no_pending_work(),
    {
        proof {
            use_type_invariant(self);
        }
        vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            let tracked (mut hist, mut g) = pair;
            proof {
                assert(hist.id() == self.atomic_inv@.constant().1);
                assert(self.atomic_inv@.constant().1 == self.atomic.id());
                assert(hist.id() == self.atomic.id());
            }
            let ghost prev = hist.history();
            let snap = self.atomic.store_relaxed(Tracked(&mut hist), Tracked(tv), value);
            let ghost next = hist.history();
            proof {
                assert(snap@.msg().value == value);
                rcu_spec::preserve_rcu_monitor_flag_inv_on_push(
                    prev,
                    next,
                    snap@.msg(),
                    g,
                    g.push(state),
                    state,
                );
                g = g.tracked_push(state);
                pair = (hist, g);
            }
        });
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
        $atomic:expr => compare_exchange_acqrel_acquire($current:expr, $new:expr, $tv:expr);
        update $prev:ident -> $next:ident;
        returning $ret:ident;
        timestamp $ts:ident;
        message $msg:ident;
        snapshot $snap:ident;
        ghost $g:ident => $b:block
    ) => {
            ::vstd::prelude::verus_exec_expr! {{
            let result;
            let atomic = &($atomic);
            let current = $current;
            let new = $new;
            proof {
                use_type_invariant(atomic);
            }
            ::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (mut hist, mut $g) = pair;
                proof {
                    assert(hist.id() == atomic.atomic_inv@.constant().1);
                    assert(atomic.atomic_inv@.constant().1 == atomic.atomic.id());
                    assert(hist.id() == atomic.atomic.id());
                }
                let ghost $prev = hist.history();
                let cas_result = atomic.atomic.compare_exchange_acqrel_acquire(
                    Tracked(&mut hist),
                    $tv,
                    current,
                    new,
                );
                result = (cas_result.0, cas_result.1);
                let ghost $next = hist.history();
                let ghost $ret = cas_result.0;
                let ghost $ts = cas_result.1@;
                let ghost $msg = $prev[$ts as int];

                proof {
                    let tracked $snap = cas_result.2.get();
                    $b
                }

                proof {
                    pair = (hist, $g);
                }
            });
            result
        }}
    };
    (
        $atomic:expr => load_acquire($tv:expr);
        returning $ret:ident;
        timestamp $ts:ident;
        message $msg:ident;
        history $history:ident;
        ghost $g:ident => $b:block
    ) => {
            ::vstd::prelude::verus_exec_expr! {{
            let result;
            let atomic = &($atomic);
            proof {
                use_type_invariant(atomic);
            }
            ::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (hist, mut $g) = pair;
                proof {
                    assert(hist.id() == atomic.atomic_inv@.constant().1);
                    assert(atomic.atomic_inv@.constant().1 == atomic.atomic.id());
                    assert(hist.id() == atomic.atomic.id());
                }
                let ghost $history = hist.history();
                result = atomic.atomic.load_acquire(Tracked(&hist), $tv);
                let ghost $ret = result.0;
                let ghost $ts = result.1@;
                let ghost $msg = hist.msg_at($ts);

                proof { $b }

                proof {
                    pair = (hist, $g);
                }
            });
            result
        }}
    };
    (
        $atomic:expr => load_relaxed($tv:expr);
        returning $ret:ident;
        timestamp $ts:ident;
        message $msg:ident;
        history $history:ident;
        ghost $g:ident => $b:block
    ) => {
            ::vstd::prelude::verus_exec_expr! {{
            let result;
            let atomic = &($atomic);
            proof {
                use_type_invariant(atomic);
            }
            ::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (hist, mut $g) = pair;
                proof {
                    assert(hist.id() == atomic.atomic_inv@.constant().1);
                    assert(atomic.atomic_inv@.constant().1 == atomic.atomic.id());
                    assert(hist.id() == atomic.atomic.id());
                }
                let ghost $history = hist.history();
                result = atomic.atomic.load_relaxed(Tracked(&hist), $tv);
                let ghost $ret = result.0;
                let ghost $ts = result.1@;
                let ghost $msg = hist.msg_at($ts);

                proof { $b }

                proof {
                    pair = (hist, $g);
                }
            });
            result
        }}
    };
    (
        $atomic:expr => store_release($value:expr, $tv:expr);
        update $prev:ident -> $next:ident;
        snapshot $snap:ident;
        ghost $g:ident => $b:block
    ) => {
            ::vstd::prelude::verus_exec_expr! {{
            let atomic = &($atomic);
            let value = $value;
            proof {
                use_type_invariant(atomic);
            }
            ::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (mut hist, mut $g) = pair;
                proof {
                    assert(hist.id() == atomic.atomic_inv@.constant().1);
                    assert(atomic.atomic_inv@.constant().1 == atomic.atomic.id());
                    assert(hist.id() == atomic.atomic.id());
                }
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
            proof {
                use_type_invariant(atomic);
            }
            ::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (mut hist, mut $g) = pair;
                proof {
                    assert(hist.id() == atomic.atomic_inv@.constant().1);
                    assert(atomic.atomic_inv@.constant().1 == atomic.atomic.id());
                    assert(hist.id() == atomic.atomic.id());
                }
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
///
/// # Soundness
///
/// The wrapped view is private and can only evolve through the TCB atomic
/// operations in this module. Those operations maintain the invariant that a
/// view never claims a timestamp at or beyond the length of that location's
/// history: loads observe an existing message, stores observe the message they
/// just appended, and acquire joins only import message views that were built
/// from existing timestamps. This keeps the `readable`-based postconditions of
/// loads satisfiable. Do not add raw mutators (e.g. an unconditional
/// `observe`/`join` proof fn): a forged view claiming an unwritten timestamp
/// would make the next load's postcondition vacuously false.
pub tracked struct ThreadView {
    ghost view: WmView,
}

impl View for ThreadView {
    type V = WmView;

    closed spec fn view(&self) -> WmView {
        self.view
    }
}

impl ThreadView {
    /// Creates a fresh token holding the empty view.
    ///
    /// The empty view is the weakest token: it lower-bounds every location at
    /// timestamp 0, so minting one is always sound — the holder merely
    /// forfeits all ordering knowledge. Note that minting a fresh view
    /// mid-thread over-approximates real executions (it forgets per-location
    /// coherence the thread has already observed) and publishes nothing useful
    /// through release stores, so executable code should thread one token per
    /// logical operation or critical section, and eventually one per task.
    pub proof fn new() -> (tracked res: Self)
        ensures
            res@ == WmView::empty(),
    {
        ThreadView { view: WmView::empty() }
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

    /// Strong compare-exchange with `AcqRel` success ordering and `Acquire`
    /// failure ordering.
    ///
    /// On success, RMW atomicity forces the read to be the latest message in
    /// the modification history, and the new release message is appended
    /// immediately after it. On failure, the operation is only an acquire
    /// load: it may read *any* readable message whose value differs from
    /// `current`, not necessarily the latest one. A strong CAS merely never
    /// fails after reading a value equal to `current`.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn compare_exchange_acqrel_acquire(
        &self,
        Tracked(auth): Tracked<&mut HistAuth<usize>>,
        Tracked(tv): Tracked<&mut ThreadView>,
        current: usize,
        new: usize,
    ) -> (res: (Result<usize, usize>, Ghost<Timestamp>, Tracked<Option<MsgSnap<usize>>>))
        requires
            old(auth).id() == self.id(),
            old(auth).wf(),
        ensures
            ({
                let read_ts = res.1@;
                let read_msg = old(auth).msg_at(read_ts);
                let after_read = old(tv)@.observe(self.id(), read_ts).join(read_msg.view);
                &&& old(auth).readable(old(tv)@, read_ts)
                &&& match res.0 {
                    Ok(v) => {
                        let write_ts = old(auth).history().len();
                        let write_msg = Msg {
                            value: new,
                            view: after_read.observe(self.id(), write_ts),
                        };
                        &&& read_ts + 1 == old(auth).history().len()
                        &&& v == current
                        &&& read_msg.value == current
                        &&& final(auth).id() == old(auth).id()
                        &&& final(auth).history() == old(auth).history().push(write_msg)
                        &&& final(auth).wf()
                        &&& final(tv)@ == after_read.observe(self.id(), write_ts)
                        &&& res.2@ is Some
                        &&& res.2@->Some_0.id() == self.id()
                        &&& res.2@->Some_0.ts() == write_ts
                        &&& res.2@->Some_0.msg() == write_msg
                        &&& res.2@->Some_0.agrees_with(*final(auth))
                    },
                    Err(v) => {
                        &&& v == read_msg.value
                        &&& read_msg.value != current
                        &&& final(auth).id() == old(auth).id()
                        &&& final(auth).history() == old(auth).history()
                        &&& final(auth).wf()
                        &&& final(tv)@ == after_read
                        &&& res.2@ is None
                    },
                }
            }),
        opens_invariants none
        no_unwind
    {
        let result = self.value.compare_exchange(current, new, Ordering::AcqRel, Ordering::Acquire);
        (result, Ghost::assume_new(), Tracked::assume_new())
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

} // verus!
/// Generate a TCB executable wrapper around one Rust integer atomic type.
///
/// All integer atomics share the same weak-memory history shape: load chooses a
/// readable message, stores append a message, and CAS either reads the latest
/// message and appends its write right after it (success), or acts as an
/// acquire read of any readable message with a different value (failure).
macro_rules! declare_integer_atomic_wrapper {
    ($wrapper:ident, $rust_atomic:ident, $value_ty:ty) => {
        verus! {
        #[repr(transparent)]
        #[verifier::external_body]
        /// TCB wrapper around a Rust integer atomic.
        pub struct $wrapper {
            value: $rust_atomic,
        }

        impl $wrapper {
            /// Logical identity of this atomic object.
            pub uninterp spec fn id(&self) -> AtomicId;

            #[inline(always)]
            #[verifier::external_body]
            pub const fn new(init: $value_ty) -> (res: (Self, Tracked<HistAuth<$value_ty>>))
                ensures
                    res.1@.id() == res.0.id(),
                    res.1@.history() == seq![Msg { value: init, view: WmView::empty() }],
                    res.1@.wf(),
            {
                let atomic = $wrapper { value: $rust_atomic::new(init) };
                (atomic, Tracked::assume_new())
            }

            #[inline(always)]
            #[verifier::external_body]
            #[verifier::atomic]
            pub fn load_relaxed(
                &self,
                Tracked(auth): Tracked<&HistAuth<$value_ty>>,
                Tracked(tv): Tracked<&mut ThreadView>,
            ) -> (res: ($value_ty, Ghost<Timestamp>))
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

            #[inline(always)]
            #[verifier::external_body]
            #[verifier::atomic]
            pub fn load_acquire(
                &self,
                Tracked(auth): Tracked<&HistAuth<$value_ty>>,
                Tracked(tv): Tracked<&mut ThreadView>,
            ) -> (res: ($value_ty, Ghost<Timestamp>))
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

            #[inline(always)]
            #[verifier::external_body]
            #[verifier::atomic]
            pub fn compare_exchange_acqrel_acquire(
                &self,
                Tracked(auth): Tracked<&mut HistAuth<$value_ty>>,
                Tracked(tv): Tracked<&mut ThreadView>,
                current: $value_ty,
                new: $value_ty,
            ) -> (res: (
                Result<$value_ty, $value_ty>,
                Ghost<Timestamp>,
                Tracked<Option<MsgSnap<$value_ty>>>,
            ))
                requires
                    old(auth).id() == self.id(),
                    old(auth).wf(),
                ensures
                    ({
                        let read_ts = res.1@;
                        let read_msg = old(auth).msg_at(read_ts);
                        let after_read = old(tv)@.observe(self.id(), read_ts).join(read_msg.view);
                        &&& old(auth).readable(old(tv)@, read_ts)
                        &&& match res.0 {
                            Ok(v) => {
                                let write_ts = old(auth).history().len();
                                let write_msg = Msg {
                                    value: new,
                                    view: after_read.observe(self.id(), write_ts),
                                };
                                &&& read_ts + 1 == old(auth).history().len()
                                &&& v == current
                                &&& read_msg.value == current
                                &&& final(auth).id() == old(auth).id()
                                &&& final(auth).history() == old(auth).history().push(write_msg)
                                &&& final(auth).wf()
                                &&& final(tv)@ == after_read.observe(self.id(), write_ts)
                                &&& res.2@ is Some
                                &&& res.2@->Some_0.id() == self.id()
                                &&& res.2@->Some_0.ts() == write_ts
                                &&& res.2@->Some_0.msg() == write_msg
                                &&& res.2@->Some_0.agrees_with(*final(auth))
                            },
                            Err(v) => {
                                &&& v == read_msg.value
                                &&& read_msg.value != current
                                &&& final(auth).id() == old(auth).id()
                                &&& final(auth).history() == old(auth).history()
                                &&& final(auth).wf()
                                &&& final(tv)@ == after_read
                                &&& res.2@ is None
                            },
                        }
                    }),
                opens_invariants none
                no_unwind
            {
                let result = self.value.compare_exchange(
                    current,
                    new,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                );
                (result, Ghost::assume_new(), Tracked::assume_new())
            }

            #[inline(always)]
            #[verifier::external_body]
            #[verifier::atomic]
            pub fn store_relaxed(
                &self,
                Tracked(auth): Tracked<&mut HistAuth<$value_ty>>,
                Tracked(tv): Tracked<&mut ThreadView>,
                value: $value_ty,
            ) -> (snap: Tracked<MsgSnap<$value_ty>>)
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

            #[inline(always)]
            #[verifier::external_body]
            #[verifier::atomic]
            pub fn store_release(
                &self,
                Tracked(auth): Tracked<&mut HistAuth<$value_ty>>,
                Tracked(tv): Tracked<&mut ThreadView>,
                value: $value_ty,
            ) -> (snap: Tracked<MsgSnap<$value_ty>>)
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
        }
    };
}

declare_integer_atomic_wrapper!(AtomicU8W, AtomicU8, u8);

declare_integer_atomic_wrapper!(AtomicU16W, AtomicU16, u16);

declare_integer_atomic_wrapper!(AtomicU32W, AtomicU32, u32);

declare_integer_atomic_wrapper!(AtomicIsizeW, AtomicIsize, isize);

declare_integer_atomic_wrapper!(AtomicI8W, AtomicI8, i8);

declare_integer_atomic_wrapper!(AtomicI16W, AtomicI16, i16);

declare_integer_atomic_wrapper!(AtomicI32W, AtomicI32, i32);

#[cfg(target_has_atomic = "64")]
declare_integer_atomic_wrapper!(AtomicU64W, AtomicU64, u64);

#[cfg(target_has_atomic = "64")]
declare_integer_atomic_wrapper!(AtomicI64W, AtomicI64, i64);

verus! {

#[repr(transparent)]
#[verifier::external_body]
/// TCB wrapper around Rust's `AtomicBool`.
///
/// Bool atomics share the load/store/CAS weak-memory protocol with integer
/// atomics, but they are not numeric atomics: this wrapper intentionally exposes
/// no arithmetic or bitwise fetch operations.
pub struct AtomicBoolW {
    value: AtomicBool,
}

impl AtomicBoolW {
    /// Logical identity of this atomic object.
    pub uninterp spec fn id(&self) -> AtomicId;

    #[inline(always)]
    #[verifier::external_body]
    pub const fn new(init: bool) -> (res: (Self, Tracked<HistAuth<bool>>))
        ensures
            res.1@.id() == res.0.id(),
            res.1@.history() == seq![Msg { value: init, view: WmView::empty() }],
            res.1@.wf(),
    {
        let atomic = AtomicBoolW { value: AtomicBool::new(init) };
        (atomic, Tracked::assume_new())
    }

    /// Relaxed load: choose a readable bool message and advance only this
    /// location's timestamp in the caller's thread view.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load_relaxed(
        &self,
        Tracked(auth): Tracked<&HistAuth<bool>>,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (bool, Ghost<Timestamp>))
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

    /// Acquire load: same bool choice as relaxed, plus import the release view
    /// carried by the selected message.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load_acquire(
        &self,
        Tracked(auth): Tracked<&HistAuth<bool>>,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (bool, Ghost<Timestamp>))
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

    /// Strong compare-exchange with `AcqRel` success ordering and `Acquire`
    /// failure ordering.
    ///
    /// On success it reads the latest message and appends `new` immediately
    /// after it; on failure it acts as an acquire load that may read any
    /// readable message with a different value, importing that message's view.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn compare_exchange_acqrel_acquire(
        &self,
        Tracked(auth): Tracked<&mut HistAuth<bool>>,
        Tracked(tv): Tracked<&mut ThreadView>,
        current: bool,
        new: bool,
    ) -> (res: (Result<bool, bool>, Ghost<Timestamp>, Tracked<Option<MsgSnap<bool>>>))
        requires
            old(auth).id() == self.id(),
            old(auth).wf(),
        ensures
            ({
                let read_ts = res.1@;
                let read_msg = old(auth).msg_at(read_ts);
                let after_read = old(tv)@.observe(self.id(), read_ts).join(read_msg.view);
                &&& old(auth).readable(old(tv)@, read_ts)
                &&& match res.0 {
                    Ok(v) => {
                        let write_ts = old(auth).history().len();
                        let write_msg = Msg {
                            value: new,
                            view: after_read.observe(self.id(), write_ts),
                        };
                        &&& read_ts + 1 == old(auth).history().len()
                        &&& v == current
                        &&& read_msg.value == current
                        &&& final(auth).id() == old(auth).id()
                        &&& final(auth).history() == old(auth).history().push(write_msg)
                        &&& final(auth).wf()
                        &&& final(tv)@ == after_read.observe(self.id(), write_ts)
                        &&& res.2@ is Some
                        &&& res.2@->Some_0.id() == self.id()
                        &&& res.2@->Some_0.ts() == write_ts
                        &&& res.2@->Some_0.msg() == write_msg
                        &&& res.2@->Some_0.agrees_with(*final(auth))
                    },
                    Err(v) => {
                        &&& v == read_msg.value
                        &&& read_msg.value != current
                        &&& final(auth).id() == old(auth).id()
                        &&& final(auth).history() == old(auth).history()
                        &&& final(auth).wf()
                        &&& final(tv)@ == after_read
                        &&& res.2@ is None
                    },
                }
            }),
        opens_invariants none
        no_unwind
    {
        let result = self.value.compare_exchange(current, new, Ordering::AcqRel, Ordering::Acquire);
        (result, Ghost::assume_new(), Tracked::assume_new())
    }

    /// Relaxed store: append a bool-valued message whose published view contains
    /// only this store's own timestamp.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store_relaxed(
        &self,
        Tracked(auth): Tracked<&mut HistAuth<bool>>,
        Tracked(tv): Tracked<&mut ThreadView>,
        value: bool,
    ) -> (snap: Tracked<MsgSnap<bool>>)
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

    /// Release store: append a bool-valued message carrying the writer's current
    /// view, then advance the writer's view for this location.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store_release(
        &self,
        Tracked(auth): Tracked<&mut HistAuth<bool>>,
        Tracked(tv): Tracked<&mut ThreadView>,
        value: bool,
    ) -> (snap: Tracked<MsgSnap<bool>>)
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

#[repr(transparent)]
#[verifier::accept_recursive_types(T)]
#[verifier::external_body]
/// TCB wrapper around Rust's `AtomicPtr<T>`.
///
/// This wrapper tracks the pointer value in the weak-memory history, but it
/// does not claim ownership of, or permission to dereference, the pointee. A
/// higher-level invariant must connect pointer values to `PointsTo`, refcount,
/// hazard-pointer, RCU, or other ownership ghost state when dereference safety
/// matters.
pub struct AtomicPtrW<T> {
    value: AtomicPtr<T>,
}

impl<T> AtomicPtrW<T> {
    /// Logical identity of this atomic pointer object.
    pub uninterp spec fn id(&self) -> AtomicId;

    #[inline(always)]
    #[verifier::external_body]
    pub const fn new(init: *mut T) -> (res: (Self, Tracked<HistAuth<*mut T>>))
        ensures
            res.1@.id() == res.0.id(),
            res.1@.history() == seq![Msg { value: init, view: WmView::empty() }],
            res.1@.wf(),
    {
        let atomic = AtomicPtrW { value: AtomicPtr::new(init) };
        (atomic, Tracked::assume_new())
    }

    /// Relaxed load: choose a readable pointer message and advance only this
    /// location's timestamp in the caller's thread view.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load_relaxed(
        &self,
        Tracked(auth): Tracked<&HistAuth<*mut T>>,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (*mut T, Ghost<Timestamp>))
        requires
            auth.id() == self.id(),
            auth.wf(),
        ensures
            ({
                let ts = res.1@;
                &&& auth.readable(old(tv)@, ts)
                &&& equal(res.0, auth.msg_at(ts).value)
                &&& final(tv)@ == old(tv)@.observe(self.id(), ts)
            }),
        opens_invariants none
        no_unwind
    {
        let value = self.value.load(Ordering::Relaxed);
        (value, Ghost::assume_new())
    }

    /// Acquire load: same pointer choice as relaxed, plus import the release
    /// view carried by the selected message.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load_acquire(
        &self,
        Tracked(auth): Tracked<&HistAuth<*mut T>>,
        Tracked(tv): Tracked<&mut ThreadView>,
    ) -> (res: (*mut T, Ghost<Timestamp>))
        requires
            auth.id() == self.id(),
            auth.wf(),
        ensures
            ({
                let ts = res.1@;
                &&& auth.readable(old(tv)@, ts)
                &&& equal(res.0, auth.msg_at(ts).value)
                &&& final(tv)@ == old(tv)@.observe(self.id(), ts).join(auth.msg_at(ts).view)
            }),
        opens_invariants none
        no_unwind
    {
        let value = self.value.load(Ordering::Acquire);
        (value, Ghost::assume_new())
    }

    /// Relaxed store: append a pointer-valued message whose published view
    /// contains only this store's own timestamp.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store_relaxed(
        &self,
        Tracked(auth): Tracked<&mut HistAuth<*mut T>>,
        Tracked(tv): Tracked<&mut ThreadView>,
        value: *mut T,
    ) -> (snap: Tracked<MsgSnap<*mut T>>)
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

    /// Release store: append a pointer-valued message carrying the writer's
    /// current view, then advance the writer's view for this location.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store_release(
        &self,
        Tracked(auth): Tracked<&mut HistAuth<*mut T>>,
        Tracked(tv): Tracked<&mut ThreadView>,
        value: *mut T,
    ) -> (snap: Tracked<MsgSnap<*mut T>>)
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

impl<T> AtomicPtrW<T> {
    /// Strong compare-exchange with `AcqRel` success ordering and `Acquire`
    /// failure ordering.
    ///
    /// Pointer CAS compares runtime pointer identity, which Verus models as
    /// address equality for sized pointers. The returned pointer and written
    /// message still carry the full pointer value, including provenance.
    ///
    /// On success the read is the latest message and the write is appended
    /// immediately after it; on failure the operation is an acquire load that
    /// may read any readable message whose address differs from `current`.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn compare_exchange_acqrel_acquire(
        &self,
        Tracked(auth): Tracked<&mut HistAuth<*mut T>>,
        Tracked(tv): Tracked<&mut ThreadView>,
        current: *mut T,
        new: *mut T,
    ) -> (res: (Result<*mut T, *mut T>, Ghost<Timestamp>, Tracked<Option<MsgSnap<*mut T>>>))
        requires
            old(auth).id() == self.id(),
            old(auth).wf(),
        ensures
            ({
                let read_ts = res.1@;
                let read_msg = old(auth).msg_at(read_ts);
                let after_read = old(tv)@.observe(self.id(), read_ts).join(read_msg.view);
                &&& old(auth).readable(old(tv)@, read_ts)
                &&& match res.0 {
                    Ok(v) => {
                        let write_ts = old(auth).history().len();
                        let write_msg = Msg {
                            value: new,
                            view: after_read.observe(self.id(), write_ts),
                        };
                        &&& read_ts + 1 == old(auth).history().len()
                        &&& current.addr() == read_msg.value.addr()
                        &&& equal(v, read_msg.value)
                        &&& final(auth).id() == old(auth).id()
                        &&& final(auth).history() == old(auth).history().push(write_msg)
                        &&& final(auth).wf()
                        &&& final(tv)@ == after_read.observe(self.id(), write_ts)
                        &&& res.2@ is Some
                        &&& res.2@->Some_0.id() == self.id()
                        &&& res.2@->Some_0.ts() == write_ts
                        &&& res.2@->Some_0.msg() == write_msg
                        &&& res.2@->Some_0.agrees_with(*final(auth))
                    },
                    Err(v) => {
                        &&& current.addr() != read_msg.value.addr()
                        &&& equal(v, read_msg.value)
                        &&& final(auth).id() == old(auth).id()
                        &&& final(auth).history() == old(auth).history()
                        &&& final(auth).wf()
                        &&& final(tv)@ == after_read
                        &&& res.2@ is None
                    },
                }
            }),
        opens_invariants none
        no_unwind
    {
        let result = self.value.compare_exchange(current, new, Ordering::AcqRel, Ordering::Acquire);
        (result, Ghost::assume_new(), Tracked::assume_new())
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
    let _ =
        weak_atomic_with_ghost! {
        atomic => load_acquire(Tracked(&mut tv));
        returning ret;
        timestamp ts;
        message msg;
        history history;
        ghost g => {
            assert(ret == msg.value);
            assert(ts < history.len());
        }
    };
    let _ =
        weak_atomic_with_ghost! {
        atomic => load_relaxed(Tracked(&mut tv));
        returning ret;
        timestamp ts;
        message msg;
        history history;
        ghost g => {
            assert(ret == msg.value);
            assert(ts < history.len());
        }
    };
    let _ =
        weak_atomic_with_ghost! {
        atomic => compare_exchange_acqrel_acquire(2, 3, Tracked(&mut tv));
        update prev -> next;
        returning ret;
        timestamp ts;
        message msg;
        snapshot snap;
        ghost g => {
            assert(ts < prev.len());
            match ret {
                Result::Ok(v) => {
                    assert(ts + 1 == prev.len());
                    assert(v == 2);
                    assert(msg.value == 2);
                    match snap {
                        Option::Some(s) => {
                            assert(next == prev.push(s.msg()));
                            assert(s.msg().value == 3);
                        },
                        Option::None => {
                            assert(false);
                        },
                    }
                },
                Result::Err(v) => {
                    assert(v == msg.value);
                    assert(msg.value != 2);
                    match snap {
                        Option::Some(_) => {
                            assert(false);
                        },
                        Option::None => {},
                    }
                    assert(next == prev);
                },
            }
        }
    };

    let bool_atomic = WeakAtomicBool::<(), (), TrueWeakAtomicInv>::new(
        Ghost(()),
        false,
        Tracked(()),
    );
    let tracked mut bool_tv = ThreadView::new();
    weak_atomic_with_ghost! {
        bool_atomic => store_release(true, Tracked(&mut bool_tv));
        update prev -> next;
        snapshot snap;
        ghost g => {
            assert(next == prev.push(snap.msg()));
            assert(snap.ts() == prev.len());
            assert(snap.msg().value == true);
        }
    }
    let _ =
        weak_atomic_with_ghost! {
        bool_atomic => load_acquire(Tracked(&mut bool_tv));
        returning ret;
        timestamp ts;
        message msg;
        history history;
        ghost g => {
            assert(ret == msg.value);
            assert(ts < history.len());
        }
    };
    let _ =
        weak_atomic_with_ghost! {
        bool_atomic => compare_exchange_acqrel_acquire(true, false, Tracked(&mut bool_tv));
        update prev -> next;
        returning ret;
        timestamp ts;
        message msg;
        snapshot snap;
        ghost g => {
            assert(ts < prev.len());
            match ret {
                Result::Ok(v) => {
                    assert(ts + 1 == prev.len());
                    assert(v == true);
                    assert(msg.value == true);
                    match snap {
                        Option::Some(s) => {
                            assert(next == prev.push(s.msg()));
                            assert(s.msg().value == false);
                        },
                        Option::None => {
                            assert(false);
                        },
                    }
                },
                Result::Err(v) => {
                    assert(v == msg.value);
                    assert(msg.value != true);
                    match snap {
                        Option::Some(_) => {
                            assert(false);
                        },
                        Option::None => {},
                    }
                    assert(next == prev);
                },
            }
        }
    };

    let null = core::ptr::null_mut::<usize>();
    let ptr_atomic = WeakAtomicPtr::<usize, (), (), TrueWeakAtomicInv>::new(
        Ghost(()),
        null,
        Tracked(()),
    );
    let tracked mut ptr_tv = ThreadView::new();
    weak_atomic_with_ghost! {
        ptr_atomic => store_release(null, Tracked(&mut ptr_tv));
        update prev -> next;
        snapshot snap;
        ghost g => {
            assert(next == prev.push(snap.msg()));
            assert(snap.ts() == prev.len());
            assert(equal(snap.msg().value, null));
        }
    }
    let _ =
        weak_atomic_with_ghost! {
        ptr_atomic => load_acquire(Tracked(&mut ptr_tv));
        returning ret;
        timestamp ts;
        message msg;
        history history;
        ghost g => {
            assert(equal(ret, msg.value));
            assert(ts < history.len());
        }
    };
    let _ =
        weak_atomic_with_ghost! {
        ptr_atomic => compare_exchange_acqrel_acquire(null, null, Tracked(&mut ptr_tv));
        update prev -> next;
        returning ret;
        timestamp ts;
        message msg;
        snapshot snap;
        ghost g => {
            assert(ts < prev.len());
            match ret {
                Result::Ok(v) => {
                    assert(ts + 1 == prev.len());
                    assert(equal(v, msg.value));
                    assert(msg.value.addr() == null.addr());
                    match snap {
                        Option::Some(s) => {
                            assert(next == prev.push(s.msg()));
                            assert(equal(s.msg().value, null));
                        },
                        Option::None => {
                            assert(false);
                        },
                    }
                },
                Result::Err(v) => {
                    assert(equal(v, msg.value));
                    assert(msg.value.addr() != null.addr());
                    match snap {
                        Option::Some(_) => {
                            assert(false);
                        },
                        Option::None => {},
                    }
                    assert(next == prev);
                },
            }
        }
    };
}

#[cfg(verus_keep_ghost)]
pub struct MessagePassingDataInv;

#[cfg(verus_keep_ghost)]
impl WeakAtomicInvariantPredicate<(), usize, ()> for MessagePassingDataInv {
    open spec fn atomic_inv(k: (), history: History<usize>, g: ()) -> bool {
        &&& history.len() >= 1
        &&& history[0].value == 0
        &&& forall|i: int| 1 <= i < history.len() ==> #[trigger] history[i].value == 1
    }
}

#[cfg(verus_keep_ghost)]
pub struct MessagePassingFlagInv;

#[cfg(verus_keep_ghost)]
impl WeakAtomicInvariantPredicate<AtomicId, usize, ()> for MessagePassingFlagInv {
    open spec fn atomic_inv(data_id: AtomicId, history: History<usize>, g: ()) -> bool {
        &&& history.len() >= 1
        &&& history[0].value == 0
        &&& forall|i: int|
            1 <= i < history.len() ==> {
                &&& #[trigger] history[i].value == 1
                &&& history[i].view.seen_at(data_id) >= 1
            }
    }
}

#[cfg(verus_keep_ghost)]
proof fn preserve_message_passing_data_inv_on_push(
    prev: History<usize>,
    next: History<usize>,
    msg: Msg<usize>,
)
    requires
        MessagePassingDataInv::atomic_inv((), prev, ()),
        next == prev.push(msg),
        msg.value == 1,
    ensures
        MessagePassingDataInv::atomic_inv((), next, ()),
{
    assert(next.len() >= 1);
    assert(next[0].value == 0);
    assert forall|i: int| 1 <= i < next.len() implies #[trigger] next[i].value == 1 by {
        if i == prev.len() {
            assert(next[i] == msg);
        } else {
            assert(i < prev.len());
        }
    };
}

#[cfg(verus_keep_ghost)]
proof fn preserve_message_passing_flag_inv_on_push(
    data_id: AtomicId,
    prev: History<usize>,
    next: History<usize>,
    msg: Msg<usize>,
)
    requires
        MessagePassingFlagInv::atomic_inv(data_id, prev, ()),
        next == prev.push(msg),
        msg.value == 1,
        msg.view.seen_at(data_id) >= 1,
    ensures
        MessagePassingFlagInv::atomic_inv(data_id, next, ()),
{
    assert(next.len() >= 1);
    assert(next[0].value == 0);
    assert forall|i: int| 1 <= i < next.len() implies {
        &&& #[trigger] next[i].value == 1
        &&& next[i].view.seen_at(data_id) >= 1
    } by {
        if i == prev.len() {
            assert(next[i] == msg);
        } else {
            assert(i < prev.len());
        }
    };
}

#[cfg(verus_keep_ghost)]
proof fn prove_message_passing_data_read(
    data_id: AtomicId,
    history: History<usize>,
    ret: usize,
    ts: Timestamp,
    msg: Msg<usize>,
    tv: WmView,
)
    requires
        MessagePassingDataInv::atomic_inv((), history, ()),
        ts < history.len(),
        ret == msg.value,
        msg == history[ts as int],
        tv.seen_at(data_id) >= 1,
        tv.seen_at(data_id) <= ts,
    ensures
        ret == 1,
{
    assert(ts >= 1);
    assert(history[ts as int].value == 1);
}

// #[cfg(verus_keep_ghost)]
// fn message_passing_release_acquire_threads_can_prove() {
//     let data = std::sync::Arc::new(
//         WeakAtomicUsize::<(), (), MessagePassingDataInv>::new(Ghost(()), 0, Tracked(())),
//     );
//     let ghost data_id = data.atomic.id();
//     let flag = std::sync::Arc::new(
//         WeakAtomicUsize::<AtomicId, (), MessagePassingFlagInv>::new(Ghost(data_id), 0, Tracked(())),
//     );
//     let data_writer = data.clone();
//     let flag_writer = flag.clone();
//     let data_reader = data.clone();
//     let flag_reader = flag.clone();
//     let writer = vstd::thread::spawn(
//         move ||
//             {
//                 let tracked mut writer_tv = ThreadView::new();
//                 weak_atomic_with_ghost! {
//             *data_writer => store_release(1, Tracked(&mut writer_tv));
//             update prev -> next;
//             snapshot snap;
//             ghost g => {
//                 preserve_message_passing_data_inv_on_push(prev, next, snap.msg());
//                 assert(writer_tv.view.seen_at(data_id) >= 1);
//             }
//         }
//                 let ghost before_flag = writer_tv.view;
//                 assert(before_flag.seen_at(data_id) >= 1);
//                 weak_atomic_with_ghost! {
//             *flag_writer => store_release(1, Tracked(&mut writer_tv));
//             update prev -> next;
//             snapshot snap;
//             ghost g => {
//                 assert(snap.msg().view == before_flag.observe(flag_writer.atomic.id(), snap.ts()));
//                 assert(snap.msg().view.seen_at(data_id) >= 1);
//                 preserve_message_passing_flag_inv_on_push(data_id, prev, next, snap.msg());
//             }
//         }
//             },
//     );
//     let reader = vstd::thread::spawn(
//         move ||
//             {
//                 let tracked mut reader_tv = ThreadView::new();
//                 let flag_result =
//                     weak_atomic_with_ghost! {
//                 *flag_reader => load_acquire(Tracked(&mut reader_tv));
//                 returning ret;
//                 timestamp ts;
//                 message msg;
//                 history history;
//                 ghost g => {
//                     if ret == 1 {
//                         assert(msg.value == 1);
//                         if ts == 0 {
//                             assert(history[0].value == 0);
//                             assert(false);
//                         }
//                         assert(ts >= 1);
//                         assert(history[ts as int].value == 1);
//                         assert(history[ts as int].view.seen_at(data_id) >= 1);
//                         assert(msg == history[ts as int]);
//                         assert(msg.view.seen_at(data_id) >= 1);
//                         assert(reader_tv.view.seen_at(data_id) >= 1);
//                     }
//                 }
//             };
//                 if flag_result.0 == 1 {
//                     assert(reader_tv.view.seen_at(data_id) >= 1);
//                     let data_result =
//                         weak_atomic_with_ghost! {
//             *data_reader => load_relaxed(Tracked(&mut reader_tv));
//             returning ret;
//             timestamp ts;
//             message msg;
//             history history;
//             ghost g => {
//                 prove_message_passing_data_read(data_id, history, ret, ts, msg, reader_tv.view);
//             }
//         };
//                     assert(data_result.0 == 1);
//                 }
//             },
//     );
//     let _ = writer.join();
//     let _ = reader.join();
// }
} // verus!
