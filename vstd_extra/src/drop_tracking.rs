use core::{marker::PhantomData, ops::Deref};
use vstd::prelude::*;
use vstd::resource::Loc;

use crate::resource::ghost_resource::excl::ExclusiveGhost;

verus! {

/// A linear-looking "must drop" obligation tied to a value of type `R`.
///
/// `R` is the *key* type used to identify the resource in the State's
/// obligation ledger — e.g. `Range<Paddr>` for a `Segment<M>`, `usize` for a
/// per-slot resource, `()` for impls that pipe the token through without a
/// per-instance ledger. Two-layer enforcement (the design that survives
/// Verus's affineness):
///
/// 1. **Token (this type)**: an `ExclusiveGhost<R>` wrapper. Each `alloc`
///    produces a unique [`Loc`]; two outstanding tokens can be proven
///    distinct via [`DropObligation::validate_with_other`]. No external_body
///    axioms — the allocation is verified by `vstd`'s resource algebra.
/// 2. **Ledger (in State)**: optional. For impls that opt in, the State
///    carries a set/multiset of outstanding keys; mint adds, redeem removes,
///    and the State's `clean_inv()` (or any boundary predicate) requires the
///    set to be empty (or the per-slot counter to be zero). Combined with
///    `1`, the linear guarantee is sound: silently dropping the token leaves
///    the ledger non-empty and breaks the boundary check.
///
/// Impls that don't add a per-state ledger still pass tokens through —
/// they get the API uniformity but not the enforcement.
#[verifier::reject_recursive_types(R)]
pub tracked struct DropObligation<R> {
    /// The token's unique-id-bearing backing. Wraps a `Resource` so that
    /// every `alloc` produces a fresh [`Loc`] — no `external_body` axiom
    /// is needed to forge fresh tokens.
    inner: ExclusiveGhost<R>,
}

impl<R> DropObligation<R> {
    pub closed spec fn value(self) -> R {
        self.inner.view()
    }

    /// Unique identifier of this token. Two outstanding `DropObligation`s
    /// can be proven distinct via [`Self::validate_with_other`].
    pub closed spec fn id(self) -> Loc {
        self.inner.id()
    }

    /// Mint a fresh obligation token. Sound on its own (no axiom — the
    /// allocation goes through `vstd`'s resource algebra and is verified).
    /// Two legitimate uses:
    ///
    /// - Inside an impl that opts out of per-state-ledger enforcement
    ///   (e.g. `Key = ()` impls): the token is a no-op marker; the trait
    ///   API stays uniform but no `clean_inv()` enforcement applies.
    /// - As the underlying allocator for a paired mint axiom on
    ///   [`HasObligations`] — the axiom adds the ledger entry alongside.
    pub proof fn tracked_mint(value: R) -> (tracked res: DropObligation<R>)
        ensures
            res.value() == value,
    {
        DropObligation { inner: ExclusiveGhost::alloc(value) }
    }

    /// Two outstanding obligations have distinct `Loc`s.
    pub proof fn validate_with_other(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *final(self),
            final(self).id() != other.id(),
    {
        self.inner.validate_with_other(&other.inner);
    }
}

/// State that carries an obligation ledger keyed by `K`.
pub trait HasObligations<K> {
    spec fn obligations(self) -> Set<K>;
}

pub trait TrackDrop: Sized {
    type State;
    /// Identifies which obligation this resource holds in the ledger.
    type Key;

    /// The ledger key for *this* instance. Pinned by
    /// `constructor_spec`'s ensures and `Drop::drop`'s requires.
    spec fn key(self) -> Self::Key;

    spec fn constructor_requires(self, s: Self::State) -> bool;

    spec fn constructor_ensures(self, s0: Self::State, s1: Self::State, obl_key: Self::Key) -> bool;

    proof fn constructor_spec(self, tracked s: &mut Self::State)
        -> (tracked obl: DropObligation<Self::Key>)
        requires
            self.constructor_requires(*old(s)),
        ensures
            self.constructor_ensures(*old(s), *final(s), obl.value()),
            obl.value() == self.key(),
    ;

    spec fn drop_requires(self, s: Self::State) -> bool;

    /// Postcondition of [`Drop::drop`]. `obl_id` is the [`Loc`] of the
    /// consumed obligation token — ledger-enforcing impls reference it
    /// to pin the ledger transition (e.g. "the entry at `obl_id` was
    /// removed"); ledger-less impls ignore it.
    spec fn drop_ensures(self, s0: Self::State, s1: Self::State, obl_key: Self::Key) -> bool;

    /// Precondition for "consume the obligation without running the
    /// destructor" (see [`ConsumeDrop`]). `obl_id` is exposed so
    /// ledger-enforcing impls can require the entry to be outstanding.
    spec fn consume_requires(self, s: Self::State, obl_key: Self::Key) -> bool;

    /// Postcondition for consuming an obligation. Encodes any ledger
    /// mutation (e.g. redeeming the entry at `obl_id`). Impls without
    /// a ledger keep `s0 == s1`.
    spec fn consume_ensures(self, s0: Self::State, s1: Self::State, obl_key: Self::Key) -> bool;

    /// Consume the obligation token without running the destructor body.
    /// Used by [`ConsumeDrop::new`] to discharge the verifier's
    /// linear-drop obligation when the underlying resource is
    /// intentionally leaked (or freed via a separate path).
    ///
    /// Impls with a real ledger should call a paired redeem axiom here;
    /// impls without (`Key = ()`) can leave the body empty — `obl` is
    /// silently dropped, which is fine because no ledger entry needs to
    /// shrink to match.
    proof fn consume_obligation(
        self,
        tracked s: &mut Self::State,
        tracked obl: DropObligation<Self::Key>,
    )
        requires
            self.consume_requires(*old(s), obl.value()),
            obl.value() == self.key(),
        ensures
            self.consume_ensures(*old(s), *final(s), obl.value()),
    ;
}

pub trait Drop: TrackDrop {
    fn drop(
        self,
        Tracked(s): Tracked<&mut Self::State>,
        Tracked(obl): Tracked<DropObligation<Self::Key>>,
    )
        requires
            // The body must call `self.consume_obligation(s, obl)` first
            // (redeeming the token / shrinking the ledger), then run the
            // destructor work. Both preconditions are required up front.
            self.consume_requires(*old(s), obl.value()),
            self.drop_requires(*old(s)),
            obl.value() == self.key(),
        ensures
            self.drop_ensures(*old(s), *final(s), obl.value()),
    ;
}

pub struct ManuallyDrop<T: TrackDrop>(
    pub T,
    pub Tracked<DropObligation<T::Key>>,
);

impl<T: TrackDrop> ManuallyDrop<T> {
    #[verifier::external_body]
    pub fn new(t: T, Tracked(s): Tracked<&mut T::State>) -> (res: Self)
        requires
            t.constructor_requires(*old(s)),
        ensures
            t.constructor_ensures(*old(s), *final(s), res.1@.value()),
            res.0 == t,
            res.1@.value() == t.key(),
    {
        let tracked obl = t.constructor_spec(s);
        Self(t, Tracked(obl))
    }
}

impl<T: Drop> ManuallyDrop<T> {
    pub fn drop(self, Tracked(s): Tracked<&mut T::State>)
        requires
            self.0.consume_requires(*old(s), self.1@.value()),
            self.0.drop_requires(*old(s)),
            self.1@.value() == self.0.key(),
        ensures
            self.0.drop_ensures(*old(s), *final(s), self.1@.value()),
    {
        let Self(value, Tracked(obl)) = self;
        value.drop(Tracked(s), Tracked(obl))
    }
}

impl<T: TrackDrop> Deref for ManuallyDrop<T> {
    type Target = T;

    #[verifier::external_body]
    fn deref(&self) -> (res: &Self::Target)
        ensures
            res == &self.0,
    {
        &self.0
    }
}

impl<T: TrackDrop> View for ManuallyDrop<T> {
    type V = T;

    open spec fn view(&self) -> (res: Self::V) {
        self.0
    }
}

/// Deliberate-leak wrapper. `ConsumeDrop::new(t, regions, obl)` consumes
/// the obligation token via `T::consume_obligation` — for impls with a
/// per-instance ledger that's a real redemption, for `Key = ()` impls
/// it's a no-op — and wraps the value. Crucially, this does **not**
/// invoke `T::constructor_spec`, so any state-mutation that
/// `ManuallyDrop::new` would have performed (e.g. bumping a `Frame`
/// slot's `raw_count`) is skipped.
///
/// Compare with [`ManuallyDrop`]:
///
/// |               | `ManuallyDrop::new` | `ConsumeDrop::new` |
/// |---------------|---------------------|--------------------|
/// | Calls         | `constructor_spec`  | `consume_obligation` |
/// | Token         | minted internally   | passed in, redeemed |
/// | State mutation| impl-defined        | impl-defined (often none) |
/// | Typical use   | "forget via raw_count"-style | "discharge obligation"-style |
///
/// Both wrappers can be silently dropped affinely; the linear-drop
/// guarantee comes from the State-side ledger.
pub struct ConsumeDrop<T: TrackDrop>(pub T);

impl<T: TrackDrop> ConsumeDrop<T> {
    #[verifier::external_body]
    pub fn new(
        t: T,
        Tracked(s): Tracked<&mut T::State>,
        Tracked(obl): Tracked<DropObligation<T::Key>>,
    ) -> (res: Self)
        requires
            t.consume_requires(*old(s), obl.value()),
            obl.value() == t.key(),
        ensures
            t.consume_ensures(*old(s), *final(s), obl.value()),
            res.0 == t,
    {
        proof {
            t.consume_obligation(s, obl);
        }
        Self(t)
    }
}

impl<T: TrackDrop> Deref for ConsumeDrop<T> {
    type Target = T;

    #[verifier::external_body]
    fn deref(&self) -> (res: &Self::Target)
        ensures
            res == &self.0,
    {
        &self.0
    }
}

impl<T: TrackDrop> View for ConsumeDrop<T> {
    type V = T;

    open spec fn view(&self) -> (res: Self::V) {
        self.0
    }
}

} // verus!
