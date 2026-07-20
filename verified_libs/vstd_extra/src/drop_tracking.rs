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
///    distinct via [`DropObligation::validate_with_other`].
/// 2. **Ledger (in State)**: optional. For impls that opt in, the State
///    carries a set/multiset of outstanding keys; mint adds, redeem removes,
///    and the State's `clean_inv()` (or any boundary predicate) requires the
///    set to be empty. Combined with
///    `1`, the linear guarantee is sound: silently dropping the token leaves
///    the ledger non-empty and breaks the boundary check.
#[verifier::reject_recursive_types(R)]
pub tracked struct DropObligation<R> {
    inner: ExclusiveGhost<R>,
}

impl<R> DropObligation<R> {
    pub closed spec fn value(self) -> R {
        self.inner.view()
    }

    /// Unique identifier of this token.
    pub closed spec fn id(self) -> Loc {
        self.inner.id()
    }

    /// Mint a fresh obligation token. S.
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

pub trait TrackDrop: Sized {
    type State;

    /// Identifies which obligation this resource holds in the ledger.
    type Key;

    /// The ledger key for *this* instance. Pinned by
    /// `constructor_spec`'s ensures and `Drop::drop`'s requires.
    spec fn key(self) -> Self::Key;

    spec fn constructor_requires(self, s: Self::State) -> bool;

    spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool;

    proof fn constructor_spec(self, tracked s: &mut Self::State) -> (tracked obl: DropObligation<
        Self::Key,
    >)
        requires
            self.constructor_requires(*old(s)),
        ensures
            self.constructor_ensures(*old(s), *final(s)),
            obl.value() == self.key(),
    ;

    spec fn drop_requires(self, s: Self::State) -> bool;

    /// Postcondition of [`Drop::drop`].
    spec fn drop_ensures(self, s0: Self::State, s1: Self::State) -> bool;

    /// Precondition for consuming the obligation without running the destructor.
    spec fn consume_requires(self, s: Self::State) -> bool;

    /// Postcondition for consuming the obligation.
    spec fn consume_ensures(self, s0: Self::State, s1: Self::State) -> bool;

    /// Consume the obligation token without running the destructor body.
    proof fn consume_obligation(
        self,
        tracked s: &mut Self::State,
        tracked obl: DropObligation<Self::Key>,
    )
        requires
            self.consume_requires(*old(s)),
            obl.value() == self.key(),
        ensures
            self.consume_ensures(*old(s), *final(s)),
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

            self.consume_requires(*old(s)),
            self.drop_requires(*old(s)),
            obl.value() == self.key(),
        ensures
            self.drop_ensures(*old(s), *final(s)),
    ;
}

/// Linear-drop obligation wrapper. `ManuallyDrop::new(t, regions)`
/// **consumes** the State-side obligation entry for `t.key()` (via
/// `T::consume_obligation`) and wraps the value. The wrapper carries only
/// the value — no embedded obligation — and can be silently dropped
/// affinely; the linear-drop guarantee comes from the State-side ledger.
///
/// The precondition `consume_requires` (e.g. `frame_obligations.count(idx)
/// > 0` for Frame) is the load-bearing safety check: callers must
/// establish an outstanding obligation entry at `t.key()`. Producers
/// like `Frame::from_raw`, `Frame::clone`, `Frame::from_unused`,
/// `Frame::from_in_use` mint that entry. The mint + consume pair is
/// net-zero on the ledger — "the borrow ends here."
///
/// # Unsoundness warning
///
/// **It is unsound to extract the inner `T` from `ManuallyDrop<T>` via
/// `take`/`into_inner`-style operations** without minting a fresh
/// obligation at the extraction site. A `ManuallyDrop<T>` carries no
/// obligation, so the extracted `T` would have none either — but
/// `T::drop` (e.g. `Frame::drop`) requires an obligation as input, so the
/// extracted value cannot legally be dropped. Any extraction site must
/// mint a fresh entry into the State-side ledger, gated by a soundness
/// justification (typically `ref_count >= 1` for `MD<Frame>`, mirroring
/// `Frame::from_raw`'s safety condition).
///
/// At the time of this redesign no ostd callsite extracts a `Frame` from
/// a `ManuallyDrop<Frame>` (only `Deref` borrows are taken; the one
/// `into_inner` is on `MD<Arc<T>>`, not `MD<Frame>`). Adding such an
/// extraction without the matching mint resurrects the double-counting
/// bug that motivated this redesign.
pub struct ManuallyDrop<T: TrackDrop>(pub T);

impl<T: TrackDrop> ManuallyDrop<T> {
    #[verifier::external_body]
    pub fn new(t: T, Tracked(s): Tracked<&mut T::State>) -> (res: Self)
        requires
            t.consume_requires(*old(s)),
        ensures
            t.consume_ensures(*old(s), *final(s)),
            res.0 == t,
    {
        proof {
            // Materialize a ledger-less identity token for `t.key()` and
            // immediately discharge it via `T::consume_obligation`. The
            // caller's `consume_requires` precondition guarantees there
            // is an outstanding ledger entry at this key for the redeem
            // axiom to remove.
            let tracked obl = DropObligation::tracked_mint(t.key());
            t.consume_obligation(s, obl);
        }
        Self(t)
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

} // verus!
