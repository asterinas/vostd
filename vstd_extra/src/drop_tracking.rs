use core::{marker::PhantomData, ops::Deref};
use vstd::prelude::*;

verus! {

/// A linear-looking "must drop" obligation tied to a value of type `R`.
///
/// `R` is the *key* type used to identify the resource in the State's
/// obligation ledger — e.g. `Range<Paddr>` for a `Segment<M>`, `usize` for a
/// per-slot resource. Two-layer enforcement (the design that survives Verus's
/// affineness):
///
/// 1. **Token (this type)**: opaque tracked struct, no exec fields, no public
///    constructor. Cannot be forged. The only producer is
///    [`DropObligation::tracked_mint`] (an axiom intended to be called only
///    from a state-mutating ledger insertion, see e.g.
///    [`MetaRegionOwners::tracked_mint_obligation`]).
/// 2. **Ledger (in State)**: a set in the State that tracks outstanding keys.
///    Constructor adds; drop removes. The State's `clean_inv()` (or any
///    boundary predicate) requires the set to be empty, so a silently-dropped
///    token leaves the ledger non-empty and the boundary check fails at the
///    enclosing function's exit.
///
/// **Why both are needed.** The token alone is insufficient because Verus
/// tracked values are affine — `let tracked _ = obl;` silently discharges
/// them. The ledger alone is insufficient because a caller could write
/// `regions.obligations.tracked_remove(key)` directly. The combination is
/// sound: the only spec/proof that shrinks `obligations()` is the redeem
/// axiom, which requires a real token to consume.
#[verifier::reject_recursive_types(R)]
pub tracked struct DropObligation<R> {
    /// The ghost identity this obligation is bound to. Private — callers
    /// can't fabricate one via struct literal.
    value: R,
}

impl<R> DropObligation<R> {
    pub closed spec fn value(self) -> R {
        self.value
    }

    /// Mint a fresh obligation token. This is an **axiom**: callers must
    /// only invoke it as part of a state mutation that also inserts `value`
    /// into the State's ledger (see `MetaRegionOwners::tracked_mint_obligation`).
    /// Calling it without such a paired ledger insert is unsound.
    #[verifier::external_body]
    pub proof fn tracked_mint(value: R) -> (tracked res: DropObligation<R>)
        ensures
            res.value() == value,
    {
        unimplemented!()
    }
}

/// State that carries an obligation ledger keyed by `Key`.
///
/// Implemented by, e.g., `MetaRegionOwners` (with `Key = Range<Paddr>` for
/// segments — extend with a sum-type Key as more resource types migrate).
pub trait HasObligations {
    type Key;

    spec fn obligations(self) -> Set<Self::Key>;
}

pub trait TrackDrop {
    type State;

    spec fn constructor_requires(self, s: Self::State) -> bool;

    spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool;

    #[verifier::returns(proof)]
    proof fn constructor_spec(self, tracked s: &mut Self::State)
        requires
            self.constructor_requires(*old(s)),
        ensures
            self.constructor_ensures(*old(s), *final(s)),
    ;

    spec fn drop_requires(self, s: Self::State) -> bool;

    spec fn drop_ensures(self, s0: Self::State, s1: Self::State) -> bool;
}

pub trait Drop: TrackDrop {
    fn drop(self, Tracked(s): Tracked<&mut Self::State>)
        requires
            self.drop_requires(*old(s)),
        ensures
            self.drop_ensures(*old(s), *final(s)),
    ;
}

pub struct ManuallyDrop<T: TrackDrop>(pub T);

impl<T: TrackDrop> ManuallyDrop<T> {
    #[verifier::external_body]
    pub fn new(t: T, Tracked(s): Tracked<&mut T::State>) -> (res: Self)
        requires
            t.constructor_requires(*old(s)),
        ensures
            t.constructor_ensures(*old(s), *final(s)),
            res.0 == t,
    {
        proof {
            t.constructor_spec(s);
        }
        Self(t)
    }
}

impl<T: Drop> ManuallyDrop<T> {
    pub fn drop(self, Tracked(s): Tracked<&mut T::State>)
        requires
            self.0.drop_requires(*old(s)),
        ensures
            self.0.drop_ensures(*old(s), *final(s)),
    {
        self.0.drop(Tracked(s))
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
