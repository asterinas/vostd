//! A specification for [`core::mem::transmute`].
//!
//! `transmute` is not one operation but a family. Whether a `Src` value may be
//! read as a `Dst`, and what it becomes if it may, depends entirely on the pair.
//! So the specification here says almost nothing on its own: it fixes the
//! *shape* -- [`can_transmute`] decides which values may be reinterpreted,
//! [`transmuted`] says what they become -- and leaves both uninterpreted.
//! Knowledge is added one shape at a time, by axioms constraining them for a
//! particular pair of types.
//!
//! Two properties follow from that arrangement, and both are deliberate.
//!
//! **It is partial.** `can_transmute` is a precondition, not a theorem. A pair
//! with no axiom covering it cannot be transmuted at all, which is
//! incompleteness rather than unsoundness -- the failure mode is a proof that
//! does not go through, never a wrong one. Padding bytes, niches and validity
//! invariants all live in this predicate.
//!
//! **It is directed.** An axiom for `Src -> Dst` says nothing about
//! `Dst -> Src`. A `bool` may be read as a `u8` always; a `u8` as a `bool` only
//! for `0` and `1`. Anything stated as a biconditional here would be wrong.
//!
//! # Adding an axiom
//!
//! Each one is an obligation, not a convenience: it asserts a layout fact that
//! Rust does not otherwise guarantee, and nothing checks it. Cite the guarantee
//! that makes it true -- `#[repr(transparent)]`, `#[repr(C)]`, or an explicit
//! promise in the reference -- at the axiom itself.
//!
//! Keep them minimal in a second sense too. An axiom about *representation*
//! should not smuggle in a claim about *identity*: that a reinterpreted value has
//! some particular meaning is a separate question, and answering it here would
//! make the axiom far stronger than the layout fact justifying it.
//!
//! [`axiom_transmute_refl`] is the only axiom supplied here, because it is the
//! only one true at every type.
use vstd::prelude::*;

verus! {

/// Whether `src` may be reinterpreted as a `Dst`.
///
/// Uninterpreted: false for every pair until an axiom says otherwise.
pub uninterp spec fn can_transmute<Src, Dst>(src: Src) -> bool;

/// The `Dst` value that `src` reinterprets to.
///
/// Only meaningful where [`can_transmute`] holds; unconstrained elsewhere.
pub uninterp spec fn transmuted<Src, Dst>(src: Src) -> Dst;

pub assume_specification<Src, Dst>[ core::mem::transmute::<Src, Dst> ](src: Src) -> (dst: Dst)
    requires
        can_transmute::<Src, Dst>(src),
    ensures
        dst == transmuted::<Src, Dst>(src),
;

/// Every value may be read as its own type, and is unchanged by it.
///
/// The one pair needing no layout argument, since there is no reinterpretation:
/// `Src` and `Dst` are the same type.
#[verifier::external_body]
pub proof fn axiom_transmute_refl<T>(v: T)
    ensures
        can_transmute::<T, T>(v),
        transmuted::<T, T>(v) == v,
{
}

} // verus!
