//! [`Any`] exercised on three types, covering the behaviors that motivate it:
//! upcast, downcast, and dispatch.
//!
//! # What this used to be
//!
//! A three-member aggregate, `L1 | (L2 | L3)`, built to check that *uniqueness
//! composes*: each nesting node had to show its two sides claimed disjoint sets of
//! hand-picked ids, and the example existed largely to demonstrate that those
//! obligations were independent of one another.
//!
//! None of that has anything to prove now. Identity is `type_id::<T>()`, so
//! distinctness is not an obligation and there is no world to close — a type does
//! not need to be enrolled in an aggregate before it can be identified. What
//! remains is the part that was always the point: an erased value can say what it
//! is, and a downcast admits exactly one type.
//!
//! # Three members, still
//!
//! Kept at three rather than two so the rejection case is not degenerate: with two
//! members, "rejects the other" and "rejects everything that is not me" cannot be
//! told apart.
use vstd::prelude::*;

use super::types::*;

verus! {

pub struct L1(pub u64);

pub struct L2(pub u64);

pub struct L3(pub u64);

// ------------------------------------------------------------------
// Upcast.
// ------------------------------------------------------------------
/// A concrete value, viewed as an erased one.
///
/// The postcondition is what makes the result usable: `type_id` is declared by
/// [`Any`] itself and is not `where Self: Sized`, so it is in the vtable and
/// survives the coercion. Without it the result would be an object nothing could
/// be concluded about.
pub exec fn upcast_l2(v: &L2) -> (r: &dyn Any)
    ensures
        r.type_id_spec() == type_id::<L2>(),
{
    v
}

// ------------------------------------------------------------------
// Downcast.
// ------------------------------------------------------------------
/// An erased `L2` is an `L2`, and is neither an `L1` nor an `L3`.
///
/// Both halves matter. The first is what a downcast needs in order to succeed;
/// the second is the soundness property, and it is the one that used to cost a
/// `DisjointFrom` witness at every node joining the members. It is now
/// definitional.
pub proof fn erased_is_exactly_one(x: &dyn Any)
    requires
        x.type_id_spec() == type_id::<L2>(),
    ensures
        is_type::<L2>(x),
        !is_type::<L1>(x),
        !is_type::<L3>(x),
{
}

/// Identifying an erased value, with no precondition at all.
///
/// The caller does not have to know what `x` is, and the `<==>` is strong enough
/// to conclude both that a match means an `L2`'s tag and that a non-match rules
/// it out.
pub exec fn is_l2(x: &dyn Any) -> (r: bool)
    ensures
        r <==> x.type_id_spec() == type_id::<L2>(),
{
    is_::<L2>(x)
}

/// The test discriminates, executably.
///
/// An `L2` is accepted and an `L3` is rejected, with neither branch assumed.
pub exec fn downcast_discriminates(b: &L2, c: &L3)
    ensures
        true,
{
    let eb: &dyn Any = b;
    let ec: &dyn Any = c;
    assert(eb.type_id_spec() == type_id::<L2>());
    assert(ec.type_id_spec() == type_id::<L3>());
    let ok = is_l2(eb);
    assert(ok);
    let no = is_l2(ec);
    assert(!no);
}

/// Distinct members never satisfy each other's test.
///
/// This is what stops an `L2` being mistaken for an `L1`, and it is why [`is_l2`]'s
/// rejecting half is sound rather than merely stated.
pub proof fn downcast_rejects_others(a: &L1, b: &L2, c: &L3)
    ensures
        a.type_id_spec() != b.type_id_spec(),
        b.type_id_spec() != c.type_id_spec(),
        a.type_id_spec() != c.type_id_spec(),
{
    lemma_distinct_types_distinct_values::<L1, L2>(a, b);
    lemma_distinct_types_distinct_values::<L2, L3>(b, c);
    lemma_distinct_types_distinct_values::<L1, L3>(a, c);
}

// ------------------------------------------------------------------
// Dispatch.
// ------------------------------------------------------------------
/// A trait the members share, so that an erased value can be *run* and not merely
/// identified.
///
/// Separate from [`Any`] on purpose: the two erasures answer different questions.
/// `Any` says which type it is; `Payload` runs its code.
pub trait Payload {
    spec fn word_spec(&self) -> u64;

    fn word(&self) -> (r: u64)
        ensures
            r == self.word_spec(),
    ;
}

impl Payload for L1 {
    open spec fn word_spec(&self) -> u64 {
        self.0
    }

    fn word(&self) -> (r: u64) {
        self.0
    }
}

impl Payload for L2 {
    open spec fn word_spec(&self) -> u64 {
        self.0
    }

    fn word(&self) -> (r: u64) {
        self.0
    }
}

impl Payload for L3 {
    open spec fn word_spec(&self) -> u64 {
        self.0
    }

    fn word(&self) -> (r: u64) {
        self.0
    }
}

/// A real vtable call through an erased reference.
pub exec fn dispatch(d: &dyn Payload) -> (r: u64)
    ensures
        r == d.word_spec(),
{
    d.word()
}

/// End to end: erase a member, then run its code, with the result pinned to the
/// value that was erased.
pub exec fn erase_then_dispatch(v: L2) -> (r: u64)
    ensures
        r == v.0,
{
    let d: &dyn Payload = &v;
    dispatch(d)
}

} // verus!
