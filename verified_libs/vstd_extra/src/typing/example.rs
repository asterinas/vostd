//! `core::any::Any` exercised on three types, covering the behaviors that
//! motivate it: upcast, downcast, and dispatch.
//!
//! # What this used to be
//!
//! Twice over. First a three-member aggregate, `L1 | (L2 | L3)`, built to check
//! that *uniqueness composes*: each nesting node had to show its two sides
//! claimed disjoint sets of hand-picked ids. Then a version written against a
//! local duplicate of `Any`'s interface, with a spec fn in the vtable and a
//! per-impl obligation tying it to `type_id::<Self>()`.
//!
//! Neither has anything left to prove. Identity is `type_id::<T>()`, so
//! distinctness is not an obligation and there is no world to close; and the
//! identity of the type *inside* an erased value is `type_id_of`, so no trait of
//! our own has to carry it. What remains is the part that was always the point:
//! an erased value can say what it is, and a downcast admits exactly one type.
//!
//! # Three members, still
//!
//! Kept at three rather than two so the rejection case is not degenerate: with
//! two members, "rejects the other" and "rejects everything that is not me"
//! cannot be told apart.
use vstd::prelude::*;

use core::any::Any;

verus! {

pub struct L1(pub u64);

pub struct L2(pub u64);

pub struct L3(pub u64);

// ------------------------------------------------------------------
// Upcast.
// ------------------------------------------------------------------
/// A concrete value, viewed as an erased one.
///
/// The postcondition is what makes the result usable, and it is about the type
/// erased *into* the object rather than about `dyn Any` itself -- those are
/// different questions, and only this one survives the coercion.
pub exec fn upcast_l2(v: &L2) -> (r: &dyn Any)
    ensures
        type_id_of(r) == type_id::<L2>(),
{
    v
}

// ------------------------------------------------------------------
// Downcast.
// ------------------------------------------------------------------
/// An erased `L2` is an `L2`, and is neither an `L1` nor an `L3`.
///
/// Both halves matter. The first is what a downcast needs in order to succeed;
/// the second is the soundness property, and it is the one a closed-world model
/// has to pay for with an explicit disjointness witness per pair of members.
/// Here it is definitional, because the ids are real type ids.
pub proof fn erased_is_exactly_one(x: &dyn Any)
    requires
        type_id_of(x) == type_id::<L2>(),
    ensures
        type_id_of(x) == type_id::<L2>(),
        type_id_of(x) != type_id::<L1>(),
        type_id_of(x) != type_id::<L3>(),
{
}

/// Identifying an erased value, with no precondition at all.
///
/// The caller does not have to know what `x` is, and the `<==>` is strong enough
/// to conclude both that a match means an `L2`'s id and that a non-match rules
/// it out.
pub exec fn is_l2(x: &dyn Any) -> (r: bool)
    ensures
        r <==> type_id_of(x) == type_id::<L2>(),
{
    x.is::<L2>()
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
    assert(type_id_of(eb) == type_id::<L2>());
    assert(type_id_of(ec) == type_id::<L3>());
    let ok = is_l2(eb);
    assert(ok);
    let no = is_l2(ec);
    assert(!no);
}

/// Distinct members never satisfy each other's test.
///
/// This is what stops an `L2` being mistaken for an `L1`, and it is why
/// [`is_l2`]'s rejecting half is sound rather than merely stated. It used to
/// need a lemma relating each value's recorded id to its type's; `type_id_of`
/// *is* that relation, so the body is empty.
pub proof fn downcast_rejects_others(a: &L1, b: &L2, c: &L3)
    ensures
        type_id_of(a) != type_id_of(b),
        type_id_of(b) != type_id_of(c),
        type_id_of(a) != type_id_of(c),
{
}

// ------------------------------------------------------------------
// Dispatch.
// ------------------------------------------------------------------
/// A trait the members share, so that an erased value can be *run* and not
/// merely identified.
///
/// Separate from `Any` on purpose: the two erasures answer different questions.
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

/// Both erasures of one value, and the identity that survives the first.
///
/// `Payload` dispatch and `Any` identification are independent: a value can be
/// erased either way, and asking one question does not require the other's
/// vtable.
pub exec fn both_erasures(v: &L2) -> (r: bool)
    ensures
        r,
{
    let p: &dyn Payload = v;
    let a: &dyn Any = v;
    let w = p.word();
    assert(w == v.0);
    is_l2(a)
}

} // verus!
