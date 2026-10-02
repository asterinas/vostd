//! Runtime type identity for erased bytes, bounded by a maximum size.
//!
//! A value stored as raw bytes has no way to say what it is. This module supplies
//! the missing piece: [`OpenTaggedArray`] carries the bytes together with a ghost
//! record of the stored type's identity, and [`ByteRepr`] is what lets a type be
//! stored in the first place.
//!
//! The world is **open**. The only restriction on what may be stored is that it
//! fit in `SIZE` bytes -- there is no enumeration of admissible types, so a
//! generic family with infinitely many instantiations needs no special treatment.
//! What is given up in exchange is exhaustiveness: there is no "the value is one
//! of these" law, only "is it this type", asked one type at a time.
//!
//! Deliberately usable without the `type_id` toolchain patch. The sibling
//! [`super::types`] models `core::any::TypeId` directly and so needs it; here the
//! id type degrades to an opaque `int`, which keeps the storage available in every
//! feature shape and confines the patch to *deciding* identity.
use vstd::prelude::*;

use vstd::std_specs::convert::{IntoSpec, TryFromSpec};

verus! {

// ===========================================================================
// Representation
// ===========================================================================
//
/// A type that fits in `SIZE` bytes.
///
/// `<=`, not `==`. Members of one aggregate are generally different sizes and sit
/// in the array with padding -- a metadata slot's members are all smaller than
/// the slot, and the frame layer's own `impl_frame_meta_for!` already checks
/// exactly this inequality. Demanding equality would admit only aggregates whose
/// members happen to be uniform.
///
/// The slack is a second reason [`CanonicalRepr`] is separate: where a value is
/// strictly smaller than the array, the leftover bytes are unconstrained, so
/// encoding cannot be onto.
pub trait ByteSized<const SIZE: usize>: Sized {
    proof fn size_correct()
        ensures
            size_of::<Self>() <= SIZE,
    ;
}

/// A type whose values can be encoded into `SIZE` bytes and recovered.
///
/// `round_trip` is the *only* law, and that is deliberate: it is all
/// [`lemma_leaf_holds`] needs, so it is all membership in an aggregate should
/// cost. See [`CanonicalRepr`] for the converse direction, which is a strictly
/// stronger claim and not always a true one.
pub trait ByteRepr<const SIZE: usize>: ByteSized<SIZE> + TryFromSpec<[u8; SIZE]> + IntoSpec<
    [u8; SIZE],
> {
    proof fn round_trip(self)
        ensures
            Self::try_from_spec(self.into_spec()) == Ok(self),
    ;

    /// The executable conversions agree with their specifications.
    ///
    /// `IntoSpec` and `TryFromSpec` both gate their postconditions on an
    /// `obeys_*` flag, so without this a *generic* `M: ByteRepr<SIZE>` cannot
    /// conclude anything from calling `into`/`try_from` -- which is most of the
    /// point of the bound. Every impl proves it trivially; a representation whose
    /// exec conversions do not match their specs is not one.
    proof fn obeys()
        ensures
            Self::obeys_into_spec(),
            Self::obeys_try_from_spec(),
    ;
}

/// A [`ByteRepr`] whose encoding is onto: every valid byte pattern is some
/// value's encoding.
///
/// Split from [`ByteRepr`] because it is **not true of every representable
/// type**, and the types it fails for are ones a metadata slot really holds. A
/// `PCell`'s value includes an abstract cell id that is nowhere in memory, so two
/// cells differing only in id share a byte pattern; `canonical` would force
/// decoding to recover an id the bytes do not contain. Requiring it of all
/// members would mean axiomatizing that for exactly the types where it is false.
///
/// Implement it for plain-old-data members, where it is a genuine layout fact,
/// and leave it off anything carrying a cell or an atomic.
pub trait CanonicalRepr<const SIZE: usize>: ByteRepr<SIZE> {
    proof fn canonical(data: [u8; SIZE])
        requires
            Self::try_from_spec(data) is Ok,
        ensures
            Self::try_from_spec(data)->Ok_0.into_spec() == data,
    ;
}

/// Reinterpret stored bytes as a reference to the value they encode.
///
/// # The one axiom
///
/// It cannot be proved. Verus has no model of the pointer cast involved, and the
/// fact being asserted is that a byte pattern satisfying `M`'s decode really may
/// be *read as* an `M` in place, rather than decoded into a fresh value. That is
/// a statement about layout, which is why the precondition is exactly the decode
/// and nothing weaker: bytes that do not decode may not be borrowed at all.
///
/// Note what this is *not*: it says nothing about identity. Deciding which type a
/// stored value is belongs to [`Any`], and with a `&M` in hand the ordinary
/// `&M -> &dyn Any` coercion carries the identity across.
#[verifier::external_body]
pub exec fn borrow_as<'a, const SIZE: usize, M: ByteRepr<SIZE>>(data: &'a [u8; SIZE]) -> (r: &'a M)
    requires
        M::try_from_spec(*data) is Ok,
    ensures
        *r == M::try_from_spec(*data)->Ok_0,
{
    unimplemented!()
}

/// Distinct valid byte patterns decode to distinct values.
///
/// The content of [`ByteRepr::canonical`], stated the way it is usually wanted:
/// decoding is injective on valid patterns. Together with
/// [`ByteRepr::round_trip`] — which makes it surjective onto values — this is the
/// bijection a storage abstraction needs in order to promise that reading a value
/// out and writing it back leaves the bytes alone.
pub proof fn lemma_decode_injective<const SIZE: usize, M: CanonicalRepr<SIZE>>(
    a: [u8; SIZE],
    b: [u8; SIZE],
)
    requires
        M::try_from_spec(a) is Ok,
        M::try_from_spec(b) is Ok,
        M::try_from_spec(a) == M::try_from_spec(b),
    ensures
        a == b,
{
    M::canonical(a);
    M::canonical(b);
}

// ===========================================================================
// Open world
// ===========================================================================
//
// Everything above closes the world: an aggregate enumerates its members as a
// `Leaf`/`Node` tree and discharges disjointness per node. That buys exhaustive
// dispatch -- `Either::type_id_laws` says a value is *exactly one* member -- at
// the price of naming every member, which an infinite family such as
// `Slab<const SLOT_SIZE>` cannot be.
//
// Below is the open-world alternative. The only restriction on what may be stored
// is that it fit in `SIZE` bytes, and identity is the *real* recorded type id
// rather than a `nat` assigned by hand. Nothing is enumerated, so nothing has to
// nest: an inner member is simply another type with a representation.
//
// The trade is exhaustiveness. There is no "exactly one of" law, because there is
// no fixed set to be one of -- only "is it this type", asked one type at a time.

/// The type of a recorded type identity.
///
/// `core::any::TypeId` where the toolchain supports it, and an opaque `int`
/// otherwise, so that the storage below is available in every feature shape and
/// only *deciding* identity needs the patch.
#[cfg(feature = "type_id")]
pub type RecordedId = core::any::TypeId;

#[cfg(not(feature = "type_id"))]
pub type RecordedId = int;

/// The identity recorded for type `M`.
#[cfg(feature = "type_id")]
pub open spec fn recorded_id<M: ?Sized>() -> RecordedId {
    type_id::<M>()
}

/// Uninterpreted without the feature: distinct types cannot be told apart, so a
/// downcast's precondition is simply not dischargeable. That is incompleteness,
/// not unsoundness -- see [`OpenTaggedArray::borrow`].
#[cfg(not(feature = "type_id"))]
pub uninterp spec fn recorded_id<M: ?Sized>() -> RecordedId;

/// Bytes plus a ghost id naming the type they hold, with the admissible types
/// left open and bounded only by `SIZE`.
///
/// # Why there is no law here
///
/// An id invented by the storage layer would need its own laws -- something saying
/// which ids are admissible, and a witness per pair that two members cannot claim
/// the same one -- because nothing about an invented tag makes it match the bytes
/// beside it. Here the id *is* the type's identity, and [`Self::holds`] states
/// decode-success directly rather than through an uninterpreted predicate. The
/// result is that this abstraction adds **no axiom of its own**: a writer
/// establishes `holds` from [`ByteRepr::round_trip`], and a reader consumes it.
///
/// Reading at the wrong type is prevented by arithmetic rather than by a law. To
/// borrow these bytes as a `B`, a caller must show `self.id@ == recorded_id::<B>()`;
/// for bytes stored as an `A` that means showing `recorded_id::<A>()` and
/// `recorded_id::<B>()` are equal, which is *disprovable* under the `type_id`
/// feature and merely unprovable without it. Either way the precondition cannot be
/// met, so no appeal to injectivity is needed.
pub struct OpenTaggedArray<const SIZE: usize> {
    /// The stored type's identity, as ghost state. Zero-sized, so the runtime
    /// footprint is still just the bytes.
    pub id: Ghost<RecordedId>,
    pub data: [u8; SIZE],
}

impl<const SIZE: usize> OpenTaggedArray<SIZE> {
    /// These bytes hold an `M`, and the recorded id says so.
    ///
    /// Both conjuncts are load-bearing. Decode-success alone is too weak -- two
    /// types may well admit one byte pattern -- and the id alone says nothing
    /// about the bytes.
    pub open spec fn holds<M: ByteRepr<SIZE>>(self) -> bool {
        &&& self.id@ == recorded_id::<M>()
        &&& M::try_from_spec(self.data) is Ok
    }

    /// The stored value, where [`Self::holds`] says there is one.
    pub open spec fn value<M: ByteRepr<SIZE>>(self) -> M {
        M::try_from_spec(self.data)->Ok_0
    }

    /// Store a value, recording its type.
    pub exec fn store<M: ByteRepr<SIZE>>(m: M) -> (r: Self)
        ensures
            r.holds::<M>(),
            r.value::<M>() == m,
    {
        let ghost m0 = m;
        proof {
            M::obeys();
            m0.round_trip();
        }
        OpenTaggedArray { id: Ghost(recorded_id::<M>()), data: m.into() }
    }

    /// Read the stored value in place.
    ///
    /// Rests on [`borrow_as`], whose precondition is exactly the decode-success
    /// that [`Self::holds`] carries.
    pub exec fn borrow<'a, M: ByteRepr<SIZE>>(&'a self) -> (r: &'a M)
        requires
            self.holds::<M>(),
        ensures
            *r == self.value::<M>(),
    {
        borrow_as::<SIZE, M>(&self.data)
    }
}

} // verus!
