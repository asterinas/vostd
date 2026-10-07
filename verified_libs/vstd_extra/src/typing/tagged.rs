//! Runtime type identity for erased bytes, bounded by a maximum size.
//!
//! A value stored as raw bytes has no way to say what it is. This module supplies
//! the missing piece: [`TaggedArray`] carries the bytes together with a ghost
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
pub trait ByteSized<const SIZE: usize>: Sized {
    proof fn size_correct()
        ensures
            size_of::<Self>() <= SIZE,
    ;
}

/// A type whose values can be encoded into `SIZE` bytes and recovered.
///
/// `round_trip` goes from value to bytes and back, and we do not assume the converse.
/// That means that if the type contains padding, we make no claims about its value after
/// a write-to-bytes; only that when we later read-from-bytes we will get what was written.
pub trait ByteRepr<const SIZE: usize>: ByteSized<SIZE> + TryFromSpec<[u8; SIZE]> + IntoSpec<
    [u8; SIZE],
> {
    proof fn round_trip(self)
        ensures
            Self::try_from_spec(self.into_spec()) == Ok(self),
    ;

    /// The executable conversions agree with their specifications.
    proof fn obeys()
        ensures
            Self::obeys_into_spec(),
            Self::obeys_try_from_spec(),
    ;
}

/// AXIOM: Reinterpret stored bytes as a reference to the value they encode.
#[verifier::external_body]
pub exec fn borrow_as<'a, const SIZE: usize, T: ByteRepr<SIZE>>(data: &'a [u8; SIZE]) -> (r: &'a T)
    requires
        T::try_from_spec(*data) is Ok,
    ensures
        *r == T::try_from_spec(*data)->Ok_0,
{
    unimplemented!()
}

/// The type of a recorded type identity.
///
/// `core::any::TypeId` where the toolchain supports it, and an opaque `int` otherwise
#[cfg(feature = "type_id")]
pub type RecordedId = core::any::TypeId;

#[cfg(not(feature = "type_id"))]
pub type RecordedId = int;

/// The identity recorded for type `T`.
#[cfg(feature = "type_id")]
pub open spec fn recorded_id<T: ?Sized>() -> RecordedId {
    type_id::<T>()
}

/// Uninterpreted without the feature: distinct types cannot be told apart, so a
/// downcast's precondition is simply not dischargeable. That is incompleteness,
/// not unsoundness.
#[cfg(not(feature = "type_id"))]
pub uninterp spec fn recorded_id<T: ?Sized>() -> RecordedId;

/// Bytes plus a ghost id naming the type they hold.
pub struct TaggedArray<const SIZE: usize> {
    /// The stored type's identity, as ghost state.
    pub id: Ghost<RecordedId>,
    pub data: [u8; SIZE],
}

impl<const SIZE: usize> TaggedArray<SIZE> {
    /// These bytes hold a `T`, and the recorded id says so.
    pub open spec fn holds<T: ByteRepr<SIZE>>(self) -> bool {
        &&& self.id@ == recorded_id::<T>()
        &&& T::try_from_spec(self.data) is Ok
    }

    /// The stored value, where [`Self::holds`] says there is one.
    pub open spec fn value<T: ByteRepr<SIZE>>(self) -> T {
        T::try_from_spec(self.data)->Ok_0
    }

    /// Store a value, recording its type.
    pub exec fn store<T: ByteRepr<SIZE>>(t: T) -> (r: Self)
        ensures
            r.holds::<T>(),
            r.value::<T>() == t,
    {
        let ghost t0 = t;
        proof {
            T::obeys();
            t0.round_trip();
        }
        TaggedArray { id: Ghost(recorded_id::<T>()), data: t.into() }
    }

    /// Read the stored value in place.
    ///
    /// Rests on [`borrow_as`], whose precondition is exactly the decode-success
    /// that [`Self::holds`] carries.
    pub exec fn borrow<'a, T: ByteRepr<SIZE>>(&'a self) -> (r: &'a T)
        requires
            self.holds::<T>(),
        ensures
            *r == self.value::<T>(),
    {
        borrow_as::<SIZE, T>(&self.data)
    }
}

} // verus!
