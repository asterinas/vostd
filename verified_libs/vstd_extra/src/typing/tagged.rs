//! Runtime type identity for erased bytes, bounded by a maximum size.
//!
//! A value stored as raw bytes has no way to say what it is. This module supplies
//! the missing piece: [`TaggedArray`] carries the bytes together with a ghost
//! record of the stored type's identity. It axiomatizes loads and stores of whole
//! objects, not details of the bytes, which may have any layout. The objects thus
//! stored are not restricted to being plain-old-data.
use vstd::prelude::*;

verus! {

/// A type that fits in `SIZE` bytes, and may therefore be stored in `SIZE`
/// bytes of tagged storage.
pub trait MaxSize<const SIZE: usize>: Sized {
    proof fn size_correct()
        ensures
            size_of::<Self>() <= SIZE,
    ;
}

/// The type of a recorded type identity.
///
/// `core::any::TypeId` where the toolchain supports it, and an opaque `int` otherwise
#[cfg(feature = "type_id")]
pub type RecordedId = core::any::TypeId;

#[cfg(not(feature = "type_id"))]
pub type RecordedId = int;

#[cfg(feature = "type_id")]
pub open spec fn recorded_id<T: ?Sized>() -> RecordedId {
    type_id::<T>()
}

#[cfg(not(feature = "type_id"))]
pub uninterp spec fn recorded_id<T: ?Sized>() -> RecordedId;

/// Interpret the contents of the array as a value of type `T`.
/// The contents of the array are indexed by an integer, `store_id`,
/// which is incremented every time the array is updated. This allows us
/// to axiomatize the connection between the written value and future reads
/// without carrying the value directly (which we cannot do, as it has no known type!)
///
/// Uninterpreted, so the only facts about it are those `store` establishes. For
/// a model to exist it must be surjective onto `T`, i.e. `T` must have at most
/// countably many values -- true of every executable type.
///
/// # Upgrade path
///
/// This is the weakest form of a pattern the RCU proofs already run properly:
/// [`crate::rcu_objects::RcuDomainAuth`] mints fresh ghost identities from a
/// monotone `next_obj` counter and publishes facts about them as
/// `GhostPersistentPointsTo`. Replacing `stored` with a `GhostMapAuth<nat, T>`
/// plus persistent points-to would buy two things:
///
/// - Freshness by construction, retiring the surjectivity side condition above.
/// - Duplicable read facts. A persistent "store `s` holds `v`" can be copied
///   freely.
pub uninterp spec fn stored<const SIZE: usize, T>(store_id: int) -> T;

/// Bytes, plus ghost records of what type they hold and which store put it there.
pub struct TaggedArray<const SIZE: usize> {
    /// The stored type's identity, as ghost state.
    pub id: Ghost<RecordedId>,
    pub store_id: Ghost<int>,
    pub data: [u8; SIZE],
}

impl<const SIZE: usize> TaggedArray<SIZE> {
    /// The recorded id corresponds to type `T`
    pub open spec fn holds<T: MaxSize<SIZE>>(self) -> bool {
        self.id@ == recorded_id::<T>()
    }

    /// The stored value, interpreted as type `T`
    pub open spec fn value<T: MaxSize<SIZE>>(self) -> T {
        stored::<SIZE, T>(self.store_id@)
    }

    /// Store a value, recording its type.
    ///
    /// This module's only axiom: what was written is what is read,
    /// for a read at the type that was written. [`Self::holds`] is the "well
    /// typed" proviso -- a read at another type learns nothing, because
    /// [`stored`] is indexed by `T` and no axiom relates two instantiations.
    #[verifier::external_body]
    pub exec fn store<T: MaxSize<SIZE>>(t: T) -> (r: Self)
        ensures
            r.holds::<T>(),
            r.value::<T>() == t,
    {
        let mut data = [0u8;SIZE];
        unsafe {
            core::ptr::copy_nonoverlapping(
                &t as *const T as *const u8,
                data.as_mut_ptr(),
                core::mem::size_of::<T>(),
            );
        }
        core::mem::forget(t);
        TaggedArray { id: Ghost(recorded_id::<T>()), store_id: Ghost(arbitrary()), data }
    }
}

} // verus!
