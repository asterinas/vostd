//! Runtime type identity for erased bytes, bounded by a maximum size.
//!
//! A value stored as raw bytes has no way to say what it is. This module supplies
//! the missing piece: [`TaggedArray`] carries the bytes together with a ghost
//! record of the stored type's identity. It axiomatizes loads and stores of whole
//! objects, not details of the bytes, which may have any layout. The objects thus
//! stored are not restricted to being plain-old-data.
use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;

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
    ///
    /// Where `T` holds cells, the claim covers their identities: the cell in
    /// `data` is a byte copy of the one in `t`, and this says the copy *is*
    /// that cell. VerusBelt's `Heap-Move-Cell` is the rule for that --
    /// `{l |-> c * l' |-> v'} *l' := *l {exists v. l |-> v * l' |-> c}` --
    /// and it "does not even require ownership of the second half (`c |-> v`);
    /// this helps us show that we can move a `PCell` without ownership of its
    /// `PCell::PointsTo`". Which is the situation here: a caller may well have
    /// dropped the contents' permission before storing. See
    /// [`crate::substructural::cell`] for the citation.
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

/// A type whose representation *is* a [`TaggedArray`] of `SIZE` bytes.
///
/// `unsafe` because implementing it asserts a layout fact Rust does not
/// otherwise guarantee and Verus cannot state: that the array's bytes begin at
/// `Self`'s own address. Implement it only for a `#[repr(transparent)]` (or
/// `#[repr(C)]`, array first) wrapper. The promise bottoms out in
/// [`TaggedArray`]'s `data` being at offset 0, which holds because its other
/// fields are `Ghost` and so zero-sized.
///
/// [`Self::array_injective`] is the part of that promise which *can* be
/// stated, and it is why [`as_perm_mut`] need say nothing about the rest of
/// `Self`: there is no rest. It is also what stops the obvious misuse -- a
/// wrapper with extra fields beside the array cannot discharge it.
pub unsafe trait TaggedStorage<const SIZE: usize>: Sized {
    /// The array this value is.
    spec fn array(self) -> TaggedArray<SIZE>;

    /// A wrapper holds nothing but its array, so the array determines it.
    proof fn array_injective(s1: Self, s2: Self)
        ensures
            s1.array() == s2.array() ==> s1 == s2,
    ;
}

/// Reinterprets a permission for tagged storage as a permission for the `T`
/// that storage holds.
///
/// TRUSTED. [`TaggedArray::holds`] is what makes it defensible: the bytes carry
/// `T`'s recorded tag, so the reinterpretation is the identity on memory -- the
/// bytes *are* the `T`, in place -- and the address is the storage's own, so no
/// new provenance is invented. It re-types ownership that already exists rather
/// than conjuring any.
pub axiom fn as_perm<'a, const SIZE: usize, S: TaggedStorage<SIZE>, T: MaxSize<SIZE>>(
    tracked perm: &'a PointsTo<S>,
) -> (tracked res: &'a PointsTo<T>)
    requires
        perm.is_init(),
        perm.value().array().holds::<T>(),
    ensures
        res.addr() == perm.addr(),
        res.is_init(),
        res.value() == perm.value().array().value::<T>(),
;

/// The mutable counterpart.
///
/// The two `final` clauses are the ones that carry weight. The tag survives a
/// write -- it is ghost state no byte write can reach -- and the stored value
/// becomes whatever the borrow ends up holding, which under [`stored`] means
/// the array is renamed to a fresh `store_id`. So this is the in-place sibling
/// of [`TaggedArray::store`]'s law rather than a separate kind of claim:
/// `store` says a whole-array write names its value, this says a write through
/// the borrow renames it.
///
/// `perm` is taken by `&mut`, which is what keeps it sound: the borrow checker
/// freezes the storage permission for all of `'a`, so there is no point at
/// which the two permissions are both observable and disagree.
pub axiom fn as_perm_mut<'a, const SIZE: usize, S: TaggedStorage<SIZE>, T: MaxSize<SIZE>>(
    tracked perm: &'a mut PointsTo<S>,
) -> (tracked res: &'a mut PointsTo<T>)
    requires
        old(perm).is_init(),
        old(perm).value().array().holds::<T>(),
    ensures
        res.addr() == old(perm).addr(),
        res.is_init(),
        res.value() == old(perm).value().array().value::<T>(),
        final(res).is_init(),
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().array().holds::<T>(),
        final(perm).value().array().value::<T>() == final(res).value(),
;

} // verus!
