//! Step 1 of the chain in [`super`]: a struct to its first field.
//!
//! Layout dependent, and the reason only the *first* field is offered. A
//! `#[repr(C)]` struct's address is its first member's (C99 6.7.2.1), so that
//! one cast is always sound; reaching any other field would need offsets, which
//! are not sound without detailed knowledge of the compiler.
use vstd::prelude::*;
use vstd::raw_ptr;

verus! {

/// A witness that a struct's remainder is set aside while its first field is
/// split out: issued by [`StructToField::split_first`] and spent by
/// [`StructToField::combine_first`].
pub tracked struct FieldSplit<S, R> {
    addr: usize,
    rest: Ghost<R>,
    _S: core::marker::PhantomData<S>,
}

impl<S, R> FieldSplit<S, R> {
    /// Where the struct this witness came from lives.
    pub closed spec fn addr(self) -> usize {
        self.addr
    }

    /// Everything but the first field, as it stood when the split happened.
    /// Still true when the witness is spent: no permission for those bytes
    /// exists while it is held, so nothing can have written them.
    pub closed spec fn rest(self) -> R {
        self.rest@
    }
}

/// A struct with an identified first field, such that it is sound to cast a pointer to the
/// struct into a pointer to that field.
///
/// The permissions are [`ExposedPointsTo`], so each exchange also carries provenance
/// exposure across. That is sound in this direction for the same reason the cast is:
/// the first field shares the struct's address *and* its allocation, so a provenance
/// already exposed for the struct is exposed for the field, and vice versa. It is why
/// these are stated over exposed permissions rather than plain ones -- a caller that
/// reached the struct by an address round trip can keep doing so for the field.
pub trait StructToField: Sized {
    type FirstField;

    type Remainder;

    spec fn split(self) -> (Self::FirstField, Self::Remainder);

    spec fn combine(f: Self::FirstField, r: Self::Remainder) -> Self;

    proof fn roundtrip(self)
        ensures
            Self::combine(self.split().0, self.split().1) == self,
    ;

    /// Exchanges a permission for the struct for one for its first field, at
    /// the same address. The remainder has no permission of its own afterwards --
    /// its value goes into the witness.
    proof fn split_first(tracked perm: raw_ptr::PointsTo<Self>) -> (tracked res: (
        FieldSplit<Self, Self::Remainder>,
        raw_ptr::PointsTo<Self::FirstField>,
    ))
        requires
            perm.is_init(),
        ensures
            res.0.addr() == perm.ptr()@.addr,
            res.0.rest() == perm.value().split().1,
            res.1.ptr() == perm.ptr() as *mut Self::FirstField,
            res.1.is_init(),
            res.1.value() == perm.value().split().0,
    ;

    /// The inverse exchange: gives up the field permission and the witness, and
    /// gets the struct permission back, its first field now holding whatever
    /// the field permission does.
    proof fn combine_first(
        tracked rest: FieldSplit<Self, Self::Remainder>,
        tracked perm: raw_ptr::PointsTo<Self::FirstField>,
    ) -> (tracked res: raw_ptr::PointsTo<Self>)
        requires
            perm.ptr()@.addr == rest.addr(),
            perm.is_init(),
        ensures
            res.ptr()@.addr == perm.ptr()@.addr,
            res.ptr()@.provenance == perm.ptr()@.provenance,
            res.is_init(),
            res.value() == Self::combine(perm.value(), rest.rest()),
    ;

    /// The borrowed form of the exchange, for reading.
    ///
    /// As with [`super::cell::CellBorrow::borrow_as_ptr`], no witness is handed out: the borrow
    /// ties the field permission's lifetime to the struct permission's, so it
    /// returns on its own and there is nothing to spend.
    proof fn borrow_first<'a>(tracked perm: &'a raw_ptr::PointsTo<Self>) -> (tracked res:
        &'a raw_ptr::PointsTo<Self::FirstField>)
        requires
            perm.is_init(),
        ensures
            res.ptr()@.addr == perm.ptr()@.addr,
            res.ptr()@.provenance == perm.ptr()@.provenance,
            res.is_init(),
            res.value() == perm.value().split().0,
    ;

    /// The borrowed form for writing.
    ///
    /// Unlike [`super::cell::CellBorrow::borrow_as_ptr_mut`], this takes the struct permission by
    /// `&mut`. A field of a plain struct is not interior-mutable, so writing it
    /// really does change the struct's value, and the final clause says how:
    /// the first field becomes whatever the borrow ends up holding, and the
    /// remainder -- which no permission reached during the borrow -- is the one
    /// it started with. That is the pairing [`Self::combine`] exists to state.
    proof fn borrow_first_mut<'a>(tracked perm: &'a mut raw_ptr::PointsTo<Self>) -> (tracked res:
        &'a mut raw_ptr::PointsTo<Self::FirstField>)
        requires
            old(perm).is_init(),
        ensures
            res.ptr()@.addr == old(perm).ptr()@.addr,
            res.ptr()@.provenance == old(perm).ptr()@.provenance,
            res.is_init(),
            res.value() == old(perm).value().split().0,
            final(res).is_init(),
            final(perm).ptr() == old(perm).ptr(),
            final(perm).is_init(),
            final(perm).value() == Self::combine(final(res).value(), old(perm).value().split().1),
    ;
}

} // verus!
