//! Tools for reasoning about substructural types (structs, arrays, cells, eventually maybe unions)
//! This library is for when we need to reason about the underlying structure of these objects.
//! For example, consider the type:
//!
//! ```
//! struct Foo<A> {
//!     a: PCell<[A, 10]>,
//! }
//! ```
//!
//! Suppose we have a pointer of type `*const Foo`. Assuming a C-style layout,
//! that pointer's address points to:
//! 0. a `Foo`
//! 1. the first field of the struct, which is a cell of type `PCell<[A, 10]>
//! 2. the array of `A`s inside the cell
//! 3. the first `A` in the array
//!
//! When is it sound to cast a `*const Foo` to a `*const A`?
//! And when is it sound to use that new pointer?
//! We can answer these questions pairwise for each step in the chain.
//!
//! Step 1: struct-to-field is layout dependent. If the struct has the `#[layout(C)]` attribute,
//! it is always sound to make this cast for the first field of the struct (C99 and later).
//! It is tempting to try adding an offset to the base pointer to find other fields, but this is
//! not sound without detailed knowledge of the compiler.
//!
//! Step 2: cell to contents is modeled by VerusBelt, and we reproduce their approach here.
//!
//! Step 3: array to contents -- see `array_ptr.rs`.
use vstd::cell::CellId;
use vstd::cell::pcell_maybe_uninit::{self, PCell};
use vstd::prelude::*;
use vstd::raw_ptr::MemContents;
use vstd::simple_pptr::PointsTo;

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
    proof fn split_first(tracked perm: PointsTo<Self>) -> (tracked res: (
        FieldSplit<Self, Self::Remainder>,
        PointsTo<Self::FirstField>,
    ))
        requires
            perm.is_init(),
        ensures
            res.0.addr() == perm.addr(),
            res.0.rest() == perm.value().split().1,
            res.1.addr() == perm.addr(),
            res.1.mem_contents() == MemContents::Init(perm.value().split().0),
    ;

    /// The inverse exchange: gives up the field permission and the witness, and
    /// gets the struct permission back, its first field now holding whatever
    /// the field permission does.
    proof fn combine_first(
        tracked rest: FieldSplit<Self, Self::Remainder>,
        tracked perm: PointsTo<Self::FirstField>,
    ) -> (tracked res: PointsTo<Self>)
        requires
            perm.addr() == rest.addr(),
            perm.is_init(),
        ensures
            res.addr() == perm.addr(),
            res.is_init(),
            res.value() == Self::combine(perm.value(), rest.rest()),
    ;

    /// The borrowed form of the exchange, for reading.
    ///
    /// As with [`CellUnwrap::unwrap_ref`], no witness is handed out: the borrow
    /// ties the field permission's lifetime to the struct permission's, so it
    /// returns on its own and there is nothing to spend.
    proof fn borrow_first<'a>(tracked perm: &'a PointsTo<Self>) -> (tracked res: &'a PointsTo<
        Self::FirstField,
    >)
        requires
            perm.is_init(),
        ensures
            res.addr() == perm.addr(),
            res.mem_contents() == MemContents::Init(perm.value().split().0),
    ;

    /// The borrowed form for writing.
    ///
    /// Unlike [`CellUnwrap::unwrap_mut`], this takes the struct permission by
    /// `&mut`. A field of a plain struct is not interior-mutable, so writing it
    /// really does change the struct's value, and the final clause says how:
    /// the first field becomes whatever the borrow ends up holding, and the
    /// remainder -- which no permission reached during the borrow -- is the one
    /// it started with. That is the pairing [`Self::combine`] exists to state.
    proof fn borrow_first_mut<'a>(tracked perm: &'a mut PointsTo<Self>) -> (tracked res:
        &'a mut PointsTo<Self::FirstField>)
        requires
            old(perm).is_init(),
        ensures
            res.addr() == old(perm).addr(),
            res.mem_contents() == MemContents::Init(old(perm).value().split().0),
            final(res).is_init(),
            final(perm).addr() == old(perm).addr(),
            final(perm).is_init(),
            final(perm).value() == Self::combine(final(res).value(), old(perm).value().split().1),
    ;
}

/// A witness that a cell lives at an address: issued by [`CellUnwrap::unwrap`]
/// and spent by [`CellUnwrap::wrap`].
pub tracked struct CellLoc {
    id: CellId,
    addr: usize,
}

impl CellLoc {
    /// The cell this witness is for.
    pub closed spec fn id(self) -> CellId {
        self.id
    }

    /// Where that cell lives.
    pub closed spec fn addr(self) -> usize {
        self.addr
    }
}

pub trait CellUnwrap: Sized {
    proof fn unwrap(
        tracked parent: PointsTo<PCell<Self>>,
        tracked perm: pcell_maybe_uninit::PointsTo<Self>,
    ) -> (tracked res: (CellLoc, PointsTo<Self>))
        requires
            parent.mem_contents() is Init,
            parent.mem_contents().value().id() == perm.id(),
        ensures
            res.0.id() == perm.id(),
            res.0.addr() == parent.addr(),
            res.1.addr() == parent.addr(),
            res.1.mem_contents() == perm.mem_contents(),
    ;

    proof fn wrap(tracked loc: CellLoc, tracked perm: PointsTo<Self>) -> (tracked res: (
        pcell_maybe_uninit::PointsTo<Self>,
        PointsTo<PCell<Self>>,
    ))
        requires
            perm.addr() == loc.addr(),
            perm.mem_contents().is_init(),
        ensures
            res.0.id() == loc.id(),
            res.0.mem_contents() == perm.mem_contents(),
            res.1.addr() == perm.addr(),
            res.1.mem_contents().is_init(),
            res.1.mem_contents().value().id() == loc.id(),
    ;

    proof fn unwrap_ref<'a>(
        tracked parent: &'a PointsTo<PCell<Self>>,
        tracked perm: &'a pcell_maybe_uninit::PointsTo<Self>,
    ) -> (tracked res: &'a PointsTo<Self>)
        requires
            parent.mem_contents() is Init,
            parent.mem_contents().value().id() == perm.id(),
        ensures
            res.addr() == parent.addr(),
            res.mem_contents() == perm.mem_contents(),
    ;

    proof fn unwrap_mut<'a>(
        tracked parent: &'a PointsTo<PCell<Self>>,
        tracked perm: &'a mut pcell_maybe_uninit::PointsTo<Self>,
    ) -> (tracked res: &'a mut PointsTo<Self>)
        requires
            parent.mem_contents() is Init,
            parent.mem_contents().value().id() == old(perm).id(),
        ensures
            res.addr() == parent.addr(),
            res.mem_contents() == old(perm).mem_contents(),
            final(perm).id() == old(perm).id(),
            final(perm).mem_contents() == final(res).mem_contents(),
    ;
}

} // verus!
