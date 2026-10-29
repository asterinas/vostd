//! Cells live in memory, so it is sound to convert from a cell permission to
//! a pointer permission, provided that we know the address of the cell;
//! i.e., if the cell is already behind a pointer. The soundness of this approach
//! follows from VerusBelt[^1]'s Iris model of cells.
//!
//! # Use case
//!
//! `f` takes a pointer, and leaves justifying the dereference to its caller.
//! `g` has a pointer to a *cell* rather than to its contents, so it converts
//! before handing `f` what it asks for:
//!
//! ```rust
//! use core::cell::UnsafeCell;
//!
//! unsafe fn f<'a, T>(ptr: *const T) -> &'a T {
//!     unsafe { &*ptr }
//! }
//!
//! unsafe fn g<'a, T>(ptr: *const UnsafeCell<T>) -> &'a T {
//!     unsafe { f(ptr as *const T) }
//! }
//! ```
//!
//! This is sound, provided that `ptr` is initialized, but how do we express it in Verus?
//! The executable equivalent is to take `ptr`'s address and retype it as a `PPtr<T>`.
//! But permission to access the interior cell is carried by a cell permission, not a pointer
//! permission! So we also need to convert the permissions into a form that `f` can use.
//! We do so using the new `unwrap_ref`.
//!
//! ```rust,ignore
//! fn f<'a, T>(ptr: PPtr<T>, Tracked(perm): Tracked<&'a PointsTo<T>>) -> &'a T
//!     requires
//!         ptr.addr() == perm.addr(),
//!         perm.is_init(),
//! {
//!     ptr.borrow(Tracked(perm))
//! }
//!
//! fn g<'a, T: CellUnwrap>(
//!     ptr: PPtr<PCell<T>>,
//!     Tracked(parent): Tracked<&'a PointsTo<PCell<T>>>,
//!     Tracked(cell_perm): Tracked<&'a pcell_maybe_uninit::PointsTo<T>>,
//! ) -> &'a T
//!     requires
//!         ptr.addr() == parent.addr(),
//!         parent.mem_contents() is Init,
//!         parent.mem_contents().value().id() == cell_perm.id(),
//!         cell_perm.is_init(),
//! {
//!     f(PPtr::from_addr(ptr.addr()), Tracked(T::unwrap_ref(parent, cell_perm)))
//! }
//! ```
//!
//! Now `g` expresses exactly what is necessary to perform the cast and call `f` soundly:
//! we must have permission to access `ptr`, it must be initialized, and we must
//! have permission to access the cell inside.
//!
//! # Correspondence with VerusBelt
//!
//! VerusBelt proves these operations sound in Iris.
//! Its *Points-To Cell Logic* (§3.4, Fig. 4) extends points-to
//! resources with chains of abstract cells, written `l ~>[cs] v`, which unfolds
//! to `(l |-> c1) * (c1 |-> c2) * ... * (cn |-> v)`.
//!
//! Translated into Verus, the first link in the chain is a `PPtr::PointsTo` object,
//! and subsequent links are `PCell::PointsTo` objects. The first link establishes the
//! address at which the cell lives. Subsequent links map the cell to its contents,
//! and if the contents happen to be another cell, to that cell's contents, and so on.
//! In VerusBelt's logic, these chained permissions are used in their entirety to borrow
//! `v`, mutably or immutably depending on the permissions of the deepest link.
//!
//! Our approach is more granular; we provide axioms that collapse the pair
//! `(l |-> c) * (c |-> v)` into `(l |-> v)`. The resulting collapsed permission can
//! be used interchangeably with other pointer permissions, as in the example above.
//! In [LINK], we have extended VerusBelt with the equivalent logical operation,
//! and show that collapse-then-read and collapse-then-write are interchangeable with
//! ordinary reads and writes.
//!
//! [^1]: Hance, Elbeheiry, Matsushita, Dreyer. *VerusBelt: A Semantic
//! Foundation for Verus\'s Proof-Oriented Extensions to the Rust Type System*.
//! Proc. ACM Program. Lang. 10, PLDI, Article 247 (June 2026).
//! <https://doi.org/10.1145/3808325>
use vstd::cell::CellId;
use vstd::cell::pcell_maybe_uninit::{self, PCell};
use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;

verus! {

/// A witness that a cell lives at an address: issued by [`CellUnwrap::unwrap`]
/// and spent by [`CellUnwrap::wrap`].
///
/// Reifies VerusBelt's `l |-> c` -- the first half of a chain link. The paper
/// needs no such token, because there the two halves are themselves resources
/// and `Cell-Sep` merely relates them. Here [`CellUnwrap::unwrap`] *consumes*
/// the parent permission, so the right to rebuild it has to be carried
/// somewhere, and this is that carrier. Its fields are private for the same
/// reason: `wrap`'s only guard is `perm.addr() == loc.addr()`, which a
/// forgeable witness would make vacuous.
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
    /// `Cell-Sep`, left to right.
    ///
    /// VerusBelt's rule is a bi-entailment,
    /// `(l ~>[cs1] c) * (c ~>[cs2] v) -|- (l ~>[cs1 ++ c :: cs2] v)`, which is
    /// why this and [`Self::wrap`] are inverse rather than independent: they
    /// are one equivalence read in its two directions. The `CellLoc` handed
    /// back stands for the `l |-> c` half this consumes.
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

    /// `Cell-Sep`, right to left.
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

    /// Borrow reference to the interior cell
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

    /// Borrow mutable reference to the interior cell
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
