//! Cells live in memory, so it is sound to convert from a cell permission to
//! a pointer permission, provided that we know the address of the cell;
//! i.e., if the cell is already behind a pointer. The soundness of this approach
//! follows from VerusBelt[^1]'s Iris model of cells.
//!
//! # Use case
//!
//! Consider a Rust program, which we would like to port to Verus.
//! The function `f` takes a pointer and dereferences it. The safety
//! of the dereference is left to the caller. But one caller, `g`, has a
//! pointer to a *cell* rather than to its contents. Taking advantage of
//! the transparent layout of the cell, it simply casts its `ptr` from
//! `*const UnsafeCell<T>` to `*const T`.
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
//! Each pointer gains a permission for what it addresses, and the cast becomes
//! `borrow_as_ptr`:
//!
//! ```rust,ignore
//! fn f<'a, T>(ptr: *const T, Tracked(perm): Tracked<&'a raw_ptr::PointsTo<T>>) -> &'a T
//!     requires
//!         ptr == perm.ptr(),
//!         perm.is_init(),
//! {
//!     ptr_ref(ptr, Tracked(perm))
//! }
//!
//! fn g<'a, T>(
//!     ptr: *const PCell<T>,
//!     Tracked(parent): Tracked<&'a raw_ptr::PointsTo<PCell<T>>>,
//!     Tracked(cell_perm): Tracked<&'a pcell_maybe_uninit::PointsTo<T>>,
//! ) -> &'a T
//!     requires
//!         ptr == parent.ptr(),
//!         parent.is_init(),
//!         parent.value().id() == cell_perm.id(),
//!         cell_perm.is_init(),
//! {
//!     let tracked perm = PCell::<T>::borrow_as_ptr(parent, cell_perm);
//!     f(ptr as *const T, Tracked(perm))
//! }
//! ```
//!
//! Now `g` expresses exactly what is necessary to perform the cast and call `f` soundly:
//! we must have permission to access `ptr`, it must be initialized, and we must
//! have permission to access the cell inside.
//!
//! Note that the permissions are [`vstd::raw_ptr::PointsTo`], carrying no exposed
//! provenance. None is needed: the cast is pointer-to-pointer, so it preserves the
//! address *and* the provenance, and the permission `borrow_as_ptr` hands back is for
//! the pointer the cast produces. Exposure is only required where an *address* becomes
//! a pointer, which is a step outside this module -- see
//! [`crate::raw_ptr::ExposedPointsTo`].
//!
//! # Correspondence with VerusBelt
//!
//! VerusBelt proves these operations sound in Iris.
//! Its *Points-To Cell Logic* (§3.4, Fig. 4) extends points-to
//! resources with chains of abstract cells, written `l ~>[cs] v`, which unfolds
//! to `(l |-> c1) * (c1 |-> c2) * ... * (cn |-> v)`.
//!
//! Translated into Verus, the first link in the chain is a pointer permission,
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
use vstd::raw_ptr;

verus! {

/// Borrowing a cell's contents as a pointer permission.
///
/// An extension trait on [`PCell`], because the exchange is a property of the
/// *cell*, not of the value it holds: "a cell permission can be traded for a
/// pointer permission" is a claim about cells, where an impl per content type
/// would have said "this type can be extracted from a cell", which is a claim
/// about nothing. One blanket impl below covers every `PCell<V>`, so no crate
/// downstream states a cell axiom of its own.
pub trait CellBorrow: Sized {
    /// The type held in the cell.
    ///
    /// An associated type rather than a parameter on the methods, so the
    /// permission handed out is for the cell's own value type -- a
    /// method-level `V` would let a `PCell<u64>`'s permission be borrowed as
    /// an `raw_ptr::PointsTo<bool>`.
    type Value;

    /// Which cell this is.
    ///
    /// Needed because `Self` is a type parameter in the clauses below, and
    /// `PCell::id` is an inherent method, which a type parameter cannot reach.
    spec fn id(&self) -> CellId;

    /// The cell's contents, as a pointer: `UnsafeCell::get`'s shape exactly.
    ///
    /// One of these, not two. A `*mut` serves reads and writes alike, as it
    /// does upstream; what cannot be mutability-agnostic is the *permission*,
    /// which is why the two below are separate -- a fractional permission can
    /// only be borrowed shared, so its holder has no `&mut` to offer.
    ///
    /// TRUSTED, and the claim is only about the **address**: `self` and
    /// `parent` describe the same cell, and a cell lives at one address. It
    /// deliberately says nothing about provenance. A pointer derived from a
    /// reference carries a fresh Stacked/Tree Borrows tag (see
    /// [`vstd::raw_ptr::ptr_ref2`]'s note), so claiming `parent`'s provenance
    /// here would be false. Tying the pointer to a permission is
    /// [`Self::borrow_as_ptr`]'s job, and it does that by taking the pointer.
    exec fn get<'a>(&self, Tracked(parent): Tracked<&'a raw_ptr::PointsTo<Self>>) -> (res:
        *mut Self::Value)
        requires
            parent.is_init(),
            parent.value().id() == self.id(),
        ensures
            res@.addr == parent.ptr()@.addr,
    ;

    /// A permission for the contents, at the pointer [`Self::get`] returned.
    ///
    /// Taking `ptr` is what keeps this honest. The permission is *for that
    /// pointer* -- tag and all -- so the caller can hand both straight to
    /// [`vstd::raw_ptr::ptr_ref`] with nothing left to prove. Only the address
    /// has to agree going in, which is exactly what `get` establishes.
    proof fn borrow_as_ptr<'a>(
        ptr: *mut Self::Value,
        tracked parent: &'a raw_ptr::PointsTo<Self>,
        tracked perm: &'a pcell_maybe_uninit::PointsTo<Self::Value>,
    ) -> (tracked res: &'a raw_ptr::PointsTo<Self::Value>)
        requires
            ptr@.addr == parent.ptr()@.addr,
            parent.is_init(),
            parent.value().id() == perm.id(),
        ensures
            res.ptr() == ptr,
            res.is_init() == perm.is_init(),
            perm.is_init() ==> res.value() == perm.value(),
    ;

    /// [`Self::borrow_as_ptr`] for exclusive access.
    proof fn borrow_as_ptr_mut<'a>(
        ptr: *mut Self::Value,
        tracked parent: &'a raw_ptr::PointsTo<Self>,
        tracked perm: &'a mut pcell_maybe_uninit::PointsTo<Self::Value>,
    ) -> (tracked res: &'a mut raw_ptr::PointsTo<Self::Value>)
        requires
            ptr@.addr == parent.ptr()@.addr,
            parent.is_init(),
            parent.value().id() == old(perm).id(),
        ensures
            res.ptr() == ptr,
            res.is_init() == old(perm).is_init(),
            old(perm).is_init() ==> res.value() == old(perm).value(),
            final(perm).id() == old(perm).id(),
            final(perm).is_init() == final(res).is_init(),
            final(res).is_init() ==> final(perm).value() == final(res).value(),
    ;
}

/// TRUSTED in its three methods, and the only place this exchange is asserted.
impl<V> CellBorrow for PCell<V> {
    type Value = V;

    // A path call, not `self.id()`: the inherent `PCell::id` and this trait
    // method share a name, and relying on inherent-wins here would be
    // needlessly delicate.
    open spec fn id(&self) -> CellId {
        PCell::id(self)
    }

    /// The body is upstream's `self.storage.get()`: a cast from the cell to
    /// its interior, address-preserving because `PCell` is a transparent
    /// wrapper around an `UnsafeCell`, and legitimate for writes because
    /// deriving a mutation-capable pointer from a shared reference to an
    /// `UnsafeCell` is what the language blesses.
    #[verifier::external_body]
    exec fn get<'a>(&self, Tracked(parent): Tracked<&'a raw_ptr::PointsTo<Self>>) -> (res: *mut V) {
        self as *const Self as *mut V
    }

    axiom fn borrow_as_ptr<'a>(
        ptr: *mut V,
        tracked parent: &'a raw_ptr::PointsTo<Self>,
        tracked perm: &'a pcell_maybe_uninit::PointsTo<V>,
    ) -> (tracked res: &'a raw_ptr::PointsTo<V>);

    axiom fn borrow_as_ptr_mut<'a>(
        ptr: *mut V,
        tracked parent: &'a raw_ptr::PointsTo<Self>,
        tracked perm: &'a mut pcell_maybe_uninit::PointsTo<V>,
    ) -> (tracked res: &'a mut raw_ptr::PointsTo<V>);
}

} // verus!
