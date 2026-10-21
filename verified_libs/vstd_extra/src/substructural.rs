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
use vstd::raw_ptr::MemContents;
use vstd::simple_pptr::PointsTo;
use vstd::prelude::*;

verus! {

pub tracked struct CellLoc {
    pub id: CellId,
    pub addr: usize
}

/// The address assigned to a cell.
///
/// Uninterpreted, and a function of the id alone, so the assignment is
/// canonical: a cell has one address, and [`CellAddr::unwrap`] hands back the
/// same one however many times it is called.
pub uninterp spec fn cell_addr(id: CellId) -> usize;

pub trait CellAddr {
    type Perm;

    /// The type held in the cell. An associated type rather than a parameter on
    /// `unwrap`, so that the `PointsTo` handed out is for the cell's own value
    /// type -- a method-level `V` would let a `PCell<u64>`'s permission be
    /// unwrapped into a `PointsTo<bool>`.
    type Value;

    spec fn id(&self) -> CellId;

    /// Which cell `perm` is a permission for.
    spec fn perm_id(perm: &Self::Perm) -> CellId;

    /// What `perm` says that cell currently holds.
    spec fn perm_contents(perm: &Self::Perm) -> MemContents<Self::Value>;

    /// Exchanges a cell permission for an addressed one: the same contents, now
    /// reachable through a pointer at the cell's assigned address.
    ///
    /// `perm_id`/`perm_contents` exist to let this be stated at all. `Perm` is
    /// an opaque associated type, so without them there is nothing to say about
    /// the input, and the result could not be tied to the cell it came from.
    proof fn unwrap(tracked perm: Self::Perm) -> (tracked res: (CellLoc, PointsTo<Self::Value>))
        ensures
            res.0.id == Self::perm_id(&perm),
            res.0.addr == cell_addr(Self::perm_id(&perm)),
            res.1.addr() == res.0.addr,
            res.1.mem_contents() == Self::perm_contents(&perm),
    ;

    /// The inverse exchange: gives up an addressed permission and the location
    /// it belongs to, and gets the cell permission back.
    ///
    /// Both `requires` carry the soundness of this direction, because
    /// [`CellLoc`]'s fields are public and so a `CellLoc` can be built out of
    /// thin air:
    ///
    /// - `perm.addr() == loc.addr` stops an unrelated `PointsTo` from being
    ///   passed off as the cell's contents.
    /// - `loc.addr == cell_addr(loc.id)` stops a fabricated `CellLoc` from
    ///   naming a cell the caller does not own. It is the obligation that cannot
    ///   be discharged for an arbitrary id: `cell_addr` is uninterpreted, so the
    ///   only way to know a cell's address is to have been given it -- in
    ///   practice, by [`Self::unwrap`].
    ///
    /// `loc` is consumed, which keeps the exchange balanced: `unwrap` issues one
    /// `CellLoc` and `wrap` spends it.
    proof fn wrap(tracked loc: CellLoc, tracked perm: PointsTo<Self::Value>) -> (tracked res:
        Self::Perm)
        requires
            loc.addr == cell_addr(loc.id),
            perm.addr() == loc.addr,
        ensures
            Self::perm_id(&res) == loc.id,
            Self::perm_contents(&res) == perm.mem_contents(),
    ;

    /// The borrowed form of the exchange, for reading.
    ///
    /// [`Self::unwrap`] consumes the cell permission, which is no help when the
    /// caller holds only a shared borrow of it, and no help either when the
    /// access hands out a reference that outlives the exchange -- the cell
    /// permission would have to stay surrendered for as long as that reference
    /// lives, with no point at which to [`Self::wrap`] it back.
    ///
    /// Borrowing ties the two lifetimes together instead: the addressed
    /// permission lives exactly as long as the borrow of the cell permission,
    /// so the cell permission returns on its own and there is nothing to spend.
    /// No [`CellLoc`] is handed out because there would be nothing in it: its
    /// `addr` is `cell_addr` of its `id`, and the caller can already name both.
    proof fn unwrap_ref<'a>(tracked perm: &'a Self::Perm) -> (tracked res: &'a PointsTo<
        Self::Value,
    >)
        ensures
            res.addr() == cell_addr(Self::perm_id(perm)),
            res.mem_contents() == Self::perm_contents(perm),
    ;

    /// The borrowed form for writing: as [`Self::unwrap_ref`], and whatever the
    /// addressed permission holds when the borrow ends is what the cell holds.
    proof fn unwrap_mut<'a>(tracked perm: &'a mut Self::Perm) -> (tracked res: &'a mut PointsTo<
        Self::Value,
    >)
        ensures
            res.addr() == cell_addr(Self::perm_id(old(perm))),
            res.mem_contents() == Self::perm_contents(old(perm)),
            Self::perm_id(final(perm)) == Self::perm_id(old(perm)),
            Self::perm_contents(final(perm)) == final(res).mem_contents(),
    ;
}

/// Gives [`PCell`] an address.
///
/// This is the `pcell_maybe_uninit` `PCell`, which is the one `ostd` stores in a
/// `MetaSlot` and the one whose permission matches the target: both it and
/// [`vstd::simple_pptr::PointsTo`] carry a [`MemContents`], so the exchange
/// preserves the initialized/uninitialized state exactly, with no side
/// condition in either direction.
impl<V> CellAddr for PCell<V> {
    type Perm = pcell_maybe_uninit::PointsTo<V>;

    type Value = V;

    // Written as a path call, not `self.id()`: the inherent `PCell::id` and this
    // trait method share a name, and relying on inherent-wins here would be
    // needlessly delicate.
    open spec fn id(&self) -> CellId {
        PCell::id(self)
    }

    open spec fn perm_id(perm: &Self::Perm) -> CellId {
        perm.id()
    }

    open spec fn perm_contents(perm: &Self::Perm) -> MemContents<V> {
        perm.mem_contents()
    }

    /// TRUSTED. This is the module's whole trust burden, and it is not a
    /// bookkeeping step: a `PCell` has no address in its specification at all
    /// -- [`CellId`] is deliberately opaque and carries no provenance -- so no
    /// proof can produce a `simple_pptr::PointsTo` from a cell permission. The
    /// exchange has to be asserted.
    ///
    /// What makes it defensible is that the cell permission is *consumed*:
    /// `perm` is taken by value, so the contents cannot be reached both ways at
    /// once. `cell_addr` being a function of the id keeps the address stable
    /// across calls, and the result's `mem_contents` is the input's, so the
    /// caller learns nothing about the value it did not already hold.
    #[verifier::external_body]
    proof fn unwrap(tracked perm: Self::Perm) -> (tracked res: (CellLoc, PointsTo<V>)) {
        unimplemented!();
    }

    /// TRUSTED, for the same reason as [`Self::unwrap`]: the two directions of
    /// one exchange, neither provable from the other.
    ///
    /// The asymmetry worth noting is in the preconditions rather than the trust.
    /// `unwrap` needs none -- holding the cell permission is already the right
    /// to the contents, and the address it hands out is whatever `cell_addr`
    /// says. `wrap` needs both of its, because a `PointsTo` plus a `CellLoc`
    /// does not by itself say the two are about the same cell.
    #[verifier::external_body]
    proof fn wrap(tracked loc: CellLoc, tracked perm: PointsTo<V>) -> (tracked res: Self::Perm) {
        unimplemented!();
    }

    /// TRUSTED, as the owning pair. These two need no precondition at all:
    /// borrowing a cell permission is already the right to its contents, and
    /// the borrow checker, not a `requires`, is what stops the addressed
    /// permission from outliving it.
    #[verifier::external_body]
    proof fn unwrap_ref<'a>(tracked perm: &'a Self::Perm) -> (tracked res: &'a PointsTo<V>) {
        unimplemented!();
    }

    #[verifier::external_body]
    proof fn unwrap_mut<'a>(tracked perm: &'a mut Self::Perm) -> (tracked res: &'a mut PointsTo<
        V,
    >) {
        unimplemented!();
    }
}

} // verus!
