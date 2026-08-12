use vstd::prelude::*;

use vstd::std_specs::convert::{IntoSpec, TryFromSpec};

use core::marker::PhantomData;

verus! {

pub trait ByteSized<const SIZE: usize>: Sized {
    proof fn size_correct()
        ensures
            size_of::<Self>() == SIZE,
    ;
}

/// A trait for types whose bit-level representation needs to be visible to Verus.
///
/// # The law
///
/// Encoding a value and decoding the result recovers it. That is the *only*
/// thing an aggregate needs from a member's representation: it is what makes
/// [`Member::holds`] achievable by a constructor — see [`lemma_leaf_holds`],
/// which is the sole consumer of this law — and hence what makes
/// [`HasId::wf`] establishable by construction rather than assumed.
///
/// Note it is *not* what supplies the id. The id is held directly as ghost state
/// beside the bytes, so nothing here has to be strong enough to recover it. That
/// separation is what lets aggregates nest; see [`GhostTaggedArray`].
///
/// Note what is deliberately absent. There is no claim that decoding an
/// *arbitrary* byte pattern fails, and none that two different types decode the
/// same bytes differently. Neither is true in general — two members may well
/// share a byte pattern — and neither is needed: telling members apart is the
/// job of [`DisjointFrom`], on the id sets, not of the encoding.
///
/// Getting that division wrong would be the classic mistake here: using the
/// representation as an identity witness. The bytes say *what the value is*; the
/// ids say *which member it belongs to*.
pub trait ByteRepr<const SIZE: usize>: ByteSized<SIZE> + TryFromSpec<[u8; SIZE]> +
    IntoSpec<[u8; SIZE]> {
    proof fn round_trip(self)
        ensures
            Self::try_from_spec(self.into_spec()) == Ok(self),
    ;
}

/// Verus does not expose the `typeId` of a type, though in principle it could.
/// So we need to do it ourselves, by enumerating all of the possible subtypes.
/// Since we are dealing with aggregate types, we model `typeId` as a boolean
/// (or a set of identifiers).
pub trait TypeId {
    spec fn inhabits(type_id: nat) -> bool where Self: Sized;

}

/// A type whose *values* carry an id, not merely a type denoting a set of them.
///
/// Split from [`TypeId`] because the two are genuinely different: a type used
/// only to name an id set (the right-hand side of a nest, say) has no values to
/// report an id for, and forcing it to invent one would mean an unprovable law.
/// Only members that actually hold a value implement this.
pub trait HasId: TypeId {
    /// The id of *this value*.
    ///
    /// `inhabits` cannot supply this: it is a set-membership test, so even for a
    /// type admitting exactly one id there is no way to *extract* that id.
    ///
    /// Deliberately not `where Self: Sized` — this is the one thing that must
    /// survive erasure, since it is what a downcast tests.
    spec fn id_of(&self) -> nat;

    /// This value's id and its contents agree.
    ///
    /// Lives on the trait rather than as an inherent predicate because the laws
    /// below need it as a precondition, and a trait method impl may not add one.
    /// For a member that carries its own identity in its type this is just
    /// `true`; for a tagged aggregate it is the tag/bytes pairing.
    ///
    /// Not `where Self: Sized`, for the same reason as `id_of`: a downcast holds
    /// an erased value and still has to know it is well-formed.
    spec fn wf(&self) -> bool;

    /// A well-formed value's id lies in its own type's set.
    ///
    /// This is the "at least one" half of [`Either`]'s law; `DisjointFrom`
    /// supplies the "not both" half. Neither implies the other, and the law
    /// needs both — disjointness alone would permit a value whose id belongs to
    /// no side at all.
    ///
    /// The `wf` precondition is not a weakening: a value whose tag disagrees
    /// with its contents has no meaningful id, so there is nothing true to say
    /// about it. Requiring it here is what lets an aggregate hold the id
    /// *directly* as a ghost field instead of having to recover it by decoding.
    proof fn id_of_inhabits(&self)
        where Self: Sized
        requires
            self.wf(),
        ensures
            Self::inhabits(self.id_of()),
    ;
}

/// A witness that two members' id sets do not overlap.
///
/// This is where the per-node obligation lives. `Either`'s law cannot be proven
/// generically — knowing a value came from one side says nothing about the other
/// side unless the two are known disjoint — so the disjointness has to be
/// supplied, and this is the thing that supplies it.
///
/// Requiring it as a bound on the aggregate means a collision is caught at the
/// node that joins the two members, at compile time, rather than by a global
/// check someone has to remember to run.
pub trait DisjointFrom<B: TypeId>: TypeId + Sized {
    proof fn disjoint(type_id: nat)
        ensures
            !(Self::inhabits(type_id) && B::inhabits(type_id)),
    ;
}

/// The erased view of an aggregate value.
///
/// # Why this declares its own `id_of`/`wf`
///
/// A spec fn survives the `&T -> &dyn Trait` coercion only if `Trait` itself
/// declares it. Inheriting it from a supertrait is not enough: Verus propagates
/// the *declaring* trait's functions across the coercion, so a postcondition
/// stated with a supertrait's spec fn is unprovable at the coercion site even
/// though the same postcondition using an own function goes through. Probed both
/// ways, generically and at a concrete type.
///
/// Hence [`Self::dyn_id`] and [`Self::dyn_wf`], which mirror [`HasId::id_of`] and
/// [`HasId::wf`]. The duplication is not free, but the alternative is an erased
/// object about which nothing can be concluded, which defeats the purpose.
///
/// [`HasId`] is deliberately *not* a supertrait, for a second reason: it extends
/// [`TypeId`], and Verus's dyn type does not satisfy that bound, so `dyn HasId`
/// does not even typecheck. Aggregates implement both traits independently —
/// `HasId` for use at the concrete type, `Either` for use through an erased one —
/// and [`lemma_dyn_agrees`] moves between them.
///
/// Note the sides are bounded by [`TypeId`], not [`HasId`]: the law below names
/// only `A::inhabits` and `B::inhabits`. That matters for nesting — the right
/// side of a nest is a *phantom* describing an id set, with no values of its own,
/// so demanding `HasId` of it would mean inventing an `id_of` for a type that
/// never has one.
pub trait Either<A: TypeId, B: TypeId> {
    /// This value's id, readable through an erased reference.
    spec fn dyn_id(&self) -> nat;

    /// This value's well-formedness, readable through an erased reference.
    spec fn dyn_wf(&self) -> bool;

    /// Every well-formed value belongs to exactly one side.
    ///
    /// This is where uniqueness comes from, and it is worth being precise about
    /// how: the obligation is discharged *per nesting node*, so a collision
    /// between two members fails a proof at the node that joins them. Nothing
    /// global has to be maintained, and nothing has to be remembered when a
    /// member is added — which is the advantage over a flat tag registry with a
    /// hand-kept range discipline.
    ///
    /// This is also the aggregate's *dispatch*: callable on `&dyn Either<A, B>`,
    /// it yields the disjunction without the caller knowing which member is live.
    ///
    /// Note what is *not* stated here: `Self::inhabits(self.dyn_id())`. It cannot
    /// be — `inhabits` is `where Self: Sized`, and with a `&self` receiver `Self`
    /// may be `dyn Either<A, B>`, which is precisely the case this trait exists
    /// to serve. It is also redundant: an impl whose `inhabits` is the union of
    /// its sides' gets it from the disjunction below.
    proof fn type_id_laws(tracked &self)
        requires
            self.dyn_wf(),
        ensures
            {
                ||| A::inhabits(self.dyn_id()) && !B::inhabits(self.dyn_id())
                ||| B::inhabits(self.dyn_id()) && !A::inhabits(self.dyn_id())
            },
    ;

}

/// A description of what byte patterns encode which members.
///
/// This is the part that nests. It has no values — it is a phantom naming an id
/// set together with a validity test — so a node can join two of them without
/// anything needing to be stored, and without either side having to be
/// recoverable from the bytes.
///
/// That is the whole trick. The earlier binary-tag design could not nest because
/// an inner tagged array's tag was not a function of its bytes, so
/// [`ByteRepr::round_trip`] was unprovable for it. Here the tag is not per-level:
/// there is one id, held once, and `holds` merely *checks* it against the bytes
/// at whatever depth the matching member sits.
pub trait Member<const SIZE: usize>: TypeId + Sized {
    /// `data` is a valid encoding of the member of this aggregate named by `id`.
    spec fn holds(id: nat, data: [u8; SIZE]) -> bool;

    /// Only ids this aggregate admits can be held by it.
    ///
    /// Proved rather than assumed at every impl below, which is what keeps
    /// `GhostTaggedArray`'s `id_of_inhabits` axiom-free.
    proof fn holds_inhabits(id: nat, data: [u8; SIZE])
        requires
            Self::holds(id, data),
        ensures
            Self::inhabits(id),
    ;
}

/// A single-member aggregate wrapping a concrete representable type.
pub struct Leaf<M>(pub PhantomData<M>);

impl<M: TypeId> TypeId for Leaf<M> {
    open spec fn inhabits(type_id: nat) -> bool {
        M::inhabits(type_id)
    }
}

impl<const SIZE: usize, M: TypeId + ByteRepr<SIZE>> Member<SIZE> for Leaf<M> {
    /// The bytes decode as `M`, and `id` is one of `M`'s ids.
    ///
    /// Note it does not say the decoded value's `id_of` *equals* `id`. It cannot
    /// without knowing that value is well-formed, and it need not: for a member
    /// owning a single id the two coincide, and for one owning several, which of
    /// them is live is not something the aggregate arbitrates.
    open spec fn holds(id: nat, data: [u8; SIZE]) -> bool {
        &&& M::try_from_spec(data) is Ok
        &&& M::inhabits(id)
    }

    proof fn holds_inhabits(id: nat, data: [u8; SIZE]) {
    }
}

/// Two aggregates joined: ids and valid encodings are the union of the sides'.
///
/// Stating `inhabits` as the union is what makes `Self::inhabits(self.id_of())`
/// derivable rather than an extra obligation: given [`Either`]'s disjunction,
/// membership in one side gives membership in the union.
pub struct Node<A, B>(pub PhantomData<(A, B)>);

impl<A: TypeId, B: TypeId> TypeId for Node<A, B> {
    open spec fn inhabits(type_id: nat) -> bool {
        A::inhabits(type_id) || B::inhabits(type_id)
    }
}

impl<const SIZE: usize, A: Member<SIZE>, B: Member<SIZE>> Member<SIZE> for Node<A, B> {
    open spec fn holds(id: nat, data: [u8; SIZE]) -> bool {
        A::holds(id, data) || B::holds(id, data)
    }

    proof fn holds_inhabits(id: nat, data: [u8; SIZE]) {
        if A::holds(id, data) {
            A::holds_inhabits(id, data);
        } else {
            B::holds_inhabits(id, data);
        }
    }
}

/// Bytes plus a ghost id saying which member of `T` they hold.
///
/// The id is held *directly* rather than recovered by decoding, and it is a
/// member id rather than a per-level `LEFT`/`RIGHT`. Both changes are what make
/// this nest: `T` may be an arbitrarily deep [`Node`] tree, and no matter how
/// deep the matching member sits, there is exactly one tag and it is stored
/// exactly once — in ghost state, so the runtime footprint is still just the
/// bytes, as upstream.
///
/// The cost is that tag and bytes can disagree, since nothing about the struct
/// forces them to. That is what [`HasId::wf`] is for: constructors carry it as a
/// postcondition and consumers as a precondition, so it is checked rather than
/// trusted. Elsewhere in this tree the same pairing — a stored word plus a ghost
/// type tag — had to be propped up by an axiom and an unenforced "always write
/// both together" convention.
pub struct GhostTaggedArray<const SIZE: usize, T: Member<SIZE>> {
    /// The member id, as ghost state.
    ///
    /// `Ghost<nat>` rather than a `ghost` field, and the difference is not
    /// cosmetic: a `ghost` field cannot be initialised from executable code
    /// ("cannot access spec-mode place in executable context"), so a struct
    /// carrying one can only ever exist as a ghost value. That would make every
    /// consumer below unreachable. `Ghost<nat>` is zero-sized, so the runtime
    /// footprint is still just the bytes.
    pub id: Ghost<nat>,
    pub data: [u8; SIZE],
    pub _t: PhantomData<T>,
}

impl<const SIZE: usize, T: Member<SIZE>> TypeId for GhostTaggedArray<SIZE, T> {
    open spec fn inhabits(type_id: nat) -> bool {
        T::inhabits(type_id)
    }
}

impl<const SIZE: usize, T: Member<SIZE>> HasId for GhostTaggedArray<SIZE, T> {
    open spec fn id_of(&self) -> nat {
        self.id@
    }

    open spec fn wf(&self) -> bool {
        T::holds(self.id@, self.data)
    }

    proof fn id_of_inhabits(&self) {
        T::holds_inhabits(self.id@, self.data);
    }
}

impl<const SIZE: usize, A: Member<SIZE> + DisjointFrom<B>, B: Member<SIZE>> Either<
    A,
    B,
> for GhostTaggedArray<SIZE, Node<A, B>> {
    open spec fn dyn_id(&self) -> nat {
        self.id@
    }

    open spec fn dyn_wf(&self) -> bool {
        Node::<A, B>::holds(self.id@, self.data)
    }

    proof fn type_id_laws(tracked &self) {
        // "not both" from the disjointness witness ...
        A::disjoint(self.dyn_id());
        // ... and "at least one" from whichever side admits the bytes.
        if A::holds(self.id@, self.data) {
            A::holds_inhabits(self.id@, self.data);
        } else {
            B::holds_inhabits(self.id@, self.data);
        }
    }
}

impl<const SIZE: usize, A: Member<SIZE> + DisjointFrom<B>, B: Member<SIZE>> GhostTaggedArray<
    SIZE,
    Node<A, B>,
> {
    /// Upcast: view the stored bytes as an erased member of the `A | B` aggregate.
    ///
    /// Borrows rather than boxing: a metadata slot has no allocator, and the
    /// caller only needs to dispatch through the value, not own it. This is the
    /// same shape as `dispatch_meta` in the frame layer.
    ///
    /// Note the `DisjointFrom` bound, which is not incidental: erasure is only
    /// available once the two sides are *known* not to collide. A design that
    /// let you erase first and check uniqueness later would have to check it
    /// globally, which is the thing this is meant to avoid.
    ///
    /// The postconditions are what make the erased value usable. Both `id_of`
    /// and `wf` survive because neither is `where Self: Sized`, so both are in
    /// the vtable — without them the result would be an opaque object nothing
    /// could be concluded about, which is what an `external_body` version of
    /// this promising nothing would have amounted to.
    pub exec fn as_dyn(&self) -> (r: &dyn Either<A, B>)
        ensures
            r.dyn_id() == self.dyn_id(),
            r.dyn_wf() == self.dyn_wf(),
    {
        self
    }
}

/// The concrete and erased views of an aggregate agree.
///
/// Both sides are `open`, so this is definitional — it exists to be cited rather
/// than to be proved, and it is the seam between constructors (which establish
/// [`HasId::wf`]) and consumers (which see [`Either::dyn_wf`]).
pub proof fn lemma_dyn_agrees<const SIZE: usize, A: Member<SIZE> + DisjointFrom<B>, B: Member<SIZE>>(
    s: &GhostTaggedArray<SIZE, Node<A, B>>,
)
    ensures
        s.dyn_id() == s.id_of(),
        s.dyn_wf() == s.wf(),
{
}

/// Storing a well-formed member establishes [`Member::holds`] at its own id.
///
/// This is the constructor side of `wf`, and the one place [`ByteRepr`]'s
/// round-trip law is consumed: it is what says the bytes just written decode
/// again, while `id_of_inhabits` says the id recorded beside them is one this
/// leaf admits.
pub proof fn lemma_leaf_holds<const SIZE: usize, M: HasId + ByteRepr<SIZE>>(m: M)
    requires
        m.wf(),
    ensures
        <Leaf<M> as Member<SIZE>>::holds(m.id_of(), m.into_spec()),
{
    m.round_trip();
    m.id_of_inhabits();
}


/// Reinterpret stored bytes as a reference to the member they encode.
///
/// # The one axiom
///
/// This is the only assumed fact in the module that is not a per-type layout
/// obligation, and it is what makes a stored member *dispatchable*: with a `&M`
/// in hand, an ordinary `&M -> &dyn Tr` coercion produces an erased reference to
/// whatever trait the members share, and Verus already tracks which impl was
/// erased across that coercion. So no `Any`-style downcast axiom is needed —
/// reinterpretation is the whole of the gap.
///
/// It cannot be proved. Verus has no model of the pointer cast involved, and the
/// fact being asserted is that a byte pattern satisfying `M`'s decode really may
/// be *read as* an `M` in place, rather than decoded into a fresh value. That is
/// a statement about layout, which is why the precondition is exactly the decode
/// and nothing weaker: bytes that do not decode may not be borrowed at all.
///
/// Note what it does *not* assume. It says nothing about which member the bytes
/// belong to — `M` is chosen by the caller, and choosing wrong is prevented by
/// the precondition, not by this signature. Identity remains the ids' job. In
/// particular this is not a downcast: it will happily borrow the same bytes as
/// two different members if both decode, and the reason that is sound is that
/// `DisjointFrom` stops both from being *the* member at one id.
///
/// The frame layer's `borrow_meta_mut` is the same axiom for the mutable case.
#[verifier::external_body]
pub exec fn borrow_as<'a, const SIZE: usize, M: ByteRepr<SIZE>>(data: &'a [u8; SIZE]) -> (r: &'a M)
    requires
        M::try_from_spec(*data) is Ok,
    ensures
        *r == M::try_from_spec(*data)->Ok_0,
{
    unimplemented!()
}

} // verus!
