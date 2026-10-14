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

pub trait ByteRepr<const SIZE: usize>: ByteSized<SIZE> + TryFromSpec<[u8; SIZE]> +
    IntoSpec<[u8; SIZE]> {
    proof fn round_trip(self)
        ensures
            Self::try_from_spec(self.into_spec()) == Ok(self),
    ;

    proof fn canonical(data: [u8; SIZE])
        requires
            Self::try_from_spec(data) is Ok,
        ensures
            Self::try_from_spec(data)->Ok_0.into_spec() == data,
    ;
}

pub trait TypeSet {
    spec fn possible_types() -> Set<nat> where Self: Sized;
}

pub trait HasId: TypeSet {
    /// The id of *this value*.
    spec fn id_of(&self) -> nat;

    /// This value's id and its contents agree.
    spec fn wf(&self) -> bool;

    proof fn id_of_in_possible_types(&self)
        where Self: Sized
        requires
            self.wf(),
        ensures
            Self::possible_types().contains(self.id_of()),
    ;
}

/// A witness that two members' id sets do not overlap.
pub trait DisjointFrom<B: TypeSet>: TypeSet + Sized {
    proof fn disjoint(type_id: nat)
        ensures
            !(Self::possible_types().contains(type_id)
              && B::possible_types().contains(type_id)),
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
/// [`TypeSet`], and Verus's dyn type does not satisfy that bound, so `dyn HasId`
/// does not even typecheck. Aggregates implement both traits independently —
/// `HasId` for use at the concrete type, `EitherType` for use through an erased
/// one — and [`lemma_dyn_agrees`] moves between them.
///
/// Note the sides are bounded by [`TypeSet`], not [`HasId`]: the law below names
/// only `A::possible_types` and `B::possible_types`. That matters for nesting — the right
/// side of a nest is a *phantom* describing an id set, with no values of its own,
/// so demanding `HasId` of it would mean inventing an `id_of` for a type that
/// never has one.
pub trait EitherType<A: TypeSet, B: TypeSet> {
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
    /// This is also the aggregate's *dispatch*: callable on `&dyn EitherType<A, B>`,
    /// it yields the disjunction without the caller knowing which member is live.
    proof fn type_id_laws(tracked &self)
        requires
            self.dyn_wf(),
        ensures
            {
                ||| A::possible_types().contains(self.dyn_id())
                    && !B::possible_types().contains(self.dyn_id())
                ||| B::possible_types().contains(self.dyn_id())
                    && !A::possible_types().contains(self.dyn_id())
            },
    ;

}

/// A description of what byte patterns encode which members.
/// 
pub trait Member<const SIZE: usize>: TypeSet + Sized {
    /// `data` is a valid encoding of the member of this aggregate named by `id`.
    spec fn valid(id: nat, data: [u8; SIZE]) -> bool;

    /// Only ids this aggregate admits can be held by it.
    ///
    /// Proved rather than assumed at every impl below, which is what keeps
    /// `GhostTaggedArray`'s `id_of_in_possible_types` axiom-free.
    proof fn valid_in_possible_types(id: nat, data: [u8; SIZE])
        requires
            Self::valid(id, data),
        ensures
            Self::possible_types().contains(id),
    ;
}

/// A single-member aggregate wrapping a concrete representable type.
pub struct LeafType<M>(pub PhantomData<M>);

impl<M: TypeSet> TypeSet for LeafType<M> {
    open spec fn possible_types() -> Set<nat> {
        M::possible_types()
    }
}

impl<const SIZE: usize, M: TypeSet + ByteRepr<SIZE>> Member<SIZE> for LeafType<M> {
    /// The bytes decode as `M`, and `id` is one of `M`'s ids.
    ///
    /// Note it does not say the decoded value's `id_of` *equals* `id`. It cannot
    /// without knowing that value is well-formed, and it need not: for a member
    /// owning a single id the two coincide, and for one owning several, which of
    /// them is live is not something the aggregate arbitrates.
    open spec fn valid(id: nat, data: [u8; SIZE]) -> bool {
        &&& M::try_from_spec(data) is Ok
        &&& M::possible_types().contains(id)
    }

    proof fn valid_in_possible_types(id: nat, data: [u8; SIZE]) {
    }
}

/// Two aggregates joined: ids and valid encodings are the union of the sides'.
///
/// Stating `possible_types` as the union is what makes
/// `Self::possible_types().contains(self.id_of())` derivable rather than an extra
/// obligation: given [`EitherType`]'s disjunction, membership in one side gives
/// membership in the union.
pub struct ConsType<A, B>(pub PhantomData<(A, B)>);

impl<A: TypeSet, B: TypeSet> TypeSet for ConsType<A, B> {
    open spec fn possible_types() -> Set<nat> {
        A::possible_types().union(B::possible_types())
    }
}

impl<const SIZE: usize, A: Member<SIZE>, B: Member<SIZE>> Member<SIZE> for ConsType<A, B> {
    open spec fn valid(id: nat, data: [u8; SIZE]) -> bool {
        A::valid(id, data) || B::valid(id, data)
    }

    proof fn valid_in_possible_types(id: nat, data: [u8; SIZE]) {
        if A::valid(id, data) {
            A::valid_in_possible_types(id, data);
        } else {
            B::valid_in_possible_types(id, data);
        }
    }
}

/// Bytes plus a ghost id saying which member of `T` they hold.
///
/// The id is held *directly* rather than recovered by decoding, and it is a
/// member id rather than a per-level `LEFT`/`RIGHT`. Both changes are what make
/// this nest: `T` may be an arbitrarily deep [`ConsType`] tree, and no matter how
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
    pub id: Ghost<nat>,
    pub data: [u8; SIZE],
    pub _t: PhantomData<T>,
}

impl<const SIZE: usize, T: Member<SIZE>> TypeSet for GhostTaggedArray<SIZE, T> {
    open spec fn possible_types() -> Set<nat> {
        T::possible_types()
    }
}

impl<const SIZE: usize, T: Member<SIZE>> HasId for GhostTaggedArray<SIZE, T> {
    open spec fn id_of(&self) -> nat {
        self.id@
    }

    open spec fn wf(&self) -> bool {
        T::valid(self.id@, self.data)
    }

    proof fn id_of_in_possible_types(&self) {
        T::valid_in_possible_types(self.id@, self.data);
    }
}

impl<const SIZE: usize, A: Member<SIZE> + DisjointFrom<B>, B: Member<SIZE>> EitherType<
    A,
    B,
> for GhostTaggedArray<SIZE, ConsType<A, B>> {
    open spec fn dyn_id(&self) -> nat {
        self.id@
    }

    open spec fn dyn_wf(&self) -> bool {
        ConsType::<A, B>::valid(self.id@, self.data)
    }

    proof fn type_id_laws(tracked &self) {
        // "not both" from the disjointness witness ...
        A::disjoint(self.dyn_id());
        // ... and "at least one" from whichever side admits the bytes.
        if A::valid(self.id@, self.data) {
            A::valid_in_possible_types(self.id@, self.data);
        } else {
            B::valid_in_possible_types(self.id@, self.data);
        }
    }
}

impl<const SIZE: usize, A: Member<SIZE> + DisjointFrom<B>, B: Member<SIZE>> GhostTaggedArray<
    SIZE,
    ConsType<A, B>,
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
    pub exec fn as_dyn(&self) -> (r: &dyn EitherType<A, B>)
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
/// [`HasId::wf`]) and consumers (which see [`EitherType::dyn_wf`]).
pub proof fn lemma_dyn_agrees<const SIZE: usize, A: Member<SIZE> + DisjointFrom<B>, B: Member<SIZE>>(
    s: &GhostTaggedArray<SIZE, ConsType<A, B>>,
)
    ensures
        s.dyn_id() == s.id_of(),
        s.dyn_wf() == s.wf(),
{
}

/// Storing a well-formed member establishes [`Member::valid`] at its own id.
///
/// This is the constructor side of `wf`, and the one place [`ByteRepr`]'s
/// round-trip law is consumed: it is what says the bytes just written decode
/// again, while `id_of_in_possible_types` says the id recorded beside them is one this
/// leaf admits.
pub proof fn lemma_leaf_valid<const SIZE: usize, M: HasId + ByteRepr<SIZE>>(m: M)
    requires
        m.wf(),
    ensures
        <LeafType<M> as Member<SIZE>>::valid(m.id_of(), m.into_spec()),
{
    m.round_trip();
    m.id_of_in_possible_types();
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

/// Distinct valid byte patterns decode to distinct values.
///
/// The content of [`ByteRepr::canonical`], stated the way it is usually wanted:
/// decoding is injective on valid patterns. Together with
/// [`ByteRepr::round_trip`] — which makes it surjective onto values — this is the
/// bijection, and it is what a storage abstraction needs in order to promise that
/// reading a value out and writing it back leaves the bytes alone.
pub proof fn lemma_decode_injective<const SIZE: usize, M: ByteRepr<SIZE>>(
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

} // verus!
