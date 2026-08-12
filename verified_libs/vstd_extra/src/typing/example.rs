//! A worked three-member aggregate, `L1 | (L2 | L3)`, to exercise the laws.
//!
//! The point is to check that uniqueness *composes*: the outer node must show
//! `L1` is disjoint from `L2 | L3`, and the inner node that `L2` is disjoint
//! from `L3`. Neither obligation mentions the other, and no global registry is
//! consulted — which is the property that a flat tag scheme cannot offer.
//!
//! Three members is the smallest size that actually tests nesting, and it is the
//! case the binary-tag design could not express at all.

use core::marker::PhantomData;

use vstd::prelude::*;
use vstd::std_specs::convert::{IntoSpec, IntoSpecImpl, TryFromSpec, TryFromSpecImpl};

use super::types::*;

verus! {

/// Byte width used throughout this example.
pub const EX_SIZE: usize = 8;

/// Sized to `EX_SIZE`, not a unit struct.
///
/// A ZST would make [`ByteSized`] *false* — `size_of::<L1>() == 0`, not 8 —
/// and axiomatizing `size_correct` for it would have been assuming
/// something untrue, which is worse than leaving it unproved.
#[repr(transparent)]
pub struct L1(pub u64);

/// Sized to `EX_SIZE`, not a unit struct.
///
/// A ZST would make [`ByteSized`] *false* — `size_of::<L2>() == 0`, not 8 —
/// and axiomatizing `size_correct` for it would have been assuming
/// something untrue, which is worse than leaving it unproved.
#[repr(transparent)]
pub struct L2(pub u64);

/// Sized to `EX_SIZE`, not a unit struct.
///
/// A ZST would make [`ByteSized`] *false* — `size_of::<L3>() == 0`, not 8 —
/// and axiomatizing `size_correct` for it would have been assuming
/// something untrue, which is worse than leaving it unproved.
#[repr(transparent)]
pub struct L3(pub u64);

// Leaves each own a single id.
impl TypeId for L1 {
    open spec fn inhabits(type_id: nat) -> bool {
        type_id == 1
    }
}

impl HasId for L1 {
    open spec fn id_of(&self) -> nat {
        1
    }

    /// A type owning exactly one id carries its identity in its type, so
    /// there is no tag that could disagree with anything.
    open spec fn wf(&self) -> bool {
        true
    }

    proof fn id_of_inhabits(&self) {
    }
}

impl TypeId for L2 {
    open spec fn inhabits(type_id: nat) -> bool {
        type_id == 2
    }
}

impl HasId for L2 {
    open spec fn id_of(&self) -> nat {
        2
    }

    /// A type owning exactly one id carries its identity in its type, so
    /// there is no tag that could disagree with anything.
    open spec fn wf(&self) -> bool {
        true
    }

    proof fn id_of_inhabits(&self) {
    }
}

impl TypeId for L3 {
    open spec fn inhabits(type_id: nat) -> bool {
        type_id == 3
    }
}

impl HasId for L3 {
    open spec fn id_of(&self) -> nat {
        3
    }

    /// A type owning exactly one id carries its identity in its type, so
    /// there is no tag that could disagree with anything.
    open spec fn wf(&self) -> bool {
        true
    }

    proof fn id_of_inhabits(&self) {
    }
}


/// Encoding of [`L1`], left uninterpreted.
///
/// A concrete byte layout is a fact about the type's representation, not
/// about the aggregate machinery. Naming it without defining it is what
/// lets the round-trip law below be the *only* thing consumers may assume.
pub uninterp spec fn l1_encode(v: L1) -> [u8; EX_SIZE];

/// Decoding of [`L1`], left uninterpreted.
///
/// Note it is total and may return `Ok` for bytes that never came from an
/// `L1`. Nothing here rules that out, and nothing should: rejecting foreign
/// byte patterns is not how members are told apart — see [`DisjointFrom`].
pub uninterp spec fn l1_decode(b: [u8; EX_SIZE]) -> Result<L1, ()>;

/// Decoding recovers what encoding produced.
///
/// Axiomatized: this is the representation obligation a real member would
/// discharge from its layout, and the single fact the aggregate needs.
#[verifier::external_body]
pub broadcast proof fn axiom_l1_round_trip(v: L1)
    ensures
        #[trigger] l1_decode(l1_encode(v)) == Ok(v),
{
}

impl TryFrom<[u8; EX_SIZE]> for L1 {
    type Error = ();

    #[verifier::external_body]
    fn try_from(b: [u8; EX_SIZE]) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}

impl TryFromSpecImpl<[u8; EX_SIZE]> for L1 {
    open spec fn obeys_try_from_spec() -> bool {
        true
    }

    open spec fn try_from_spec(b: [u8; EX_SIZE]) -> Result<Self, Self::Error> {
        l1_decode(b)
    }
}

#[allow(clippy::from_over_into)]
impl Into<[u8; EX_SIZE]> for L1 {
    #[verifier::external_body]
    fn into(self) -> [u8; EX_SIZE] {
        unimplemented!()
    }
}

impl IntoSpecImpl<[u8; EX_SIZE]> for L1 {
    open spec fn obeys_into_spec() -> bool {
        true
    }

    open spec fn into_spec(self) -> [u8; EX_SIZE] {
        l1_encode(self)
    }
}

impl ByteSized<{ EX_SIZE }> for L1 {
    /// Axiomatized: `#[repr(transparent)]` over a `u64` is 8 bytes, which is
    /// a layout fact Verus does not derive for user structs.
    #[verifier::external_body]
    proof fn size_correct() {
    }
}

impl ByteRepr<{ EX_SIZE }> for L1 {
    proof fn round_trip(self) {
        broadcast use axiom_l1_round_trip;
    }
}

/// Encoding of [`L2`], left uninterpreted.
///
/// A concrete byte layout is a fact about the type's representation, not
/// about the aggregate machinery. Naming it without defining it is what
/// lets the round-trip law below be the *only* thing consumers may assume.
pub uninterp spec fn l2_encode(v: L2) -> [u8; EX_SIZE];

/// Decoding of [`L2`], left uninterpreted.
///
/// Note it is total and may return `Ok` for bytes that never came from an
/// `L2`. Nothing here rules that out, and nothing should: rejecting foreign
/// byte patterns is not how members are told apart — see [`DisjointFrom`].
pub uninterp spec fn l2_decode(b: [u8; EX_SIZE]) -> Result<L2, ()>;

/// Decoding recovers what encoding produced.
///
/// Axiomatized: this is the representation obligation a real member would
/// discharge from its layout, and the single fact the aggregate needs.
#[verifier::external_body]
pub broadcast proof fn axiom_l2_round_trip(v: L2)
    ensures
        #[trigger] l2_decode(l2_encode(v)) == Ok(v),
{
}

impl TryFrom<[u8; EX_SIZE]> for L2 {
    type Error = ();

    #[verifier::external_body]
    fn try_from(b: [u8; EX_SIZE]) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}

impl TryFromSpecImpl<[u8; EX_SIZE]> for L2 {
    open spec fn obeys_try_from_spec() -> bool {
        true
    }

    open spec fn try_from_spec(b: [u8; EX_SIZE]) -> Result<Self, Self::Error> {
        l2_decode(b)
    }
}

#[allow(clippy::from_over_into)]
impl Into<[u8; EX_SIZE]> for L2 {
    #[verifier::external_body]
    fn into(self) -> [u8; EX_SIZE] {
        unimplemented!()
    }
}

impl IntoSpecImpl<[u8; EX_SIZE]> for L2 {
    open spec fn obeys_into_spec() -> bool {
        true
    }

    open spec fn into_spec(self) -> [u8; EX_SIZE] {
        l2_encode(self)
    }
}

impl ByteSized<{ EX_SIZE }> for L2 {
    /// Axiomatized: `#[repr(transparent)]` over a `u64` is 8 bytes, which is
    /// a layout fact Verus does not derive for user structs.
    #[verifier::external_body]
    proof fn size_correct() {
    }
}

impl ByteRepr<{ EX_SIZE }> for L2 {
    proof fn round_trip(self) {
        broadcast use axiom_l2_round_trip;
    }
}

/// Encoding of [`L3`], left uninterpreted.
///
/// A concrete byte layout is a fact about the type's representation, not
/// about the aggregate machinery. Naming it without defining it is what
/// lets the round-trip law below be the *only* thing consumers may assume.
pub uninterp spec fn l3_encode(v: L3) -> [u8; EX_SIZE];

/// Decoding of [`L3`], left uninterpreted.
///
/// Note it is total and may return `Ok` for bytes that never came from an
/// `L3`. Nothing here rules that out, and nothing should: rejecting foreign
/// byte patterns is not how members are told apart — see [`DisjointFrom`].
pub uninterp spec fn l3_decode(b: [u8; EX_SIZE]) -> Result<L3, ()>;

/// Decoding recovers what encoding produced.
///
/// Axiomatized: this is the representation obligation a real member would
/// discharge from its layout, and the single fact the aggregate needs.
#[verifier::external_body]
pub broadcast proof fn axiom_l3_round_trip(v: L3)
    ensures
        #[trigger] l3_decode(l3_encode(v)) == Ok(v),
{
}

impl TryFrom<[u8; EX_SIZE]> for L3 {
    type Error = ();

    #[verifier::external_body]
    fn try_from(b: [u8; EX_SIZE]) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}

impl TryFromSpecImpl<[u8; EX_SIZE]> for L3 {
    open spec fn obeys_try_from_spec() -> bool {
        true
    }

    open spec fn try_from_spec(b: [u8; EX_SIZE]) -> Result<Self, Self::Error> {
        l3_decode(b)
    }
}

#[allow(clippy::from_over_into)]
impl Into<[u8; EX_SIZE]> for L3 {
    #[verifier::external_body]
    fn into(self) -> [u8; EX_SIZE] {
        unimplemented!()
    }
}

impl IntoSpecImpl<[u8; EX_SIZE]> for L3 {
    open spec fn obeys_into_spec() -> bool {
        true
    }

    open spec fn into_spec(self) -> [u8; EX_SIZE] {
        l3_encode(self)
    }
}

impl ByteSized<{ EX_SIZE }> for L3 {
    /// Axiomatized: `#[repr(transparent)]` over a `u64` is 8 bytes, which is
    /// a layout fact Verus does not derive for user structs.
    #[verifier::external_body]
    proof fn size_correct() {
    }
}

impl ByteRepr<{ EX_SIZE }> for L3 {
    proof fn round_trip(self) {
        broadcast use axiom_l3_round_trip;
    }
}

// The aggregate tree. Each leaf wraps a representable type; nodes join them.
/// `L1` as a one-member aggregate.
pub type M1 = Leaf<L1>;

/// `L2` as a one-member aggregate.
pub type M2 = Leaf<L2>;

/// `L3` as a one-member aggregate.
pub type M3 = Leaf<L3>;

/// The inner node, `L2 | L3`.
pub type Inner = Node<M2, M3>;

/// The whole aggregate, `L1 | (L2 | L3)`.
pub type Outer = Node<M1, Inner>;

/// Bytes tagged with which of the three members they hold.
///
/// One tag for a three-deep tree — the point of moving from `LEFT`/`RIGHT` to
/// a member id. Under the old design this type could not be written at all.
pub type Store = GhostTaggedArray<{ EX_SIZE }, Outer>;

// Disjointness witnesses, discharged by computation on the leaf ids. Note
// these are stated on the *aggregates*, since that is what `Either` joins.
impl DisjointFrom<M3> for M2 {
    proof fn disjoint(type_id: nat) {
    }
}

impl DisjointFrom<Inner> for M1 {
    proof fn disjoint(type_id: nat) {
    }
}

/// Storing an `L2` yields a well-formed `Store` reporting `L2`'s id.
///
/// The payoff: `wf` is established by construction, two levels down, with no
/// axiom and nothing to remember at the call site.
pub exec fn store_l2(v: L2) -> (r: Store)
    ensures
        r.wf(),
        r.id_of() == 2,
        r.data == <L2 as IntoSpec<[u8; EX_SIZE]>>::into_spec(v),
{
    proof {
        lemma_leaf_holds::<{ EX_SIZE }, L2>(v);
    }
    let data: [u8; EX_SIZE] = v.into();
    Store { id: Ghost(2nat), data, _t: PhantomData }
}

/// A well-formed `Store` holding `L2`'s id satisfies the `Either` law at the
/// outer node: the id belongs to the `L2 | L3` side and not to `L1`.
pub proof fn stored_is_one_side(tracked r: &Store)
    requires
        r.wf(),
        r.id_of() == 2,
    ensures
        Inner::inhabits(r.id_of()) && !M1::inhabits(r.id_of()),
{
    r.type_id_laws();
}

/// Disjointness at the inner node: `L2` and `L3` share no id.
pub proof fn inner_disjoint(t: nat)
    ensures
        !(M2::inhabits(t) && M3::inhabits(t)),
{
}

/// Disjointness at the outer node: `L1` shares no id with `L2 | L3`.
///
/// Note this is discharged *without* reference to the inner node's own
/// obligation. That independence is the composition property being checked:
/// adding a member changes only the node that admits it.
pub proof fn outer_disjoint(t: nat)
    ensures
        !(M1::inhabits(t) && Inner::inhabits(t)),
{
}

/// A member of the aggregate lands in exactly one leaf.
///
/// This is the shape a downcast consumes: given an id known to inhabit the
/// aggregate, exactly one leaf claims it, so testing against a leaf cannot
/// succeed for the wrong one.
pub proof fn exactly_one_leaf(t: nat)
    requires
        Outer::inhabits(t),
    ensures
        ({
            &&& L1::inhabits(t) ==> !L2::inhabits(t) && !L3::inhabits(t)
            &&& L2::inhabits(t) ==> !L1::inhabits(t) && !L3::inhabits(t)
            &&& L3::inhabits(t) ==> !L1::inhabits(t) && !L2::inhabits(t)
        }),
{
}

// ------------------------------------------------------------------
// The three behaviors.
// ------------------------------------------------------------------

/// **Upcast.** A stored member, viewed as an erased aggregate.
///
/// Two erasures compose here: the concrete `L2` becomes bytes-plus-ghost-id
/// ([`store_l2`]), and that becomes `&dyn Either<M1, Inner>` (`as_dyn`). The id
/// survives both, which is what makes the result useful rather than opaque.
pub fn upcast_l2(s: &Store) -> (r: &dyn Either<M1, Inner>)
    requires
        s.wf(),
        s.id_of() == 2,
    ensures
        r.dyn_id() == 2,
        r.dyn_wf(),
{
    proof {
        lemma_dyn_agrees::<{ EX_SIZE }, M1, Inner>(s);
    }
    s.as_dyn()
}

/// **Dispatch, at the aggregate.** Get the uniqueness law through an erased
/// reference, without knowing which member is live.
///
/// This is proof-mode dynamic dispatch: `type_id_laws` is resolved through the
/// vtable of whatever concrete type was erased.
pub proof fn dispatch_erased(tracked r: &dyn Either<M1, Inner>)
    requires
        r.dyn_wf(),
    ensures
        ({
            ||| M1::inhabits(r.dyn_id()) && !Inner::inhabits(r.dyn_id())
            ||| Inner::inhabits(r.dyn_id()) && !M1::inhabits(r.dyn_id())
        }),
{
    r.type_id_laws();
}

/// **Downcast.** Recover the concrete `L2` from the aggregate.
///
/// The `id` parameter is not redundant with the ghost tag: the tag is *ghost*,
/// so no executable code may branch on it. A runtime witness has to come from
/// somewhere, and the precondition is what ties it to the ghost tag — exactly
/// the pairing the frame layer maintains between a stored word and its ghost
/// twin, except stated as a precondition instead of assumed by an axiom.
///
/// The postcondition is an `<==>`, so this records both halves: the downcast
/// *succeeds* for the right member and *fails* for every other one. The second
/// half is the soundness property, and it is where `DisjointFrom` is spent.
///
/// This discriminates rather than verifying vacuously. Probed by substituting
/// `L3::try_from` for `L2::try_from` with everything else unchanged: the
/// unreachability of the `Err` branch stops being provable, because a tag of
/// `2` says nothing about whether the bytes decode as an `L3`.
pub fn downcast_l2(s: &Store, id: usize) -> (r: Option<L2>)
    requires
        s.wf(),
        id as nat == s.id_of(),
    ensures
        (r is Some) <==> s.id_of() == 2,
{
    if id == 2 {
        assert(<M2 as Member<{ EX_SIZE }>>::holds(2, s.data)) by {
            assert(!<M1 as Member<{ EX_SIZE }>>::holds(2, s.data));
            assert(!<M3 as Member<{ EX_SIZE }>>::holds(2, s.data));
        }
        match L2::try_from(s.data) {
            Ok(v) => Some(v),
            Err(_) => {
                assert(false);
                None
            },
        }
    } else {
        None
    }
}

/// The downcast cannot succeed for a member other than the one stored.
///
/// Stated separately because it is the property worth having in isolation:
/// given only that some id inhabits the aggregate, at most one leaf claims it.
pub proof fn downcast_rejects_others(s: &Store)
    requires
        s.wf(),
        s.id_of() == 2,
    ensures
        !M1::inhabits(s.id_of()),
        !M3::inhabits(s.id_of()),
        M2::inhabits(s.id_of()),
{
}

/// **Dispatch, at the member.** A real three-way vtable call.
///
/// Separate from the aggregate's erased view, and necessarily so: the
/// aggregate's tag is ghost, so nothing executable can branch on it. Runtime
/// dispatch has to come from a real vtable, which means erasing the *member*
/// types rather than the storage. The two erasures answer different questions —
/// `Either` says which member it is, `Payload` runs its code.
///
/// Note `Payload` has no supertrait. Giving it [`HasId`] would drag in
/// [`TypeId`], which `dyn` does not satisfy, so it re-declares the id itself.
pub trait Payload {
    spec fn word_spec(&self) -> u64;

    spec fn payload_id(&self) -> nat;

    fn word(&self) -> (r: u64)
        ensures
            r == self.word_spec(),
    ;
}

impl Payload for L1 {
    open spec fn word_spec(&self) -> u64 {
        self.0
    }

    open spec fn payload_id(&self) -> nat {
        1
    }

    fn word(&self) -> (r: u64) {
        self.0
    }
}

impl Payload for L2 {
    open spec fn word_spec(&self) -> u64 {
        self.0
    }

    open spec fn payload_id(&self) -> nat {
        2
    }

    fn word(&self) -> (r: u64) {
        self.0
    }
}

impl Payload for L3 {
    open spec fn word_spec(&self) -> u64 {
        self.0
    }

    open spec fn payload_id(&self) -> nat {
        3
    }

    fn word(&self) -> (r: u64) {
        self.0
    }
}

/// Dispatch through an erased member: three impls, one call site.
pub fn dispatch_payload(d: &dyn Payload) -> (r: u64)
    ensures
        r == d.word_spec(),
{
    d.word()
}

/// Upcast a member and dispatch to it, with the id carried across.
///
/// The `assert`s are the point: after erasure Verus still knows *which* impl
/// was erased, so both the id and the dispatched value are pinned down.
pub fn upcast_and_dispatch_l2(v: L2) -> (r: u64)
    ensures
        r == v.0,
{
    let d: &dyn Payload = &v;
    assert(d.payload_id() == 2);
    assert(d.word_spec() == v.0);
    dispatch_payload(d)
}


/// The word carried by the member that `data` encodes at `id`.
///
/// Needed because [`dispatch_store`] promising only the id would make dispatch
/// useless: a caller could tell *which* member is live but learn nothing from
/// running its code. This is the closed-world match at the spec level, and it is
/// what lets the value survive erasure.
pub open spec fn word_at(id: nat, data: [u8; EX_SIZE]) -> u64 {
    if id == 1 {
        <L1 as TryFromSpec<[u8; EX_SIZE]>>::try_from_spec(data)->Ok_0.0
    } else if id == 2 {
        <L2 as TryFromSpec<[u8; EX_SIZE]>>::try_from_spec(data)->Ok_0.0
    } else {
        <L3 as TryFromSpec<[u8; EX_SIZE]>>::try_from_spec(data)->Ok_0.0
    }
}

/// **The bridge.** Stored bytes to a dispatchable reference to the shared trait.
///
/// This is what `dispatch_meta` does in the frame layer, and it is the piece that
/// makes an aggregate useful rather than merely identifiable: the caller gets to
/// *run the member's code* without knowing which member it is.
///
/// The `tag` argument is the ghost id's runtime witness, as in [`downcast_l2`] —
/// exec code cannot branch on ghost state, and vtable selection is exec. Upstream
/// that word is the vtable pointer already living in the slot, so carrying it
/// costs nothing that was not already being paid.
///
/// Two things are worth noting about the proof. The match is *exhaustive over the
/// aggregate*, not over `usize`: the default arm is dead because `wf` forces the
/// id to inhabit `Outer`, i.e. to be one of `1`, `2`, `3`. And the postcondition
/// holds because each arm's `&Ln -> &dyn Payload` coercion is one Verus tracks —
/// it knows which impl was erased, so it knows the erased `payload_id`.
///
/// So the only assumed step in the whole path is [`borrow_as`].
///
/// This discriminates. Probed by swapping one arm's member while leaving its
/// guard alone: both postconditions fail *and* `borrow_as`'s precondition fails,
/// since a tag of `2` neither makes the bytes an `L1` nor gives `L1`'s id.
pub fn dispatch_store(s: &Store, tag: usize) -> (r: &dyn Payload)
    requires
        s.wf(),
        tag as nat == s.id_of(),
    ensures
        r.payload_id() == s.id_of(),
        r.word_spec() == word_at(s.id_of(), s.data),
{
    proof {
        // `wf` says some member admits these bytes; that pins the id to a leaf.
        <Outer as Member<{ EX_SIZE }>>::holds_inhabits(s.id_of(), s.data);
    }
    if tag == 1 {
        assert(<M1 as Member<{ EX_SIZE }>>::holds(1, s.data));
        borrow_as::<{ EX_SIZE }, L1>(&s.data)
    } else if tag == 2 {
        assert(<M2 as Member<{ EX_SIZE }>>::holds(2, s.data));
        borrow_as::<{ EX_SIZE }, L2>(&s.data)
    } else {
        assert(tag == 3);
        assert(<M3 as Member<{ EX_SIZE }>>::holds(3, s.data));
        borrow_as::<{ EX_SIZE }, L3>(&s.data)
    }
}

/// End to end: store a member, then run its code through the erased reference.
///
/// Neither `dispatch_store` nor `dispatch_payload` is told which member is live,
/// yet the returned word is pinned to the one that was stored.
pub fn store_then_dispatch(v: L2) -> (r: u64)
    ensures
        r == v.0,
{
    let s = store_l2(v);
    let d = dispatch_store(&s, 2);
    proof {
        // The bytes decode back to `v`, so the erased word is `v`'s.
        v.round_trip();
    }
    assert(d.payload_id() == 2);
    dispatch_payload(d)
}

} // verus!
