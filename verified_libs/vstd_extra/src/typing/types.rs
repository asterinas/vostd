use vstd::prelude::*;

use vstd::std_specs::convert::{IntoSpec, TryFromSpec};

verus! {

/// A duplicate of [`core::any::Any`]'s interface.
///
/// Never implemented by hand. The blanket impl below is the only impl and covers
/// every sized type; coherence forbids a competing one. That is exactly `std`'s
/// arrangement, and it is what makes a downcast sound: `type_id_spec` *cannot*
/// report the wrong type, because no one is in a position to write a version that
/// does.
pub trait Any {
    /// The identity of this value's concrete type.
    spec fn type_id_spec(&self) -> TypeIdSpec;

    /// The same identity, as a runtime value.
    fn type_id(&self) -> (r: TypeId)
        ensures
            r.view() == self.type_id_spec(),
    ;

    /// A value's identity is its type's identity.
    proof fn type_id_correct(&self) where Self: Sized
        ensures
            self.type_id_spec() == type_id::<Self>(),
    ;
}

pub trait AnyCast: Any {
    /// Mimics the cast `as & dyn Any`
    exec fn to_any(&self) -> (r: &dyn Any)
        ensures
            r.type_id_spec() == self.type_id_spec(),
    ;
}

/// Blanket implementation of `Any` for all sized types.
impl<T: Sized> Any for T {
    open spec fn type_id_spec(&self) -> TypeIdSpec {
        type_id::<T>()
    }

    fn type_id(&self) -> (r: TypeId) {
        TypeId::of::<T>()
    }

    proof fn type_id_correct(&self) {
    }
}

impl<T: Sized> AnyCast for T {
    fn to_any(&self) -> (r: &dyn Any) {
        let d: &dyn Any = self;
        // The `ToDyn` coercion preserves the trait's own spec fns; naming that
        // step is what connects the erased value's identity to `T`'s.
        assert(d.type_id_spec() == self.type_id_spec());
        d
    }
}

/// `x.is::<T>()`.
pub open spec fn is_type<T>(x: &dyn Any) -> bool {
    x.type_id_spec() == type_id::<T>()
}

/// Two erased values of different types are different values.
pub proof fn lemma_distinct_types_distinct_values<A: Any + Sized, B: Any + Sized>(a: &A, b: &B)
    requires
        type_id::<A>() != type_id::<B>(),
    ensures
        a.type_id_spec() != b.type_id_spec(),
{
    a.type_id_correct();
    b.type_id_correct();
}

/// The exec counterpart of the ghost [`TypeIdSpec`].
#[verifier::external_body]
pub struct TypeId {
    _private: (),
}

impl TypeId {
    /// The ghost identity this runtime value stands for.
    pub uninterp spec fn view(&self) -> TypeIdSpec;

    /// `core::any::TypeIdSpec::of::<T>()`.
    #[verifier::external_body]
    pub exec fn of<T>() -> (r: Self)
        ensures
            r.view() == type_id::<T>(),
    {
        unimplemented!()
    }

    /// Deciding identity at runtime.
    #[verifier::external_body]
    pub exec fn eq(&self, other: &Self) -> (r: bool)
        returns
            self.view() == other.view(),
    {
        unimplemented!()
    }
}

/// `<dyn Any>::is`
pub exec fn is_<T>(x: &dyn Any) -> (r: bool)
    ensures
        r == is_type::<T>(x),
{
    x.type_id().eq(&TypeId::of::<T>())
}

/// Reinterpretation, once identity is settled.
///
/// The module's remaining assumed fact about identity, and it is now only the
/// *cast*: the test that guards it is [`is_`], which is verified. What licenses
/// the cast is [`Any::type_id_correct`] -- a value's reported identity is its
/// concrete type's, so a matching identity really does mean a `T`.
#[verifier::external_body]
pub exec fn downcast_ref_unchecked<'a, T: Any + Sized>(x: &'a dyn Any) -> (r: &'a T)
    requires
        is_type::<T>(x),
    ensures
        r.type_id_spec() == x.type_id_spec(),
{
    unimplemented!()
}

/// `<dyn Any>::downcast_ref`.
///
/// The `<==>` records both halves: it succeeds for the right type *and fails for
/// every other one*.
pub exec fn downcast_ref<'a, T: Any + Sized>(x: &'a dyn Any) -> (r: Option<&'a T>)
    ensures
        (r is Some) <==> is_type::<T>(x),
        r matches Some(v) ==> v.type_id_spec() == x.type_id_spec(),
{
    if is_::<T>(x) {
        Some(downcast_ref_unchecked::<T>(x))
    } else {
        None
    }
}

// ===========================================================================
// Representation
// ===========================================================================
//
pub trait ByteSized<const SIZE: usize>: Sized {
    proof fn size_correct()
        ensures
            size_of::<Self>() == SIZE,
    ;
}

pub trait ByteRepr<const SIZE: usize>: ByteSized<SIZE> + TryFromSpec<[u8; SIZE]> + IntoSpec<
    [u8; SIZE],
> {
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

/// Reinterpret stored bytes as a reference to the value they encode.
///
/// # The one axiom
///
/// It cannot be proved. Verus has no model of the pointer cast involved, and the
/// fact being asserted is that a byte pattern satisfying `M`'s decode really may
/// be *read as* an `M` in place, rather than decoded into a fresh value. That is
/// a statement about layout, which is why the precondition is exactly the decode
/// and nothing weaker: bytes that do not decode may not be borrowed at all.
///
/// Note what this is *not*: it says nothing about identity. Deciding which type a
/// stored value is belongs to [`Any`], and with a `&M` in hand the ordinary
/// `&M -> &dyn Any` coercion carries the identity across.
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
/// bijection a storage abstraction needs in order to promise that reading a value
/// out and writing it back leaves the bytes alone.
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
