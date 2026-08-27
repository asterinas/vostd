use vstd::prelude::*;

use core::any::TypeId;

use vstd::std_specs::convert::{IntoSpec, TryFromSpec};

verus! {

/// A duplicate of [`core::any::Any`]'s interface.
///
/// Never implemented by hand. The blanket impl below is the only impl and covers
/// every sized type; coherence forbids a competing one. That is exactly `std`'s
/// arrangement, and it is half of what a downcast needs: `type_id_spec` *cannot*
/// report the wrong type, because no one is in a position to write a version that
/// does. The other half -- that a tag *determines* the type -- now holds too,
/// since identity became decoration-sensitive; it rests on the collision
/// assumption documented in `vstd::std_specs::any`. See
/// [`crate::typing::soundness`] for the full argument.
pub trait Any {
    /// The identity of this value's concrete type.
    spec fn type_id_spec(&self) -> TypeId;

    /// The same identity, at runtime. The *same* value, not a counterpart: there
    /// is one `TypeId` type, so no `view()` is needed to relate them.
    fn type_id(&self) -> (r: TypeId)
        ensures
            r == self.type_id_spec(),
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

/// Blanket implementation of `Any` for all sized `'static` types.
///
/// The `'static` bound is `core::any::TypeId::of`'s, and `core::any::Any`'s too --
/// a non-`'static` type has no runtime identity to report.
impl<T: Sized + 'static> Any for T {
    open spec fn type_id_spec(&self) -> TypeId {
        type_id::<T>()
    }

    fn type_id(&self) -> (r: TypeId) {
        TypeId::of::<T>()
    }

    proof fn type_id_correct(&self) {
    }
}

impl<T: Sized + 'static> AnyCast for T {
    fn to_any(&self) -> (r: &dyn Any) {
        let d: &dyn Any = self;
        // The `ToDyn` coercion preserves the trait's own spec fns; naming that
        // step is what connects the erased value's identity to `T`'s.
        assert(d.type_id_spec() == self.type_id_spec());
        d
    }
}

/// `x.is::<T>()`.
///
/// Identity is decoration-sensitive, so this is false for `&T`, `Box<T>`,
/// `Rc<T>` and `Arc<T>` -- each has its own tag, at every level of nesting.
/// Rejecting is unconditionally sound; accepting rests on the collision
/// assumption in `vstd::std_specs::any`. See [`crate::typing::soundness`].
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

/// `<dyn Any>::is`.
///
/// Both sides are `core::any::TypeId` values -- the one dispatched through the
/// vtable and the one the compiler knows statically -- compared with the real
/// `PartialEq`.
pub exec fn is_<T: 'static>(x: &dyn Any) -> (r: bool)
    ensures
        r == is_type::<T>(x),
{
    x.type_id().eq(&TypeId::of::<T>())
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
