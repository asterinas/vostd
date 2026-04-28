//! Specifications for `core::num::NonZero<T>` for the concrete element types
//! we use (`usize`, `u8`).
//!
//! ## Why wrappers instead of `assume_specification`
//!
//! `core::num::NonZero::<T>::{new, get}` are generic over
//! `T: ZeroablePrimitive`, where `ZeroablePrimitive` is a sealed external
//! trait (its `Sealed` super-trait is private to `core`). That combination
//! makes both standard escape hatches unusable:
//!   * `assume_specification` requires a *byte-for-byte* signature match with
//!     the original generic function, so it cannot be specialized.
//!   * `#[verifier::external_trait_specification]` for `ZeroablePrimitive`
//!     fails because the proxy trait cannot reproduce the private `Sealed`
//!     super-trait bound.
//!
//! Either path forces Verus into `--no-lifetime`, which is infectious across
//! crate boundaries (any downstream `--import`er would also need it).
//!
//! Instead, we wrap the std `NonZero<T>` in our own `#[verifier::external_body]`
//! newtypes (one per element type) and expose `new`/`get` as `external_body`
//! exec functions whose Verus signatures only mention the wrapper. The std
//! `NonZero<T>` therefore never appears in any spec or wrapper signature,
//! which lets verification run with full lifetime checking enabled.

use core::num::NonZero;
use vstd::prelude::*;

verus! {

// ---- NonZeroUsize ----

#[verifier::external_body]
pub struct NonZeroUsize {
    inner: NonZero<usize>,
}

pub uninterp spec fn spec_nonzero_usize_view(nz: NonZeroUsize) -> usize;

#[verifier::external_body]
pub fn nonzero_usize_new(v: usize) -> (r: Option<NonZeroUsize>)
    ensures
        r.is_some() <==> v != 0,
        r.is_some() ==> spec_nonzero_usize_view(r.unwrap()) == v,
{
    NonZero::<usize>::new(v).map(|inner| NonZeroUsize { inner })
}

#[verifier::external_body]
pub fn nonzero_usize_get(nz: NonZeroUsize) -> (r: usize)
    ensures
        r == spec_nonzero_usize_view(nz),
        r != 0,
{
    nz.inner.get()
}

// ---- NonZeroU8 ----

#[verifier::external_body]
pub struct NonZeroU8 {
    inner: NonZero<u8>,
}

pub uninterp spec fn spec_nonzero_u8_view(nz: NonZeroU8) -> u8;

#[verifier::external_body]
pub fn nonzero_u8_new(v: u8) -> (r: Option<NonZeroU8>)
    ensures
        r.is_some() <==> v != 0,
        r.is_some() ==> spec_nonzero_u8_view(r.unwrap()) == v,
{
    NonZero::<u8>::new(v).map(|inner| NonZeroU8 { inner })
}

#[verifier::external_body]
pub fn nonzero_u8_get(nz: NonZeroU8) -> (r: u8)
    ensures
        r == spec_nonzero_u8_view(nz),
        r != 0,
{
    nz.inner.get()
}

} // verus!

// Outside `verus!`, expose interop with the underlying std type for callers
// that need to bridge with non-Verus exec code. These are plain Rust impls
// (not part of the verifier surface), so they don't reintroduce the
// `ZeroablePrimitive` bound into Verus.
impl NonZeroUsize {
    #[inline]
    pub fn into_inner(self) -> NonZero<usize> {
        self.inner
    }

    #[inline]
    pub fn from_inner(inner: NonZero<usize>) -> Self {
        Self { inner }
    }
}

impl NonZeroU8 {
    #[inline]
    pub fn into_inner(self) -> NonZero<u8> {
        self.inner
    }

    #[inline]
    pub fn from_inner(inner: NonZero<u8>) -> Self {
        Self { inner }
    }
}
