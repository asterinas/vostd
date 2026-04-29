//! Specifications for `core::num::NonZero<usize>` using a wrapper type `NonZeroUsize`.
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
//! Instead, we wrap the std `NonZero<usize>` in our own
//! `#[verifier::external_body]` newtype and expose `new`/`get` as
//! `external_body` exec functions whose Verus signatures only mention the
//! wrapper. The std `NonZero<usize>` therefore never appears in any spec or
//! wrapper signature, which lets verification run with full lifetime checking
//! enabled.
use core::cmp::Ordering;
use core::ops::BitOr;
use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use vstd::std_specs::ops::BitOrSpecImpl;

verus! {

#[verifier::external_body]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NonZeroUsize {
    pub inner: core::num::NonZero<usize>,
}

impl View for NonZeroUsize {
    type V = usize;

    uninterp spec fn view(&self) -> Self::V;
}

impl NonZeroUsize {
    pub uninterp spec fn nonzero_usize_from_usize(n: usize) -> Self;

    pub broadcast axiom fn axiom_nonzero_usize_from_usize_view_eq(n: usize)
        requires
            n != 0,
        ensures
            (#[trigger] Self::nonzero_usize_from_usize(n)).view() == n,
    ;

    pub broadcast axiom fn axiom_view_nonzero_usize_from_usize_eq(self)
        ensures
            Self::nonzero_usize_from_usize(#[trigger] self.view()) == self,
    ;

    #[verifier::external_body]
    pub const fn new(n: usize) -> (ret: Option<Self>)
        ensures
            match ret {
                Some(nz) => nz.view() == n,
                None => n == 0,
            },
    {
        if let Some(inner) = core::num::NonZeroUsize::new(n) {
            Some(NonZeroUsize { inner })
        } else {
            None
        }
    }

    #[verifier::external_body]
    #[verifier::when_used_as_spec(nonzero_usize_from_usize)]
    pub const unsafe fn new_unchecked(n: usize) -> (ret: Self)
        ensures
            ret.view() == n,
            ret == Self::nonzero_usize_from_usize(n),
    {
        NonZeroUsize { inner: core::num::NonZeroUsize::new_unchecked(n) }
    }

    #[verifier::external_body]
    pub const fn get(&self) -> (ret: usize)
        ensures
            ret == self.view(),
    {
        self.inner.get()
    }

    broadcast axiom fn lemma_nonzero_neq_zero(self)
        ensures
            #[trigger] self.view() != 0,
    ;
}

impl Clone for NonZeroUsize {
    #[verifier::external_body]
    fn clone(&self) -> (ret: Self)
        ensures
            ret.view() == self.view(),
    {
        NonZeroUsize { inner: self.inner }
    }
}

impl Copy for NonZeroUsize {

}

impl PartialEqSpecImpl for NonZeroUsize {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        self.view() == other.view()
    }
}

impl PartialOrdSpecImpl for NonZeroUsize {
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<Ordering> {
        if self.view() < other.view() {
            Some(Ordering::Less)
        } else if self.view() > other.view() {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

impl OrdSpecImpl for NonZeroUsize {
    open spec fn obeys_cmp_spec() -> bool {
        true
    }

    open spec fn cmp_spec(&self, other: &Self) -> Ordering {
        vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(self, other)->Some_0
    }
}

pub broadcast group group_nonzero_axioms {
    NonZeroUsize::lemma_nonzero_neq_zero,
    NonZeroUsize::axiom_nonzero_usize_from_usize_view_eq,
    NonZeroUsize::axiom_view_nonzero_usize_from_usize_eq,
}

impl BitOrSpecImpl<usize> for NonZeroUsize {
    open spec fn obeys_bitor_spec() -> bool {
        true
    }

    open spec fn bitor_req(self, rhs: usize) -> bool {
        true
    }

    open spec fn bitor_spec(self, rhs: usize) -> Self {
        Self::nonzero_usize_from_usize(self.view() | rhs)
    }
}

impl BitOr<usize> for NonZeroUsize {
    type Output = Self;

    fn bitor(self, rhs: usize) -> (ret: Self::Output)
        ensures
            ret.view() == self.view() | rhs,
    {
        unsafe { Self::new_unchecked(self.get() | rhs) }
    }
}

} // verus!
