use core::alloc::Layout;

use vstd::{layout::valid_layout, prelude::*};

verus! {

/// Verus-visible counterpart of the external `core::alloc::Layout` type.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLayout(Layout);

/// Additional specification functions for `core::alloc::Layout`.
pub trait LayoutAdditionalSpecFns {
    /// The layout's size in bytes.
    spec fn spec_size(self) -> usize;

    /// The layout's alignment in bytes.
    spec fn spec_align(self) -> usize;
}

impl LayoutAdditionalSpecFns for Layout {
    uninterp spec fn spec_size(self) -> usize;

    uninterp spec fn spec_align(self) -> usize;
}

/// Core's documented `Layout` validity invariant, trusted for `l`.
pub axiom fn axiom_layout_model(l: Layout)
    ensures
        valid_layout(l.spec_size(), l.spec_align()),
;

/// `Layout::size`, trusted to equal `(*self_).spec_size()`.
pub assume_specification[ core::alloc::Layout::size ](self_: &Layout) -> usize
    returns
        (*self_).spec_size(),
;

/// `Layout::align`, trusted to equal `(*self_).spec_align()`.
pub assume_specification[ core::alloc::Layout::align ](self_: &Layout) -> usize
    returns
        (*self_).spec_align(),
;

} // verus!
