use core::alloc::Layout;

use vstd::{layout::valid_layout, prelude::*};

verus! {

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

/// `Layout::size`, trusted to equal `l.spec_size()`.
/// Layout validity is guaranteed only by executable calls.
pub assume_specification[ core::alloc::Layout::size ](l: &Layout) -> usize
    ensures
        valid_layout(l.spec_size(), l.spec_align()),
    returns
        l.spec_size(),
;

/// `Layout::align`, trusted to equal `l.spec_align()`.
pub assume_specification[ core::alloc::Layout::align ](l: &Layout) -> usize
    returns
        l.spec_align(),
;

} // verus!
