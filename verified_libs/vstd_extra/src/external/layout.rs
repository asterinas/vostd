use core::alloc::Layout;

use vstd::{layout::valid_layout, prelude::*};

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLayout(Layout);

/// Logical size and alignment of `Layout`.
pub trait LayoutAdditionalSpecFns {
    spec fn spec_size(self) -> usize;

    spec fn spec_align(self) -> usize;
}

impl LayoutAdditionalSpecFns for Layout {
    uninterp spec fn spec_size(self) -> usize;

    uninterp spec fn spec_align(self) -> usize;
}

pub open spec fn layout_size(l: &Layout) -> usize {
    l.spec_size()
}

pub open spec fn layout_align(l: &Layout) -> usize {
    l.spec_align()
}

// Only executable getter calls establish layout validity.
#[verifier::when_used_as_spec(layout_size)]
pub assume_specification[ core::alloc::Layout::size ](l: &Layout) -> usize
    ensures
        valid_layout(l.spec_size(), l.spec_align()),
    returns
        l.spec_size(),
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(layout_align)]
pub assume_specification[ core::alloc::Layout::align ](l: &Layout) -> usize
    ensures
        valid_layout(l.spec_size(), l.spec_align()),
    returns
        l.spec_align(),
    opens_invariants none
    no_unwind
;

} // verus!
