//! Specifications for the bitmap-backed ID allocator.
use core::ops::Range;

use id_alloc::IdAlloc;
use vstd::prelude::*;

verus! {

/// Verus model for the external bitmap-backed ID allocator.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIdAlloc(IdAlloc);

/// IDs currently allocated by an external `IdAlloc`.
pub uninterp spec fn id_alloc_view(allocator: &IdAlloc) -> Set<usize>;

/// Capacity configured for an external `IdAlloc`.
pub uninterp spec fn id_alloc_capacity(allocator: &IdAlloc) -> usize;

pub assume_specification[ IdAlloc::with_capacity ](capacity: usize) -> (allocator: IdAlloc)
    ensures
        id_alloc_capacity(&allocator) == capacity,
        id_alloc_view(&allocator) == Set::<usize>::empty(),
;

pub assume_specification[ IdAlloc::is_allocated ](allocator: &IdAlloc, id: usize) -> (allocated:
    bool)
    ensures
        id < id_alloc_capacity(allocator) ==> allocated == id_alloc_view(allocator).contains(id),
;

pub assume_specification[ IdAlloc::alloc_specific ](allocator: &mut IdAlloc, id: usize) -> (result:
    Option<usize>)
    requires
        id < id_alloc_capacity(old(allocator)),
    ensures
        id_alloc_capacity(final(allocator)) == id_alloc_capacity(old(allocator)),
        id_alloc_view(final(allocator)) == id_alloc_view(old(allocator)).insert(id),
        id_alloc_view(old(allocator)).subset_of(id_alloc_view(final(allocator))),
        id_alloc_view(old(allocator)).contains(id) ==> {
            &&& result is None
        },
        !id_alloc_view(old(allocator)).contains(id) ==> {
            &&& result == Some(id)
        },
    no_unwind
;

pub assume_specification[ IdAlloc::free_consecutive ](allocator: &mut IdAlloc, range: Range<usize>)
    requires
        range.end <= id_alloc_capacity(old(allocator)),
    ensures
        id_alloc_capacity(final(allocator)) == id_alloc_capacity(old(allocator)),
        forall|id: usize| #[trigger]
            id_alloc_view(final(allocator)).contains(id) <==> id_alloc_view(
                old(allocator),
            ).contains(id) && !(range.start <= id < range.end),
    no_unwind
;

} // verus!
