//！ Sum types for ghost resources.
use vstd::prelude::*;

verus! {

pub ghost enum CsumP<A, B> {
    Unit,
    Cinl(A),
    Cinr(B),
    CsumInvalid,
}

} // verus!
