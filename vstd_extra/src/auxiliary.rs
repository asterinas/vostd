use vstd::prelude::*;

verus! {

// Produces an arbitrary PointsTo permission for type T, this is sound because one can not use
// such a permission to access memory.
#[verifier(external_body)]
pub proof fn arbitrary_cell_pointsto<T>() -> (tracked res: vstd::cell::pcell::PointsTo<T>) {
    unimplemented!();
}

} // verus!
