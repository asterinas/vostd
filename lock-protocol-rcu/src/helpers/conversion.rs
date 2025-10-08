use vstd::prelude::*;

verus! {

pub axiom fn usize_mod_is_int_mod(x: usize, m: usize, z: usize)
    requires
        x % m == z,
    ensures
        (x as int) % (m as int) == (z as int),
;

} // verus!
