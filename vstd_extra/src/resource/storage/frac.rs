//! This module defines the real-based fractional permissions storage protocol.

use vstd::prelude::*;
use vstd::storage_protocol::*;

verus!{

#[verifier::ext_equal]
pub tracked enum FracS<T> {
    Unit,
    Frac(real, T),
    Invalid,
}

}