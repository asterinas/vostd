//! Leaf-style resource algebras based on storage-protocol.

/// Fractional permission for shared read access
pub mod frac;


use vstd::prelude::*;

pub type SingleStorage<T> = Map<(), T>;
pub type OptionSingleStorage<T> = Map<(), Option<T>>;