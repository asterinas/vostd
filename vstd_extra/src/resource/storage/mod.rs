//! Leaf-style resource algebras based on storage-protocol.
/// Fractional ownership.
pub mod frac;
/// Product of a PCM and a storage-protocol resource algebra.
pub mod hybrid_product;

pub use frac::*;
pub use hybrid_product::*;
