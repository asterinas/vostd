//! Leaf-style resource algebras based on storage-protocol.
/// Product of a PCM and a storage-protocol resource algebra.
pub mod hybrid_product;

/// A combination of fractional ownership and counter PCM.
pub mod count_frac;
/// Fractional ownership.
pub mod frac;

pub use frac::*;
pub use hybrid_product::*;
