//! Leaf-style resource algebras based on storage-protocol.
/// Product of a PCM and a storage-protocol resource algebra.
pub mod hybrid_product;

/// Fractional ownership.
pub mod frac;
/// A combination of fractional ownership and counter PCM.
pub mod count_frac;

pub use hybrid_product::*;
pub use frac::*;
