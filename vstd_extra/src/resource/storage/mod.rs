//! Leaf-style resource algebras based on storage-protocol.
/// Product of a PCM and a storage-protocol resource algebra.
pub mod hybrid_product;

/// Fractional permission which supports fractional ghost resource and counting mechanism.
pub mod frac;

pub use hybrid_product::*;
pub use frac::*;
