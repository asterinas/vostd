//! Partial commutative monoid (PCM) based resource algebras.
/// Agreement resource algebra
pub mod agree;
/// Reference counting resource algebra
pub mod count;
/// Csum resource algebra
pub mod csum;
/// Exclusive resource algebra
pub mod excl;
/// Fractional resource algebra
pub mod frac;

pub use agree::*;
pub use count::*;
pub use csum::*;
pub use excl::*;
pub use frac::*;
