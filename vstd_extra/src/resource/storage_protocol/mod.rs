//! Aster-specific Leaf-style storage protocols.
//!
//! The generic storage-protocol API itself now comes from `vstd::resource::storage_protocol`.
pub use vstd::resource::storage_protocol::*;

pub mod csum;
