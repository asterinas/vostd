//! Runtime type identity.
//!
//! [`tagged`] stores a value as bytes beside a ghost record of its type, for
//! reading back at that type later. Its id degrades to an opaque `int` without the
//! `type_id` toolchain patch, so the storage is available in every feature shape
//! and only *deciding* identity needs the patch.
//!
//! [`types`] models `core::any::TypeId` directly -- the real identity, usable
//! through a `dyn` reference -- and needs the patch outright, so it is gated.
pub mod tagged;

#[cfg(feature = "type_id")]
pub mod types;

#[cfg(feature = "type_id")]
pub mod example;
