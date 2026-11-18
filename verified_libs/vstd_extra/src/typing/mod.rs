//! Runtime type identity.
//!
//! [`tagged`] stores a value as bytes beside a ghost record of its type, for
//! reading back at that type later. The recorded id is a real
//! `core::any::TypeId`; it used to degrade to an opaque `int` without the
//! toolchain patch, which is no longer a shape this workspace builds in.
//!
//! There used to be a `types` module here duplicating `core::any::Any`'s
//! interface, because Verus could not model `Any`. It can now: `dyn Any` is a
//! legal type, `type_id_of` answers which type is inside one, and
//! `<dyn Any>::is` is specified in `vstd::std_specs::any`. [`example`]
//! exercises the real API in place of the duplicate.
pub mod tagged;

pub mod example;
