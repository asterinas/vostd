//! A closed-world model of runtime type identity.
//!
//! Verus does not expose `TypeId`, so a value that has been erased has no way to
//! say what it is. This module builds the missing piece out of ordinary traits:
//! members are given ids, aggregates are built by nesting, and uniqueness of ids
//! is discharged *per nesting node* rather than by a global registry — so adding
//! a member changes only the node that admits it.
//!
//! [`types`] has the machinery; [`example`] exercises it on a three-member
//! aggregate, including the three behaviors that motivate the whole thing:
//! upcast, downcast, and dispatch.
#[macro_use]
pub mod any_of;

pub mod types;

pub mod example;

pub mod example_meta;

pub mod example_any_of;
