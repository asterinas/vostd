//! The "extra standard library" for [Verus](https://github.com/verus-lang/verus).
//! Contains various utilities and general datatypes for proofs useful in Asterinas verification,
//! as well as extending [Verus standard library(vstd)](https://verus-lang.github.io/verus/verusdoc/vstd) with additional functionality.
#![feature(nonzero_internals)]
#![feature(sized_hierarchy)]
#![feature(proc_macro_hygiene)]
#![feature(core_intrinsics)]
#![cfg_attr(verus_keep_ghost, feature(allocator_api))]
#![allow(non_snake_case)]
#![allow(unused_parens)]
#![allow(unused_braces)]
#![allow(rustdoc::invalid_rust_codeblocks)]
#![allow(rustdoc::invalid_html_tags)]
#![allow(rustdoc::broken_intra_doc_links)]

extern crate alloc;

pub mod arithmetic;
pub mod array_ptr;
pub mod auxiliary;
pub mod cast_ptr;
pub mod drop_tracking;
pub mod external;
pub mod function_properties;
pub mod ghost_tree;
pub mod ownership;
pub mod panic;
pub mod resource;

#[macro_use]
pub mod trans_macros;
pub mod map_extra;

pub mod prelude;
pub mod raw_ptr_extra;
pub mod seq_extra;
pub mod set_extra;
pub mod spec_operators;
pub mod state_machine;
pub mod sum;
pub mod temporal_logic;
