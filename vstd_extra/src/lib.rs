//! The "extra standard library" for [Verus](https://github.com/verus-lang/verus).
//! Contains various utilities and general datatypes for proofs useful in Asterinas verification,
//! as well as extending [Verus standard library(vstd)](https://verus-lang.github.io/verus/verusdoc/vstd) with additional functionality.
#![feature(sized_hierarchy)]
#![feature(proc_macro_hygiene)]
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
pub mod bit_mapping;
pub mod cast_ptr;
pub mod extern_const;
pub mod external;
pub mod function_properties;
pub mod ghost_tree;
pub mod ownership;
pub mod resource;
pub mod undroppable;

#[macro_use]
pub mod ptr_extra;
pub mod map_extra;

pub mod prelude;
pub mod raw_ptr_extra;
pub mod seq_extra;
pub mod set_extra;
pub mod state_machine;
pub mod std_extra;
pub mod temporal_logic;
