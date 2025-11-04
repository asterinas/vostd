// #![feature(generic_const_exprs)]
#![allow(unused)]
#![feature(slice_ptr_get)]
#![feature(core_intrinsics)]
#![allow(non_snake_case)]
#![feature(sync_unsafe_cell)]
#![allow(type_alias_bounds)]

extern crate alloc;

pub mod mm;
pub mod prelude;
pub mod spec;
pub mod task;
pub mod x86_64;
#[macro_use]
pub mod helpers;
pub mod sync;

pub mod configs;
