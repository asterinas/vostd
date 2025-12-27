#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(unused_attributes)]
// #![feature(generic_const_exprs)]
#![feature(proc_macro_hygiene)]
#![feature(core_intrinsics)]

mod arch;
mod error;
mod mm;
mod task;

use arch::*;
use error::*;
use mm::*;
use task::*;

pub mod prelude;
