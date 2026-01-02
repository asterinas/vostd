#![allow(unused_imports)]

pub mod cpu;
pub mod kspace;
pub mod mm;
pub mod page_table_entry;
pub mod page_table_flags;
pub mod paging_consts;

use vstd::prelude::*;

use super::*;

pub use cpu::*;
pub use kspace::*;
pub use mm::*;
pub use page_table_entry::*;
pub use page_table_flags::*;
pub use paging_consts::*;

verus! {

global size_of usize == 8;

global size_of isize == 8;

} // verus!
