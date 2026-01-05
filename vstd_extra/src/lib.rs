#![allow(non_snake_case)]
#![feature(sized_hierarchy)]
#![feature(proc_macro_hygiene)]

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
pub mod undroppable;
pub mod virtual_ptr;

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
