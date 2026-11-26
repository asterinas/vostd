//! Specifications for functions from Rust standard library but not specified in `vstd`.
//!
//! These specifications are determined with careful inspection of the std library source code and documentation, and trusted as TCB.
//! They are subject to change if `vstd` covers more cases in the future.
pub mod acpi;
mod bitvec;
pub mod bytemuck;
pub mod cmp;
pub mod convert;
pub mod fmt;
pub mod ilog2;
pub mod int_specs;
#[cfg(target_arch = "x86_64")]
pub mod io_port;
pub mod iter;
pub mod nonnull;
pub mod ptr;
pub mod range;
pub mod slice;
pub mod smallvec;
pub mod smart_ptr;
pub mod str;
pub mod time;
pub mod vec;
#[cfg(target_arch = "x86_64")]
pub mod x86;
#[cfg(target_arch = "x86_64")]
mod x86_64;
pub mod xmas_elf;

pub use acpi::*;
pub use bitvec::*;
pub use cmp::*;
pub use ilog2::*;
pub use int_specs::*;
#[cfg(target_arch = "x86_64")]
pub use io_port::*;
pub use iter::*;
pub use nonnull::*;
pub use ptr::*;
pub use range::*;
pub use slice::*;
pub use smallvec::*;
pub use smart_ptr::*;
pub use str::*;
pub use time::*;
pub use vec::*;
#[cfg(target_arch = "x86_64")]
pub use x86::*;
#[cfg(target_arch = "x86_64")]
pub use x86_64::*;

use vstd::{
    layout::{align_of, size_of, spec_size_of_val},
    prelude::*,
};

verus! {

pub assume_specification[ core::hint::spin_loop ]()
    opens_invariants none
    no_unwind
;

/// For any `Sized` type, `core::mem::size_of_val` equals `size_of::<V>()`.
///
/// Ref: Rust `core::mem::size_of_val` documentation.
pub broadcast axiom fn axiom_size_of_val_sized<V: Sized>(val: &V)
    ensures
        #[trigger] spec_size_of_val::<V>(val) == size_of::<V>(),
;

/// For any array `[T; N]`, `size_of::<[T; N]>() == N * size_of::<T>()` and
/// `align_of::<[T; N]>() == align_of::<T>()`.
///
/// Ref: The Rust Reference, Type Layout (Array Layout).
pub broadcast axiom fn axiom_layout_of_array<T, const N: usize>()
    ensures
        #![trigger size_of::<[T; N]>()]
        #![trigger align_of::<[T; N]>()]
        size_of::<[T; N]>() == N * size_of::<T>(),
        align_of::<[T; N]>() == align_of::<T>(),
;

} // verus!
