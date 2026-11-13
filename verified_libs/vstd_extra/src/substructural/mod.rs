//! Tools for reasoning about substructural types (structs, arrays, cells, eventually maybe unions)
//! This library is for when we need to reason about the underlying structure of these objects.
//! For example, consider the type:
//!
//! ```
//! struct Foo<A> {
//!     a: PCell<[A, 10]>,
//! }
//! ```
//!
//! Suppose we have a pointer of type `*const Foo`. Assuming a C-style layout,
//! that pointer's address points to:
//! 0. a `Foo`
//! 1. the first field of the struct, which is a cell of type `PCell<[A, 10]>
//! 2. the array of `A`s inside the cell
//! 3. the first `A` in the array
//!
//! When is it sound to cast a `*const Foo` to a `*const A`?
//! And when is it sound to use that new pointer?
//! We can answer these questions pairwise for each step in the chain.
//!
//! Step 1: struct-to-field is layout dependent. If the struct has the `#[layout(C)]` attribute,
//! it is always sound to make this cast for the first field of the struct (C99 and later).
//! It is tempting to try adding an offset to the base pointer to find other fields, but this is
//! not sound without detailed knowledge of the compiler.
//!
//! Step 2: cell to contents is modeled by VerusBelt, and we reproduce their approach here.
//!
//! Step 3: array to contents -- see `array_ptr.rs`.
//!
//! Step 1 is [`struct_field`], step 2 is [`cell`]; they compose, and a caller
//! that needs the whole chain uses both.
pub mod cell;

pub mod struct_field;
