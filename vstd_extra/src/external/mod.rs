// Specifications for external functions and traits
pub mod deref;
pub mod ilog2;
pub mod manually_drop;
pub mod nonnull;
pub mod smart_ptr;

pub use deref::*;
pub use ilog2::*;
pub use manually_drop::*;
pub use nonnull::*;
pub use smart_ptr::*;

use vstd::prelude::*;

verus! {

pub assume_specification[ core::hint::spin_loop ]()
    opens_invariants none
    no_unwind
;

} // verus!
