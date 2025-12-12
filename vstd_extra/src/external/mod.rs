// Specifications for external functions and traits

pub mod deref;
pub mod manually_drop;
pub mod nonnull;

pub use deref::*;
pub use manually_drop::*;
pub use nonnull::*;