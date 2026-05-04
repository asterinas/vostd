//! Re-exports of upstream `vstd::resource` resource-algebra APIs.
//!
//! The old local PCM definitions were copied from pre-resource-module `vstd`.
//! Keep this module as an import path only; new definitions come from `vstd`.
pub use vstd::resource::agree;
pub use vstd::resource::algebra;
pub use vstd::resource::auth;
pub use vstd::resource::exclusive;
pub use vstd::resource::frac;
pub use vstd::resource::option;
pub use vstd::resource::pcm::*;
pub use vstd::resource::product;
pub use vstd::resource::relations;
pub use vstd::resource::sum;
