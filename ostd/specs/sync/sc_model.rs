//! This module models the semantics for the SC fences and global SC views
//! coupled with relaxed accesses. It is based on the semantics of the C11
//! memory model but we exclude the SC access mode which is unnecessary.
//!
//! This is important to verifying some sync primitives like raw RCU.
use vstd::prelude::*;

verus! {


} // verus!
