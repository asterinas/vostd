use builtin::*;
use builtin_macros::*;

use crate::spec::rw::*;

verus! {

pub type SpecInstance = TreeSpec::Instance;

pub type NodeToken = TreeSpec::nodes;

pub type RcToken = TreeSpec::reader_counts;

pub type CursorToken = TreeSpec::cursors;

} // verus!
