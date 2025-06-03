use builtin::*;
use builtin_macros::*;

use crate::spec::tree::*;

verus! {

pub type SpecInstance = TreeSpec::Instance;

pub type NodeToken = TreeSpec::nodes;

pub type RcToken = TreeSpec::reader_counts;

pub type CursorToken = TreeSpec::cursors;

} // verus!
