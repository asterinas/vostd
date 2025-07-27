use vstd::prelude::*;
use crate::spec::rcu::*;

verus! {

pub type SpecInstance = TreeSpec::Instance;

pub type NodeToken = TreeSpec::nodes;

pub type PteToken = TreeSpec::ptes;

pub type CursorToken = TreeSpec::cursors;

} // verus!
