use vstd::prelude::*;
use crate::spec::rcu::*;

verus! {

pub type SpecInstance = TreeSpec::Instance;

pub type NodeToken = TreeSpec::nodes;

pub type PteArrayToken = TreeSpec::pte_arrays;

pub type CursorToken = TreeSpec::cursors;

pub type StrayToken = TreeSpec::strays;

pub type FreePaddrToken = TreeSpec::free_paddrs;

} // verus!
