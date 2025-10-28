use vstd::prelude::*;
use crate::spec::rcu::TreeSpec;

verus! {

pub type SpecInstance<C> = TreeSpec::Instance<C>;

pub type NodeToken<C> = TreeSpec::nodes<C>;

pub type PteArrayToken<C> = TreeSpec::pte_arrays<C>;

pub type CursorToken<C> = TreeSpec::cursors<C>;

pub type StrayToken<C> = TreeSpec::strays<C>;

pub type FreePaddrToken<C> = TreeSpec::free_paddrs<C>;

} // verus!
