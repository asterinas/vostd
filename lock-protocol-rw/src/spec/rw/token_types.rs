use vstd::prelude::*;
use crate::spec::rw::TreeSpec;

verus! {

pub type SpecInstance<C> = TreeSpec::Instance<C>;

pub type NodeToken<C> = TreeSpec::nodes<C>;

pub type PteArrayToken<C> = TreeSpec::pte_arrays<C>;

pub type RcToken<C> = TreeSpec::reader_counts<C>;

pub type CursorToken<C> = TreeSpec::cursors<C>;

} // verus!
