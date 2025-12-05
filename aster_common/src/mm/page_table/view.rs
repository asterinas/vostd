use vstd::prelude::*;

use vstd_extra::ownership::*;

use std::marker::PhantomData;

use super::*;

verus! {

pub tracked struct Mapping {
    pub pa: usize,
    pub is_locked: bool,
    pub page_size:
        usize,/*  TODO: below are some "payload" fields that do not directly impact verification of the page table,
            but which will be important for the long-term goal of merging verification targets into a single,
            end-to-end verified system. We omit these for now.
        pub flags: PageFlags,
        pub privilege: PrivilegedPageFlags,
        pub cache: CachePolicy, */
}

impl Mapping {
    pub open spec fn inv(self) -> bool {
        &&& set![4096, 2097152, 1073741824].contains(self.page_size)
        &&& self.pa % self.page_size == 0
    }
}

pub type PageTableFlatView = Map<usize, Option<Mapping>>;

} // verus!
