use vstd::prelude::*;
use vstd::simple_pptr::*;

verus! {

pub tracked struct VmIoModel {
    pub ghost start: int,
    pub ghost end: int,
}

} // verus!
verus! {

impl VmIoModel {
    pub open spec fn range_valid(&self) -> bool {
        0 <= self.start <= self.end
    }

    pub open spec fn cursor_within_range(&self, cursor: usize) -> bool {
        self.start <= cursor <= self.end
    }

    pub open spec fn state_eq(&self, old_state: &Self) -> bool {
        self.start == old_state.start && self.end == old_state.end
    }
}

} // verus!
