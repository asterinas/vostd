use vstd::prelude::*;

use vstd_extra::ownership::*;
use vstd_extra::prelude::TreePath;

use aster_common::prelude::*;
use aster_common::prelude::page_table::*;

verus!{
impl CursorModel {

    #[rustc_allow_incoherent_impl]
    pub open spec fn push_level_spec(self) -> Self {
        Self {
            path: self.path.push_tail(0 as usize),
            ..self
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn pop_level_spec(self) -> Self {
        let (tail, popped) = self.path.pop_tail();
        Self {
            path: popped,
            ..self
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn inc_pop_aligned_rec(path: TreePath<CONST_NR_ENTRIES>) -> TreePath<CONST_NR_ENTRIES>
        decreases path.len(),
    {
        if path.len() == 0 {
            path
        } else {
            let n = path.len();
            let val = path.0[n - 1];
            let new_path = path.0.update(n - 1, (val + 1) as usize);

            if new_path[n - 1] % NR_ENTRIES() == 0 {
                let (tail, popped) = path.pop_tail();
                Self::inc_pop_aligned_rec(popped)
            } else {
                path
            }
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn move_forward_spec(self) -> Self {
        Self {
            path: Self::inc_pop_aligned_rec(self.path),
            ..self
        }
    }
}
}