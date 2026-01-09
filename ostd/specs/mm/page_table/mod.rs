pub mod cursor;
pub mod node;
mod owners;
mod view;

pub use cursor::*;
pub use node::*;
pub use owners::*;
pub use view::*;

use vstd::prelude::*;

use crate::mm::page_table::PageTableConfig;

verus! {

/*impl<'rcu, C: PageTableConfig> PageTableOwner<'rcu, C> {
    pub open spec fn mappings_unique_spec(self) -> bool {
        forall |i: usize, j: usize |
            i != j ==> #[trigger] self@.mappings[i].pa != self@.mappings[j].pa
    }

}*/

}