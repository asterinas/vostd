pub mod entry_owners;
pub mod entry_view;
pub mod owners;
pub mod page_table_node_specs;

pub use entry_owners::*;
pub use entry_view::*;
pub use owners::*;
pub use page_table_node_specs::*;

use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::mm::page_table::{PageTableConfig, PageTableGuard};

verus! {

pub type GuardPerm<'rcu, C: PageTableConfig> = PointsTo<PageTableGuard<'rcu, C>>;

pub tracked struct Guards<'rcu, C: PageTableConfig> {
    pub guards: Map<usize, Tracked<GuardPerm<'rcu, C>>>,
}

} // verus!