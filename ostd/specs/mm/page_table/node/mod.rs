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
    pub guards: Map<usize, Option<GuardPerm<'rcu, C>>>,
}

impl<'rcu, C: PageTableConfig> Guards<'rcu, C> {
    pub open spec fn locked(self, addr: usize) -> bool {
        self.guards.contains_key(addr)
    }

    pub open spec fn unlocked(self, addr: usize) -> bool {
        !self.guards.contains_key(addr)
    }

    pub open spec fn lock_held(self, addr: usize) -> bool {
        self.guards.contains_key(addr) && self.guards[addr] is None
    }

    pub proof fn take(tracked &mut self, addr: usize) -> (tracked guard: Tracked<GuardPerm<'rcu, C>>)
        requires
            old(self).locked(addr),
            old(self).guards[addr] is Some,
        ensures
            self.lock_held(addr),
            guard == old(self).guards[addr].unwrap(),
    {
        let tracked guard = self.guards.tracked_remove(addr).tracked_unwrap();
        self.guards.tracked_insert(addr, None);
        Tracked(guard)
    }

    pub proof fn put(tracked &mut self, addr: usize, tracked guard: Tracked<GuardPerm<'rcu, C>>)
        requires
            old(self).lock_held(addr),
        ensures
            self.locked(addr),
            self.guards[addr] == Some(guard@),
    {
        let _ = self.guards.tracked_remove(addr);
        self.guards.tracked_insert(addr, Some(guard.get()));
    }
}

} // verus!