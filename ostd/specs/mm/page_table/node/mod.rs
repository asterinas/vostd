pub mod entry_owners;
pub mod owners;

use vstd::prelude::*;
use vstd_extra::typing::tagged::MaxSize;
use crate::specs::mm::frame::meta_owners::META_STORAGE_SIZE;
use vstd_extra::drop_tracking::*;

use crate::specs::mm::frame::meta_owners::MetaSlotStorage;

use crate::mm::{
    frame::Frame,
    page_table::{PageTableConfig, PageTableGuard, PageTablePageMeta},
};
use core::marker::PhantomData;
pub use entry_owners::*;
pub use owners::*;

verus! {

pub tracked struct Guards {
    /// The set of node addresses that are currently guarded (locked).
    pub ghost guards: Set<usize>,
}

impl Guards {
    pub open spec fn unlocked(self, addr: usize) -> bool {
        !self.guards.contains(addr)
    }

    pub open spec fn lock_held(self, addr: usize) -> bool {
        self.guards.contains(addr)
    }
}

impl<'rcu, C: PageTableConfig> TrackDrop for PageTableGuard<'rcu, C> {
    type State = Guards;

    /// The node address whose lock this guard holds. The token
    /// thus identifies *which* guard it tracks; `drop_requires`'s key
    /// match prevents a guard's obligation from being used to drop a
    /// different guard. The real lock-set ledger is `Guards::guards`;
    /// this trait's discipline lifts the existing state-side discipline
    /// onto the obligation token by carrying the locked address.
    type Obligation = DropObligation<usize>;

    open spec fn tracked_redeem_requires(self, s: Self::State) -> bool {
        s.lock_held(self.inner.inner@.ptr.addr())
    }

    open spec fn tracked_redeem_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        &&& s1.guards == s0.guards.remove(self.inner.inner@.ptr.addr())
        &&& obl.value() == self.inner.inner@.ptr.addr()
    }

    proof fn tracked_redeem(self, tracked s: &mut Self::State) -> (tracked obl: Self::Obligation) {
        s.guards = s.guards.remove(self.inner.inner@.ptr.addr());
        DropObligation::tracked_mint(self.inner.inner@.ptr.addr())
    }

    open spec fn drop_requires(self, s: Self::State, obl: Self::Obligation) -> bool {
        &&& s.unlocked(self.inner.inner@.ptr.addr())
        &&& obl.value() == self.inner.inner@.ptr.addr()
    }

    open spec fn drop_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        s1.guards == s0.guards.insert(self.inner.inner@.ptr.addr())
    }
}

pub uninterp spec fn drop_tree_spec<C: PageTableConfig>(
    _page: Frame<PageTablePageMeta<C>>,
) -> Frame<PageTablePageMeta<C>>;

impl<C: PageTableConfig> MaxSize<{ META_STORAGE_SIZE }> for PageTablePageMeta<C> {
    /// Axiomatized: a layout fact.
    #[verifier::external_body]
    proof fn size_correct() {
    }
}

} // verus!
