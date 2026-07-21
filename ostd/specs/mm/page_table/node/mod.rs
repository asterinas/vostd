pub mod entry_owners;
pub mod entry_view;
pub mod owners;

pub use entry_owners::*;
pub use entry_view::*;
pub use owners::*;

use core::marker::PhantomData;

use vstd::prelude::*;

use vstd_extra::{cast_ptr::Repr, drop_tracking::*};

use crate::specs::mm::frame::meta_owners::{MetaSlotStorage, StoredPageTablePageMeta};

use crate::mm::{
    frame::Frame,
    page_table::{PageTableConfig, PageTableGuard, PageTablePageMeta},
};

verus! {

pub tracked struct Guards<'rcu> {
    /// The set of node addresses that are currently guarded (locked).
    pub ghost guards: Set<usize>,
    pub _phantom: PhantomData<&'rcu ()>,
}

impl<'rcu> Guards<'rcu> {
    pub open spec fn locked(self, addr: usize) -> bool {
        self.guards.contains(addr)
    }

    pub open spec fn unlocked(self, addr: usize) -> bool {
        !self.guards.contains(addr)
    }

    pub open spec fn lock_held(self, addr: usize) -> bool {
        self.guards.contains(addr)
    }
}

impl<'rcu, C: PageTableConfig> TrackDrop for PageTableGuard<'rcu, C> {
    type State = Guards<'rcu>;

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

impl<C: PageTableConfig> PageTablePageMeta<C> {
    pub open spec fn into_spec(self) -> StoredPageTablePageMeta {
        StoredPageTablePageMeta {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into(self) -> (res: StoredPageTablePageMeta)
        ensures
            res == self.into_spec(),
    {
        StoredPageTablePageMeta {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }
}

impl StoredPageTablePageMeta {
    pub open spec fn into_spec<C: PageTableConfig>(self) -> PageTablePageMeta<C> {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into<C: PageTableConfig>(self) -> (res: PageTablePageMeta<C>)
        ensures
            res == self.into_spec::<C>(),
    {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }
}

pub uninterp spec fn drop_tree_spec<C: PageTableConfig>(
    _page: Frame<PageTablePageMeta<C>>,
) -> Frame<PageTablePageMeta<C>>;

impl<C: PageTableConfig> Repr<MetaSlotStorage> for PageTablePageMeta<C> {
    type Perm = ();

    open spec fn wf(r: MetaSlotStorage, perm: ()) -> bool {
        matches!(r, MetaSlotStorage::PTNode(_))
    }

    open spec fn to_repr_spec(self, perm: ()) -> (MetaSlotStorage, ()) {
        (MetaSlotStorage::PTNode(self.into_spec()), ())
    }

    #[verifier::external_body]
    fn to_repr(self, Tracked(perm): Tracked<&mut ()>) -> MetaSlotStorage {
        unimplemented!()
    }

    open spec fn from_repr_spec(r: MetaSlotStorage, perm: ()) -> Self {
        match r {
            MetaSlotStorage::PTNode(node) => node.into_spec::<C>(),
            _ => arbitrary(),
        }
    }

    #[verifier::external_body]
    fn from_repr(r: MetaSlotStorage, Tracked(perm): Tracked<&()>) -> Self {
        unimplemented!()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlotStorage, Tracked(perm): Tracked<&'a ()>) -> &'a Self {
        unimplemented!()
    }

    proof fn from_to_repr(self, perm: ()) {
    }

    proof fn to_from_repr(r: MetaSlotStorage, perm: ()) {
        match r {
            MetaSlotStorage::PTNode(node) => {},
            _ => {
                assert(false);
            },
        }
    }

    proof fn to_repr_wf(self, perm: ()) {
    }
}

} // verus!
