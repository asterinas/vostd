pub mod entry_owners;
pub mod entry_view;
pub mod owners;

pub use entry_owners::*;
pub use entry_view::*;
pub use owners::*;

use core::marker::PhantomData;
use vstd::prelude::*;
use vstd::simple_pptr::*;

use vstd_extra::cast_ptr::Repr;
use vstd_extra::drop_tracking::*;

use crate::mm::frame::Frame;
use crate::mm::page_table::{PageTableConfig, PageTableGuard, PageTablePageMeta};
use crate::specs::mm::frame::meta_owners::{MetaSlotStorage, StoredPageTablePageMeta};

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

    pub proof fn take(tracked &mut self, addr: usize) -> (tracked guard: GuardPerm<'rcu, C>)
        requires
            old(self).locked(addr),
            old(self).guards[addr] is Some,
        ensures
            self.lock_held(addr),
            guard == old(self).guards[addr].unwrap(),
    {
        let tracked guard = self.guards.tracked_remove(addr).tracked_unwrap();
        self.guards.tracked_insert(addr, None);
        guard
    }

    pub proof fn put(tracked &mut self, addr: usize, tracked guard: GuardPerm<'rcu, C>)
        requires
            old(self).lock_held(addr),
        ensures
            self.locked(addr),
            self.guards[addr] == Some(guard),
    {
        let _ = self.guards.tracked_remove(addr);
        self.guards.tracked_insert(addr, Some(guard));
    }
}

impl<'rcu, C: PageTableConfig> TrackDrop for PageTableGuard<'rcu, C> {
    type State = Guards<'rcu, C>;

    open spec fn constructor_requires(self, s: Self::State) -> bool {
        s.lock_held(self.inner.inner@.ptr.addr())
    }

    open spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        s1.guards == s0.guards.remove(self.inner.inner@.ptr.addr())
    }

    proof fn constructor_spec(self, tracked s: &mut Self::State)
    {
        s.guards.tracked_remove(self.inner.inner@.ptr.addr());
    }

    open spec fn drop_requires(self, s: Self::State) -> bool {
        s.unlocked(self.inner.inner@.ptr.addr())
    }

    open spec fn drop_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        s1.guards == s0.guards.insert(self.inner.inner@.ptr.addr(), None)
    }

    proof fn drop_spec(self, tracked s: &mut Self::State)
    {
        s.guards.tracked_insert(self.inner.inner@.ptr.addr(), None);
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

pub uninterp spec fn drop_tree_spec<C: PageTableConfig>(_page: Frame<PageTablePageMeta<C>>) -> Frame<PageTablePageMeta<C>>;

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
        assert(self.to_repr_spec(perm) == (MetaSlotStorage::PTNode(self.into_spec()), ()));
        assert(StoredPageTablePageMeta::into_spec::<C>(self.into_spec()) == self);
    }

    proof fn to_from_repr(r: MetaSlotStorage, perm: ()) {
        match r {
            MetaSlotStorage::PTNode(node) => {
                assert(Self::from_repr_spec(r, perm) == node.into_spec::<C>());
                assert(Self::from_repr_spec(r, perm).to_repr_spec(perm) == (MetaSlotStorage::PTNode(node), ()));
            },
            _ => {
                assert(false);
            },
        }
    }

    proof fn to_repr_wf(self, perm: ()) {
        assert(self.to_repr_spec(perm).0 is PTNode);
    }
}

} // verus!
