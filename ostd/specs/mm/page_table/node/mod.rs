pub mod entry_owners;
pub mod owners;

use vstd::prelude::*;
use vstd_extra::typing::tagged::{ByteRepr, ByteSized};
use crate::specs::mm::frame::meta_owners::META_STORAGE_SIZE;
use vstd::std_specs::convert::{IntoSpecImpl, TryFromSpecImpl};
use vstd_extra::drop_tracking::*;

use crate::specs::mm::frame::meta_owners::{
    MetaSlotStorage, StoredPageTablePageMeta, axiom_pt_node_round_trip, pt_node_decode,
    pt_node_encode,
};

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
    pub fn into(self) -> StoredPageTablePageMeta
        returns
            self.into_spec(),
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
    pub fn into<C: PageTableConfig>(self) -> PageTablePageMeta<C>
        returns
            self.into_spec::<C>(),
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

// ---------------------------------------------------------------------------
// `PageTablePageMeta<C>` as a stored type in its own right
// ---------------------------------------------------------------------------
//
// `StoredPageTablePageMeta` demotes to an encoding detail, as `StoredLink` does
// for links: the slot's tag becomes `recorded_id::<PageTablePageMeta<C>>()`, which
// names the type a handle claims rather than its byte-shaped stand-in.

impl<C: PageTableConfig> TryFrom<[u8; META_STORAGE_SIZE]> for PageTablePageMeta<C> {
    type Error = ();

    #[verifier::external_body]
    fn try_from(b: [u8; META_STORAGE_SIZE]) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}

impl<C: PageTableConfig> TryFromSpecImpl<[u8; META_STORAGE_SIZE]> for PageTablePageMeta<C> {
    open spec fn obeys_try_from_spec() -> bool {
        true
    }

    open spec fn try_from_spec(b: [u8; META_STORAGE_SIZE]) -> Result<Self, Self::Error> {
        match pt_node_decode(b) {
            Ok(node) => Ok(node.into_spec::<C>()),
            Err(_) => Err(()),
        }
    }
}

#[allow(clippy::from_over_into)]
impl<C: PageTableConfig> Into<[u8; META_STORAGE_SIZE]> for PageTablePageMeta<C> {
    #[verifier::external_body]
    fn into(self) -> [u8; META_STORAGE_SIZE] {
        unimplemented!()
    }
}

impl<C: PageTableConfig> IntoSpecImpl<[u8; META_STORAGE_SIZE]> for PageTablePageMeta<C> {
    open spec fn obeys_into_spec() -> bool {
        true
    }

    open spec fn into_spec(self) -> [u8; META_STORAGE_SIZE] {
        pt_node_encode(PageTablePageMeta::<C>::into_spec(self))
    }
}

impl<C: PageTableConfig> ByteSized<{ META_STORAGE_SIZE }> for PageTablePageMeta<C> {
    /// Axiomatized: a layout fact.
    #[verifier::external_body]
    proof fn size_correct() {
    }
}

impl<C: PageTableConfig> ByteRepr<{ META_STORAGE_SIZE }> for PageTablePageMeta<C> {
    /// The byte round trip is the axiom, and the `Stored` <-> live identity
    /// unfolds, both `into_spec`s being `open`.
    proof fn round_trip(self) {
        broadcast use axiom_pt_node_round_trip;
    }

    proof fn obeys() {
    }
}

} // verus!
