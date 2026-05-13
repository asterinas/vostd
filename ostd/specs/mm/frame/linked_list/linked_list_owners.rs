use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::simple_pptr::*;

use vstd::std_specs::convert::{FromSpec, FromSpecImpl};
use vstd_extra::cast_ptr::{Repr, ReprPtr};
use vstd_extra::ownership::*;

use core::marker::PhantomData;

use super::*;
use crate::mm::frame::{AnyFrameMeta, CursorMut, Link, LinkedList, MetaSlot};
use crate::mm::Paddr;
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::MAX_NR_PAGES;
use crate::specs::mm::frame::mapping::META_SLOT_SIZE;
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::unique::UniqueFrameOwner;

verus! {

pub struct MetaSlotSmall;

/// Representation of a link as stored in the metadata slot.
pub struct StoredLink {
    pub next: Option<Paddr>,
    pub prev: Option<Paddr>,
    pub slot: MetaSlotSmall,
}

pub tracked struct LinkInnerPerms<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub storage: <M as Repr<MetaSlotSmall>>::Perm,
    pub ghost next_ptr: Option<PPtr<MetaSlot>>,
    pub ghost prev_ptr: Option<PPtr<MetaSlot>>,
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Repr<MetaSlotStorage> for Link<M> {
    type Perm = LinkInnerPerms<M>;

    open spec fn wf(r: MetaSlotStorage, perm: LinkInnerPerms<M>) -> bool {
        match r {
            MetaSlotStorage::FrameLink(link) => {
                &&& M::wf(link.slot, perm.storage)
                &&& (link.next is Some) == (perm.next_ptr is Some)
                &&& (link.prev is Some) == (perm.prev_ptr is Some)
                &&& link.next is Some ==> link.next->0 == perm.next_ptr->0.addr()
                &&& link.prev is Some ==> link.prev->0 == perm.prev_ptr->0.addr()
            },
            _ => false,
        }
    }

    open spec fn to_repr_spec(self, perm: LinkInnerPerms<M>) -> (MetaSlotStorage, LinkInnerPerms<M>) {
        let (slot, storage) = self.meta.to_repr_spec(perm.storage);
        (
            MetaSlotStorage::FrameLink(StoredLink {
                next: match self.next {
                    Some(ptr) => Some(ptr.ptr.addr()),
                    None => None,
                },
                prev: match self.prev {
                    Some(ptr) => Some(ptr.ptr.addr()),
                    None => None,
                },
                slot,
            }),
            LinkInnerPerms {
                storage,
                next_ptr: match self.next {
                    Some(ptr) => Some(ptr.ptr),
                    None => None,
                },
                prev_ptr: match self.prev {
                    Some(ptr) => Some(ptr.ptr),
                    None => None,
                },
            },
        )
    }

    #[verifier::external_body]
    fn to_repr(self, Tracked(perm): Tracked<&mut LinkInnerPerms<M>>) -> MetaSlotStorage {
        unimplemented!()
    }

    open spec fn from_repr_spec(r: MetaSlotStorage, perm: LinkInnerPerms<M>) -> Self {
        match r {
            MetaSlotStorage::FrameLink(link) => Link {
                next: match link.next {
                    Some(addr) => Some(ReprPtr {
                        ptr: perm.next_ptr.unwrap(),
                        _T: PhantomData,
                    }),
                    None => None,
                },
                prev: match link.prev {
                    Some(addr) => Some(ReprPtr {
                        ptr: perm.prev_ptr.unwrap(),
                        _T: PhantomData,
                    }),
                    None => None,
                },
                meta: M::from_repr_spec(link.slot, perm.storage),
            },
            _ => Link {
                next: None,
                prev: None,
                meta: M::from_repr_spec(MetaSlotSmall, perm.storage),
            },
        }
    }

    #[verifier::external_body]
    fn from_repr(r: MetaSlotStorage, Tracked(perm): Tracked<&LinkInnerPerms<M>>) -> Self {
        unimplemented!()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlotStorage, Tracked(perm): Tracked<&'a LinkInnerPerms<M>>) -> &'a Self {
        unimplemented!()
    }

    proof fn from_to_repr(self, perm: LinkInnerPerms<M>) {
        <M as Repr<MetaSlotSmall>>::from_to_repr(self.meta, perm.storage);
    }

    proof fn to_from_repr(r: MetaSlotStorage, perm: LinkInnerPerms<M>) {
        match r {
            MetaSlotStorage::FrameLink(link) => {
                M::to_from_repr(link.slot, perm.storage);
            },
            _ => {
                assert(false);
            },
        }
    }

    proof fn to_repr_wf(self, perm: LinkInnerPerms<M>) {
        <M as Repr<MetaSlotSmall>>::to_repr_wf(self.meta, perm.storage);
    }
}

pub ghost struct LinkModel {
    pub paddr: Paddr,
}

impl Inv for LinkModel {
    open spec fn inv(self) -> bool {
        true
    }
}

pub tracked struct LinkOwner {
    pub paddr: Paddr,
    pub in_list: u64,
}

impl Inv for LinkOwner {
    open spec fn inv(self) -> bool {
        true
    }
}

impl View for LinkOwner {
    type V = LinkModel;

    open spec fn view(&self) -> Self::V {
        LinkModel { paddr: self.paddr }
    }
}

impl InvView for LinkOwner {
    proof fn view_preserves_inv(self) {
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> OwnerOf for Link<M> {
    type Owner = LinkOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        true
        //        &&& owner.self_perm@.mem_contents().value() == self
        //        &&& owner.next == self.next
        //        &&& owner.prev == self.prev

    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> ModelOf for Link<M> {

}

pub ghost struct LinkedListModel {
    pub list: Seq<LinkModel>,
}

impl LinkedListModel {
    pub open spec fn front(self) -> Option<LinkModel> {
        if self.list.len() > 0 {
            Some(self.list[0])
        } else {
            None
        }
    }

    pub open spec fn back(self) -> Option<LinkModel> {
        if self.list.len() > 0 {
            Some(self.list[self.list.len() - 1])
        } else {
            None
        }
    }
}

impl Inv for LinkedListModel {
    open spec fn inv(self) -> bool {
        true
    }
}

pub tracked struct LinkedListOwner<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub list: Seq<LinkOwner>,
    pub perms: Map<int, vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<Link<M>>>>,
    pub list_id: u64,
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Inv for LinkedListOwner<M> {
    open spec fn inv(self) -> bool {
        forall|i: int| 0 <= i < self.list.len() ==> self.inv_at(i)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedListOwner<M> {
    pub open spec fn inv_at(self, i: int) -> bool {
        &&& self.perms.contains_key(i)
        &&& self.perms[i].addr() == self.list[i].paddr
        &&& self.perms[i].points_to.addr() == self.list[i].paddr
        &&& self.perms[i].wf(&self.perms[i].inner_perms)
        &&& self.perms[i].addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= self.perms[i].addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
        &&& self.perms[i].is_init()
        &&& self.perms[i].value().metadata.wf(self.list[i])
        &&& i == 0 <==> self.perms[i].value().metadata.prev is None
        &&& i == self.list.len() - 1 <==> self.perms[i].value().metadata.next is None
        &&& 0 < i ==> {
            &&& self.perms[i].value().metadata.prev is Some
            &&& self.perms[i].value().metadata.prev.unwrap().addr() == self.perms[i - 1].addr()
            &&& self.perms[i].value().metadata.prev.unwrap().ptr == self.perms[i - 1].points_to.pptr()
        }
        &&& i < self.list.len() - 1 ==> {
            &&& self.perms[i].value().metadata.next is Some
            &&& self.perms[i].value().metadata.next.unwrap().addr() == self.perms[i + 1].addr()
            &&& self.perms[i].value().metadata.next.unwrap().ptr == self.perms[i + 1].points_to.pptr()
        }
        &&& self.list[i].inv()
        &&& self.list[i].in_list == self.list_id
    }

    pub open spec fn view_helper(owners: Seq<LinkOwner>) -> Seq<LinkModel>
        decreases owners.len(),
    {
        if owners.len() == 0 {
            Seq::<LinkModel>::empty()
        } else {
            seq![owners[0].view()].add(Self::view_helper(owners.remove(0)))
        }
    }

    pub proof fn view_preserves_len(owners: Seq<LinkOwner>)
        ensures
            Self::view_helper(owners).len() == owners.len(),
        decreases owners.len(),
    {
        if owners.len() == 0 {
        } else {
            Self::view_preserves_len(owners.remove(0))
        }
    }

    /// Proves that view_helper preserves indexing: view_helper(s)[i] == s[i].view()
    pub proof fn view_helper_index(owners: Seq<LinkOwner>, i: int)
        requires
            0 <= i < owners.len(),
        ensures
            Self::view_helper(owners)[i] == owners[i].view(),
        decreases owners.len(),
    {
        Self::view_preserves_len(owners);
        if i > 0 {
            Self::view_helper_index(owners.remove(0), i - 1);
        }
    }

    /// Proves that view_helper commutes with remove:
    /// view_helper(s.remove(i)) =~= view_helper(s).remove(i)
    pub proof fn view_helper_remove(owners: Seq<LinkOwner>, i: int)
        requires
            0 <= i < owners.len(),
        ensures
            Self::view_helper(owners.remove(i)) =~= Self::view_helper(owners).remove(i),
    {
        Self::view_preserves_len(owners);
        Self::view_preserves_len(owners.remove(i));
        assert forall |j: int| 0 <= j < Self::view_helper(owners.remove(i)).len() implies
            Self::view_helper(owners.remove(i))[j] == Self::view_helper(owners).remove(i)[j]
        by {
            Self::view_helper_index(owners.remove(i), j);
            if j < i {
                Self::view_helper_index(owners, j);
            } else {
                Self::view_helper_index(owners, j + 1);
            }
        };
    }

    /// Proves that view_helper commutes with insert:
    /// view_helper(s.insert(i, v)) =~= view_helper(s).insert(i, v.view())
    pub proof fn view_helper_insert(owners: Seq<LinkOwner>, i: int, v: LinkOwner)
        requires
            0 <= i <= owners.len(),
        ensures
            Self::view_helper(owners.insert(i, v)) =~= Self::view_helper(owners).insert(i, v.view()),
    {
        Self::view_preserves_len(owners);
        Self::view_preserves_len(owners.insert(i, v));
        assert forall |j: int| 0 <= j < Self::view_helper(owners.insert(i, v)).len() implies
            #[trigger] Self::view_helper(owners.insert(i, v))[j] == Self::view_helper(owners).insert(i, v.view())[j]
        by {
            Self::view_helper_index(owners.insert(i, v), j);
            if j < i {
                Self::view_helper_index(owners, j);
            } else if j == i {
                // owners.insert(i, v)[i] == v, and view_helper(owners).insert(i, v@)[i] == v@
            } else {
                Self::view_helper_index(owners, j - 1);
            }
        };
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> View for LinkedListOwner<M> {
    type V = LinkedListModel;

    open spec fn view(&self) -> Self::V {
        LinkedListModel { list: Self::view_helper(self.list) }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> InvView for LinkedListOwner<M> {
    proof fn view_preserves_inv(self) {
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedListOwner<M> {
    /// Take ownership of `*owner` by swapping it with a fresh empty
    /// `LinkedListOwner`. The resulting "leftover" `*owner` has an empty
    /// `list` and `perms`, so its `inv()` holds vacuously and it claims no
    /// external permissions. Used by drop-style call sites that need to feed
    /// an owned `LinkedListOwner` to a downstream API while themselves only
    /// having a `&mut` to it.
    #[verifier::external_body]
    pub proof fn tracked_take(tracked owner: &mut Self) -> (tracked res: Self)
        ensures
            res == *old(owner),
            final(owner).list =~= Seq::<LinkOwner>::empty(),
            final(owner).perms =~= Map::<int, vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<Link<M>>>>::empty(),
            final(owner).inv(),
    {
        unimplemented!()
    }

    /// Discard a logically-empty `LinkedListOwner`. Sound because such an
    /// owner has an empty `perms` map (no external tracked permissions) and
    /// an empty `list`, so consuming it leaks nothing.
    #[verifier::external_body]
    pub proof fn tracked_destroy_empty(tracked self)
        requires
            self.list =~= Seq::<LinkOwner>::empty(),
            self.perms =~= Map::<int, vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<Link<M>>>>::empty(),
    {
        unimplemented!()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> OwnerOf for LinkedList<M> {
    type Owner = LinkedListOwner<M>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.front is None <==> owner.list.len() == 0
        &&& self.back is None <==> owner.list.len() == 0
        &&& owner.list.len() > 0 ==> self.front is Some && self.front.unwrap().addr()
            == owner.list[0].paddr && owner.perms[0].pptr().addr() == self.front.unwrap().addr()
            && self.front.unwrap().ptr == owner.perms[0].points_to.pptr()
            && self.back is Some && self.back.unwrap().addr() == owner.list[owner.list.len()
            - 1].paddr && owner.perms[owner.list.len() - 1].pptr().addr() == self.back.unwrap().addr()
            && self.back.unwrap().ptr == owner.perms[owner.list.len() - 1].points_to.pptr()
        &&& self.size == owner.list.len()
        &&& self.list_id == owner.list_id
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> ModelOf for LinkedList<M> {

}

pub ghost struct CursorModel {
    pub ghost fore: Seq<LinkModel>,
    pub ghost rear: Seq<LinkModel>,
    pub ghost list_model: LinkedListModel,
}

impl Inv for CursorModel {
    open spec fn inv(self) -> bool {
        self.list_model.inv()
    }
}

pub tracked struct CursorOwner<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub list_own: LinkedListOwner<M>,
    pub index: int,
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Inv for CursorOwner<M> {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.index <= self.length()
        &&& self.list_own.inv()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> View for CursorOwner<M> {
    type V = CursorModel;

    open spec fn view(&self) -> Self::V {
        let list = self.list_own.view();
        CursorModel {
            fore: list.list.take(self.index),
            rear: list.list.skip(self.index),
            list_model: list,
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> InvView for CursorOwner<M> {
    proof fn view_preserves_inv(self) {
    }
}

impl<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>> OwnerOf for CursorMut<'a, M> {
    type Owner = CursorOwner<M>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& 0 <= owner.index < owner.length() ==> self.current.is_some()
            && self.current.unwrap().addr() == owner.list_own.list[owner.index].paddr
            && owner.list_own.perms[owner.index].pptr().addr() == self.current.unwrap().addr()
            && self.current.unwrap().ptr == owner.list_own.perms[owner.index].points_to.pptr()
        &&& owner.index == owner.list_own.list.len() ==> self.current.is_none()
        &&& (*self.list).wf(owner.list_own)
    }
}

impl<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>> ModelOf for CursorMut<'a, M> {

}

impl CursorModel {
    pub open spec fn current(self) -> Option<LinkModel> {
        if self.rear.len() > 0 {
            Some(self.rear[0])
        } else {
            None
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> CursorOwner<M> {
    pub open spec fn length(self) -> int {
        self.list_own.list.len() as int
    }

    pub open spec fn current(self) -> Option<LinkOwner> {
        if 0 <= self.index < self.length() {
            Some(self.list_own.list[self.index])
        } else {
            None
        }
    }

    pub axiom fn list_insert(
        tracked cursor: &mut Self,
        tracked link: &mut LinkOwner,
        tracked perm: &vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<Link<M>>>,
    )
        ensures
            final(link).paddr == old(link).paddr,
            final(link).in_list == final(cursor).list_own.list_id,
            final(cursor).list_own.list == old(cursor).list_own.list.insert(old(cursor).index, *final(link)),
            final(cursor).list_own.list_id == old(cursor).list_own.list_id,
            forall|idx: int| 0 <= idx < final(cursor).length() ==> final(cursor).list_own.perms.contains_key(idx),
            forall|idx: int|
                0 <= idx < final(cursor).index ==> final(cursor).list_own.perms[idx] == old(
                    cursor,
                ).list_own.perms[idx],
            forall|idx: int|
                old(cursor).index < idx <= old(cursor).length() ==> final(cursor).list_own.perms[idx]
                    == old(cursor).list_own.perms[idx - 1],
            final(cursor).list_own.perms[old(cursor).index] == perm,
            final(cursor).index == old(cursor).index + 1;

    pub open spec fn front_owner_spec(
        list_own: LinkedListOwner<M>,
    ) -> Self {
        CursorOwner::<M> { list_own: list_own, index: 0 }
    }

    pub open spec fn cursor_mut_at_owner_spec(
        list_own: LinkedListOwner<M>,
        index: int,
    ) -> Self {
        CursorOwner::<M> { list_own: list_own, index: index }
    }

    #[verifier::returns(proof)]
    pub axiom fn cursor_mut_at_owner(list_own: LinkedListOwner<M>, index: int) -> Self
        returns Self::cursor_mut_at_owner_spec(list_own, index);

    #[verifier::returns(proof)]
    pub axiom fn front_owner(
        list_own: LinkedListOwner<M>,
    ) -> (res: Self)
        ensures
            res == Self::front_owner_spec(list_own);
    pub open spec fn back_owner_spec(
        list_own: LinkedListOwner<M>,
    ) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            index: if list_own.list.len() > 0 {
                list_own.list.len() as int - 1
            } else {
                0
            },
        }
    }

    #[verifier::returns(proof)]
    #[verifier::external_body]
    pub proof fn back_owner(
        list_own: LinkedListOwner<M>,
    ) -> (res: Self)
        ensures
            res == Self::back_owner_spec(list_own),
    {
        CursorOwner::<M> {
            list_own: list_own,
            index: if list_own.list.len() > 0 {
                list_own.list.len() as int - 1
            } else {
                0
            },
        }
    }

    pub open spec fn ghost_owner_spec(
        list_own: LinkedListOwner<M>,
    ) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            index: list_own.list.len() as int,
        }
    }

    #[verifier::returns(proof)]
    #[verifier::external_body]
    pub proof fn ghost_owner(
        list_own: LinkedListOwner<M>,
    ) -> (res: Self)
        ensures
            res == Self::ghost_owner_spec(list_own),
    {
        CursorOwner::<M> {
            list_own: list_own,
            index: list_own.list.len() as int,
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> UniqueFrameOwner<Link<M>> {
    pub open spec fn frame_link_inv(&self) -> bool {
        &&& self.meta_perm.value().metadata.prev is None
        &&& self.meta_perm.value().metadata.next is None
        &&& self.meta_own.paddr == self.meta_perm.addr()
    }
}

pub struct MetadataAsLink<M: AnyFrameMeta> {
    pub metadata: M,
    pub next: Option<PPtr<MetaSlot>>,
    pub prev: Option<PPtr<MetaSlot>>,
    pub ref_count: u64,
    pub vtable_ptr: MemContents<usize>,
    pub in_list: u64,
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Repr<MetaSlot> for MetadataAsLink<M> {
    type Perm = MetadataInnerPerms;

    open spec fn wf(r: MetaSlot, perm: MetadataInnerPerms) -> bool {
        &&& <Metadata<Link<M>> as Repr<MetaSlot>>::wf(r, perm)
    }

    open spec fn to_repr_spec(self, perm: MetadataInnerPerms) -> (MetaSlot, MetadataInnerPerms) {
        <Metadata<Link<M>> as Repr<MetaSlot>>::to_repr_spec(
            <Metadata<Link<M>> as FromSpec<MetadataAsLink<M>>>::from_spec(self),
            perm,
        )
    }
    #[verifier::external_body]
    fn to_repr(self, Tracked(perm): Tracked<&mut MetadataInnerPerms>) -> MetaSlot {
        unimplemented!()
    }

    open spec fn from_repr_spec(r: MetaSlot, perm: MetadataInnerPerms) -> Self {
        <MetadataAsLink<M> as FromSpec<Metadata<Link<M>>>>::from_spec(
            <Metadata<Link<M>> as Repr<MetaSlot>>::from_repr_spec(r, perm),
        )
    }

    #[verifier::external_body]
    fn from_repr(r: MetaSlot, Tracked(perm): Tracked<&MetadataInnerPerms>) -> Self {
        unimplemented!()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlot, Tracked(perm): Tracked<&'a MetadataInnerPerms>) -> &'a Self {
        unimplemented!()
    }

    proof fn from_to_repr(self, perm: MetadataInnerPerms) {
        let md = <Metadata<Link<M>> as FromSpec<MetadataAsLink<M>>>::from_spec(self);
        <Metadata<Link<M>> as Repr<MetaSlot>>::from_to_repr(md, perm);
        assert(<MetadataAsLink<M> as FromSpec<Metadata<Link<M>>>>::from_spec(md) == self);
    }

    proof fn to_from_repr(r: MetaSlot, perm: MetadataInnerPerms) {
        let md = <Metadata<Link<M>> as Repr<MetaSlot>>::from_repr_spec(r, perm);
        <Metadata<Link<M>> as Repr<MetaSlot>>::to_from_repr(r, perm);
        assert(<Metadata<Link<M>> as FromSpec<MetadataAsLink<M>>>::from_spec(
            <MetadataAsLink<M> as FromSpec<Metadata<Link<M>>>>::from_spec(md),
        ) == md);
    }

    proof fn to_repr_wf(self, perm: MetadataInnerPerms) {
        let md = <Metadata<Link<M>> as FromSpec<MetadataAsLink<M>>>::from_spec(self);
        <Metadata<Link<M>> as Repr<MetaSlot>>::to_repr_wf(md, perm);
        <Metadata<Link<M>> as Repr<MetaSlot>>::from_to_repr(md, perm);
    }

}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> FromSpecImpl<Metadata<Link<M>>> for MetadataAsLink<M> {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(m: Metadata<Link<M>>) -> MetadataAsLink<M> {
        MetadataAsLink {
            metadata: m.metadata.meta,
            next: match m.metadata.next {
                Some(repr_ptr) => Some(repr_ptr.ptr),
                None => None,
            },
            prev: match m.metadata.prev {
                Some(repr_ptr) => Some(repr_ptr.ptr),
                None => None,
            },
            ref_count: m.ref_count,
            vtable_ptr: m.vtable_ptr,
            in_list: m.in_list,
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> From<Metadata<Link<M>>> for MetadataAsLink<M> {
    fn from(m: Metadata<Link<M>>) -> Self {
        let next = match m.metadata.next {
            Some(repr_ptr) => Some(repr_ptr.ptr),
            None => None,
        };
        let prev = match m.metadata.prev {
            Some(repr_ptr) => Some(repr_ptr.ptr),
            None => None,
        };
        MetadataAsLink {
            metadata: m.metadata.meta,
            next,
            prev,
            ref_count: m.ref_count,
            vtable_ptr: m.vtable_ptr,
            in_list: m.in_list,
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> FromSpecImpl<MetadataAsLink<M>> for Metadata<Link<M>> {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(m: MetadataAsLink<M>) -> Metadata<Link<M>> {
        Metadata {
            metadata: Link {
                next: match m.next {
                    Some(pptr) => Some(ReprPtr { ptr: pptr, _T: PhantomData }),
                    None => None,
                },
                prev: match m.prev {
                    Some(pptr) => Some(ReprPtr { ptr: pptr, _T: PhantomData }),
                    None => None,
                },
                meta: m.metadata,
            },
            ref_count: m.ref_count,
            vtable_ptr: m.vtable_ptr,
            in_list: m.in_list,
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> From<MetadataAsLink<M>> for Metadata<Link<M>> {
    fn from(m: MetadataAsLink<M>) -> Self {
        let next = match m.next {
            Some(pptr) => Some(ReprPtr { ptr: pptr, _T: PhantomData }),
            None => None,
        };
        let prev = match m.prev {
            Some(pptr) => Some(ReprPtr { ptr: pptr, _T: PhantomData }),
            None => None,
        };
        Metadata {
            metadata: Link { next, prev, meta: m.metadata },
            ref_count: m.ref_count,
            vtable_ptr: m.vtable_ptr,
            in_list: m.in_list,
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> MetadataAsLink<M> {
    pub fn cast_to_metadata(ptr: ReprPtr<MetaSlot, Self>) -> (res: ReprPtr<MetaSlot, Metadata<Link<M>>>)
        ensures
            res.addr() == ptr.addr(),
            res.ptr == ptr.ptr,
    {
        ReprPtr { ptr: ptr.ptr, _T: PhantomData }
    }

    pub fn cast_from_metadata(ptr: ReprPtr<MetaSlot, Metadata<Link<M>>>) -> (res: ReprPtr<MetaSlot, Self>)
        ensures
            res.addr() == ptr.addr(),
            res.ptr == ptr.ptr,
    {
        ReprPtr { ptr: ptr.ptr, _T: PhantomData }
    }

}

} // verus!
