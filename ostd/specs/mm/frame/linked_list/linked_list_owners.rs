use vstd::atomic::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::simple_pptr::*;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::ownership::*;

use super::*;
use crate::mm::frame::{AnyFrameMeta, CursorMut, Link, LinkedList, MetaSlot};
use crate::mm::Paddr;
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::MAX_NR_PAGES;
use crate::specs::mm::frame::mapping::META_SLOT_SIZE;
use crate::specs::mm::frame::meta_owners::MetaSlotStorage;
use crate::specs::mm::frame::meta_owners::Metadata;
use crate::specs::mm::frame::unique::UniqueFrameOwner;

verus! {

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> Repr<MetaSlotStorage> for Link<M> {
    uninterp spec fn wf(r: MetaSlotStorage) -> bool;

    uninterp spec fn to_repr_spec(self) -> MetaSlotStorage;

    #[verifier::external_body]
    fn to_repr(self) -> MetaSlotStorage {
        unimplemented!()
    }

    uninterp spec fn from_repr_spec(r: MetaSlotStorage) -> Self;

    #[verifier::external_body]
    fn from_repr(r: MetaSlotStorage) -> Self {
        unimplemented!()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlotStorage) -> &'a Self {
        unimplemented!()
    }

    proof fn from_to_repr(self)
        ensures
            Self::from_repr(self.to_repr()) == self,
    {
        admit();
    }

    proof fn to_from_repr(r: MetaSlotStorage)
        ensures
            Self::from_repr(r).to_repr() == r,
    {
        admit();
    }

    proof fn to_repr_wf(self)
        ensures
            <Self as Repr<MetaSlotStorage>>::wf(self.to_repr()),
    {
        admit();
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

// TODO: Technically M needs to be smaller than Link<M>, at minimum enough to fit the two pointers
impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> OwnerOf for Link<M> {
    type Owner = LinkOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        true
        //        &&& owner.self_perm@.mem_contents().value() == self
        //        &&& owner.next == self.next
        //        &&& owner.prev == self.prev

    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> ModelOf for Link<M> {

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

pub tracked struct LinkedListOwner<M: AnyFrameMeta + Repr<MetaSlotStorage>> {
    pub list: Seq<LinkOwner>,
    pub perms: Map<int, vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<Link<M>>>>,
    pub list_id: u64,
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> Inv for LinkedListOwner<M> {
    open spec fn inv(self) -> bool {
        forall|i: int| 0 <= i < self.list.len() ==> self.inv_at(i)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> LinkedListOwner<M> {
    pub open spec fn inv_at(self, i: int) -> bool {
        &&& self.perms.contains_key(i)
        &&& self.perms[i].addr() == self.list[i].paddr
        &&& self.perms[i].points_to.addr() == self.list[i].paddr
        &&& self.perms[i].wf()
        &&& self.perms[i].addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= self.perms[i].addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
        &&& self.perms[i].is_init()
        &&& self.perms[i].value().metadata.wf(self.list[i])
        &&& i == 0 <==> self.perms[i].value().metadata.prev is None
        &&& i == self.list.len() - 1 <==> self.perms[i].value().metadata.next is None
        &&& 0 < i ==> {
            &&& self.perms[i].value().metadata.prev is Some
            &&& self.perms[i].value().metadata.prev.unwrap() == self.perms[i - 1].pptr()
        }
        &&& i < self.list.len() - 1 ==> {
            &&& self.perms[i].value().metadata.next is Some
            &&& self.perms[i].value().metadata.next.unwrap() == self.perms[i + 1].pptr()
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
            Self::view_helper(owners.insert(i, v))[j] == Self::view_helper(owners).insert(i, v.view())[j]
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

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> View for LinkedListOwner<M> {
    type V = LinkedListModel;

    open spec fn view(&self) -> Self::V {
        LinkedListModel { list: Self::view_helper(self.list) }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> InvView for LinkedListOwner<M> {
    proof fn view_preserves_inv(self) {
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> OwnerOf for LinkedList<M> {
    type Owner = LinkedListOwner<M>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.front is None <==> owner.list.len() == 0
        &&& self.back is None <==> owner.list.len() == 0
        &&& owner.list.len() > 0 ==> self.front is Some && self.front.unwrap().addr()
            == owner.list[0].paddr && owner.perms[0].pptr() == self.front.unwrap()
            && self.back is Some && self.back.unwrap().addr() == owner.list[owner.list.len()
            - 1].paddr && owner.perms[owner.list.len() - 1].pptr() == self.back.unwrap()
        &&& self.size == owner.list.len()
        &&& self.list_id == owner.list_id
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> ModelOf for LinkedList<M> {

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

pub tracked struct CursorOwner<M: AnyFrameMeta + Repr<MetaSlotStorage>> {
    pub list_own: LinkedListOwner<M>,
    pub list_perm: PointsTo<LinkedList<M>>,
    pub index: int,
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> Inv for CursorOwner<M> {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.index <= self.length()
        &&& self.list_own.inv()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> View for CursorOwner<M> {
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

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> InvView for CursorOwner<M> {
    proof fn view_preserves_inv(self) {
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> OwnerOf for CursorMut<M> {
    type Owner = CursorOwner<M>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& 0 <= owner.index < owner.length() ==> self.current.is_some()
            && self.current.unwrap().addr() == owner.list_own.list[owner.index].paddr
            && owner.list_own.perms[owner.index].pptr() == self.current.unwrap()
        &&& owner.index == owner.list_own.list.len() ==> self.current.is_none()
        &&& owner.list_perm.pptr() == self.list
        &&& owner.list_perm.is_init()
        &&& owner.list_perm.mem_contents().value().wf(owner.list_own)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> ModelOf for CursorMut<M> {

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

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> CursorOwner<M> {
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
            link.paddr == old(link).paddr,
            link.in_list == cursor.list_own.list_id,
            cursor.list_own.list == old(cursor).list_own.list.insert(old(cursor).index, *link),
            cursor.list_own.list_id == old(cursor).list_own.list_id,
            forall|idx: int| 0 <= idx < cursor.length() ==> cursor.list_own.perms.contains_key(idx),
            forall|idx: int|
                0 <= idx < cursor.index ==> cursor.list_own.perms[idx] == old(
                    cursor,
                ).list_own.perms[idx],
            forall|idx: int|
                old(cursor).index < idx <= old(cursor).length() ==> cursor.list_own.perms[idx]
                    == old(cursor).list_own.perms[idx - 1],
            cursor.list_own.perms[old(cursor).index] == perm,
            cursor.index == old(cursor).index + 1,
            cursor.list_perm == old(cursor).list_perm;

    pub open spec fn front_owner_spec(
        list_own: LinkedListOwner<M>,
        list_perm: PointsTo<LinkedList<M>>,
    ) -> Self {
        CursorOwner::<M> { list_own: list_own, list_perm: list_perm, index: 0 }
    }

    pub open spec fn cursor_mut_at_owner_spec(
        list_own: LinkedListOwner<M>,
        list_perm: PointsTo<LinkedList<M>>,
        index: int,
    ) -> Self {
        CursorOwner::<M> { list_own: list_own, list_perm: list_perm, index: index }
    }

    #[verifier::returns(proof)]
    pub axiom fn cursor_mut_at_owner(list_own: LinkedListOwner<M>, list_perm: PointsTo<LinkedList<M>>, index: int) -> Self
        returns Self::cursor_mut_at_owner_spec(list_own, list_perm, index);

    #[verifier::returns(proof)]
    pub axiom fn front_owner(
        list_own: LinkedListOwner<M>,
        list_perm: PointsTo<LinkedList<M>>,
    ) -> (res: Self)
        ensures
            res == Self::front_owner_spec(list_own, list_perm);

    pub open spec fn back_owner_spec(
        list_own: LinkedListOwner<M>,
        list_perm: PointsTo<LinkedList<M>>,
    ) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            list_perm: list_perm,
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
        list_perm: PointsTo<LinkedList<M>>,
    ) -> (res: Self)
        ensures
            res == Self::back_owner_spec(list_own, list_perm),
    {
        CursorOwner::<M> {
            list_own: list_own,
            list_perm: list_perm,
            index: if list_own.list.len() > 0 {
                list_own.list.len() as int - 1
            } else {
                0
            },
        }
    }

    pub open spec fn ghost_owner_spec(
        list_own: LinkedListOwner<M>,
        list_perm: PointsTo<LinkedList<M>>,
    ) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            list_perm: list_perm,
            index: list_own.list.len() as int,
        }
    }

    #[verifier::returns(proof)]
    #[verifier::external_body]
    pub proof fn ghost_owner(
        list_own: LinkedListOwner<M>,
        list_perm: PointsTo<LinkedList<M>>,
    ) -> (res: Self)
        ensures
            res == Self::ghost_owner_spec(list_own, list_perm),
    {
        CursorOwner::<M> {
            list_own: list_own,
            list_perm: list_perm,
            index: list_own.list.len() as int,
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> UniqueFrameOwner<Link<M>> {
    pub open spec fn frame_link_inv(&self) -> bool {
        &&& self.meta_perm.value().metadata.prev is None
        &&& self.meta_perm.value().metadata.next is None
        &&& self.meta_own.paddr == self.meta_perm.addr()
    }
}

} // verus!
