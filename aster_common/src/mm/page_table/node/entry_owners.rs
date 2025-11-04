use vstd::prelude::*;

use vstd::simple_pptr::PointsTo;
use vstd_extra::array_ptr;

use super::*;

verus! {

pub tracked struct EntryOwner<'rcu, C: PageTableConfig> {
    pub node_own: NodeOwner<C>,
    pub guard_perm: Tracked<PointsTo<PageTableGuard<'rcu, C>>>,
    pub children_perm: Option<array_ptr::PointsTo<Entry<'rcu, C>, CONST_NR_ENTRIES>>,
    pub slot_perm: Tracked<PointsTo<MetaSlot>>,
}

impl<'rcu, C: PageTableConfig> Inv for EntryOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& self.guard_perm@.is_init()
        &&& self.guard_perm@.value().inner.inner.ptr == self.slot_perm@.pptr()
        &&& self.guard_perm@.value().inner.inner.wf(self.node_own)
        &&& self.node_own.inv()
        &&& self.slot_perm@.is_init()
        &&& self.slot_perm@.value().storage == self.node_own.meta_perm@.points_to@.pptr()
        &&& self.node_own.meta_perm@.pptr().ptr.0 == self.slot_perm@.value().storage.addr()
        &&& self.node_own.meta_perm@.pptr().addr == self.slot_perm@.value().storage.addr()
        &&& meta_to_frame(self.slot_perm@.addr()) < VMALLOC_BASE_VADDR()
            - LINEAR_MAPPING_BASE_VADDR()
    }
}

impl<'rcu, C: PageTableConfig> EntryOwner<'rcu, C> {
    pub open spec fn relate_slot_owner(self, slot_own: &MetaSlotOwner) -> bool {
        &&& slot_own.inv()
        &&& self.slot_perm@.value().wf(*slot_own)
        &&& self.slot_perm@.addr() == slot_own.self_addr
    }
}

impl<'rcu, C: PageTableConfig> InvView for EntryOwner<'rcu, C> {
    type V = EntryView<C>;

    #[verifier::external_body]
    open spec fn view(self) -> <Self as InvView>::V {
        unimplemented!()
    }

    proof fn view_preserves_inv(self) {
    }
}

impl<'rcu, C: PageTableConfig> OwnerOf for Entry<'rcu, C> {
    type Owner = EntryOwner<'rcu, C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.idx < NR_ENTRIES()
        &&& self.pte.paddr() % PAGE_SIZE() == 0
        &&& self.pte.paddr() < MAX_PADDR()
        &&& self.node == owner.guard_perm@.pptr()
    }
}

} // verus!
