use vstd::atomic::*;
use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use super::meta_owners::{
    MetaSlotModel, MetaSlotOwner, MetaSlotStatus, MetaSlotStorage, Metadata, PageUsage,
};
use crate::mm::frame::meta::{
    REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
    mapping::{
        frame_to_index, frame_to_meta, frame_to_meta_spec, index_to_frame,
        lemma_paddr_to_meta_biinjective, meta_addr, meta_to_frame_spec,
    },
};
use crate::mm::frame::*;
use crate::mm::kspace::FRAME_METADATA_RANGE;
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::MetadataInnerPerms;
use crate::specs::mm::frame::meta_region_owners::{MetaRegionModel, MetaRegionOwners};

use core::marker::PhantomData;

verus! {

impl MetaSlot {
    /// A helper function that casts a `MetaSlot` pointer to a `Metadata` pointer of type `M`.
    #[verus_spec(res =>
        with
            Tracked(perm): Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>,
        requires
            perm.value() == self,
            addr == perm.addr(),
        ensures
            res.ptr.addr() == addr,
            res.addr() == addr,
    )]
    pub fn cast_slot<M: AnyFrameMeta + Repr<MetaSlotStorage>>(&self, addr: usize) -> ReprPtr<
        MetaSlot,
        Metadata<M>,
    > {
        ReprPtr::<MetaSlot, Metadata<M>> { ptr: PPtr::from_addr(addr), _T: PhantomData }
    }

    pub open spec fn get_from_unused_inner_perms_spec(
        as_unique: bool,
        perms: MetadataInnerPerms,
    ) -> bool {
        &&& perms.ref_count.value() == (if as_unique {
            REF_COUNT_UNIQUE as u64
        } else {
            1u64
        })
        &&& perms.in_list.value() == 0
        &&& perms.storage.is_init()
        &&& perms.vtable_ptr.is_init()
    }

    /// The `slot_owners`/`obligations` transition of claiming an unused slot,
    /// *agnostic to where the extracted slot perm ends up*. Says nothing about
    /// `regions.slots` — callers pin the permission location separately with
    /// [`slot_perm_extracted_spec`] (perm handed out, slot removed) or
    /// [`slot_perm_reparked_spec`] (perm re-parked, domain preserved).
    pub open spec fn get_from_unused_spec(
        paddr: Paddr,
        as_unique: bool,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
            pre.inv(),
    {
        let idx = frame_to_index(paddr);
        {
            &&& post.slot_owners.dom() =~= pre.slot_owners.dom()
            &&& MetaSlot::get_from_unused_inner_perms_spec(
                as_unique,
                post.slot_owners[idx].inner_perms,
            )
            &&& post.slot_owners[idx].usage == PageUsage::Frame
            &&& post.slot_owners[idx].self_addr == pre.slot_owners[idx].self_addr
            &&& post.slot_owners[idx].paths_in_pt == pre.slot_owners[idx].paths_in_pt
            &&& forall|i: usize| i != idx ==> (#[trigger] post.slot_owners[i] == pre.slot_owners[i])
            &&& pre.slot_owners[idx].inner_perms.ref_count.value()
                == REF_COUNT_UNUSED
            // Linear-drop pilot: claiming an unused slot doesn't mint or
            // redeem segment obligations.

        }
    }

    /// Variant of [`get_from_unused_spec`] for allocating a page-table *node*
    /// (always non-unique). Identical except the claimed slot becomes
    /// `PageUsage::PageTable` rather than `PageUsage::Frame`: a page-table
    /// node is tracked with `PageTable` usage, which gives a clean
    /// usage-based discriminator between node slots and data-frame slots
    /// (the latter are `Frame`/MMIO). Used by the node allocators
    /// (`PageTableNode::alloc`, `PageTable::empty_with_owner`).
    pub open spec fn get_node_from_unused_spec(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
            pre.inv(),
    {
        let idx = frame_to_index(paddr);
        {
            &&& post.slot_owners.dom() =~= pre.slot_owners.dom()
            &&& MetaSlot::get_from_unused_inner_perms_spec(false, post.slot_owners[idx].inner_perms)
            &&& post.slot_owners[idx].usage == PageUsage::PageTable
            &&& post.slot_owners[idx].self_addr == pre.slot_owners[idx].self_addr
            &&& post.slot_owners[idx].paths_in_pt == pre.slot_owners[idx].paths_in_pt
            &&& forall|i: usize| i != idx ==> (#[trigger] post.slot_owners[i] == pre.slot_owners[i])
            &&& pre.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNUSED
        }
    }

    /// Permission-location clause: the slot perm was *extracted* (handed back to
    /// the caller via an out-param), so `regions.slots` loses it. Pairs with
    /// [`get_from_unused_spec`] to describe [`crate::mm::frame::MetaSlot::get_from_unused`].
    pub open spec fn slot_perm_extracted_spec(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool {
        post.slots =~= pre.slots.remove(frame_to_index(paddr))
    }

    /// Permission-location clause: the extracted slot perm was *re-parked* into
    /// `regions.slots`, so the domain is preserved and every other slot's perm
    /// is untouched. Callers that re-park (see
    /// [`crate::mm::frame::Frame::from_unused`] — it hands the perm back via the
    /// `perm` out-param and re-inserts it) pair this with [`get_from_unused_spec`]
    /// (the `slot_owners` transition) to fully describe the Design-B post-state.
    pub open spec fn slot_perm_reparked_spec(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool {
        let idx = frame_to_index(paddr);
        &&& post.slots.dom() =~= pre.slots.dom()
        &&& forall|k: usize|
            #![trigger post.slots[k]]
            k != idx && pre.slots.contains_key(k) ==> post.slots[k] == pre.slots[k]
    }

    /// Obligation-ledger effect of producing a fresh live `Frame` handle on
    /// success (e.g. [`crate::mm::frame::Frame::from_unused`] or
    /// [`crate::mm::frame::Frame::from_in_use`]): the segment `obligations`
    /// ledger is untouched, and the new handle mints its pending-Drop entry in
    /// `frame_obligations` at `paddr`.
    pub open spec fn live_frame_obligations_ok_spec(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool {
        &&& post.frame_obligations =~= pre.frame_obligations.insert(frame_to_index(paddr))
    }

    /// Obligation-ledger effect on failure: both the segment and frame ledgers
    /// are left untouched.
    pub open spec fn live_frame_obligations_err_spec(
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool {
        &&& post.frame_obligations =~= pre.frame_obligations
    }

    pub open spec fn get_from_unused_perm_spec<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        paddr: Paddr,
        metadata: M,
        as_unique: bool,
        ptr: PPtr<MetaSlot>,
        perm: simple_pptr::PointsTo<MetaSlot>,
    ) -> bool {
        &&& ptr.addr() == frame_to_meta(paddr)
        &&& perm.addr() == frame_to_meta(paddr)
        &&& perm.is_init()
        &&& perm.pptr() == ptr
    }

    pub open spec fn inc_ref_count_panic_cond(rc_perm: PermissionU64) -> bool {
        rc_perm.value() >= REF_COUNT_MAX
    }

    pub open spec fn frame_paddr_safety_cond(perm: vstd::simple_pptr::PointsTo<MetaSlot>) -> bool {
        &&& FRAME_METADATA_RANGE.start <= perm.addr() < FRAME_METADATA_RANGE.end
        &&& perm.addr() % META_SLOT_SIZE == 0
    }

    pub open spec fn get_from_in_use_panic_cond(paddr: Paddr, regions: MetaRegionOwners) -> bool {
        let idx = frame_to_index(paddr);
        let pre_perms = regions.slot_owners[idx].inner_perms.ref_count.value();
        pre_perms + 1 >= REF_COUNT_MAX
    }

    pub open spec fn get_from_in_use_success(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
            pre.inv(),
    {
        let idx = frame_to_index(paddr);
        let pre_perms = pre.slot_owners[idx].inner_perms.ref_count.value();
        {
            &&& post.slot_owners[idx].inner_perms.ref_count.value() == pre_perms + 1
            &&& post.slot_owners[idx].inner_perms.ref_count.id()
                == pre.slot_owners[idx].inner_perms.ref_count.id()
            &&& post.slot_owners[idx].inner_perms.storage
                == pre.slot_owners[idx].inner_perms.storage
            &&& post.slot_owners[idx].inner_perms.vtable_ptr
                == pre.slot_owners[idx].inner_perms.vtable_ptr
            &&& post.slot_owners[idx].inner_perms.in_list
                == pre.slot_owners[idx].inner_perms.in_list
            &&& post.slot_owners[idx].self_addr == pre.slot_owners[idx].self_addr
            &&& post.slot_owners[idx].usage == pre.slot_owners[idx].usage
            &&& post.slot_owners[idx].paths_in_pt == pre.slot_owners[idx].paths_in_pt
            &&& forall|i: usize| i != idx ==> (#[trigger] post.slot_owners[i] == pre.slot_owners[i])
        }
    }

    pub open spec fn drop_last_in_place_safety_cond(owner: MetaSlotOwner) -> bool {
        &&& (owner.inner_perms.ref_count.value() == 0 || owner.inner_perms.ref_count.value()
            == REF_COUNT_UNIQUE)
        &&& owner.inner_perms.storage.is_init()
        &&& owner.inner_perms.in_list.value()
            == 0
        // The slot is torn down to `REF_COUNT_UNUSED`; the strengthened
        // `MetaSlotOwner::inv` UNUSED branch requires an empty
        // `paths_in_pt`, and `drop_last_in_place` does not touch
        // `paths_in_pt`, so it must already be empty. Sound: a slot at
        // the teardown point has no live PTE mapping (a mapping is a
        // reference — it would keep the count above the teardown
        // threshold).
        &&& owner.paths_in_pt.is_empty()
    }

    pub open spec fn inc_ref_count_spec(&self, pre: MetaSlotModel) -> (MetaSlotModel)
        recommends
            pre.inv(),
            pre.status == MetaSlotStatus::SHARED,
    {
        MetaSlotModel { ref_count: (pre.ref_count + 1) as u64, ..pre }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Frame<M> {
    pub open spec fn from_raw_spec(paddr: Paddr) -> Self {
        Frame::<M> {
            ptr: PPtr::<MetaSlot>(frame_to_meta(paddr), PhantomData),
            _marker: PhantomData,
        }
    }
}

/// Index round-trip: the slot index recovered from a slot's metadata address
/// is the original index. Callers holding `ptr.addr() == meta_addr(slot_index)`
/// (via [`crate::mm::frame::unique::UniqueFrame::wf`]) use this to re-derive
/// region facts phrased over `frame_to_index(meta_to_frame(ptr.addr))` at
/// `slot_index` (e.g. recovering `ref_count == REF_COUNT_UNIQUE` from
/// `global_inv`).
pub broadcast proof fn lemma_meta_addr_to_index(i: usize)
    requires
        i < MAX_NR_PAGES,
    ensures
        #[trigger] frame_to_index(meta_to_frame_spec(meta_addr(i))) == i,
{
    assert(MAX_NR_PAGES == 0x80000 && PAGE_SIZE == 4096 && MAX_PADDR == 0x8000_0000
        && META_SLOT_SIZE == 64) by (compute_only);

    let p = index_to_frame(i);
    assert(i * PAGE_SIZE < MAX_PADDR) by (nonlinear_arith)
        requires
            i < 0x80000,
            PAGE_SIZE == 4096,
            MAX_PADDR == 0x8000_0000,
    ;
    assert(p == i * PAGE_SIZE);
    assert(p % PAGE_SIZE == 0) by (nonlinear_arith)
        requires
            p == i * PAGE_SIZE,
            PAGE_SIZE == 4096,
    ;
    assert(p / PAGE_SIZE == i) by (nonlinear_arith)
        requires
            p == i * PAGE_SIZE,
            PAGE_SIZE == 4096,
    ;
    // `meta_addr(i)` is exactly the metadata address of physical page `p`.
    assert(meta_addr(i) == frame_to_meta_spec(p));
    // Existing biinjectivity closes `meta_to_frame(frame_to_meta(p)) == p`.
    lemma_paddr_to_meta_biinjective(p);
    assert(meta_to_frame_spec(meta_addr(i)) == p);
    assert(frame_to_index(p) == i);
}

} // verus!
