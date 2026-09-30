//! Flat ownership model for page tables.
//!
//! The model does not recursively own child node resources. A node entry
//! records only the physical address of its child;
//! the corresponding linear resources live in `FlatPageTableOwner::nodes`.
use core::{marker::PhantomData, ops::Range};
use vstd::prelude::*;
use vstd_extra::{array_ptr, ghost_tree::TreePath, ownership::*};

use crate::mm::frame::meta::{
    META_SLOT_SIZE, REF_COUNT_MAX, REF_COUNT_UNUSED, mapping::meta_to_frame,
};
use crate::mm::kspace::{FRAME_METADATA_RANGE, LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR};
use crate::mm::page_prop::PageProperty;
use crate::mm::page_table::{PageTableConfig, PageTableEntryTrait, PageTableGuard};
use crate::mm::{Paddr, PagingLevel, Vaddr, paddr_to_vaddr, page_size};
use crate::specs::arch::{MAX_PADDR, NR_ENTRIES, NR_LEVELS, PAGE_SIZE, valid_frame_paddr};
use crate::specs::mm::frame::mapping::{frame_to_index, index_to_meta, max_meta_slots};
use crate::specs::mm::frame::{
    meta_owners::{FracMetadataPerm, PageUsage, typed_meta_wf},
    meta_region_owners::MetaRegionOwners,
};
use crate::specs::mm::page_table::node::entry_owners::FrameEntryOwner;
use crate::specs::mm::page_table::node::Guards;
use crate::specs::mm::page_table::node::owners::PageMetaOwner;
use crate::specs::mm::page_table::owners::INC_LEVELS;
use crate::specs::mm::page_table::{AbstractVaddr, Mapping, PageTableView, vaddr_of};

verus! {

/// Ownership of one PTE in the flat model. The node variant deliberately
/// contains only an address; its structural resources are stored in the node
/// map.
pub tracked enum FlatEntryOwnerKind<C: PageTableConfig> {
    Node(ghost Paddr),
    Frame(FrameEntryOwner<C>),
    Borrowed(ghost Set<Mapping>),
    Absent,
}

pub tracked struct FlatEntryOwner<C: PageTableConfig> {
    pub kind: FlatEntryOwnerKind<C>,
    pub ghost path: TreePath<NR_ENTRIES>,
    pub ghost parent_level: PagingLevel,
}

impl<C: PageTableConfig> FlatEntryOwner<C> {
    pub open spec fn is_node(self) -> bool {
        self.kind is Node
    }

    pub open spec fn is_frame(self) -> bool {
        self.kind is Frame
    }

    pub open spec fn is_borrowed(self) -> bool {
        self.kind is Borrowed
    }

    pub open spec fn is_absent(self) -> bool {
        self.kind is Absent
    }

    pub open spec fn child_paddr(self) -> Paddr
        recommends
            self.is_node(),
    {
        self.kind->Node_0
    }

    pub open spec fn frame(self) -> FrameEntryOwner<C>
        recommends
            self.is_frame(),
    {
        self.kind->Frame_0
    }

    pub open spec fn borrowed(self) -> Set<Mapping>
        recommends
            self.is_borrowed(),
    {
        self.kind->Borrowed_0
    }

    pub open spec fn frame_permission(self) -> Option<C::Perm>
        recommends
            self.is_frame(),
    {
        self.frame().permission
    }

    pub open spec fn frame_is_tracked(self) -> bool
        recommends
            self.is_frame(),
    {
        self.frame_permission() is Some
    }

    /// Metadata-region facts for the base pages covered by a huge mapping.
    /// This is the flat equivalent of `EntryOwner::frame_sub_pages_valid`;
    /// node metadata is deliberately handled by the node map instead.
    pub open spec fn frame_sub_pages_valid(self, regions: MetaRegionOwners) -> bool {
        self.is_frame() && self.parent_level > 1 ==> {
            let pa = self.frame().mapped_pa;
            let nr_pages = page_size(self.parent_level) / PAGE_SIZE;
            forall|j: usize|
                #![trigger frame_to_index((pa + j * PAGE_SIZE) as usize)]
                0 < j < nr_pages ==> {
                    let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                    &&& regions.slots.contains_key(sub_idx)
                    &&& self.frame_is_tracked() ==> {
                        &&& regions.ref_count(sub_idx) != REF_COUNT_UNUSED
                        &&& 0 < regions.ref_count(sub_idx) <= REF_COUNT_MAX
                    }
                }
        }
    }

    /// Region relation for a leaf entry. A flat node edge contains only a
    /// paddr, so its node-side relation is stated once over the node map.
    pub open spec fn metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        if self.is_frame() {
            let idx = frame_to_index(self.frame().mapped_pa);
            &&& regions.slots.contains_key(idx)
            &&& regions.slots[idx].addr() == index_to_meta(idx)
            &&& regions.slots[idx].is_init()
            &&& regions.slots[idx].value().wf(regions.slot_owners[idx])
            &&& regions.slot_owners[idx].usage !is PageTable
            &&& regions.slot_owners[idx].usage !is MMIO ==> {
                &&& 0 < regions.ref_count(idx) <= REF_COUNT_MAX
            }
            &&& regions.slot_owners[idx].paths_in_pt.contains(self.path)
            &&& self.frame_sub_pages_valid(regions)
            &&& C::perm_well_formed_with_region(
                self.frame().mapped_pa,
                Tracked(self.frame_permission()),
                regions,
            )
        } else {
            true
        }
    }

    pub open spec fn match_pte(self, pte: C::E) -> bool {
        &&& valid_frame_paddr(pte.paddr())
        &&& !pte.is_present() ==> {
            &&& self.is_absent()
            &&& self.parent_level > 1 ==> !pte.is_last(self.parent_level)
        }
        &&& pte.is_present() && !pte.is_last(self.parent_level) ==> {
            &&& self.is_node()
            &&& self.child_paddr() == pte.paddr()
        }
        &&& pte.is_present() && pte.is_last(self.parent_level) ==> {
            &&& self.is_frame()
            &&& self.frame().mapped_pa == pte.paddr()
            &&& self.frame().prop == pte.prop()
        }
    }

    pub open spec fn borrowed_match_pte(self, pte: C::E) -> bool {
        &&& self.is_borrowed()
        &&& valid_frame_paddr(pte.paddr())
        &&& pte.is_present()
        &&& !pte.is_last(self.parent_level)
    }

    pub open spec fn inv(self) -> bool {
        &&& self.path.inv()
        &&& 1 <= self.parent_level <= NR_LEVELS
        &&& self.is_node() ==> {
            &&& 1 < self.parent_level
            &&& valid_frame_paddr(self.child_paddr())
        }
        &&& self.is_frame() ==> {
            &&& self.parent_level < NR_LEVELS
            &&& valid_frame_paddr(self.frame().mapped_pa)
            &&& self.frame().mapped_pa % page_size(self.parent_level) == 0
            &&& self.frame().mapped_pa + page_size(self.parent_level) <= MAX_PADDR
            &&& C::raw_item_well_formed(
                (
                    self.frame().mapped_pa,
                    self.parent_level,
                    self.frame().prop,
                    Tracked(self.frame_permission()),
                ),
            )
            &&& C::E::new_page_req(self.frame().mapped_pa, self.parent_level, self.frame().prop)
        }
    }

    pub open spec fn new_absent(path: TreePath<NR_ENTRIES>, parent_level: PagingLevel) -> Self {
        Self { kind: FlatEntryOwnerKind::Absent, path, parent_level }
    }

    pub proof fn tracked_new_absent(
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
    ) -> (tracked result: Self)
        returns
            Self::new_absent(path, parent_level),
    {
        Self { kind: FlatEntryOwnerKind::Absent, path, parent_level }
    }

    pub open spec fn new_node(
        child: Paddr,
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
    ) -> Self {
        Self { kind: FlatEntryOwnerKind::Node(child), path, parent_level }
    }

    pub proof fn tracked_new_node(
        child: Paddr,
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
    ) -> (tracked result: Self)
        returns
            Self::new_node(child, path, parent_level),
    {
        Self { kind: FlatEntryOwnerKind::Node(child), path, parent_level }
    }

    pub open spec fn new_frame(
        paddr: Paddr,
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
        prop: PageProperty,
        permission: Option<C::Perm>,
    ) -> Self {
        Self {
            kind: FlatEntryOwnerKind::Frame(FrameEntryOwner { mapped_pa: paddr, prop, permission }),
            path,
            parent_level,
        }
    }

    pub proof fn tracked_new_frame(
        paddr: Paddr,
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
        prop: PageProperty,
        tracked permission: Option<C::Perm>,
    ) -> (tracked result: Self)
        returns
            Self::new_frame(paddr, path, parent_level, prop, permission),
    {
        Self {
            kind: FlatEntryOwnerKind::Frame(FrameEntryOwner { mapped_pa: paddr, prop, permission }),
            path,
            parent_level,
        }
    }
}

/// Structural node ownership is shared by both the flat page-table map and
/// node operations.  It deliberately excludes the metadata permission; live
/// frames own that permission, while raw children park it in the flat map.
pub type FlatNodeOwner<C> = crate::specs::mm::page_table::node::owners::NodeOwner<C>;

/// Linear structural resources and PTE owners for one physical page-table
/// node.  Metadata permission intentionally lives outside this record.
pub tracked struct FlatNodeRecord<C: PageTableConfig> {
    pub node: FlatNodeOwner<C>,
    pub entries: Seq<FlatEntryOwner<C>>,
    pub ghost path: TreePath<NR_ENTRIES>,
}

impl<C: PageTableConfig> FlatNodeRecord<C> {
    pub open spec fn paddr(self) -> Paddr {
        meta_to_frame(self.node.slot_vaddr())
    }

    pub open spec fn relate_guard<'rcu>(self, guard: PageTableGuard<'rcu, C>) -> bool {
        self.node.relate_guard(guard)
    }

    pub open spec fn local_inv(self) -> bool {
        &&& self.node.inv()
        &&& self.path.inv()
        &&& self.entries.len() == NR_ENTRIES
        &&& forall|i: int|
            0 <= i < NR_ENTRIES ==> {
                let entry = #[trigger] self.entries[i];
                let pte = self.node.children_perm.value()[i];
                &&& entry.inv()
                &&& entry.path == self.path.push_tail(i)
                &&& entry.parent_level == self.node.level
                &&& entry.match_pte(pte) || (self.node.level == NR_LEVELS && C::LEADING_BITS_spec()
                    == 0 && entry.borrowed_match_pte(pte))
            }
    }

    /// Structural result of allocating a zero-filled page-table node.
    /// `path` is supplied by the caller, so a fresh node never needs the old
    /// recursive-tree "allocate at empty path, then rebase children" dance.
    pub open spec fn allocated_empty(self, level: PagingLevel, path: TreePath<NR_ENTRIES>) -> bool {
        &&& self.node.inv()
        &&& self.node.level == level
        &&& self.node.tree_level == INC_LEVELS - level - 1
        &&& self.path == path
        &&& self.entries.len() == NR_ENTRIES
        &&& forall|i: int|
            0 <= i < NR_ENTRIES ==> {
                let entry = #[trigger] self.entries[i];
                &&& entry.is_absent()
                &&& entry.inv()
                &&& entry.path == path.push_tail(i)
                &&& entry.parent_level == level
                &&& self.node.children_perm.value()[i] == C::E::new_absent_spec()
            }
    }

    pub open spec fn new(
        node: FlatNodeOwner<C>,
        entries: Seq<FlatEntryOwner<C>>,
        path: TreePath<NR_ENTRIES>,
    ) -> Self {
        Self { node, entries, path }
    }

    pub proof fn tracked_new(
        tracked node: FlatNodeOwner<C>,
        tracked entries: Seq<FlatEntryOwner<C>>,
        path: TreePath<NR_ENTRIES>,
    ) -> (tracked result: Self)
        returns
            Self::new(node, entries, path),
    {
        Self { node, entries, path }
    }

    proof fn tracked_new_absent_entries(
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
        len: nat,
    ) -> (tracked entries: Seq<FlatEntryOwner<C>>)
        ensures
            entries.len() == len,
            forall|i: int|
                0 <= i < len ==> {
                    let entry = #[trigger] entries[i];
                    &&& entry.is_absent()
                    &&& entry.path == path.push_tail(i)
                    &&& entry.parent_level == parent_level
                },
        decreases len,
    {
        if len == 0 {
            Seq::tracked_empty()
        } else {
            let tracked mut entries = Self::tracked_new_absent_entries(
                path,
                parent_level,
                (len - 1) as nat,
            );
            let tracked entry = FlatEntryOwner::tracked_new_absent(
                path.push_tail((len - 1) as int),
                parent_level,
            );
            entries.tracked_push(entry);
            entries
        }
    }

    /// Builds the structural record returned by page-table-node allocation.
    /// No recursive owner is created: all PTE slots are represented directly
    /// in this record, and the frame metadata permission remains separate.
    pub proof fn tracked_new_empty(
        tracked node: FlatNodeOwner<C>,
        path: TreePath<NR_ENTRIES>,
    ) -> (tracked result: Self)
        ensures
            result.node == node,
            result.path == path,
            result.entries.len() == NR_ENTRIES,
            forall|i: int|
                0 <= i < NR_ENTRIES ==> {
                    let entry = #[trigger] result.entries[i];
                    &&& entry.is_absent()
                    &&& entry.path == path.push_tail(i)
                    &&& entry.parent_level == node.level
                },
    {
        let ghost parent_level = node.level;
        let tracked entries = Self::tracked_new_absent_entries(
            path,
            parent_level,
            NR_ENTRIES as nat,
        );
        Self { node, entries, path }
    }

    pub open spec fn set_entry(self, idx: int, entry: FlatEntryOwner<C>) -> Self
        recommends
            0 <= idx < self.entries.len(),
    {
        Self { entries: self.entries.update(idx, entry), ..self }
    }

    pub proof fn tracked_borrow_entry<'a>(tracked &'a self, idx: int) -> (tracked entry:
        &'a FlatEntryOwner<C>)
        requires
            0 <= idx < self.entries.len(),
        ensures
            *entry == self.entries[idx],
    {
        self.entries.tracked_borrow(idx)
    }

    pub proof fn tracked_borrow_entry_mut<'a>(tracked &'a mut self, idx: int) -> (tracked entry:
        &'a mut FlatEntryOwner<C>)
        requires
            0 <= idx < old(self).entries.len(),
        ensures
            *entry == old(self).entries[idx],
            *final(self) == old(self).set_entry(idx, *final(entry)),
    {
        self.entries.tracked_borrow_mut(idx)
    }

    pub proof fn tracked_set_entry(tracked &mut self, idx: int, tracked entry: FlatEntryOwner<C>)
        requires
            0 <= idx < old(self).entries.len(),
        ensures
            *final(self) == old(self).set_entry(idx, entry),
    {
        let tracked slot = self.entries.tracked_borrow_mut(idx);
        *slot = entry;
    }

    /// Replaces one absent flat entry with a frame owner.  The caller updates
    /// `node.children_perm` through the actual PTE write; keeping that linear
    /// array permission in `node` avoids recreating recursive child ownership.
    pub proof fn tracked_set_absent_entry_to_frame(
        tracked &mut self,
        idx: int,
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
        tracked permission: Option<C::Perm>,
    )
        requires
            0 <= idx < old(self).entries.len(),
            old(self).entries[idx].is_absent(),
            old(self).entries[idx].parent_level == level,
        ensures
            final(self).node == old(self).node,
            final(self).path == old(self).path,
            final(self).entries == old(self).entries.update(
                idx,
                FlatEntryOwner::new_frame(
                    paddr,
                    old(self).entries[idx].path,
                    level,
                    prop,
                    permission,
                ),
            ),
    {
        let ghost path = self.entries[idx].path;
        let tracked entry = FlatEntryOwner::tracked_new_frame(paddr, path, level, prop, permission);
        self.tracked_set_entry(idx, entry);
    }
}

/// Flat authoritative ownership of one page table.
pub tracked struct FlatPageTableOwner<C: PageTableConfig> {
    pub ghost root: Paddr,
    pub nodes: Map<Paddr, FlatNodeRecord<C>>,
    /// Full metadata permissions parked for nodes currently held raw in PTEs.
    /// The root is deliberately absent: its live `Frame` owns that permission.
    pub raw_node_permissions: Map<Paddr, FracMetadataPerm>,
}

/// Stable borrow of a raw node.  The two references originate from separate
/// maps, so clients can inspect structural ownership without moving either
/// resource.
pub tracked struct FlatRawNodeRef<'a, C: PageTableConfig> {
    pub record: &'a FlatNodeRecord<C>,
    pub permission: &'a FracMetadataPerm,
}

/// Mutable structural access paired with an immutable, stable metadata
/// permission.  Guard creation borrows `permission`; node operations mutate
/// only `record`.
pub tracked struct FlatRawNodeMut<'a, C: PageTableConfig> {
    pub record: &'a mut FlatNodeRecord<C>,
    pub permission: &'a FracMetadataPerm,
}

/// The not-yet-leased portion of the two authoritative resource maps.
///
/// This value is consumed when one node is leased.  The returned remainder
/// retains the original lifetime, so a cursor can repeatedly split disjoint
/// nodes while previously returned leases stay alive.
pub tracked struct FlatOwnerPartition<'a, C: PageTableConfig> {
    pub nodes: &'a mut Map<Paddr, FlatNodeRecord<C>>,
    pub permissions: &'a mut Map<Paddr, FracMetadataPerm>,
}

/// Resources for one raw page-table node split out of a flat partition.
/// `permission` may be borrowed for the lifetime of a `FrameRef`, while
/// `record` remains independently mutable for PTE and metadata bookkeeping.
pub tracked struct FlatRawNodeLease<'a, C: PageTableConfig> {
    pub ghost paddr: Paddr,
    pub record: &'a mut FlatNodeRecord<C>,
    pub permission: &'a FracMetadataPerm,
}

/// Structural lease for the root node.  Its metadata permission remains in
/// the live root `Frame`, so unlike a raw child lease this contains no
/// `FracMetadataPerm`.
pub tracked struct FlatRootNodeLease<'a, C: PageTableConfig> {
    pub ghost paddr: Paddr,
    pub record: &'a mut FlatNodeRecord<C>,
}

/// Cursor-local ownership of raw nodes.
///
/// A node moves from `remainder` to `leases` at most once.  Moving the lease
/// value itself is harmless: both references still point into the stable flat
/// maps, so a `FrameRef<'a, _>` can keep borrowing its metadata permission
/// while the cursor mutates other, disjoint node records.
pub tracked struct FlatCursorResources<'a, C: PageTableConfig> {
    pub root: FlatRootNodeLease<'a, C>,
    pub remainder: FlatOwnerPartition<'a, C>,
    pub leases: Map<Paddr, FlatRawNodeLease<'a, C>>,
}

/// One level of a flat cursor path.  It identifies the node by physical
/// address; ownership of the node itself remains in `FlatCursorResources`.
pub ghost struct FlatCursorContinuation<'rcu, C: PageTableConfig> {
    pub ghost node: Paddr,
    pub ghost idx: usize,
    pub ghost path: TreePath<NR_ENTRIES>,
    pub ghost level: PagingLevel,
    pub ghost guard: PageTableGuard<'rcu, C>,
}

/// One borrow-free level of long-lived cursor navigation state.
pub ghost struct FlatCursorStateContinuation {
    pub ghost node: Paddr,
    pub ghost idx: usize,
    pub ghost path: TreePath<NR_ENTRIES>,
    pub ghost level: PagingLevel,
}

/// Borrow-free cursor state used by long-lived logical stores.
///
/// The executable cursor may outlive an individual proof step, but a global
/// owner store cannot contain a `FlatCursorOwner` that borrows another field
/// of the same store.  This projection keeps only navigation state;
/// linear node resources remain in the authoritative `FlatPageTableOwner` and
/// guards and resources are borrowed by `FlatCursorOwner` only while an
/// operation is in progress.
pub ghost struct FlatCursorState<C: PageTableConfig> {
    pub ghost continuations: Map<int, FlatCursorStateContinuation>,
    pub ghost root: Paddr,
    pub ghost level: PagingLevel,
    pub ghost guard_level: PagingLevel,
    pub ghost va: AbstractVaddr,
    pub ghost prefix: AbstractVaddr,
    pub ghost popped_too_high: bool,
    pub ghost phantom: PhantomData<C>,
}

/// Cursor ownership after the recursive tree has been removed.
///
/// `continuations` contains navigation state only.  Linear node resources and
/// raw metadata permissions are addressed through `resources` by paddr.
pub tracked struct FlatCursorOwner<'a, 'rcu, C: PageTableConfig> {
    pub resources: FlatCursorResources<'a, C>,
    pub ghost continuations: Map<int, FlatCursorContinuation<'rcu, C>>,
    pub ghost root: Paddr,
    pub ghost level: PagingLevel,
    pub ghost guard_level: PagingLevel,
    /// Logical cursor position.  Keeping this beside the flat path avoids
    /// rebuilding an owning tree merely to recover the current PTE index.
    pub ghost va: AbstractVaddr,
    /// Start of the locked page-table chunk.  This is navigation state only;
    /// all linear node resources remain in `resources`.
    pub ghost prefix: AbstractVaddr,
    pub ghost popped_too_high: bool,
}

impl<'a, C: PageTableConfig> FlatOwnerPartition<'a, C> {
    pub open spec fn contains_raw_node(self, paddr: Paddr) -> bool {
        self.nodes.contains_key(paddr) && self.permissions.contains_key(paddr)
    }

    /// Splits one raw node out of the partition.  Unlike borrowing directly
    /// from the full maps, this freezes only the selected slots; `remainder`
    /// can still be mutated or split again while `lease` is alive.
    pub proof fn tracked_lease_raw_node(tracked self, paddr: Paddr) -> (tracked (lease, remainder):
        (FlatRawNodeLease<'a, C>, FlatOwnerPartition<'a, C>))
        requires
            self.contains_raw_node(paddr),
        ensures
            lease.paddr == paddr,
            *lease.record == (*old(self.nodes))[paddr],
            *lease.permission == (*old(self.permissions))[paddr],
            *remainder.nodes == old(self.nodes).remove_keys(set![paddr]),
            *remainder.permissions == old(self.permissions).remove_keys(set![paddr]),
    {
        let ghost key = set![paddr];
        let tracked (node_slot, nodes) = self.nodes.tracked_borrow_mut_split(key);
        let tracked (permission_slot, permissions) = self.permissions.tracked_borrow_mut_split(key);
        let tracked record = node_slot.tracked_borrow_mut(paddr);
        let tracked permission = permission_slot.tracked_borrow(paddr);
        (FlatRawNodeLease { paddr, record, permission }, FlatOwnerPartition { nodes, permissions })
    }

    pub proof fn tracked_insert_raw_node(
        tracked &mut self,
        paddr: Paddr,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    )
        requires
            !old(self).nodes.contains_key(paddr),
            !old(self).permissions.contains_key(paddr),
            record.paddr() == paddr,
            permission.frac() == 1,
            record.node.permission_matches(permission),
        ensures
            *final(self).nodes == old(self).nodes.insert(paddr, record),
            *final(self).permissions == old(self).permissions.insert(paddr, permission),
    {
        self.nodes.tracked_insert(paddr, record);
        self.permissions.tracked_insert(paddr, permission);
    }

    /// Inserts a freshly converted raw node and immediately splits it out as
    /// a stable lease.  Allocation paths need this combined operation: the
    /// returned `PageTableNodeRef` borrows the permission for `'a`, while the
    /// remainder must stay available for later cursor descents/allocations.
    pub proof fn tracked_insert_and_lease_raw_node(
        tracked self,
        paddr: Paddr,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    ) -> (tracked (lease, remainder): (FlatRawNodeLease<'a, C>, FlatOwnerPartition<'a, C>))
        requires
            !self.nodes.contains_key(paddr),
            !self.permissions.contains_key(paddr),
            record.paddr() == paddr,
            permission.frac() == 1,
            record.node.permission_matches(permission),
        ensures
            lease.paddr == paddr,
            *lease.record == record,
            *lease.permission == permission,
            *remainder.nodes == *old(self.nodes),
            *remainder.permissions == *old(self.permissions),
    {
        self.nodes.tracked_insert(paddr, record);
        self.permissions.tracked_insert(paddr, permission);
        self.tracked_lease_raw_node(paddr)
    }
}

impl<'a, C: PageTableConfig> FlatRawNodeLease<'a, C> {
    pub open spec fn node(self) -> FlatNodeOwner<C> {
        self.record.node
    }

    pub open spec fn entry(self, idx: int) -> FlatEntryOwner<C>
        recommends
            0 <= idx < self.record.entries.len(),
    {
        self.record.entries[idx]
    }

    pub proof fn tracked_borrow_entry(tracked &self, idx: int) -> (tracked entry: &FlatEntryOwner<
        C,
    >)
        requires
            0 <= idx < self.record.entries.len(),
        ensures
            *entry == self.entry(idx),
    {
        self.record.tracked_borrow_entry(idx)
    }

    pub proof fn tracked_borrow_entry_mut(tracked &mut self, idx: int) -> (tracked entry:
        &mut FlatEntryOwner<C>)
        requires
            0 <= idx < old(self).record.entries.len(),
        ensures
            *entry == old(self).entry(idx),
            final(self).paddr == old(self).paddr,
            *final(self).permission == *old(self).permission,
            *final(self).record == old(self).record.set_entry(idx, *final(entry)),
    {
        self.record.tracked_borrow_entry_mut(idx)
    }
}

impl<'a, C: PageTableConfig> FlatCursorResources<'a, C> {
    /// Reassembles a read-only logical view of the authoritative node map.
    /// This does not move any resource: every value is read through the
    /// stable references held by the root lease, raw leases, and remainder.
    pub open spec fn node_map(self) -> Map<Paddr, FlatNodeRecord<C>> {
        (*self.remainder.nodes).union_prefer_right(
            self.leases.map_values(|lease: FlatRawNodeLease<'a, C>| *lease.record),
        ).insert(self.root.paddr, *self.root.record)
    }

    pub open spec fn permission_map(self) -> Map<Paddr, FracMetadataPerm> {
        (*self.remainder.permissions).union_prefer_right(
            self.leases.map_values(|lease: FlatRawNodeLease<'a, C>| *lease.permission),
        )
    }

    pub open spec fn owner_view(self) -> FlatPageTableOwner<C> {
        FlatPageTableOwner {
            root: self.root.paddr,
            nodes: self.node_map(),
            raw_node_permissions: self.permission_map(),
        }
    }

    pub open spec fn contains_leased(self, paddr: Paddr) -> bool {
        self.root.paddr == paddr || self.leases.contains_key(paddr)
    }

    pub open spec fn contains_raw_leased(self, paddr: Paddr) -> bool {
        self.leases.contains_key(paddr)
    }

    pub open spec fn contains_unleased(self, paddr: Paddr) -> bool {
        self.remainder.contains_raw_node(paddr)
    }

    pub open spec fn inv(self) -> bool {
        &&& self.root.record.paddr() == self.root.paddr
        &&& self.root.record.local_inv()
        &&& !self.leases.contains_key(self.root.paddr)
        &&& !self.remainder.nodes.contains_key(self.root.paddr)
        &&& !self.remainder.permissions.contains_key(self.root.paddr)
        &&& self.remainder.nodes.dom() == self.remainder.permissions.dom()
        &&& self.leases.dom().disjoint(self.remainder.nodes.dom())
        &&& forall|paddr: Paddr| #[trigger]
            self.remainder.nodes.contains_key(paddr) ==> {
                &&& (*self.remainder.nodes)[paddr].paddr() == paddr
                &&& (*self.remainder.nodes)[paddr].local_inv()
                &&& (*self.remainder.permissions)[paddr].frac() == 1
                &&& (*self.remainder.nodes)[paddr].node.permission_matches(
                    (*self.remainder.permissions)[paddr],
                )
            }
        &&& forall|paddr: Paddr| #[trigger]
            self.leases.contains_key(paddr) ==> {
                let lease = self.leases[paddr];
                &&& lease.paddr == paddr
                &&& lease.record.paddr() == paddr
                &&& lease.record.local_inv()
                &&& lease.permission.frac() == 1
                &&& lease.record.node.permission_matches(*lease.permission)
            }
    }

    pub proof fn tracked_new(
        tracked remainder: FlatOwnerPartition<'a, C>,
        root: Paddr,
    ) -> (tracked result: Self)
        requires
            remainder.nodes.contains_key(root),
            !remainder.permissions.contains_key(root),
        ensures
            result.root.paddr == root,
            *result.root.record == (*old(remainder.nodes))[root],
            result.leases =~= Map::empty(),
            *result.remainder.nodes == old(remainder.nodes).remove_keys(set![root]),
            *result.remainder.permissions == *old(remainder.permissions),
    {
        let tracked FlatOwnerPartition { nodes, permissions } = remainder;
        let tracked (root_slot, nodes) = nodes.tracked_borrow_mut_split(set![root]);
        let tracked record = root_slot.tracked_borrow_mut(root);
        Self {
            root: FlatRootNodeLease { paddr: root, record },
            remainder: FlatOwnerPartition { nodes, permissions },
            leases: Map::tracked_empty(),
        }
    }

    /// Leases a node on first visit.  Already leased nodes are looked up by
    /// paddr through `tracked_borrow_permission`/`tracked_borrow_record_mut`;
    /// they are never removed and reinserted while cursor guards are alive.
    pub proof fn tracked_lease_node(tracked self, paddr: Paddr) -> (tracked result: Self)
        requires
            self.contains_unleased(paddr),
            !self.contains_leased(paddr),
        ensures
            result.contains_leased(paddr),
            result.leases.dom() == self.leases.dom().insert(paddr),
            *result.remainder.nodes == old(self.remainder.nodes).remove_keys(set![paddr]),
            *result.remainder.permissions == old(self.remainder.permissions).remove_keys(
                set![paddr],
            ),
            result.owner_view() == self.owner_view(),
    {
        let tracked Self { root, remainder, mut leases } = self;
        let tracked (lease, remainder) = remainder.tracked_lease_raw_node(paddr);
        leases.tracked_insert(paddr, lease);
        Self { root, remainder, leases }
    }

    /// Leases an existing raw node and returns the stable metadata-permission
    /// reference needed to construct its `FrameRef`.
    pub proof fn tracked_lease_node_with_permission(tracked self, paddr: Paddr) -> (tracked (
        result,
        permission,
    ): (Self, &'a FracMetadataPerm))
        requires
            self.contains_unleased(paddr),
            !self.contains_leased(paddr),
        ensures
            result.contains_raw_leased(paddr),
            result.leases.dom() == self.leases.dom().insert(paddr),
            *result.remainder.nodes == old(self.remainder.nodes).remove_keys(set![paddr]),
            *result.remainder.permissions == old(self.remainder.permissions).remove_keys(
                set![paddr],
            ),
            *permission == *result.leases[paddr].permission,
            result.owner_view() == self.owner_view(),
    {
        let tracked result = self.tracked_lease_node(paddr);
        let tracked permission = result.tracked_borrow_permission(paddr);
        (result, permission)
    }

    /// Parks a newly allocated node's metadata permission in the flat store
    /// and retains a lease for the guard returned by the allocation path.
    pub proof fn tracked_insert_and_lease_node(
        tracked self,
        paddr: Paddr,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    ) -> (tracked result: Self)
        requires
            !self.contains_leased(paddr),
            !self.contains_unleased(paddr),
            record.paddr() == paddr,
            permission.frac() == 1,
            record.node.permission_matches(permission),
        ensures
            result.contains_leased(paddr),
            result.leases.dom() == self.leases.dom().insert(paddr),
            *result.remainder.nodes == *old(self.remainder.nodes),
            *result.remainder.permissions == *old(self.remainder.permissions),
    {
        let tracked Self { root, remainder, mut leases } = self;
        let tracked (lease, remainder) = remainder.tracked_insert_and_lease_raw_node(
            paddr,
            record,
            permission,
        );
        leases.tracked_insert(paddr, lease);
        Self { root, remainder, leases }
    }

    /// Variant used by guard construction.  The returned reference points
    /// into the authoritative permission map (lifetime `'a`), rather than
    /// borrowing the returned cursor-resource wrapper.
    pub proof fn tracked_insert_and_lease_node_with_permission(
        tracked self,
        paddr: Paddr,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    ) -> (tracked (result, stable_permission): (Self, &'a FracMetadataPerm))
        requires
            !self.contains_leased(paddr),
            !self.contains_unleased(paddr),
            record.paddr() == paddr,
            permission.frac() == 1,
            record.node.permission_matches(permission),
        ensures
            result.contains_leased(paddr),
            result.leases.dom() == self.leases.dom().insert(paddr),
            *result.remainder.nodes == *old(self.remainder.nodes),
            *result.remainder.permissions == *old(self.remainder.permissions),
            *stable_permission == *result.leases[paddr].permission,
    {
        let tracked result = self.tracked_insert_and_lease_node(paddr, record, permission);
        let tracked stable_permission = result.tracked_borrow_permission(paddr);
        (result, stable_permission)
    }

    /// Installs a freshly converted raw child in one atomic tracked step:
    /// the parent PTE owner stores only the child's paddr, while the child's
    /// structural record and metadata permission enter the flat maps.
    pub proof fn tracked_attach_and_lease_child(
        tracked self,
        parent: Paddr,
        idx: int,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    ) -> (tracked result: Self)
        requires
            self.contains_leased(parent),
            0 <= idx < self.leased_record(parent).entries.len(),
            self.leased_record(parent).entries[idx].is_absent(),
            !self.contains_leased(record.paddr()),
            !self.contains_unleased(record.paddr()),
            permission.frac() == 1,
            record.node.permission_matches(permission),
            record.path == self.leased_record(parent).entries[idx].path,
            record.node.level + 1 == self.leased_record(parent).entries[idx].parent_level,
        ensures
            result.contains_leased(parent),
            result.contains_raw_leased(record.paddr()),
            result.leased_record(parent).entries[idx].is_node(),
            result.leased_record(parent).entries[idx].child_paddr() == record.paddr(),
            result.leased_record(parent).entries[idx].path == self.leased_record(
                parent,
            ).entries[idx].path,
            result.leased_record(parent).entries[idx].parent_level == self.leased_record(
                parent,
            ).entries[idx].parent_level,
    {
        let ghost child = record.paddr();
        let ghost old_entry = self.leased_record(parent).entries[idx];
        let tracked mut this = self;
        let tracked child_entry = FlatEntryOwner::tracked_new_node(
            child,
            old_entry.path,
            old_entry.parent_level,
        );
        {
            let tracked parent_record = this.tracked_borrow_record_mut(parent);
            parent_record.tracked_set_entry(idx, child_entry);
        }
        this.tracked_insert_and_lease_node(child, record, permission)
    }

    /// Replaces an existing entry (not necessarily absent) with a freshly
    /// allocated raw child.  Huge-page splitting uses this operation: the old
    /// frame entry is consumed and the new node is parked in the flat maps in
    /// the same tracked transition.
    pub proof fn tracked_replace_and_lease_child(
        tracked self,
        parent: Paddr,
        idx: int,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    ) -> (tracked result: Self)
        requires
            self.contains_leased(parent),
            0 <= idx < self.leased_record(parent).entries.len(),
            !self.contains_leased(record.paddr()),
            !self.contains_unleased(record.paddr()),
            permission.frac() == 1,
            record.node.permission_matches(permission),
            record.path == self.leased_record(parent).entries[idx].path,
            record.node.level + 1 == self.leased_record(parent).entries[idx].parent_level,
        ensures
            result.contains_leased(parent),
            result.contains_raw_leased(record.paddr()),
            result.leased_record(parent).entries[idx].is_node(),
            result.leased_record(parent).entries[idx].child_paddr() == record.paddr(),
            result.leased_record(parent).entries[idx].path == self.leased_record(
                parent,
            ).entries[idx].path,
            result.leased_record(parent).entries[idx].parent_level == self.leased_record(
                parent,
            ).entries[idx].parent_level,
    {
        let ghost child = record.paddr();
        let ghost old_entry = self.leased_record(parent).entries[idx];
        let tracked mut this = self;
        let tracked child_entry = FlatEntryOwner::tracked_new_node(
            child,
            old_entry.path,
            old_entry.parent_level,
        );
        {
            let tracked parent_record = this.tracked_borrow_record_mut(parent);
            parent_record.tracked_set_entry(idx, child_entry);
        }
        this.tracked_insert_and_lease_node(child, record, permission)
    }

    pub proof fn tracked_borrow_permission(tracked &self, paddr: Paddr) -> (tracked permission:
        &'a FracMetadataPerm)
        requires
            self.contains_raw_leased(paddr),
        ensures
            *permission == *self.leases[paddr].permission,
    {
        let tracked lease = self.leases.tracked_borrow(paddr);
        lease.permission
    }

    pub open spec fn leased_record(self, paddr: Paddr) -> FlatNodeRecord<C>
        recommends
            self.contains_leased(paddr),
    {
        if self.root.paddr == paddr {
            *self.root.record
        } else {
            *self.leases[paddr].record
        }
    }

    pub proof fn tracked_borrow_record_mut<'b>(
        tracked &'b mut self,
        paddr: Paddr,
    ) -> (tracked record: &'b mut FlatNodeRecord<C>)
        requires
            old(self).contains_leased(paddr),
        ensures
            *record == old(self).leased_record(paddr),
            final(self).leases.dom() == old(self).leases.dom(),
            *final(self).remainder.nodes == *old(self).remainder.nodes,
            *final(self).remainder.permissions == *old(self).remainder.permissions,
    {
        if self.root.paddr == paddr {
            &mut *self.root.record
        } else {
            let tracked lease = self.leases.tracked_borrow_mut(paddr);
            &mut *lease.record
        }
    }

    pub proof fn tracked_borrow_record<'b>(tracked &'b self, paddr: Paddr) -> (tracked record:
        &'b FlatNodeRecord<C>)
        requires
            self.contains_leased(paddr),
        ensures
            *record == self.leased_record(paddr),
    {
        if self.root.paddr == paddr {
            &*self.root.record
        } else {
            let tracked lease = self.leases.tracked_borrow(paddr);
            &*lease.record
        }
    }
}

impl<'rcu, C: PageTableConfig> FlatCursorContinuation<'rcu, C> {
    pub open spec fn new(
        node: Paddr,
        idx: usize,
        path: TreePath<NR_ENTRIES>,
        level: PagingLevel,
        guard: PageTableGuard<'rcu, C>,
    ) -> Self {
        Self { node, idx, path, level, guard }
    }
}

impl<C: PageTableConfig> FlatCursorState<C> {
    pub open spec fn is_path_node(self, paddr: Paddr) -> bool {
        exists|key: int|
            self.continuations.contains_key(key) && self.continuations[key].node == paddr
    }

    pub open spec fn current(self) -> FlatCursorStateContinuation
        recommends
            self.continuations.contains_key(self.level - 1),
    {
        self.continuations[self.level - 1]
    }

    pub open spec fn locked_range(self) -> Range<Vaddr> {
        Range {
            start: self.prefix.align_down(self.guard_level as int).to_vaddr(),
            end: self.prefix.align_up(self.guard_level as int).to_vaddr(),
        }
    }

    pub open spec fn in_locked_range(self) -> bool {
        self.locked_range().start <= self.va.to_vaddr() < self.locked_range().end
    }

    pub open spec fn local_inv(self, owner: FlatPageTableOwner<C>) -> bool {
        &&& owner.inv()
        &&& self.root == owner.root
        &&& self.va.inv()
        &&& self.va.offset == 0
        &&& self.prefix.inv()
        &&& self.prefix.offset == 0
        &&& self.va.leading_bits == C::LEADING_BITS_spec()
        &&& self.prefix.leading_bits == C::LEADING_BITS_spec()
        &&& 1 <= self.level <= self.guard_level <= NR_LEVELS
        &&& forall|key: int| #[trigger]
            self.continuations.contains_key(key) <==> self.level - 1 <= key < self.guard_level
        &&& forall|key: int| #[trigger]
            self.continuations.contains_key(key) ==> {
                let cont = self.continuations[key];
                &&& cont.level == key + 1
                &&& cont.idx < NR_ENTRIES
                &&& cont.path.inv()
                &&& owner.contains_node(cont.node)
                &&& owner.node(cont.node).path == cont.path
                &&& owner.node(cont.node).node.level == cont.level
            }
        &&& self.continuations.contains_key(self.level - 1)
        &&& self.current().idx == self.va.index[self.level - 1]
        &&& forall|child_key: int|
            self.level - 1 <= child_key < self.guard_level - 1 ==> {
                let child = self.continuations[child_key];
                let parent = self.continuations[child_key + 1];
                &&& child.path == parent.path.push_tail(parent.idx as int)
                &&& owner.node(parent.node).entries[parent.idx as int].is_node()
                &&& owner.node(parent.node).entries[parent.idx as int].child_paddr() == child.node
            }
    }

    pub open spec fn nodes_locked(self, owner: FlatPageTableOwner<C>, guards: Guards) -> bool {
        forall|key: int| #[trigger]
            self.continuations.contains_key(key) ==> guards.lock_held(
                owner.node(self.continuations[key].node).node.slot_vaddr(),
            )
    }

    pub open spec fn children_not_locked(
        self,
        owner: FlatPageTableOwner<C>,
        guards: Guards,
    ) -> bool {
        forall|paddr: Paddr| #[trigger]
            owner.contains_node(paddr) && !self.is_path_node(paddr)
                ==> guards.unlocked(owner.node(paddr).node.slot_vaddr())
    }
}

impl<'a, 'rcu, C: PageTableConfig> FlatCursorOwner<'a, 'rcu, C> {
    pub open spec fn state(self) -> FlatCursorState<C> {
        FlatCursorState {
            continuations: self.continuations.map_values(
                |cont: FlatCursorContinuation<'rcu, C>| FlatCursorStateContinuation {
                    node: cont.node,
                    idx: cont.idx,
                    path: cont.path,
                    level: cont.level,
                },
            ),
            root: self.root,
            level: self.level,
            guard_level: self.guard_level,
            va: self.va,
            prefix: self.prefix,
            popped_too_high: self.popped_too_high,
            phantom: PhantomData,
        }
    }

    pub open spec fn as_page_table_owner(self) -> FlatPageTableOwner<C> {
        self.resources.owner_view()
    }

    pub open spec fn view_mappings(self) -> Set<Mapping> {
        self.as_page_table_owner().view_rec()
    }

    pub open spec fn metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        self.as_page_table_owner().metaregion_sound(regions)
    }

    pub open spec fn is_path_node(self, paddr: Paddr) -> bool {
        exists|key: int|
            self.continuations.contains_key(key) && self.continuations[key].node == paddr
    }

    /// Every continuation whose runtime guard is retained by the cursor is
    /// represented by one lock-ledger entry.  Leased records outside the
    /// current path are intentionally excluded.
    pub open spec fn nodes_locked(self, guards: Guards) -> bool {
        forall|key: int| #[trigger]
            self.continuations.contains_key(key) ==> guards.lock_held(
                self.resources.leased_record(self.continuations[key].node).node.slot_vaddr(),
            )
    }

    /// Flat counterpart of the recursive model's `children_not_locked`:
    /// records not selected by a continuation are off the active path.
    pub open spec fn children_not_locked(self, guards: Guards) -> bool {
        forall|paddr: Paddr| #[trigger]
            self.as_page_table_owner().contains_node(paddr) && !self.is_path_node(paddr)
                ==> guards.unlocked(self.as_page_table_owner().node(paddr).node.slot_vaddr())
    }

    /// During descent the child named by the current PTE may already be
    /// locked before it is installed as a continuation; all other off-path
    /// records remain unlocked.
    pub open spec fn only_current_locked(self, guards: Guards) -> bool {
        forall|paddr: Paddr| #[trigger]
            self.as_page_table_owner().contains_node(paddr) && !self.is_path_node(paddr)
                && (!self.current_entry().is_node()
                    || self.current_entry().child_paddr() != paddr)
                ==> guards.unlocked(self.as_page_table_owner().node(paddr).node.slot_vaddr())
    }

    pub open spec fn locked_range(self) -> Range<Vaddr> {
        Range {
            start: self.prefix.align_down(self.guard_level as int).to_vaddr(),
            end: self.prefix.align_up(self.guard_level as int).to_vaddr(),
        }
    }

    pub open spec fn in_locked_range(self) -> bool {
        self.locked_range().start <= self.va.to_vaddr() < self.locked_range().end
    }

    pub open spec fn above_locked_range(self) -> bool {
        self.va.to_vaddr() >= self.locked_range().end
    }

    pub open spec fn continuation_inv(self, key: int) -> bool
        recommends
            self.continuations.contains_key(key),
    {
        let cont = self.continuations[key];
        &&& cont.level == key + 1
        &&& cont.idx < NR_ENTRIES
        &&& cont.path.inv()
        &&& self.resources.contains_leased(cont.node)
        &&& self.resources.leased_record(cont.node).path == cont.path
        &&& self.resources.leased_record(cont.node).node.level == cont.level
        &&& self.resources.leased_record(cont.node).node.relate_guard(cont.guard)
        &&& cont.node != self.root ==> {
            &&& self.resources.contains_raw_leased(cont.node)
            &&& **cont.guard.inner.tracked_metadata_perm
                == *self.resources.leases[cont.node].permission
        }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.resources.inv()
        &&& self.resources.root.paddr == self.root
        &&& self.as_page_table_owner().inv()
        &&& self.va.inv()
        &&& self.va.offset == 0
        &&& self.prefix.inv()
        &&& self.prefix.offset == 0
        &&& self.va.leading_bits == C::LEADING_BITS_spec()
        &&& self.prefix.leading_bits == C::LEADING_BITS_spec()
        &&& 1 <= self.level <= self.guard_level <= NR_LEVELS
        &&& forall|key: int| #[trigger]
            self.continuations.contains_key(key) <==> self.level - 1 <= key < self.guard_level
        &&& forall|key: int| #[trigger]
            self.continuations.contains_key(key) ==> self.continuation_inv(key)
        &&& self.continuations.contains_key(self.level - 1)
        &&& self.current().idx == self.va.index[self.level - 1]
        &&& forall|child_key: int|
            self.level - 1 <= child_key < self.guard_level - 1 ==> {
                let child = self.continuations[child_key];
                let parent = self.continuations[child_key + 1];
                let parent_record = self.resources.leased_record(parent.node);
                &&& child.path == parent.path.push_tail(parent.idx as int)
                &&& parent_record.entries[parent.idx as int].is_node()
                &&& parent_record.entries[parent.idx as int].child_paddr() == child.node
            }
    }

    pub open spec fn current(self) -> FlatCursorContinuation<'rcu, C>
        recommends
            self.continuations.contains_key(self.level - 1),
    {
        self.continuations[self.level - 1]
    }

    pub open spec fn current_paddr(self) -> Paddr
        recommends
            self.continuations.contains_key(self.level - 1),
    {
        self.current().node
    }

    pub open spec fn current_record(self) -> FlatNodeRecord<C>
        recommends
            self.continuations.contains_key(self.level - 1),
            self.resources.contains_leased(self.current_paddr()),
    {
        self.resources.leased_record(self.current_paddr())
    }

    pub open spec fn current_entry(self) -> FlatEntryOwner<C>
        recommends
            self.continuations.contains_key(self.level - 1),
            self.resources.contains_leased(self.current_paddr()),
            self.current().idx < self.current_record().entries.len(),
    {
        self.current_record().entries[self.current().idx as int]
    }

    pub open spec fn cur_entry_owner(self) -> FlatEntryOwner<C>
        recommends
            self.continuations.contains_key(self.level - 1),
            self.resources.contains_leased(self.current_paddr()),
            self.current().idx < self.current_record().entries.len(),
    {
        self.current_entry()
    }

    pub open spec fn index(self) -> usize
        recommends
            self.continuations.contains_key(self.level - 1),
    {
        self.current().idx
    }

    pub open spec fn cur_va(self) -> Vaddr {
        self.va.to_vaddr()
    }

    pub open spec fn cur_va_range(self) -> Range<AbstractVaddr> {
        Range {
            start: self.va.align_down(self.level as int),
            end: self.va.align_up(self.level as int),
        }
    }

    pub open spec fn set_va_in_node(self, new_va: AbstractVaddr) -> Self
        recommends
            self.continuations.contains_key(self.level - 1),
    {
        let key = self.level - 1;
        let current = self.continuations[key];
        Self {
            va: new_va,
            continuations: self.continuations.insert(
                key,
                FlatCursorContinuation {
                    idx: new_va.index[key] as usize,
                    ..current
                },
            ),
            popped_too_high: false,
            ..self
        }
    }

    pub proof fn tracked_new(
        tracked resources: FlatCursorResources<'a, C>,
        root: Paddr,
        va: AbstractVaddr,
        path: TreePath<NR_ENTRIES>,
        guard: PageTableGuard<'rcu, C>,
    ) -> (tracked result: Self)
        requires
            resources.inv(),
            resources.root.paddr == root,
            resources.owner_view().inv(),
            resources.root.record.node.level == NR_LEVELS,
            resources.root.record.path == path,
            resources.root.record.node.relate_guard(guard),
            va.inv(),
            va.offset == 0,
            va.leading_bits == C::LEADING_BITS_spec(),
        ensures
            result.inv(),
            result.root == root,
            result.level == NR_LEVELS,
            result.guard_level == NR_LEVELS,
            result.continuations.dom() == set![(NR_LEVELS - 1) as int],
            result.continuations[(NR_LEVELS - 1) as int].node == root,
            result.continuations[(NR_LEVELS - 1) as int].idx == va.index[NR_LEVELS - 1],
            result.continuations[(NR_LEVELS - 1) as int].path == path,
            result.va == va,
            result.prefix == va,
            !result.popped_too_high,
    {
        let ghost idx = va.index[NR_LEVELS - 1] as usize;
        let ghost root_cont = FlatCursorContinuation::new(
            root,
            idx,
            path,
            NR_LEVELS as PagingLevel,
            guard,
        );
        let ghost continuations = Map::empty().insert((NR_LEVELS - 1) as int, root_cont);
        Self {
            resources,
            continuations,
            root,
            level: NR_LEVELS as PagingLevel,
            guard_level: NR_LEVELS as PagingLevel,
            va,
            prefix: va,
            popped_too_high: false,
        }
    }

    pub proof fn tracked_borrow_node_permission(tracked &self, paddr: Paddr) -> (tracked permission:
        &'a FracMetadataPerm)
        requires
            self.resources.contains_raw_leased(paddr),
        ensures
            *permission == *self.resources.leases[paddr].permission,
    {
        self.resources.tracked_borrow_permission(paddr)
    }

    pub proof fn tracked_borrow_node_record_mut<'b>(
        tracked &'b mut self,
        paddr: Paddr,
    ) -> (tracked record: &'b mut FlatNodeRecord<C>)
        requires
            old(self).resources.contains_leased(paddr),
        ensures
            *record == old(self).resources.leased_record(paddr),
            final(self).root == old(self).root,
            final(self).level == old(self).level,
            final(self).guard_level == old(self).guard_level,
            final(self).continuations == old(self).continuations,
    {
        self.resources.tracked_borrow_record_mut(paddr)
    }

    pub proof fn tracked_borrow_current_record_mut<'b>(tracked &'b mut self) -> (tracked record:
        &'b mut FlatNodeRecord<C>)
        requires
            old(self).continuations.contains_key(old(self).level - 1),
            old(self).resources.contains_leased(old(self).current_paddr()),
        ensures
            *record == old(self).current_record(),
            final(self).root == old(self).root,
            final(self).level == old(self).level,
            final(self).guard_level == old(self).guard_level,
            final(self).continuations == old(self).continuations,
    {
        let ghost current = self.current_paddr();
        self.resources.tracked_borrow_record_mut(current)
    }

    pub proof fn tracked_borrow_current_record<'b>(tracked &'b self) -> (tracked record:
        &'b FlatNodeRecord<C>)
        requires
            self.continuations.contains_key(self.level - 1),
            self.resources.contains_leased(self.current_paddr()),
        ensures
            *record == self.current_record(),
    {
        self.resources.tracked_borrow_record(self.current_paddr())
    }

    pub proof fn tracked_borrow_current_entry<'b>(tracked &'b self) -> (tracked entry:
        &'b FlatEntryOwner<C>)
        requires
            self.continuations.contains_key(self.level - 1),
            self.resources.contains_leased(self.current_paddr()),
            self.current().idx < self.current_record().entries.len(),
        ensures
            *entry == self.current_entry(),
    {
        let tracked record = self.tracked_borrow_current_record();
        record.tracked_borrow_entry(self.current().idx as int)
    }

    pub proof fn tracked_borrow_current_entry_mut<'b>(tracked &'b mut self) -> (tracked entry:
        &'b mut FlatEntryOwner<C>)
        requires
            old(self).continuations.contains_key(old(self).level - 1),
            old(self).resources.contains_leased(old(self).current_paddr()),
            old(self).current().idx < old(self).current_record().entries.len(),
        ensures
            *entry == old(self).current_entry(),
            final(self).root == old(self).root,
            final(self).level == old(self).level,
            final(self).guard_level == old(self).guard_level,
            final(self).continuations == old(self).continuations,
    {
        let ghost idx = self.current().idx;
        let tracked record = self.tracked_borrow_current_record_mut();
        record.tracked_borrow_entry_mut(idx as int)
    }

    /// Changes only the navigation index of the current continuation.
    pub proof fn tracked_set_current_index(tracked &mut self, idx: usize)
        requires
            old(self).continuations.contains_key(old(self).level - 1),
            idx < NR_ENTRIES,
        ensures
            final(self).resources == old(self).resources,
            final(self).root == old(self).root,
            final(self).level == old(self).level,
            final(self).guard_level == old(self).guard_level,
            final(self).current().node == old(self).current().node,
            final(self).current().idx == idx,
            final(self).current().path == old(self).current().path,
            final(self).current().level == old(self).current().level,
            final(self).current().guard == old(self).current().guard,
            final(self).va == (AbstractVaddr {
                index: old(self).va.index.insert(old(self).level - 1, idx as int),
                ..old(self).va
            }),
            final(self).prefix == old(self).prefix,
            final(self).popped_too_high == false,
            final(self).as_page_table_owner() == old(self).as_page_table_owner(),
    {
        let ghost key = self.level - 1;
        let ghost current = self.continuations[key];
        let ghost updated = FlatCursorContinuation { idx, ..current };
        self.continuations = self.continuations.insert(key, updated);
        self.va = AbstractVaddr { index: self.va.index.insert(key, idx as int), ..self.va };
        self.popped_too_high = false;
    }

    /// Repositions the cursor inside its current node without touching any
    /// authoritative node or permission slot.
    pub proof fn tracked_set_va_in_node(tracked &mut self, new_va: AbstractVaddr)
        requires
            old(self).continuations.contains_key(old(self).level - 1),
            new_va.inv(),
            new_va.offset == 0,
            new_va.leading_bits == old(self).va.leading_bits,
            0 <= new_va.index[old(self).level - 1] < NR_ENTRIES,
        ensures
            *final(self) == old(self).set_va_in_node(new_va),
            final(self).resources == old(self).resources,
            final(self).as_page_table_owner() == old(self).as_page_table_owner(),
    {
        let ghost key = self.level - 1;
        let ghost current = self.continuations[key];
        let ghost updated = FlatCursorContinuation {
            idx: new_va.index[key] as usize,
            ..current
        };
        self.continuations = self.continuations.insert(key, updated);
        self.va = new_va;
        self.popped_too_high = false;
    }

    /// Pops one navigation level.  Node leases intentionally remain in the
    /// cursor resource set so guards and permission borrows stay stable.
    pub proof fn tracked_pop_level(tracked &mut self)
        requires
            old(self).level < old(self).guard_level,
            old(self).continuations.contains_key(old(self).level - 1),
            old(self).continuations.contains_key(old(self).level as int),
        ensures
            final(self).resources == old(self).resources,
            final(self).root == old(self).root,
            final(self).guard_level == old(self).guard_level,
            final(self).level == old(self).level + 1,
            final(self).continuations == old(self).continuations.remove(old(self).level - 1),
            final(self).va == old(self).va,
            final(self).prefix == old(self).prefix,
            final(self).popped_too_high == old(self).popped_too_high,
            final(self).as_page_table_owner() == old(self).as_page_table_owner(),
    {
        let ghost key = self.level - 1;
        self.continuations = self.continuations.remove(key);
        self.level = (self.level + 1) as PagingLevel;
    }

    /// Commits the subtree root selected by the range-locking phase.  Path
    /// entries above `guard_level` are navigation snapshots only, so they can
    /// be discarded without returning or moving any node lease.
    pub proof fn tracked_set_guard_level(tracked &mut self, guard_level: PagingLevel)
        requires
            old(self).level <= guard_level <= old(self).guard_level,
        ensures
            final(self).resources == old(self).resources,
            final(self).root == old(self).root,
            final(self).level == old(self).level,
            final(self).guard_level == guard_level,
            final(self).continuations == old(self).continuations.remove_keys(
                old(self).continuations.dom().filter(|key: int| guard_level <= key),
            ),
            final(self).va == old(self).va,
            final(self).prefix == old(self).prefix,
            final(self).popped_too_high == old(self).popped_too_high,
            final(self).as_page_table_owner() == old(self).as_page_table_owner(),
    {
        let ghost removed = self.continuations.dom().filter(|key: int| guard_level <= key);
        self.continuations = self.continuations.remove_keys(removed);
        self.guard_level = guard_level;
    }

    /// First half of descending to an existing raw child.  Navigation is
    /// unchanged until the caller has built a guard from `permission`.
    pub proof fn tracked_lease_child_with_permission(tracked self, child: Paddr) -> (tracked (
        result,
        permission,
    ): (Self, &'a FracMetadataPerm))
        requires
            self.continuations.contains_key(self.level - 1),
            self.resources.contains_leased(self.current_paddr()),
            self.current().idx < self.current_record().entries.len(),
            self.current_entry().is_node(),
            self.current_entry().child_paddr() == child,
            self.resources.contains_unleased(child),
            !self.resources.contains_leased(child),
        ensures
            result.root == self.root,
            result.level == self.level,
            result.guard_level == self.guard_level,
            result.continuations == self.continuations,
            result.resources.contains_raw_leased(child),
            *permission == *result.resources.leases[child].permission,
            result.as_page_table_owner() == self.as_page_table_owner(),
    {
        let tracked Self {
            resources,
            continuations,
            root,
            level,
            guard_level,
            va,
            prefix,
            popped_too_high,
        } = self;
        let tracked (resources, permission) = resources.tracked_lease_node_with_permission(child);
        (
            Self {
                resources,
                continuations,
                root,
                level,
                guard_level,
                va,
                prefix,
                popped_too_high,
            },
            permission,
        )
    }

    /// Second half of descent: records navigation only after a guard borrowing
    /// the leased permission has been constructed.
    pub proof fn tracked_push_leased_child(
        tracked self,
        child: Paddr,
        idx: usize,
        path: TreePath<NR_ENTRIES>,
        child_level: PagingLevel,
        guard: PageTableGuard<'rcu, C>,
    ) -> (tracked result: Self)
        requires
            self.continuations.contains_key(self.level - 1),
            self.resources.contains_raw_leased(child),
            self.current().idx < self.current_record().entries.len(),
            self.current_entry().is_node(),
            self.current_entry().child_paddr() == child,
            idx < NR_ENTRIES,
            path == self.current_entry().path,
            child_level + 1 == self.level,
            idx == self.va.index[child_level - 1],
            self.resources.leased_record(child).path == path,
            self.resources.leased_record(child).node.level == child_level,
            self.resources.leased_record(child).node.relate_guard(guard),
            **guard.inner.tracked_metadata_perm == *self.resources.leases[child].permission,
        ensures
            result.root == self.root,
            result.level == child_level,
            result.guard_level == self.guard_level,
            result.resources == self.resources,
            result.continuations.dom() == self.continuations.dom().insert((child_level - 1) as int),
            result.continuations[child_level - 1].node == child,
            result.continuations[child_level - 1].idx == idx,
            result.continuations[child_level - 1].path == path,
            result.continuations[child_level - 1].guard == guard,
            result.va == self.va,
            result.prefix == self.prefix,
            result.popped_too_high == self.popped_too_high,
            result.as_page_table_owner() == self.as_page_table_owner(),
    {
        let tracked Self {
            resources,
            continuations,
            root,
            level: _,
            guard_level,
            va,
            prefix,
            popped_too_high,
        } = self;
        let ghost continuation = FlatCursorContinuation::new(child, idx, path, child_level, guard);
        let ghost continuations = continuations.insert((child_level - 1) as int, continuation);
        Self {
            resources,
            continuations,
            root,
            level: child_level,
            guard_level,
            va,
            prefix,
            popped_too_high,
        }
    }

    pub proof fn tracked_attach_and_lease_child(
        tracked self,
        parent: Paddr,
        idx: int,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    ) -> (tracked result: Self)
        requires
            self.resources.contains_leased(parent),
            0 <= idx < self.resources.leased_record(parent).entries.len(),
            self.resources.leased_record(parent).entries[idx].is_absent(),
            !self.resources.contains_leased(record.paddr()),
            !self.resources.contains_unleased(record.paddr()),
            permission.frac() == 1,
            record.node.permission_matches(permission),
            record.path == self.resources.leased_record(parent).entries[idx].path,
            record.node.level + 1 == self.resources.leased_record(parent).entries[idx].parent_level,
        ensures
            result.root == self.root,
            result.level == self.level,
            result.guard_level == self.guard_level,
            result.continuations == self.continuations,
            result.resources.contains_leased(parent),
            result.resources.contains_raw_leased(record.paddr()),
            result.resources.leased_record(parent).entries[idx].is_node(),
            result.resources.leased_record(parent).entries[idx].child_paddr() == record.paddr(),
    {
        let tracked Self {
            resources,
            continuations,
            root,
            level,
            guard_level,
            va,
            prefix,
            popped_too_high,
        } = self;
        let tracked resources = resources.tracked_attach_and_lease_child(
            parent,
            idx,
            record,
            permission,
        );
        Self {
            resources,
            continuations,
            root,
            level,
            guard_level,
            va,
            prefix,
            popped_too_high,
        }
    }

    /// Attaches a child at the cursor's current entry.  Navigation state is
    /// unchanged; the newly leased child can be pushed as a continuation only
    /// after its runtime guard has been created.
    pub proof fn tracked_attach_current_and_lease_child(
        tracked self,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    ) -> (tracked result: Self)
        requires
            self.continuations.contains_key(self.level - 1),
            self.resources.contains_leased(self.current_paddr()),
            self.current().idx < self.current_record().entries.len(),
            self.current_entry().is_absent(),
            !self.resources.contains_leased(record.paddr()),
            !self.resources.contains_unleased(record.paddr()),
            permission.frac() == 1,
            record.node.permission_matches(permission),
            record.path == self.current_entry().path,
            record.node.level + 1 == self.current_entry().parent_level,
        ensures
            result.root == self.root,
            result.level == self.level,
            result.guard_level == self.guard_level,
            result.continuations == self.continuations,
            result.resources.contains_raw_leased(record.paddr()),
            result.current_entry().is_node(),
            result.current_entry().child_paddr() == record.paddr(),
    {
        let ghost parent = self.current_paddr();
        let ghost idx = self.current().idx;
        self.tracked_attach_and_lease_child(parent, idx as int, record, permission)
    }

    /// Attaches the current child and exposes the stable permission reference
    /// that a `FrameRef<'a, _>` must retain.
    pub proof fn tracked_attach_current_and_lease_child_with_permission(
        tracked self,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    ) -> (tracked (result, stable_permission): (Self, &'a FracMetadataPerm))
        requires
            self.continuations.contains_key(self.level - 1),
            self.resources.contains_leased(self.current_paddr()),
            self.current().idx < self.current_record().entries.len(),
            self.current_entry().is_absent(),
            !self.resources.contains_leased(record.paddr()),
            !self.resources.contains_unleased(record.paddr()),
            permission.frac() == 1,
            record.node.permission_matches(permission),
            record.path == self.current_entry().path,
            record.node.level + 1 == self.current_entry().parent_level,
        ensures
            result.root == self.root,
            result.level == self.level,
            result.guard_level == self.guard_level,
            result.continuations == self.continuations,
            result.resources.contains_raw_leased(record.paddr()),
            result.current_entry().is_node(),
            result.current_entry().child_paddr() == record.paddr(),
            *stable_permission == *result.resources.leases[record.paddr()].permission,
    {
        let ghost child = record.paddr();
        let tracked result = self.tracked_attach_current_and_lease_child(record, permission);
        let tracked stable_permission = result.tracked_borrow_node_permission(child);
        (result, stable_permission)
    }

    /// Huge-page counterpart of `tracked_attach_current_and_lease_child`.
    /// The current frame owner is replaced by the child edge while the new
    /// node and its raw metadata permission are installed in the flat maps.
    pub proof fn tracked_replace_current_and_lease_child_with_permission(
        tracked self,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    ) -> (tracked (result, stable_permission): (Self, &'a FracMetadataPerm))
        requires
            self.continuations.contains_key(self.level - 1),
            self.resources.contains_leased(self.current_paddr()),
            self.current().idx < self.current_record().entries.len(),
            self.current_entry().is_frame(),
            !self.resources.contains_leased(record.paddr()),
            !self.resources.contains_unleased(record.paddr()),
            permission.frac() == 1,
            record.node.permission_matches(permission),
            record.path == self.current_entry().path,
            record.node.level + 1 == self.current_entry().parent_level,
        ensures
            result.root == self.root,
            result.level == self.level,
            result.guard_level == self.guard_level,
            result.continuations == self.continuations,
            result.resources.contains_raw_leased(record.paddr()),
            result.current_entry().is_node(),
            result.current_entry().child_paddr() == record.paddr(),
            *stable_permission == *result.resources.leases[record.paddr()].permission,
    {
        let ghost parent = self.current_paddr();
        let ghost idx = self.current().idx;
        let ghost child = record.paddr();
        let tracked Self {
            resources,
            continuations,
            root,
            level,
            guard_level,
            va,
            prefix,
            popped_too_high,
        } = self;
        let tracked resources = resources.tracked_replace_and_lease_child(
            parent,
            idx as int,
            record,
            permission,
        );
        let tracked result = Self {
            resources,
            continuations,
            root,
            level,
            guard_level,
            va,
            prefix,
            popped_too_high,
        };
        let tracked stable_permission = result.tracked_borrow_node_permission(child);
        (result, stable_permission)
    }
}

impl<C: PageTableConfig> FlatPageTableOwner<C> {
    pub open spec fn new(root: Paddr, record: FlatNodeRecord<C>) -> Self {
        Self { root, nodes: Map::empty().insert(root, record), raw_node_permissions: Map::empty() }
    }

    pub proof fn tracked_new(root: Paddr, tracked record: FlatNodeRecord<C>) -> (tracked result:
        Self)
        returns
            Self::new(root, record),
    {
        let tracked mut nodes = Map::tracked_empty();
        nodes.tracked_insert(root, record);
        Self { root, nodes, raw_node_permissions: Map::tracked_empty() }
    }

    pub open spec fn contains_node(self, paddr: Paddr) -> bool {
        self.nodes.contains_key(paddr)
    }

    pub open spec fn node(self, paddr: Paddr) -> FlatNodeRecord<C>
        recommends
            self.contains_node(paddr),
    {
        self.nodes[paddr]
    }

    /// Mapping view of every entry in one flat node.  Recursion follows
    /// address edges in the map; no linear owner is reconstructed or moved.
    pub open spec fn view_node_children(self, paddr: Paddr, depth: nat) -> Seq<Set<Mapping>>
        decreases depth, 0nat,
    {
        if depth == 0 || !self.contains_node(paddr) {
            Seq::empty()
        } else {
            self.node(paddr).entries.map(
                |_, entry: FlatEntryOwner<C>|
                    if entry.is_frame() {
                        let va = vaddr_of::<C>(entry.path);
                        let size = page_size(entry.parent_level);
                        set![Mapping {
                            va_range: Range { start: va as int, end: va + size },
                            pa_range: Range {
                                start: entry.frame().mapped_pa,
                                end: (entry.frame().mapped_pa + size) as Paddr,
                            },
                            page_size: size,
                            property: entry.frame().prop,
                        }]
                    } else if entry.is_node() {
                        self.view_rec_at(entry.child_paddr(), (depth - 1) as nat)
                    } else {
                        Set::empty()
                    },
            )
        }
    }

    /// Abstract mappings reachable from `paddr` in the flat ownership map.
    pub open spec fn view_rec_at(self, paddr: Paddr, depth: nat) -> Set<Mapping>
        decreases depth, 1nat,
    {
        if depth == 0 || !self.contains_node(paddr) {
            Set::empty()
        } else {
            self.view_node_children(paddr, depth).to_set().flatten()
        }
    }

    pub open spec fn view_rec(self) -> Set<Mapping> {
        self.view_rec_at(self.root, NR_LEVELS as nat)
    }

    pub open spec fn local_node_inv(self, paddr: Paddr) -> bool {
        &&& self.contains_node(paddr)
        &&& self.node(paddr).paddr() == paddr
        &&& self.node(paddr).local_inv()
        &&& forall|i: int|
            0 <= i < NR_ENTRIES ==> {
                let entry = #[trigger] self.node(paddr).entries[i];
                entry.is_node() ==> {
                    &&& self.contains_node(entry.child_paddr())
                    &&& self.raw_node_permissions.contains_key(entry.child_paddr())
                    &&& self.node(entry.child_paddr()).path == entry.path
                    &&& self.node(entry.child_paddr()).node.level + 1 == self.node(paddr).node.level
                }
            }
    }

    /// Paging level decreases on every node edge, bounding recursion.
    pub open spec fn subtree_inv_at(self, paddr: Paddr, depth: nat) -> bool
        decreases depth,
    {
        &&& self.local_node_inv(paddr)
        &&& self.node(paddr).node.level == depth
        &&& if depth == 0 {
            false
        } else {
            forall|i: int|
                0 <= i < NR_ENTRIES ==> {
                    let entry = #[trigger] self.node(paddr).entries[i];
                    entry.is_node() ==> self.subtree_inv_at(entry.child_paddr(), (depth - 1) as nat)
                }
        }
    }

    pub open spec fn reachable_from(self, from: Paddr, target: Paddr, depth: nat) -> bool
        decreases depth,
    {
        from == target || (depth > 0 && self.contains_node(from) && exists|i: int|
            0 <= i < NR_ENTRIES && {
                let entry = #[trigger] self.node(from).entries[i];
                entry.is_node() && self.reachable_from(
                    entry.child_paddr(),
                    target,
                    (depth - 1) as nat,
                )
            })
    }

    pub open spec fn unique_parent(self) -> bool {
        forall|parent1: Paddr, parent2: Paddr, i: int, j: int|
            self.contains_node(parent1) && self.contains_node(parent2) && 0 <= i < NR_ENTRIES && 0
                <= j < NR_ENTRIES && (#[trigger] self.node(parent1).entries[i]).is_node() && (
            #[trigger] self.node(parent2).entries[j]).is_node() && self.node(
                parent1,
            ).entries[i].child_paddr() == self.node(parent2).entries[j].child_paddr() ==> parent1
                == parent2 && i == j
    }

    pub open spec fn root_has_no_parent(self) -> bool {
        forall|parent: Paddr, i: int|
            self.contains_node(parent) && 0 <= i < NR_ENTRIES && (#[trigger] self.node(
                parent,
            ).entries[i]).is_node() ==> self.node(parent).entries[i].child_paddr() != self.root
    }

    pub open spec fn all_nodes_reachable(self) -> bool {
        forall|paddr: Paddr| #[trigger]
            self.contains_node(paddr) ==> self.reachable_from(self.root, paddr, NR_LEVELS as nat)
    }

    pub open spec fn subtree_nodes(self, root: Paddr) -> Set<Paddr> {
        self.nodes.dom().filter(|paddr: Paddr| self.reachable_from(root, paddr, NR_LEVELS as nat))
    }

    pub open spec fn raw_nodes_metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        forall|paddr: Paddr| #[trigger]
            self.raw_node_permissions.contains_key(paddr) ==> {
                &&& self.contains_node(paddr)
                &&& self.node(paddr).node.metaregion_sound(
                    self.raw_node_permissions[paddr],
                    regions,
                )
            }
    }

    /// Region facts common to live-root and raw child nodes. Metadata
    /// permission ownership is intentionally absent here: the live root keeps
    /// it in its `Frame`, while raw children are covered separately below.
    pub open spec fn nodes_metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        forall|paddr: Paddr| #[trigger]
            self.contains_node(paddr) ==> {
                let record = self.node(paddr);
                let idx = record.node.slot_index;
                &&& regions.ref_count(idx) != REF_COUNT_UNUSED
                &&& 0 < regions.ref_count(idx) <= REF_COUNT_MAX
                &&& regions.slot_owners[idx].slot_vaddr == record.node.slot_vaddr()
                &&& regions.slots[idx].value().wf(regions.slot_owners[idx])
                &&& regions.slot_owners[idx].paths_in_pt == set![record.path]
                &&& record.node.metaregion_sound_node(regions)
            }
    }

    pub open spec fn entries_metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        forall|paddr: Paddr, idx: int|
            self.contains_node(paddr) && 0 <= idx < NR_ENTRIES ==> #[trigger]
                self.node(paddr).entries[idx].metaregion_sound(regions)
    }

    pub open spec fn metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        &&& self.nodes_metaregion_sound(regions)
        &&& self.raw_nodes_metaregion_sound(regions)
        &&& self.entries_metaregion_sound(regions)
    }

    pub open spec fn inv(self) -> bool {
        &&& self.contains_node(self.root)
        &&& self.raw_node_permissions.dom() == self.nodes.dom().remove(self.root)
        &&& forall|paddr: Paddr| #[trigger]
            self.raw_node_permissions.contains_key(paddr) ==> {
                &&& self.raw_node_permissions[paddr].frac() == 1
                &&& self.node(paddr).node.permission_matches(self.raw_node_permissions[paddr])
            }
        &&& self.node(self.root).path == TreePath::<NR_ENTRIES>::new(Seq::empty())
        &&& self.subtree_inv_at(self.root, NR_LEVELS as nat)
        &&& self.unique_parent()
        &&& self.root_has_no_parent()
        &&& self.all_nodes_reachable()
    }

    pub proof fn tracked_borrow_node<'a>(tracked &'a self, paddr: Paddr) -> (tracked node:
        &'a FlatNodeRecord<C>)
        requires
            self.contains_node(paddr),
        ensures
            *node == self.node(paddr),
    {
        self.nodes.tracked_borrow(paddr)
    }

    pub proof fn tracked_borrow_entry<'a>(
        tracked &'a self,
        paddr: Paddr,
        idx: int,
    ) -> (tracked entry: &'a FlatEntryOwner<C>)
        requires
            self.contains_node(paddr),
            0 <= idx < self.node(paddr).entries.len(),
        ensures
            *entry == self.node(paddr).entries[idx],
    {
        self.nodes.tracked_borrow(paddr).tracked_borrow_entry(idx)
    }

    pub proof fn tracked_borrow_raw_node_permission<'a>(
        tracked &'a self,
        paddr: Paddr,
    ) -> (tracked permission: &'a FracMetadataPerm)
        requires
            self.raw_node_permissions.contains_key(paddr),
        ensures
            *permission == self.raw_node_permissions[paddr],
    {
        self.raw_node_permissions.tracked_borrow(paddr)
    }

    pub proof fn tracked_borrow_raw_node<'a>(tracked &'a self, paddr: Paddr) -> (tracked raw_node:
        FlatRawNodeRef<'a, C>)
        requires
            self.contains_node(paddr),
            self.raw_node_permissions.contains_key(paddr),
        ensures
            *raw_node.record == self.node(paddr),
            *raw_node.permission == self.raw_node_permissions[paddr],
    {
        let tracked record = self.nodes.tracked_borrow(paddr);
        let tracked permission = self.raw_node_permissions.tracked_borrow(paddr);
        FlatRawNodeRef { record, permission }
    }

    pub proof fn tracked_borrow_raw_node_mut<'a>(
        tracked &'a mut self,
        paddr: Paddr,
    ) -> (tracked raw_node: FlatRawNodeMut<'a, C>)
        requires
            old(self).contains_node(paddr),
            old(self).raw_node_permissions.contains_key(paddr),
        ensures
            *raw_node.record == old(self).node(paddr),
            *raw_node.permission == old(self).raw_node_permissions[paddr],
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.insert(paddr, *final(raw_node.record)),
            final(self).raw_node_permissions == old(self).raw_node_permissions,
    {
        let tracked record = self.nodes.tracked_borrow_mut(paddr);
        let tracked permission = self.raw_node_permissions.tracked_borrow(paddr);
        FlatRawNodeMut { record, permission }
    }

    /// Borrows both authoritative maps as a consumable partition.  Leases
    /// produced from this partition are disjoint and do not move their
    /// `FlatNodeRecord`s.
    pub proof fn tracked_partition<'a>(tracked &'a mut self) -> (tracked partition:
        FlatOwnerPartition<'a, C>)
        ensures
            *partition.nodes == old(self).nodes,
            *partition.permissions == old(self).raw_node_permissions,
            final(self).root == old(self).root,
            final(self).nodes == *final(partition.nodes),
            final(self).raw_node_permissions == *final(partition.permissions),
    {
        FlatOwnerPartition { nodes: &mut self.nodes, permissions: &mut self.raw_node_permissions }
    }

    /// Starts cursor borrowing directly from the authoritative flat owner.
    /// The root record is split out structurally; only non-root raw nodes can
    /// contribute metadata permissions to later leases.
    pub proof fn tracked_cursor_resources<'a>(tracked &'a mut self) -> (tracked resources:
        FlatCursorResources<'a, C>)
        requires
            old(self).inv(),
        ensures
            resources.inv(),
            resources.owner_view() == *old(self),
            resources.root.paddr == old(self).root,
            *resources.root.record == old(self).node(old(self).root),
            resources.leases =~= Map::empty(),
            *resources.remainder.nodes == old(self).nodes.remove_keys(set![old(self).root]),
            *resources.remainder.permissions == old(self).raw_node_permissions,
    {
        let ghost root = self.root;
        let tracked partition = self.tracked_partition();
        FlatCursorResources::tracked_new(partition, root)
    }

    /// Borrows the authoritative flat maps and initializes cursor navigation
    /// at the live root.  The owner-map borrow may outlive the RCU guard; it
    /// only needs to remain valid for at least `'rcu`.
    pub proof fn tracked_cursor_owner<'a: 'rcu, 'rcu>(
        tracked &'a mut self,
        va: AbstractVaddr,
        guard: PageTableGuard<'rcu, C>,
    ) -> (tracked result: FlatCursorOwner<'a, 'rcu, C>)
        requires
            old(self).inv(),
            va.inv(),
            va.offset == 0,
            va.leading_bits == C::LEADING_BITS_spec(),
            old(self).node(old(self).root).node.relate_guard(guard),
        ensures
            result.inv(),
            result.root == old(self).root,
            result.level == NR_LEVELS,
            result.guard_level == NR_LEVELS,
            result.current().node == old(self).root,
            result.current().idx == va.index[NR_LEVELS - 1],
            result.va == va,
            result.prefix == va,
    {
        let ghost root = self.root;
        let ghost path = self.node(root).path;
        let tracked resources = self.tracked_cursor_resources();
        FlatCursorOwner::tracked_new(resources, root, va, path, guard)
    }

    pub proof fn tracked_borrow_subtree<'a>(tracked &'a self, root: Paddr) -> (tracked subtree:
        FlatSubtreeRef<'a, C>)
        requires
            self.contains_node(root),
        ensures
            subtree.root == root,
            *subtree.owner == *self,
    {
        FlatSubtreeRef { owner: self, root }
    }

    /// Borrow a subtree by splitting the flat map. No node record is removed
    /// or moved; the complement remains borrowed in `remainder`.
    pub proof fn tracked_borrow_subtree_mut<'a>(
        tracked &'a mut self,
        root: Paddr,
    ) -> (tracked subtree: FlatSubtreeMut<'a, C>)
        requires
            old(self).contains_node(root),
        ensures
            subtree.root == root,
            *subtree.nodes == old(self).nodes.restrict(old(self).subtree_nodes(root)),
            *subtree.remainder == old(self).nodes.remove_keys(old(self).subtree_nodes(root)),
            *subtree.permissions == old(self).raw_node_permissions.restrict(
                old(self).subtree_nodes(root).remove(old(self).root),
            ),
            *subtree.permission_remainder == old(self).raw_node_permissions.remove_keys(
                old(self).subtree_nodes(root).remove(old(self).root),
            ),
    {
        let ghost keys = self.subtree_nodes(root);
        assert(keys <= self.nodes.dom());
        let ghost permission_keys = keys.remove(self.root);
        assert(permission_keys <= self.raw_node_permissions.dom());
        let tracked (nodes, remainder) = self.nodes.tracked_borrow_mut_split(keys);
        let tracked (permissions, permission_remainder) =
            self.raw_node_permissions.tracked_borrow_mut_split(permission_keys);
        FlatSubtreeMut { nodes, remainder, permissions, permission_remainder, root }
    }

    pub proof fn tracked_insert_node(
        tracked &mut self,
        paddr: Paddr,
        tracked record: FlatNodeRecord<C>,
    )
        requires
            !old(self).contains_node(paddr),
            record.paddr() == paddr,
        ensures
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.insert(paddr, record),
    {
        self.nodes.tracked_insert(paddr, record);
    }

    /// Inserts a node that has just been converted from an owned `Frame` into
    /// a raw child PTE.  The permission transfer is atomic at the model level.
    pub proof fn tracked_insert_raw_node(
        tracked &mut self,
        paddr: Paddr,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    )
        requires
            !old(self).contains_node(paddr),
            !old(self).raw_node_permissions.contains_key(paddr),
            paddr != old(self).root,
            record.paddr() == paddr,
            permission.frac() == 1,
            record.node.permission_matches(permission),
        ensures
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.insert(paddr, record),
            final(self).raw_node_permissions == old(self).raw_node_permissions.insert(
                paddr,
                permission,
            ),
    {
        self.nodes.tracked_insert(paddr, record);
        self.raw_node_permissions.tracked_insert(paddr, permission);
    }

    /// Installs a detached node under `parent[idx]`.  Only one entry in the
    /// parent record and two flat-map slots change; no ancestor or sibling
    /// owner is taken out and reinserted.
    pub proof fn tracked_attach_raw_child(
        tracked &mut self,
        parent: Paddr,
        idx: int,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    )
        requires
            old(self).contains_node(parent),
            0 <= idx < old(self).node(parent).entries.len(),
            old(self).node(parent).entries[idx].is_absent(),
            !old(self).contains_node(record.paddr()),
            !old(self).raw_node_permissions.contains_key(record.paddr()),
            record.paddr() != old(self).root,
            permission.frac() == 1,
            record.node.permission_matches(permission),
        ensures
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.insert(
                parent,
                old(self).node(parent).set_entry(
                    idx,
                    FlatEntryOwner::new_node(
                        record.paddr(),
                        old(self).node(parent).entries[idx].path,
                        old(self).node(parent).entries[idx].parent_level,
                    ),
                ),
            ).insert(record.paddr(), record),
            final(self).raw_node_permissions == old(self).raw_node_permissions.insert(
                record.paddr(),
                permission,
            ),
    {
        let ghost child = record.paddr();
        let ghost old_entry = self.node(parent).entries[idx];
        let tracked edge = FlatEntryOwner::tracked_new_node(
            child,
            old_entry.path,
            old_entry.parent_level,
        );
        {
            let tracked parent_record = self.nodes.tracked_borrow_mut(parent);
            parent_record.tracked_set_entry(idx, edge);
        }
        self.nodes.tracked_insert(child, record);
        self.raw_node_permissions.tracked_insert(child, permission);
    }

    pub proof fn tracked_remove_node(tracked &mut self, paddr: Paddr) -> (tracked record:
        FlatNodeRecord<C>)
        requires
            old(self).contains_node(paddr),
            paddr != old(self).root,
        ensures
            record == old(self).node(paddr),
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.remove(paddr),
    {
        self.nodes.tracked_remove(paddr)
    }

    /// Removes a raw child node and returns both resources needed to rebuild
    /// an owning `Frame` handle.
    pub proof fn tracked_remove_raw_node(tracked &mut self, paddr: Paddr) -> (tracked (
        record,
        permission,
    ): (FlatNodeRecord<C>, FracMetadataPerm))
        requires
            old(self).contains_node(paddr),
            old(self).raw_node_permissions.contains_key(paddr),
            paddr != old(self).root,
        ensures
            record == old(self).node(paddr),
            permission == old(self).raw_node_permissions[paddr],
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.remove(paddr),
            final(self).raw_node_permissions == old(self).raw_node_permissions.remove(paddr),
    {
        let tracked record = self.nodes.tracked_remove(paddr);
        let tracked permission = self.raw_node_permissions.tracked_remove(paddr);
        (record, permission)
    }

    /// Detaches `parent[idx]` and returns the child resources that an owning
    /// `Frame` reconstruction needs.  This is the inverse ownership transfer
    /// of `tracked_attach_raw_child`.
    pub proof fn tracked_detach_raw_child(tracked &mut self, parent: Paddr, idx: int) -> (tracked (
        record,
        permission,
    ): (FlatNodeRecord<C>, FracMetadataPerm))
        requires
            old(self).contains_node(parent),
            0 <= idx < old(self).node(parent).entries.len(),
            old(self).node(parent).entries[idx].is_node(),
            old(self).contains_node(old(self).node(parent).entries[idx].child_paddr()),
            old(self).raw_node_permissions.contains_key(
                old(self).node(parent).entries[idx].child_paddr(),
            ),
            old(self).node(parent).entries[idx].child_paddr() != old(self).root,
        ensures
            record == old(self).node(old(self).node(parent).entries[idx].child_paddr()),
            permission == old(self).raw_node_permissions[old(self).node(
                parent,
            ).entries[idx].child_paddr()],
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.insert(
                parent,
                old(self).node(parent).set_entry(
                    idx,
                    FlatEntryOwner::new_absent(
                        old(self).node(parent).entries[idx].path,
                        old(self).node(parent).entries[idx].parent_level,
                    ),
                ),
            ).remove(old(self).node(parent).entries[idx].child_paddr()),
            final(self).raw_node_permissions == old(self).raw_node_permissions.remove(
                old(self).node(parent).entries[idx].child_paddr(),
            ),
    {
        let ghost old_entry = self.node(parent).entries[idx];
        let ghost child = old_entry.child_paddr();
        let tracked absent = FlatEntryOwner::tracked_new_absent(
            old_entry.path,
            old_entry.parent_level,
        );
        {
            let tracked parent_record = self.nodes.tracked_borrow_mut(parent);
            parent_record.tracked_set_entry(idx, absent);
        }
        let tracked record = self.nodes.tracked_remove(child);
        let tracked permission = self.raw_node_permissions.tracked_remove(child);
        (record, permission)
    }
}

impl<C: PageTableConfig> View for FlatPageTableOwner<C> {
    type V = PageTableView;

    open spec fn view(&self) -> Self::V {
        PageTableView { mappings: self.view_rec() }
    }
}

/// Immutable borrowed subtree: a store reference plus a root address.
pub tracked struct FlatSubtreeRef<'a, C: PageTableConfig> {
    pub owner: &'a FlatPageTableOwner<C>,
    pub ghost root: Paddr,
}

impl<'a, C: PageTableConfig> FlatSubtreeRef<'a, C> {
    pub open spec fn inv(self) -> bool {
        self.owner.contains_node(self.root)
    }

    pub open spec fn record(self) -> FlatNodeRecord<C>
        recommends
            self.inv(),
    {
        self.owner.node(self.root)
    }

    pub open spec fn entry(self, idx: int) -> FlatEntryOwner<C>
        recommends
            self.inv(),
            0 <= idx < NR_ENTRIES,
    {
        self.record().entries[idx]
    }

    pub proof fn tracked_borrow_record(tracked &self) -> (tracked record: &'a FlatNodeRecord<C>)
        requires
            self.inv(),
        ensures
            *record == self.record(),
    {
        self.owner.nodes.tracked_borrow(self.root)
    }

    pub proof fn tracked_borrow_entry(tracked &self, idx: int) -> (tracked entry:
        &'a FlatEntryOwner<C>)
        requires
            self.inv(),
            0 <= idx < self.record().entries.len(),
        ensures
            *entry == self.entry(idx),
    {
        self.owner.nodes.tracked_borrow(self.root).tracked_borrow_entry(idx)
    }

    pub proof fn tracked_child(tracked &self, idx: int) -> (tracked child: FlatSubtreeRef<'a, C>)
        requires
            self.inv(),
            self.owner.local_node_inv(self.root),
            0 <= idx < NR_ENTRIES,
            self.entry(idx).is_node(),
        ensures
            child.inv(),
            child.root == self.entry(idx).child_paddr(),
            *child.owner == *self.owner,
    {
        FlatSubtreeRef { owner: self.owner, root: self.entry(idx).child_paddr() }
    }

    pub proof fn tracked_borrow_raw_root(tracked &self) -> (tracked raw_node: FlatRawNodeRef<'a, C>)
        requires
            self.inv(),
            self.root != self.owner.root,
            self.owner.raw_node_permissions.contains_key(self.root),
        ensures
            *raw_node.record == self.owner.node(self.root),
            *raw_node.permission == self.owner.raw_node_permissions[self.root],
    {
        self.owner.tracked_borrow_raw_node(self.root)
    }
}

/// Mutable borrow of a subtree and the disjoint complement of its node map.
pub tracked struct FlatSubtreeMut<'a, C: PageTableConfig> {
    pub nodes: &'a mut Map<Paddr, FlatNodeRecord<C>>,
    pub remainder: &'a mut Map<Paddr, FlatNodeRecord<C>>,
    pub permissions: &'a mut Map<Paddr, FracMetadataPerm>,
    pub permission_remainder: &'a mut Map<Paddr, FracMetadataPerm>,
    pub ghost root: Paddr,
}

impl<'a, C: PageTableConfig> FlatSubtreeMut<'a, C> {
    pub open spec fn contains_node(self, paddr: Paddr) -> bool {
        self.nodes.contains_key(paddr)
    }

    pub open spec fn record(self, paddr: Paddr) -> FlatNodeRecord<C>
        recommends
            self.contains_node(paddr),
    {
        self.nodes[paddr]
    }

    pub proof fn tracked_borrow_node(tracked &self, paddr: Paddr) -> (tracked node: &FlatNodeRecord<
        C,
    >)
        requires
            self.contains_node(paddr),
        ensures
            *node == self.record(paddr),
    {
        self.nodes.tracked_borrow(paddr)
    }

    pub proof fn tracked_borrow_node_mut(tracked &mut self, paddr: Paddr) -> (tracked node:
        &mut FlatNodeRecord<C>)
        requires
            old(self).contains_node(paddr),
        ensures
            *node == old(self).record(paddr),
            final(self).root == old(self).root,
            *final(self).remainder == *old(self).remainder,
            *final(self).nodes == old(self).nodes.insert(paddr, *final(node)),
    {
        self.nodes.tracked_borrow_mut(paddr)
    }

    pub proof fn tracked_borrow_entry(tracked &self, paddr: Paddr, idx: int) -> (tracked entry:
        &FlatEntryOwner<C>)
        requires
            self.contains_node(paddr),
            0 <= idx < self.record(paddr).entries.len(),
        ensures
            *entry == self.record(paddr).entries[idx],
    {
        self.nodes.tracked_borrow(paddr).tracked_borrow_entry(idx)
    }

    pub proof fn tracked_borrow_entry_mut(
        tracked &mut self,
        paddr: Paddr,
        idx: int,
    ) -> (tracked entry: &mut FlatEntryOwner<C>)
        requires
            old(self).contains_node(paddr),
            0 <= idx < old(self).record(paddr).entries.len(),
        ensures
            *entry == old(self).record(paddr).entries[idx],
            final(self).root == old(self).root,
            *final(self).remainder == *old(self).remainder,
            *final(self).permissions == *old(self).permissions,
            *final(self).permission_remainder == *old(self).permission_remainder,
            *final(self).nodes == old(self).nodes.insert(
                paddr,
                old(self).record(paddr).set_entry(idx, *final(entry)),
            ),
    {
        self.nodes.tracked_borrow_mut(paddr).tracked_borrow_entry_mut(idx)
    }

    pub proof fn tracked_borrow_raw_node_permission(
        tracked &self,
        paddr: Paddr,
    ) -> (tracked permission: &FracMetadataPerm)
        requires
            self.permissions.contains_key(paddr),
        ensures
            *permission == (*old(self.permissions))[paddr],
    {
        self.permissions.tracked_borrow(paddr)
    }

    pub proof fn tracked_borrow_raw_node_mut<'b>(
        tracked &'b mut self,
        paddr: Paddr,
    ) -> (tracked raw_node: FlatRawNodeMut<'b, C>)
        requires
            old(self).contains_node(paddr),
            old(self).permissions.contains_key(paddr),
        ensures
            *raw_node.record == old(self).record(paddr),
            *raw_node.permission == (*old(self.permissions))[paddr],
            final(self).root == old(self).root,
            *final(self).remainder == *old(self).remainder,
            *final(self).permission_remainder == *old(self).permission_remainder,
            *final(self).nodes == old(self).nodes.insert(paddr, *final(raw_node.record)),
            *final(self).permissions == *old(self).permissions,
    {
        let tracked record = self.nodes.tracked_borrow_mut(paddr);
        let tracked permission = self.permissions.tracked_borrow(paddr);
        FlatRawNodeMut { record, permission }
    }
}

} // verus!
